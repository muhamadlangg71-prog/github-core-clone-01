#!/usr/bin/env python3
"""github-core-clone-01: a standalone GitHub-compatible git forge.

One process, Python 3.13 stdlib only. Serves, from its own in-memory store:
  - git smart HTTP (clone and push; protocol v0 and v2, receive-pack)
  - the REST v3 API (repositories, issues, pull requests, contents, git refs)
  - GraphQL v4 (the query/mutation shapes gh and github-mcp-server send)
  - MCP (tools) over JSON-RPC at /mcp (modern 2026-07-28 discover + legacy initialize)

Lifecycle (see starter/main.ts): bind an ephemeral port, POST {"port": N} to
$MAKEFUN_ENV_URL/register, poll GET $MAKEFUN_ENV_URL/done until {"done": true},
then exit 0. Without MAKEFUN_ENV_URL the server still starts on an ephemeral
port and serves (handy for local runs); pass --port N to pick a port.

Auth: any non-empty "Authorization: Bearer <token>" is the viewer
(adaiversen, the scenario's viewer login, derived from the fixed
SCENARIO_SEED 0x6a09e667f3bcc909 — the token does not encode the login).
Missing/empty token -> 401. A repository belongs to the viewer login; the
same name under another owner is 404, never 403.

Determinism: server-created commits use a fixed author/committer and a fixed
timestamp; ids are counters; no wall clock or randomness reaches any stored
state (request ids are a per-process counter).
"""

import base64
import hashlib
import json
import os
import re
import socket
import struct
import sys
import threading
import time
import urllib.request
import urllib.error
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# --------------------------------------------------------------------------------------------
# constants
# --------------------------------------------------------------------------------------------

VIEWER_LOGIN = "adaiversen"          # scenario viewer (SCENARIO_SEED fixed)
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
VIEWER_ID = 1000
ZERO_OID = "0" * 40
FIXED_TS = 1700000000                # fixed timestamp for server-created commits
FORGE_VERSION = "1.0.0"
FORGE_AGENT = "forge/1.0"
JSON_TYPE = "application/json; charset=utf-8"
DEFAULT_BRANCH = "main"
GIT_TYPES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
GIT_TYPE_NAMES = {1: "commit", 2: "tree", 3: "blob", 4: "tag", 6: "ofs-delta", 7: "ref-delta"}

# --------------------------------------------------------------------------------------------
# small utilities
# --------------------------------------------------------------------------------------------

_sha1 = hashlib.sha1


def sha1_hex(data: bytes) -> str:
    return _sha1(data).hexdigest()


def git_hash(obj_type: str, data: bytes) -> str:
    """The git object id: sha1("<type> <len>\\0<data>")."""
    h = _sha1()
    h.update(obj_type.encode("ascii"))
    h.update(b" ")
    h.update(str(len(data)).encode("ascii"))
    h.update(b"\0")
    h.update(data)
    return h.hexdigest()


def b64e(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def b64d(text: str) -> bytes:
    text = "".join(text.split())
    return base64.b64decode(text)


def is_oid(s) -> bool:
    return isinstance(s, str) and len(s) == 40 and all(c in "0123456789abcdef" for c in s.lower())


def json_bytes(obj) -> bytes:
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


# --------------------------------------------------------------------------------------------
# git object model
# --------------------------------------------------------------------------------------------

def parse_tree(data: bytes):
    """-> list of (mode_str, name, oid_hex), in stored order."""
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp].decode("ascii")
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries


def build_tree(entries):
    """entries: list of (mode_str, name, oid_hex). Sorted git-style (dirs as name+'/')."""
    def sort_key(e):
        mode, name, _ = e
        return name + ("/" if mode == "40000" else "")
    out = bytearray()
    for mode, name, oid in sorted(entries, key=sort_key):
        out += mode.encode("ascii") + b" " + name.encode("utf-8", "surrogateescape") + b"\0"
        out += bytes.fromhex(oid)
    return bytes(out)


def parse_commit(data: bytes):
    """-> dict(tree, parents, author, committer, message_bytes)."""
    blank = data.find(b"\n\n")
    if blank < 0:
        head, message = data, b""
    else:
        head, message = data[:blank], data[blank + 2:]
    tree = ""
    parents = []
    author = ""
    committer = ""
    for line in head.decode("utf-8", "surrogateescape").split("\n"):
        if not line:
            continue
        if line.startswith("tree "):
            tree = line[5:].strip()
        elif line.startswith("parent "):
            parents.append(line[7:].strip())
        elif line.startswith("author "):
            author = line[7:]
        elif line.startswith("committer "):
            committer = line[10:]
    return {"tree": tree, "parents": parents, "author": author,
            "committer": committer, "message": message}


def build_commit(tree_oid, parents, message, ts=FIXED_TS):
    ident = "%s <%s> %d +0000" % (VIEWER_NAME, VIEWER_EMAIL, ts)
    lines = ["tree " + tree_oid]
    for p in parents:
        lines.append("parent " + p)
    lines.append("author " + ident)
    lines.append("committer " + ident)
    lines.append("")
    msg = message if message.endswith("\n") else message + "\n"
    # join ends with one "\n" (trailing "" element); add the second so the
    # header/message separator is a blank line ("\n\n")
    return ("\n".join(lines) + "\n" + msg).encode("utf-8")


def parse_tag(data: bytes):
    blank = data.find(b"\n\n")
    head = data if blank < 0 else data[:blank]
    message = b"" if blank < 0 else data[blank + 2:]
    obj = ""
    typ = ""
    tag = ""
    tagger = ""
    for line in head.decode("utf-8", "surrogateescape").split("\n"):
        if line.startswith("object "):
            obj = line[7:].strip()
        elif line.startswith("type "):
            typ = line[5:].strip()
        elif line.startswith("tag "):
            tag = line[4:].strip()
        elif line.startswith("tagger "):
            tagger = line[7:]
    return {"object": obj, "type": typ, "tag": tag, "tagger": tagger, "message": message}


def flatten_tree(objects, tree_oid, prefix=""):
    """-> {path: (mode, oid)} for every blob under tree_oid (recursive)."""
    out = {}
    obj = objects.get(tree_oid)
    if obj is None or obj[0] != "tree":
        return out
    for mode, name, oid in parse_tree(obj[1]):
        path = prefix + name
        if mode == "40000":
            out.update(flatten_tree(objects, oid, path + "/"))
        else:
            out[path] = (mode, oid)
    return out


def tree_from_files(objects, files):
    """files: {path: (mode, blob_oid)}. Builds nested trees bottom-up, stores them.
    Returns the root tree oid."""
    # group by directory
    dirs = {}

    def add(path, mode, oid):
        parts = path.split("/")
        dirs.setdefault(tuple(parts[:-1]), []).append((parts[-1], mode, oid))

    for path, (mode, oid) in files.items():
        add(path, mode, oid)
    # build from the deepest directories up
    memo = {}

    def build(dirpath):
        if dirpath in memo:
            return memo[dirpath]
        entries = []
        for name, mode, oid in dirs.get(dirpath, []):
            entries.append((mode, name, oid))
        # subdirectories of dirpath
        subdirs = sorted({p[len(dirpath)] for p in dirs if len(p) > len(dirpath) and p[:len(dirpath)] == dirpath})
        for sub in subdirs:
            entries.append(("40000", sub, build(dirpath + (sub,))))
        data = build_tree(entries)
        oid = git_hash("tree", data)
        objects[oid] = ("tree", data)
        memo[dirpath] = oid
        return oid

    return build(())


def commit_ancestors(objects, tip):
    """All commit oids reachable from tip (tip inclusive), newest-first BFS."""
    seen = []
    seen_set = set()
    queue = [tip]
    while queue:
        cur = queue.pop(0)
        if cur in seen_set:
            continue
        obj = objects.get(cur)
        if obj is None or obj[0] != "commit":
            continue
        seen_set.add(cur)
        seen.append(cur)
        queue.extend(parse_commit(obj[1])["parents"])
    return seen


def reachable_objects(objects, tips):
    """All object oids reachable from tips (commits, tags, trees, blobs)."""
    out = set()
    stack = list(tips)
    while stack:
        oid = stack.pop()
        if oid in out:
            continue
        obj = objects.get(oid)
        if obj is None:
            continue
        out.add(oid)
        typ, data = obj
        if typ == "commit":
            c = parse_commit(data)
            stack.append(c["tree"])
            stack.extend(c["parents"])
        elif typ == "tree":
            for _, _, child in parse_tree(data):
                stack.append(child)
        elif typ == "tag":
            stack.append(parse_tag(data)["object"])
    return out


def is_ancestor(objects, anc, desc):
    if anc == desc:
        return True
    return anc in set(commit_ancestors(objects, desc))


def merge_base(objects, a, b):
    """A common ancestor of a and b (first found walking from b through a's set)."""
    a_set = set(commit_ancestors(objects, a))
    for c in commit_ancestors(objects, b):
        if c in a_set:
            return c
    return None


def diff_trees(objects, base_tree, head_tree):
    """-> list of {path, status, old, new} comparing two trees (None = absent)."""
    base = flatten_tree(objects, base_tree) if base_tree else {}
    head = flatten_tree(objects, head_tree) if head_tree else {}
    out = []
    for path in sorted(set(base) | set(head)):
        b = base.get(path)
        h = head.get(path)
        if b is None:
            out.append({"path": path, "status": "added", "old": None, "new": h[1]})
        elif h is None:
            out.append({"path": path, "status": "removed", "old": b[1], "new": None})
        elif b[1] != h[1]:
            out.append({"path": path, "status": "modified", "old": b[1], "new": h[1]})
    return out


def three_way_merge(objects, base_tree, head_tree, target_tree):
    """Merge head into target with base as ancestor.
    Returns (merged_files {path: (mode, oid)}, conflict_bool)."""
    base = flatten_tree(objects, base_tree) if base_tree else {}
    head = flatten_tree(objects, head_tree) if head_tree else {}
    target = flatten_tree(objects, target_tree) if target_tree else {}
    merged = dict(target)
    conflict = False
    for path in sorted(set(base) | set(head) | set(target)):
        b = base.get(path)
        h = head.get(path)
        t = target.get(path)
        if h == t:
            continue  # both sides agree (or both unchanged)
        if b == h:
            continue  # only target changed: keep target
        if b == t:
            # only head changed: take head (or its deletion)
            if h is None:
                merged.pop(path, None)
            else:
                merged[path] = h
            continue
        conflict = True  # both changed differently
    return merged, conflict


# --------------------------------------------------------------------------------------------
# packfiles
# --------------------------------------------------------------------------------------------

def _pack_obj_header(obj_type_num, size):
    first = (obj_type_num << 4) | (size & 0x0F)
    size >>= 4
    out = bytearray()
    if size:
        first |= 0x80
    out.append(first)
    while size:
        out.append(size & 0x7F | (0x80 if size > 0x7F else 0))
        size >>= 7
    return bytes(out)


def write_pack(obj_list):
    """obj_list: [(oid, type, data)] — plain objects only, no deltas.
    Deterministic order: sorted by (type, oid)."""
    items = sorted(obj_list, key=lambda e: (e[1], e[0]))
    out = bytearray()
    out += b"PACK" + struct.pack(">II", 2, len(items))
    for oid, typ, data in items:
        out += _pack_obj_header(GIT_TYPES[typ], len(data))
        out += zlib.compress(data)
    trailer = sha1_hex(bytes(out))
    out += bytes.fromhex(trailer)
    return bytes(out)


def _read_varint(data, pos):
    value = data[pos] & 0x7F
    pos += 1
    shift = 7
    while data[pos - 1] & 0x80:
        value |= (data[pos] & 0x7F) << shift
        pos += 1
        shift += 7
    return value, pos


def apply_delta(base, delta):
    """Apply a git delta to base bytes -> target bytes."""
    pos = 0
    src_size, pos = _read_varint(delta, pos)
    tgt_size, pos = _read_varint(delta, pos)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            off = 0
            size = 0
            for i in range(4):
                if op & (1 << i):
                    off |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            if size == 0:
                size = 0x10000
            out += base[off:off + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


def read_pack(data):
    """Parse a packfile -> {oid: (type, data)}. Handles OFS/REF deltas."""
    if len(data) < 12 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version, count = struct.unpack(">II", data[4:12])
    if version not in (2, 3):
        raise ValueError("bad pack version %d" % version)
    pos = 12
    objects = {}
    by_offset = {}
    pending = []  # (oid, delta_type, base_ref, delta_data, offset)
    for _ in range(count):
        start = pos
        byte = data[pos]
        pos += 1
        typ_num = (byte >> 4) & 0x7
        size = byte & 0x0F
        shift = 4
        while byte & 0x80:
            byte = data[pos]
            pos += 1
            size |= (byte & 0x7F) << shift
            shift += 7
        if typ_num == 6:  # OFS_DELTA
            byte = data[pos]
            pos += 1
            off = byte & 0x7F
            while byte & 0x80:
                byte = data[pos]
                pos += 1
                off = ((off + 1) << 7) | (byte & 0x7F)
            base_offset = start - off
            decomp = zlib.decompressobj()
            delta = decomp.decompress(data[pos:])
            pos += len(data[pos:]) - len(decomp.unused_data)
            # placeholder oid: computed after resolving
            pending.append((None, 6, base_offset, delta, start))
            by_offset[start] = ("ofs-delta", pending[-1])
        elif typ_num == 7:  # REF_DELTA
            base_oid = data[pos:pos + 20].hex()
            pos += 20
            decomp = zlib.decompressobj()
            delta = decomp.decompress(data[pos:])
            pos += len(data[pos:]) - len(decomp.unused_data)
            pending.append((None, 7, base_oid, delta, start))
            by_offset[start] = ("ref-delta", pending[-1])
        else:
            typ = GIT_TYPE_NAMES.get(typ_num)
            if typ is None:
                raise ValueError("bad pack object type %d" % typ_num)
            decomp = zlib.decompressobj()
            obj_data = decomp.decompress(data[pos:])
            pos += len(data[pos:]) - len(decomp.unused_data)
            if len(obj_data) != size:
                raise ValueError("pack object size mismatch")
            oid = git_hash(typ, obj_data)
            objects[oid] = (typ, obj_data)
            by_offset[start] = (typ, (oid, obj_data))
    # resolve deltas (may chain; iterate until stable)
    unresolved = list(pending)
    for _ in range(len(unresolved) + 2):
        if not unresolved:
            break
        still = []
        for entry in unresolved:
            _, dtyp, base_ref, delta, _off = entry
            if dtyp == 6:
                base = by_offset.get(base_ref)
                if base is None or base[0] in ("ofs-delta", "ref-delta"):
                    still.append(entry)
                    continue
                base_oid, base_data = base[1][0], base[1][1]
                base_type = base[0]
            else:
                if base_ref not in objects:
                    still.append(entry)
                    continue
                base_type, base_data = objects[base_ref]
                base_oid = base_ref
            target = apply_delta(base_data, delta)
            oid = git_hash(base_type, target)
            objects[oid] = (base_type, target)
            by_offset[_off] = (base_type, (oid, target))
        if len(still) == len(unresolved):
            break
        unresolved = still
    return objects


def verify_pack_checksum(data):
    if len(data) < 32:
        return False
    return sha1_hex(data[:-20]) == data[-20:].hex()


# --------------------------------------------------------------------------------------------
# pkt-line
# --------------------------------------------------------------------------------------------

def pkt_line(payload: bytes) -> bytes:
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_flush() -> bytes:
    return b"0000"


def pkt_delim() -> bytes:
    return b"0001"


def parse_pkt_lines(data: bytes):
    """-> list of ('data', payload) | ('flush',) | ('delim',). Raises ValueError on garbage."""
    out = []
    pos = 0
    n = len(data)
    while pos < n:
        if pos + 4 > n:
            raise ValueError("truncated pkt-line")
        chunk = data[pos:pos + 4]
        if chunk == b"0000":
            out.append(("flush",))
            pos += 4
            continue
        if chunk == b"0001":
            out.append(("delim",))
            pos += 4
            continue
        try:
            size = int(chunk.decode("ascii"), 16)
        except ValueError:
            raise ValueError("bad pkt-line length %r" % chunk)
        if size < 4 or pos + size > n:
            raise ValueError("bad pkt-line size %d" % size)
        out.append(("data", data[pos + 4:pos + size]))
        pos += size
    return out


def pkt_data_lines(data: bytes):
    """All 'data' payloads, in order; flush/delim ignored."""
    return [pkt[1] for pkt in parse_pkt_lines(data) if pkt[0] == "data"]


def sideband_pack(pack: bytes, chunk=60000):
    """Wrap pack bytes in sideband band-1 pkt-lines (each <= 65520 raw)."""
    out = bytearray()
    for i in range(0, len(pack), chunk):
        payload = b"\x01" + pack[i:i + chunk]
        out += pkt_line(payload)
    return bytes(out)

# --------------------------------------------------------------------------------------------
# store
# --------------------------------------------------------------------------------------------

class Repo:
    def __init__(self, owner, name, private, description):
        self.owner = owner
        self.name = name
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = DEFAULT_BRANCH
        self.db_id = 0
        self.objects = {}          # oid -> (type, bytes)
        self.refs = {}             # "refs/heads/main" -> oid
        self.issues = {}           # number -> dict
        self.next_issue = 1
        self.next_comment = 1
        self.pulls = {}            # number -> dict
        self.next_pull = 1
        self.labels = {}           # name -> {"name":..., "color":...}
        self.seq = 0               # mutation counter (cache invalidation)

    # -- git helpers -----------------------------------------------------------
    def head_oid(self, branch=None):
        return self.refs.get("refs/heads/" + (branch or self.default_branch))

    def resolve_ref(self, ref):
        """ref: branch name, full ref, or oid -> commit oid or None."""
        if not ref:
            return self.head_oid()
        if ref in self.refs:
            return self.refs[ref]
        full = "refs/heads/" + ref
        if full in self.refs:
            return self.refs[full]
        if is_oid(ref) and ref in self.objects and self.objects[ref][0] == "commit":
            return ref
        return None

    def commit_list(self, tip):
        """[(oid, commit_dict)] newest first from tip."""
        out = []
        for oid in commit_ancestors(self.objects, tip):
            out.append((oid, parse_commit(self.objects[oid][1])))
        return out

    def create_commit(self, files, parents, message):
        """files: {path: (mode, bytes)} — stores blobs+trees, returns commit oid."""
        blob_oids = {}
        for path, (mode, data) in files.items():
            oid = git_hash("blob", data)
            self.objects[oid] = ("blob", data)
            blob_oids[path] = (mode, oid)
        tree_oid = tree_from_files(self.objects, blob_oids)
        commit_data = build_commit(tree_oid, parents, message)
        commit_oid = git_hash("commit", commit_data)
        self.objects[commit_oid] = ("commit", commit_data)
        self.seq += 1
        return commit_oid

    def current_files(self, branch=None):
        """{path: (mode, blob_oid)} at the tip of branch ({} when unborn)."""
        tip = self.head_oid(branch)
        if tip is None:
            return {}
        tree = parse_commit(self.objects[tip][1])["tree"]
        return flatten_tree(self.objects, tree)

    def put_file(self, path, content_bytes, message, branch=None):
        """Contents-API write: create/update one file, commit, move the branch.
        Returns (commit_oid, blob_oid, status) with status 201 (create) or 200 (update)."""
        branch = branch or self.default_branch
        tip = self.head_oid(branch)
        files = self.current_files(branch)
        existed = path in files
        new_files = dict(files)
        blob_oid = git_hash("blob", content_bytes)
        self.objects[blob_oid] = ("blob", content_bytes)
        new_files[path] = ("100644", blob_oid)
        parents = [tip] if tip else []
        commit_oid = self.create_commit(
            {p: (m, self.objects[o][1]) for p, (m, o) in new_files.items()},
            parents, message)
        self.refs["refs/heads/" + branch] = commit_oid
        return commit_oid, blob_oid, (200 if existed else 201)

    def delete_file(self, path, message, branch=None):
        branch = branch or self.default_branch
        tip = self.head_oid(branch)
        if tip is None:
            return None
        files = self.current_files(branch)
        if path not in files:
            return None
        new_files = {p: v for p, v in files.items() if p != path}
        commit_oid = self.create_commit(
            {p: (m, self.objects[o][1]) for p, (m, o) in new_files.items()},
            [tip], message)
        self.refs["refs/heads/" + branch] = commit_oid
        return commit_oid


class Forge:
    def __init__(self):
        self.repos = {}            # (owner, name) -> Repo
        self.next_repo_id = 1
        self.lock = threading.RLock()
        self.req_counter = 0
        self.pack_cache = {}       # (db_id, seq, wants, haves, depth) -> pack bytes
        self.want_cache = {}       # (db_id, seq, wants, haves, depth) -> (send, shallow, included)

    def want_set(self, repo, wants, haves, depth):
        """Memoized _want_set: the 50 concurrent clones of one repo share
        the same BFS/tree-closure work."""
        key = (repo.db_id, repo.seq, tuple(sorted(wants)), tuple(sorted(haves)), depth)
        hit = self.want_cache.get(key)
        if hit is None:
            hit = _want_set(repo, wants, haves, depth)
            if len(self.want_cache) >= 16:
                self.want_cache.pop(next(iter(self.want_cache)))
            self.want_cache[key] = hit
        return hit

    def fetch_pack(self, repo, wants, haves, depth, send):
        """Memoized pack build: identical fetches of an unchanged repo
        (the 50 concurrent shallow clones) share one pack build."""
        key = (repo.db_id, repo.seq, tuple(sorted(wants)), tuple(sorted(haves)), depth)
        pack = self.pack_cache.get(key)
        if pack is None:
            pack = write_pack([(oid, typ, data) for oid, (typ, data) in send.items()])
            if len(self.pack_cache) >= 16:
                self.pack_cache.pop(next(iter(self.pack_cache)))
            self.pack_cache[key] = pack
        return pack

    def next_request_id(self):
        with self.lock:
            self.req_counter += 1
            return "req-%08x" % self.req_counter

    def create_repo(self, owner, name, private, description):
        key = (owner, name)
        if key in self.repos:
            return None
        repo = Repo(owner, name, private, description)
        repo.db_id = self.next_repo_id
        self.next_repo_id += 1
        self.repos[key] = repo
        return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def delete_repo(self, owner, name):
        self.repos.pop((owner, name), None)

    def user_repos(self, owner):
        return [r for (o, _), r in sorted(self.repos.items()) if o == owner]


FORGE = Forge()

# --------------------------------------------------------------------------------------------
# global ids (Relay, opaque + stable)
# --------------------------------------------------------------------------------------------

def gid(kind, *parts):
    raw = kind + ":" + "/".join(str(p) for p in parts)
    return base64.b64encode(raw.encode("utf-8")).decode("ascii")


def ungid(value):
    try:
        raw = base64.b64decode("".join(str(value).split())).decode("utf-8")
    except Exception:
        return None
    kind, _, rest = raw.partition(":")
    return kind, rest


def repo_gid(repo):
    return gid("Repository", repo.owner, repo.name)


def issue_gid(repo, number):
    return gid("Issue", repo.owner, repo.name, number)


def pull_gid(repo, number):
    return gid("PullRequest", repo.owner, repo.name, number)


def comment_gid(repo, cid):
    return gid("IssueComment", repo.owner, repo.name, cid)


# --------------------------------------------------------------------------------------------
# REST shapes
# --------------------------------------------------------------------------------------------

def repo_json(repo):
    return {
        "id": repo.db_id,
        "node_id": repo_gid(repo),
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "has_issues": True,
        "url": "/api/v3/repos/%s/%s" % (repo.owner, repo.name),
    }


def issue_json(repo, issue):
    return {
        "id": issue["db_id"],
        "node_id": issue_gid(repo, issue["number"]),
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": [{"name": n, "color": repo.labels.get(n, {}).get("color", "ededed")}
                   for n in issue["labels"]],
        "user": {"login": VIEWER_LOGIN},
        "comments": len(issue["comments"]),
    }


def pull_json(repo, pr):
    base_tip = repo.head_oid(pr["base"])
    head_tip = repo.head_oid(pr["head"])
    return {
        "id": pr["db_id"],
        "node_id": pull_gid(repo, pr["number"]),
        "number": pr["number"],
        "title": pr["title"],
        "body": pr["body"],
        "state": pr["state"],
        "merged": pr["merged"],
        "merged_at": pr["merged_at"],
        "merge_commit_sha": pr["merge_commit_sha"],
        "head": {"ref": pr["head"], "sha": head_tip, "label": "%s:%s" % (repo.owner, pr["head"])},
        "base": {"ref": pr["base"], "sha": base_tip, "label": "%s:%s" % (repo.owner, pr["base"])},
        "user": {"login": VIEWER_LOGIN},
    }


def pr_files(repo, pr):
    """Diff base tree vs head tree -> [{filename, status, additions, deletions, changes}]."""
    base_tip = repo.head_oid(pr["base"])
    head_tip = repo.head_oid(pr["head"])
    base_tree = parse_commit(repo.objects[base_tip][1])["tree"] if base_tip else None
    head_tree = parse_commit(repo.objects[head_tip][1])["tree"] if head_tip else None
    out = []
    for d in diff_trees(repo.objects, base_tree, head_tree):
        old = repo.objects[d["old"]][1] if d["old"] else b""
        new = repo.objects[d["new"]][1] if d["new"] else b""
        old_lines = old.decode("utf-8", "replace").splitlines() if old else []
        new_lines = new.decode("utf-8", "replace").splitlines() if new else []
        if d["status"] == "added":
            additions, deletions = len(new_lines), 0
        elif d["status"] == "removed":
            additions, deletions = 0, len(old_lines)
        else:
            # line-level count via difflib-free LCS-free heuristic: count differing lines
            additions = deletions = 0
            import difflib
            for line in difflib.unified_diff(old_lines, new_lines, lineterm=""):
                if line.startswith("+") and not line.startswith("+++"):
                    additions += 1
                elif line.startswith("-") and not line.startswith("---"):
                    deletions += 1
        out.append({"filename": d["path"], "status": d["status"],
                    "additions": additions, "deletions": deletions,
                    "changes": additions + deletions})
    return out


def pr_mergeable(repo, pr):
    """MERGEABLE / CONFLICTING / UNKNOWN for a PR."""
    if pr["state"] != "open":
        return "UNKNOWN"
    base_tip = repo.head_oid(pr["base"])
    head_tip = repo.head_oid(pr["head"])
    if base_tip is None or head_tip is None:
        return "UNKNOWN"
    base_tree = parse_commit(repo.objects[base_tip][1])["tree"]
    head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
    mb = merge_base(repo.objects, base_tip, head_tip)
    if mb is None:
        return "UNKNOWN"
    mb_tree = parse_commit(repo.objects[mb][1])["tree"]
    _, conflict = three_way_merge(repo.objects, mb_tree, head_tree, base_tree)
    return "CONFLICTING" if conflict else "MERGEABLE"


def do_merge(repo, pr, method="squash"):
    """Squash-merge pr into its base branch. Returns (merge_sha, conflict_bool)."""
    base_tip = repo.head_oid(pr["base"])
    head_tip = repo.head_oid(pr["head"])
    base_tree = parse_commit(repo.objects[base_tip][1])["tree"]
    head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
    mb = merge_base(repo.objects, base_tip, head_tip)
    mb_tree = parse_commit(repo.objects[mb][1])["tree"] if mb else None
    merged, conflict = three_way_merge(repo.objects, mb_tree, head_tree, base_tree)
    if conflict:
        return None, True
    # build the merged tree + one squash commit on the base branch
    blob_files = {}
    for path, (mode, oid) in merged.items():
        blob_files[path] = (mode, repo.objects[oid][1])
    merge_sha = repo.create_commit(blob_files, [base_tip],
                                   "Merge pull request #%d from %s\n\n%s" % (
                                       pr["number"], pr["head"], pr["title"]))
    repo.refs["refs/heads/" + pr["base"]] = merge_sha
    pr["state"] = "closed"
    pr["merged"] = True
    pr["merged_at"] = "2025-01-01T00:00:00Z"
    pr["merge_commit_sha"] = merge_sha
    return merge_sha, False

# --------------------------------------------------------------------------------------------
# HTTP plumbing
# --------------------------------------------------------------------------------------------

class ApiError(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


class Ctx:
    """One request's context."""

    def __init__(self, handler, method, path, query, headers, body):
        self.handler = handler
        self.method = method
        self.path = path
        self.query = query          # {name: [values]}
        self.headers = headers
        self.body = body            # raw bytes
        self._json = ...
        self.auth = False

    def q(self, name, default=None):
        vals = self.query.get(name)
        return vals[0] if vals else default

    def json_body(self):
        """Parsed JSON body; {} when empty; raises ApiError(400) when malformed."""
        if self._json is ...:
            if not self.body or not self.body.strip():
                self._json = {}
            else:
                try:
                    self._json = json.loads(self.body.decode("utf-8"))
                except Exception:
                    raise ApiError(400, "Invalid JSON in request body")
                if not isinstance(self._json, (dict, list)):
                    raise ApiError(400, "Request body must be a JSON object")
        return self._json

    def json_or_400(self):
        data = self.json_body()
        if not isinstance(data, dict):
            raise ApiError(400, "Request body must be a JSON object")
        return data


def check_auth(ctx, required=True):
    """Bearer token present -> the viewer. Absent -> 401 (when required)."""
    auth = ctx.headers.get("Authorization", "")
    if auth.startswith("Bearer ") and auth[7:].strip():
        ctx.auth = True
        return True
    if required:
        raise ApiError(401, "Requires authentication")
    return False


class ForgeServer(ThreadingHTTPServer):
    # set BEFORE construction: server_activate() calls listen() with this
    # value during __init__ (assigning it afterwards is a no-op). The clone
    # workload opens 50 connections in one instant; the default backlog (5)
    # drops SYNs and costs 1s+ retransmits per round.
    request_queue_size = 256
    daemon_threads = True
    allow_reuse_address = True


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def setup(self):
        super().setup()
        # disable Nagle: the client delays ACKs ~40ms, and a response split
        # across two small writes would otherwise cost a full RTT per request
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass

    # -- quiet logging ---------------------------------------------------------
    def log_message(self, fmt, *args):
        pass

    # -- response helpers ------------------------------------------------------
    def _send(self, status, body: bytes, ctype, extra=None):
        headers = {"Content-Type": ctype, "Content-Length": str(len(body)),
                   "X-GitHub-Request-Id": FORGE.next_request_id()}
        if extra:
            headers.update(extra)
        try:
            self.send_response(status)
            for k, v in headers.items():
                self.send_header(k, v)
            self.end_headers()
            if body:
                self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def send_json(self, status, obj, extra=None):
        self._send(status, json_bytes(obj), JSON_TYPE, extra)

    def send_no_content(self, status=204):
        headers = {"Content-Type": JSON_TYPE, "Content-Length": "0",
                   "X-GitHub-Request-Id": FORGE.next_request_id()}
        try:
            self.send_response(status)
            for k, v in headers.items():
                self.send_header(k, v)
            self.end_headers()
        except (BrokenPipeError, ConnectionResetError):
            pass

    def send_error_json(self, status, message):
        self.send_json(status, {"message": message})

    def send_bytes(self, status, body: bytes, ctype, extra=None):
        self._send(status, body, ctype, extra)

    # -- request intake --------------------------------------------------------
    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _dispatch(self, method):
        parsed = urlparse(self.path)
        path = parsed.path
        # collapse duplicate slashes, strip trailing slash (except root)
        path = re.sub(r"/+", "/", path)
        if len(path) > 1 and path.endswith("/"):
            path = path[:-1]
        query = parse_qs(parsed.query)
        body = self._read_body()
        ctx = Ctx(self, method, path, query, self.headers, body)
        try:
            route(ctx)
        except ApiError as e:
            self.send_error_json(e.status, e.message)
        except Exception as e:  # never crash the server on one request
            sys.stderr.write("[forge] %s %s: %r\n" % (method, path, e))
            try:
                self.send_error_json(500, "Internal Server Error")
            except Exception:
                pass

    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")

    def do_PUT(self):
        self._dispatch("PUT")

    def do_PATCH(self):
        self._dispatch("PATCH")

    def do_DELETE(self):
        self._dispatch("DELETE")

    def do_HEAD(self):
        self._dispatch("HEAD")


# --------------------------------------------------------------------------------------------
# git smart HTTP
# --------------------------------------------------------------------------------------------

def git_repo_or_404(ctx, owner, repo_name):
    repo = FORGE.get_repo(owner, repo_name)
    if repo is None:
        raise ApiError(404, "Not Found")
    return repo


def _ref_lines(repo):
    """[(oid, name)] for the v0 advertisement: HEAD first, then heads, then tags + peels."""
    lines = []
    head = repo.head_oid()
    if head is None:
        return lines, True
    lines.append((head, "HEAD"))
    for name in sorted(repo.refs):
        if name.startswith("refs/heads/"):
            lines.append((repo.refs[name], name))
    for name in sorted(repo.refs):
        if name.startswith("refs/tags/"):
            oid = repo.refs[name]
            lines.append((oid, name))
            obj = repo.objects.get(oid)
            if obj and obj[0] == "tag":
                target = parse_tag(obj[1])["object"]
                if target in repo.objects:
                    lines.append((target, name + "^{}"))
    return lines, False


def _v0_caps(repo, service):
    if service == "git-receive-pack":
        return ("report-status side-band-64k delete-refs ofs-delta "
                "object-format=sha1 agent=%s" % FORGE_AGENT)
    return ("symref=HEAD:refs/heads/main side-band-64k thin-pack ofs-delta "
            "object-format=sha1 agent=%s" % FORGE_AGENT)


def handle_info_refs(ctx, owner, repo_name, service):
    check_auth(ctx)
    repo = git_repo_or_404(ctx, owner, repo_name)
    is_v2 = ctx.headers.get("Git-Protocol", "") == "version=2"
    ctype = "application/x-%s-advertisement" % service
    if service == "git-receive-pack":
        is_v2 = False
    out = bytearray()
    if is_v2:
        out += pkt_line(b"version 2\n")
        out += pkt_line(b"ls-refs=unborn\n")
        out += pkt_line(b"fetch=shallow filter\n")
        out += pkt_line(("agent=%s\n" % FORGE_AGENT).encode("ascii"))
        out += pkt_line(b"object-format=sha1\n")
        out += pkt_flush()
        ctx.handler.send_bytes(200, bytes(out), ctype)
        return
    # v0
    out += pkt_line(("# service=%s\n" % service).encode("ascii"))
    out += pkt_flush()
    lines, empty = _ref_lines(repo)
    caps = _v0_caps(repo, service)
    if empty:
        out += pkt_line((ZERO_OID + " capabilities^{}\0" + caps + "\n").encode("ascii"))
    else:
        first = True
        for oid, name in lines:
            if first:
                out += pkt_line(("%s %s\0%s\n" % (oid, name, caps)).encode("ascii"))
                first = False
            else:
                out += pkt_line(("%s %s\n" % (oid, name)).encode("ascii"))
    out += pkt_flush()
    ctx.handler.send_bytes(200, bytes(out), ctype)


def _tree_closure(objects, tree_oid):
    """A tree plus all its subtree and blob oids (recursive)."""
    out = set()
    stack = [tree_oid]
    while stack:
        t = stack.pop()
        if t in out:
            continue
        obj = objects.get(t)
        if obj is None or obj[0] != "tree":
            continue
        out.add(t)
        for mode, _name, child in parse_tree(obj[1]):
            if mode == "40000":
                stack.append(child)
            else:
                out.add(child)
    return out


def _shallow_held(objects, tips):
    """Objects a shallow holder of `tips` owns: each tip plus its tree
    closure, but none of the tips' parents (a shallow clone's boundary)."""
    out = set()
    for tip in tips:
        obj = objects.get(tip)
        if obj is None:
            continue
        out.add(tip)
        if obj[0] == "commit":
            out |= _tree_closure(objects, parse_commit(obj[1])["tree"])
    return out


def _want_set(repo, wants, haves, depth):
    """Objects to send for a fetch: reachable(wants) - reachable(haves), depth-limited.
    Returns (objects {oid: (type, data)}, shallow_list, unshallow_list)."""
    objects = repo.objects
    # commits within depth of the wants
    if depth is not None:
        included_commits = set()
        boundary = set()
        queue = [(w, 0) for w in wants]
        seen = set()
        while queue:
            oid, d = queue.pop(0)
            if oid in seen:
                continue
            seen.add(oid)
            obj = objects.get(oid)
            if obj is None or obj[0] != "commit":
                continue
            if d < depth:
                included_commits.add(oid)
                for p in parse_commit(obj[1])["parents"]:
                    queue.append((p, d + 1))
            else:
                boundary.add(oid)
        # shallow = included commits whose parents are not all included
        shallow = set()
        for oid in included_commits:
            parents = parse_commit(objects[oid][1])["parents"]
            if any(p not in included_commits for p in parents):
                shallow.add(oid)
        send = set()
        for oid in included_commits:
            send.add(oid)
            send |= _tree_closure(objects, parse_commit(objects[oid][1])["tree"])
    else:
        included_commits = None
        send = reachable_objects(objects, wants)
        shallow = set()
    # subtract everything the client already has
    if haves:
        if depth is not None:
            # a depth fetch's haves are shallow boundary commits: the client
            # holds only each have's own tree, not its parents
            send -= _shallow_held(objects, haves)
        else:
            send -= reachable_objects(objects, haves)
    # unshallow: previously-shallow commits now fully present
    result = {}
    for oid in send:
        obj = objects.get(oid)
        if obj is not None:
            result[oid] = obj
    return result, sorted(shallow), included_commits


def handle_fetch_v2(ctx, repo, lines):
    """lines: pkt-line data payloads of the v2 fetch request."""
    wants, haves, shallow_req, depth = [], [], [], None
    for raw in lines:
        text = raw.decode("utf-8", "replace").strip()
        if text.startswith("want "):
            wants.append(text[5:].strip())
        elif text.startswith("have "):
            haves.append(text[5:].strip())
        elif text.startswith("shallow "):
            shallow_req.append(text[8:].strip())
        elif text.startswith("deepen "):
            try:
                depth = int(text[7:].strip())
            except ValueError:
                depth = None
    send, shallow, included = FORGE.want_set(repo, wants, haves, depth)
    # unshallow: shallow_req commits that are now fully included
    unshallow = []
    if included is not None:
        for oid in shallow_req:
            if oid in included:
                parents = parse_commit(repo.objects[oid][1])["parents"] if oid in repo.objects else []
                if all(p in included for p in parents):
                    unshallow.append(oid)
    elif shallow_req:
        # full fetch: everything previously shallow is now unshallow
        unshallow = [o for o in shallow_req if o in repo.objects]
    pack = FORGE.fetch_pack(repo, wants, haves, depth, send)
    out = bytearray()
    if haves:
        out += pkt_line(b"acknowledgments\n")
        known = [h for h in haves if h in repo.objects]
        if known:
            for h in known:
                out += pkt_line(("ACK %s\n" % h).encode("ascii"))
            out += pkt_line(b"ready\n")
        else:
            out += pkt_line(b"NAK\n")
        out += pkt_delim()
    if shallow or unshallow:
        out += pkt_line(b"shallow-info\n")
        for oid in shallow:
            out += pkt_line(("shallow %s\n" % oid).encode("ascii"))
        for oid in unshallow:
            out += pkt_line(("unshallow %s\n" % oid).encode("ascii"))
        out += pkt_delim()
    out += pkt_line(b"packfile\n")
    out += sideband_pack(pack)
    out += pkt_flush()
    ctx.handler.send_bytes(200, bytes(out), "application/x-git-upload-pack-result")


def handle_fetch_v0(ctx, repo, lines):
    wants, haves, shallow_req, depth = [], [], [], None
    for raw in lines:
        text = raw.decode("utf-8", "replace").strip()
        if text.startswith("want "):
            wants.append(text[5:].strip())
        elif text.startswith("have "):
            haves.append(text[5:].strip())
        elif text.startswith("shallow "):
            shallow_req.append(text[8:].strip())
        elif text.startswith("deepen "):
            try:
                depth = int(text[7:].strip())
            except ValueError:
                depth = None
    send, shallow, included = FORGE.want_set(repo, wants, haves, depth)
    unshallow = []
    if included is not None:
        for oid in shallow_req:
            if oid in included:
                parents = parse_commit(repo.objects[oid][1])["parents"] if oid in repo.objects else []
                if all(p in included for p in parents):
                    unshallow.append(oid)
    elif shallow_req:
        unshallow = [o for o in shallow_req if o in repo.objects]
    pack = FORGE.fetch_pack(repo, wants, haves, depth, send)
    out = bytearray()
    for oid in shallow:
        out += pkt_line(("shallow %s\n" % oid).encode("ascii"))
    for oid in unshallow:
        out += pkt_line(("unshallow %s\n" % oid).encode("ascii"))
    if haves:
        known = [h for h in haves if h in repo.objects]
        if known:
            for h in known:
                out += pkt_line(("ACK %s\n" % h).encode("ascii"))
        else:
            out += pkt_line(b"NAK\n")
    out += sideband_pack(pack)
    ctx.handler.send_bytes(200, bytes(out), "application/x-git-upload-pack-result")


def handle_ls_refs(ctx, repo, lines):
    """v2 ls-refs: honour peel/symrefs/unborn args and ref-prefix filters."""
    prefixes = []
    peel = False
    symrefs = False
    for raw in lines:
        text = raw.decode("utf-8", "replace").strip()
        if text.startswith("ref-prefix "):
            prefixes.append(text[11:].strip())
        elif text == "peel":
            peel = True
        elif text == "symrefs":
            symrefs = True
    out = bytearray()
    head = repo.head_oid()
    head_oid = head if head is not None else ZERO_OID
    # HEAD is a ref like any other for prefix filtering: it only survives
    # when no prefix is given (or one matches "HEAD").
    if not prefixes or any("HEAD".startswith(p) for p in prefixes):
        if symrefs:
            out += pkt_line(("%s HEAD symref-target:refs/heads/main\n" % head_oid).encode("ascii"))
        else:
            out += pkt_line(("%s HEAD\n" % head_oid).encode("ascii"))
    refs = []
    for name in sorted(repo.refs):
        oid = repo.refs[name]
        peeled = None
        obj = repo.objects.get(oid)
        if peel and obj and obj[0] == "tag":
            target = parse_tag(obj[1])["object"]
            if target in repo.objects:
                peeled = target
        refs.append((oid, name, peeled))
    for oid, name, peeled in refs:
        if prefixes and not any(name.startswith(p) for p in prefixes):
            continue
        if peeled is not None:
            line = "%s %s peeled:%s\n" % (oid, name, peeled)
        else:
            line = "%s %s\n" % (oid, name)
        out += pkt_line(line.encode("ascii"))
    out += pkt_flush()
    ctx.handler.send_bytes(200, bytes(out), "application/x-git-upload-pack-result")


def handle_upload_pack(ctx, owner, repo_name):
    check_auth(ctx)
    repo = git_repo_or_404(ctx, owner, repo_name)
    try:
        lines = pkt_data_lines(ctx.body)
    except ValueError:
        raise ApiError(400, "malformed pkt-line")
    # ls-refs vs fetch: first line decides
    first = lines[0].decode("utf-8", "replace").strip() if lines else ""
    if first.startswith("command=ls-refs"):
        handle_ls_refs(ctx, repo, lines)
        return
    if first.startswith("command=fetch") or any(
            l.decode("utf-8", "replace").strip().startswith("want ") for l in lines):
        if ctx.headers.get("Git-Protocol", "") == "version=2":
            handle_fetch_v2(ctx, repo, lines)
        else:
            handle_fetch_v0(ctx, repo, lines)
        return
    # unknown / empty command: answer an empty v2-style packfile so the client survives
    if ctx.headers.get("Git-Protocol", "") == "version=2":
        out = pkt_line(b"packfile\n") + sideband_pack(write_pack([])) + pkt_flush()
    else:
        out = sideband_pack(write_pack([]))
    ctx.handler.send_bytes(200, out, "application/x-git-upload-pack-result")


def handle_receive_pack(ctx, owner, repo_name):
    check_auth(ctx)
    repo = git_repo_or_404(ctx, owner, repo_name)
    body = ctx.body
    # Walk pkt-lines one at a time until the first flush; everything after it
    # is the raw pack (NOT pkt-line framed — never parse it as pkt-lines).
    commands = []
    p = 0
    n = len(body)
    pack_start = n
    while p < n:
        if body[p:p + 4] == b"0000":
            pack_start = p + 4
            break
        if body[p:p + 4] == b"0001":
            p += 4
            continue
        try:
            size = int(body[p:p + 4].decode("ascii"), 16)
        except ValueError:
            raise ApiError(400, "malformed pkt-line")
        if size < 4 or p + size > n:
            raise ApiError(400, "malformed pkt-line")
        commands.append(body[p + 4:p + size])
        p += size
    pack_data = body[pack_start:]
    # parse the command list
    parsed = []
    for payload in commands:
        text = payload.decode("utf-8", "replace")
        if "\0" in text:
            text = text.split("\0", 1)[0]
        parts = text.strip().split(" ")
        if len(parts) != 3:
            continue
        parsed.append((parts[0], parts[1], parts[2]))
    # unpack the pack (always, even when a ref update is refused)
    unpack_ok = True
    unpack_detail = ""
    if pack_data:
        try:
            new_objects = read_pack(pack_data)
            with FORGE.lock:
                repo.objects.update(new_objects)
                repo.seq += 1
        except Exception as e:
            unpack_ok = False
            unpack_detail = str(e)
    # apply the ref updates
    report = []
    with FORGE.lock:
        for old_oid, new_oid, ref in parsed:
            current = repo.refs.get(ref)
            if new_oid == ZERO_OID:
                # delete
                if current is None:
                    report.append((ref, False, "cannot delete a ref that does not exist"))
                elif old_oid != ZERO_OID and old_oid != current:
                    report.append((ref, False, "old value does not match"))
                else:
                    del repo.refs[ref]
                    report.append((ref, True, ""))
                continue
            if old_oid == ZERO_OID:
                # create
                if ref in repo.refs:
                    report.append((ref, False, "already exists"))
                    continue
            else:
                if current is None:
                    report.append((ref, False, "cannot update a ref that does not exist"))
                    continue
                if current != old_oid:
                    report.append((ref, False, "old value does not match"))
                    continue
                if not is_ancestor(repo.objects, current, new_oid):
                    report.append((ref, False, "non-fast-forward"))
                    continue
            repo.refs[ref] = new_oid
            report.append((ref, True, ""))
        repo.seq += 1
    # report-status stream, sideband band 1
    stream = bytearray()
    if unpack_ok:
        stream += pkt_line(b"unpack ok\n")
    else:
        stream += pkt_line(("unpack %s\n" % unpack_detail).encode("utf-8", "replace"))
    for ref, ok, reason in report:
        if ok:
            stream += pkt_line(("ok %s\n" % ref).encode("ascii"))
        else:
            stream += pkt_line(("ng %s %s\n" % (ref, reason)).encode("utf-8", "replace"))
    stream += pkt_flush()
    # sideband frames, then a top-level flush to terminate the stream
    out = sideband_pack(bytes(stream), chunk=60000) + pkt_flush()
    ctx.handler.send_bytes(200, out, "application/x-git-receive-pack-result")

# --------------------------------------------------------------------------------------------
# REST v3
# --------------------------------------------------------------------------------------------

def rest_repo(ctx, owner, name):
    """The repo for this token, or 404 (foreign owner is 404, never 403)."""
    if owner != VIEWER_LOGIN:
        raise ApiError(404, "Not Found")
    repo = FORGE.get_repo(owner, name)
    if repo is None:
        raise ApiError(404, "Not Found")
    return repo


def paginate(ctx, items, default_per_page=30):
    """(page_items, link_header_or_None). per_page/page from the query."""
    try:
        per_page = int(ctx.q("per_page", default_per_page))
    except ValueError:
        per_page = default_per_page
    per_page = max(1, min(100, per_page))
    try:
        page = int(ctx.q("page", 1))
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    chunk = items[start:start + per_page]
    link = None
    if start + per_page < total:
        host = ctx.headers.get("Host", "127.0.0.1")
        base = "http://%s%s" % (host, ctx.path)
        qs = []
        for k, vals in ctx.query.items():
            if k == "page":
                continue
            for v in vals:
                qs.append("%s=%s" % (k, v))
        qs.append("page=%d" % (page + 1))
        nxt = "%s?%s" % (base, "&".join(qs))
        last_page = (total + per_page - 1) // per_page
        qs[-1] = "page=%d" % last_page
        link = '<%s>; rel="next", <%s?%s>; rel="last"' % (nxt, base, "&".join(qs))
    return chunk, link


def rest_root(ctx):
    check_auth(ctx)
    ctx.handler.send_json(200, {"current_user_url": "/api/v3/user",
                                "rate_limit_url": "/api/v3/rate_limit"},
                          {"X-OAuth-Scopes": "repo, read:org"})


def rest_meta(ctx):
    check_auth(ctx)
    ctx.handler.send_json(200, {"installed_version": FORGE_VERSION})


def rest_user(ctx):
    check_auth(ctx)
    ctx.handler.send_json(200, {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"})


def rest_create_repo(ctx):
    check_auth(ctx)
    data = ctx.json_or_400()
    name = data.get("name")
    if not isinstance(name, str) or not name:
        raise ApiError(422, "name is required")
    repo = FORGE.create_repo(VIEWER_LOGIN, name, data.get("private", False),
                             data.get("description", ""))
    if repo is None:
        raise ApiError(422, "Repository already exists")
    ctx.handler.send_json(201, repo_json(repo))


def rest_list_user_repos(ctx):
    check_auth(ctx)
    repos = FORGE.user_repos(VIEWER_LOGIN)
    chunk, link = paginate(ctx, repos)
    extra = {"Link": link} if link else None
    ctx.handler.send_json(200, [repo_json(r) for r in chunk], extra)


def rest_get_repo(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    ctx.handler.send_json(200, repo_json(repo))


def rest_patch_repo(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    if "description" in data:
        repo.description = data["description"] or ""
    if "private" in data:
        repo.private = bool(data["private"])
    ctx.handler.send_json(200, repo_json(repo))


def rest_delete_repo(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    FORGE.delete_repo(owner, name)
    ctx.handler.send_no_content(204)


def rest_list_branches(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    out = []
    for ref in sorted(repo.refs):
        if ref.startswith("refs/heads/"):
            out.append({"name": ref[len("refs/heads/"):],
                        "commit": {"sha": repo.refs[ref]}})
    ctx.handler.send_json(200, out)


def rest_get_branch(ctx, owner, name, branch):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    oid = repo.head_oid(branch)
    if oid is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, {"name": branch, "commit": {"sha": oid}})


def rest_list_commits(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    ref = ctx.q("sha")
    tip = repo.resolve_ref(ref) if ref else repo.head_oid()
    if tip is None:
        ctx.handler.send_json(200, [])
        return
    out = []
    for oid, c in repo.commit_list(tip):
        msg = c["message"].decode("utf-8", "replace")
        if msg.endswith("\n"):
            msg = msg[:-1]
        out.append({"sha": oid, "commit": {"message": msg,
                                           "author": {"name": VIEWER_NAME, "email": VIEWER_EMAIL},
                                           "committer": {"name": VIEWER_NAME, "email": VIEWER_EMAIL}},
                    "author": {"login": VIEWER_LOGIN}})
    ctx.handler.send_json(200, out)


def rest_create_ref(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    ref = data.get("ref", "")
    sha = data.get("sha", "")
    if not ref.startswith("refs/") or not is_oid(sha) or sha not in repo.objects:
        raise ApiError(422, "Invalid ref or sha")
    if ref in repo.refs:
        raise ApiError(422, "Reference already exists")
    repo.refs[ref] = sha
    ctx.handler.send_json(201, {"ref": ref, "object": {"sha": sha, "type": "commit"}})


def rest_get_ref(ctx, owner, name, refpath):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    ref = "refs/" + refpath
    oid = repo.refs.get(ref)
    if oid is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, {"ref": ref, "object": {"sha": oid, "type": "commit"}})


def _tree_at(repo, tip, path):
    """("file", blob_oid, blob_bytes) | ("dir", [entries], None) | None.
    Walks the tree objects so directory entries carry their real tree shas."""
    if tip is None:
        return None
    tree_oid = parse_commit(repo.objects[tip][1])["tree"]
    segments = [s for s in path.split("/") if s != ""]
    cur = tree_oid
    for i, seg in enumerate(segments):
        obj = repo.objects.get(cur)
        if obj is None or obj[0] != "tree":
            return None
        found = None
        for mode, name, oid in parse_tree(obj[1]):
            if name == seg:
                found = (mode, oid)
                break
        if found is None:
            return None
        mode, oid = found
        last = i == len(segments) - 1
        if mode == "40000":
            if last:
                entries = []
                tobj = repo.objects.get(oid)
                if tobj is not None:
                    for m2, n2, o2 in parse_tree(tobj[1]):
                        entries.append({"type": "dir" if m2 == "40000" else "file",
                                        "name": n2,
                                        "path": "/".join(segments + [n2]),
                                        "sha": o2})
                return ("dir", entries, None)
            cur = oid
        else:
            if last:
                return ("file", oid, repo.objects[oid][1])
            return None
    # path == "" (root): list the root tree
    entries = []
    tobj = repo.objects.get(tree_oid)
    if tobj is not None:
        for m2, n2, o2 in parse_tree(tobj[1]):
            entries.append({"type": "dir" if m2 == "40000" else "file",
                            "name": n2, "path": n2, "sha": o2})
    return ("dir", entries, None)


def rest_get_contents(ctx, owner, name, fpath):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    tip = repo.resolve_ref(ctx.q("ref"))
    if tip is None:
        raise ApiError(404, "Not Found")
    found = _tree_at(repo, tip, fpath)
    if found is None:
        raise ApiError(404, "Not Found")
    kind, a, b = found
    if kind == "dir":
        ctx.handler.send_json(200, a)
        return
    _, oid, data = found
    ctx.handler.send_json(200, {"type": "file", "encoding": "base64",
                                "content": b64e(data), "sha": oid,
                                "size": len(data), "name": fpath.split("/")[-1],
                                "path": fpath})


def rest_put_contents(ctx, owner, name, fpath):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    message = data.get("message", "")
    content = data.get("content", "")
    branch = data.get("branch") or repo.default_branch
    sha = data.get("sha")
    try:
        raw = b64d(content) if content else b""
    except Exception:
        raise ApiError(422, "content is not valid base64")
    tip = repo.head_oid(branch)
    if tip is not None:
        files = flatten_tree(repo.objects, parse_commit(repo.objects[tip][1])["tree"])
        current = files.get(fpath)
        if sha is not None:
            # an update must name the current blob sha
            if current is None or current[1] != sha:
                raise ApiError(409, "sha does not match the current file")
    commit_oid, blob_oid, status = repo.put_file(fpath, raw, message, branch)
    ctx.handler.send_json(status, {"content": {"sha": blob_oid, "encoding": "base64",
                                              "name": fpath.split("/")[-1], "path": fpath,
                                              "size": len(raw)},
                                   "commit": {"sha": commit_oid}})


def rest_delete_contents(ctx, owner, name, fpath):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_body() if ctx.body and ctx.body.strip() else {}
    if not isinstance(data, dict):
        raise ApiError(400, "Request body must be a JSON object")
    message = data.get("message", "")
    branch = data.get("branch") or repo.default_branch
    sha = data.get("sha")
    tip = repo.head_oid(branch)
    if tip is None:
        raise ApiError(404, "Not Found")
    files = flatten_tree(repo.objects, parse_commit(repo.objects[tip][1])["tree"])
    current = files.get(fpath)
    if current is None:
        raise ApiError(404, "Not Found")
    if sha is not None and current[1] != sha:
        raise ApiError(409, "sha does not match the current file")
    commit_oid = repo.delete_file(fpath, message, branch)
    ctx.handler.send_json(200, {"commit": {"sha": commit_oid}})


def rest_create_label(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    label = data.get("name")
    if not isinstance(label, str) or not label:
        raise ApiError(422, "name is required")
    color = data.get("color", "ededed")
    repo.labels[label] = {"name": label, "color": color}
    ctx.handler.send_json(201, {"name": label, "color": color})


def rest_create_issue(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    title = data.get("title", "")
    body = data.get("body", "")
    labels = data.get("labels", []) or []
    for label in labels:
        if label not in repo.labels:
            raise ApiError(422, "Label '%s' does not exist" % label)
    number = repo.next_issue
    repo.next_issue += 1
    issue = {"number": number, "title": title, "body": body, "state": "open",
             "labels": list(labels), "comments": [], "db_id": 100000 + number,
             "_repo": repo}
    repo.issues[number] = issue
    ctx.handler.send_json(201, issue_json(repo, issue))


def rest_list_issues(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    state = ctx.q("state", "open")
    sort = ctx.q("sort", "created")
    direction = ctx.q("direction", "desc")
    issues = list(repo.issues.values())
    if state != "all":
        issues = [i for i in issues if i["state"] == state]
    reverse = direction != "asc"
    issues.sort(key=lambda i: i["number"], reverse=reverse)
    chunk, link = paginate(ctx, issues, default_per_page=30)
    extra = {"Link": link} if link else None
    ctx.handler.send_json(200, [issue_json(repo, i) for i in chunk], extra)


def rest_get_issue(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, issue_json(repo, issue))


def rest_patch_issue(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    data = ctx.json_or_400()
    if "state" in data and data["state"] in ("open", "closed"):
        issue["state"] = data["state"]
    if "title" in data:
        issue["title"] = data["title"]
    if "body" in data:
        issue["body"] = data["body"]
    ctx.handler.send_json(200, issue_json(repo, issue))


def rest_create_comment(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    data = ctx.json_or_400()
    body = data.get("body", "")
    cid = repo.next_comment
    repo.next_comment += 1
    comment = {"id": cid, "node_id": comment_gid(repo, cid), "body": body,
               "user": {"login": VIEWER_LOGIN}}
    issue["comments"].append(comment)
    ctx.handler.send_json(201, comment)


def rest_list_comments(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    issue = repo.issues.get(number)
    if issue is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, issue["comments"])


def rest_create_pull(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    data = ctx.json_or_400()
    head = data.get("head", "")
    base = data.get("base", "")
    title = data.get("title", "")
    body = data.get("body", "")
    if repo.head_oid(head) is None:
        raise ApiError(422, "Head branch '%s' does not exist" % head)
    if repo.head_oid(base) is None:
        raise ApiError(422, "Base branch '%s' does not exist" % base)
    # an open PR from the same head branch already exists -> 422 (re-run tolerant)
    for pr in repo.pulls.values():
        if pr["head"] == head and pr["state"] == "open":
            raise ApiError(422, "A pull request already exists for %s" % head)
    number = repo.next_pull
    repo.next_pull += 1
    pr = {"number": number, "title": title, "body": body, "state": "open",
          "merged": False, "merged_at": None, "merge_commit_sha": None,
          "head": head, "base": base, "db_id": 200000 + number, "_repo": repo}
    repo.pulls[number] = pr
    ctx.handler.send_json(201, pull_json(repo, pr))


def rest_list_pulls(ctx, owner, name):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    state = ctx.q("state", "open")
    pulls = list(repo.pulls.values())
    if state != "all":
        pulls = [p for p in pulls if p["state"] == state]
    pulls.sort(key=lambda p: p["number"])
    chunk, link = paginate(ctx, pulls, default_per_page=30)
    extra = {"Link": link} if link else None
    ctx.handler.send_json(200, [pull_json(repo, p) for p in chunk], extra)


def rest_get_pull(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    pr = repo.pulls.get(number)
    if pr is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, pull_json(repo, pr))


def rest_list_pull_files(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    pr = repo.pulls.get(number)
    if pr is None:
        raise ApiError(404, "Not Found")
    ctx.handler.send_json(200, pr_files(repo, pr))


def rest_merge_pull(ctx, owner, name, number):
    check_auth(ctx)
    repo = rest_repo(ctx, owner, name)
    pr = repo.pulls.get(number)
    if pr is None:
        raise ApiError(404, "Not Found")
    if pr["state"] != "open":
        raise ApiError(405, "Pull request is not open")
    data = ctx.json_body() if ctx.body and ctx.body.strip() else {}
    method = (data.get("merge_method") or "squash").lower() if isinstance(data, dict) else "squash"
    merge_sha, conflict = do_merge(repo, pr, method)
    if conflict:
        raise ApiError(405, "Merge conflict")
    ctx.handler.send_json(200, {"sha": merge_sha, "merged": True,
                                "message": "Pull request successfully merged"})

# --------------------------------------------------------------------------------------------
# GraphQL v4 (the documents gh and github-mcp-server send)
# --------------------------------------------------------------------------------------------

# Static schema used for __type introspection.
GQL_SCHEMA = {
    "Issue": {"kind": "OBJECT", "fields": ["id", "number", "title", "state", "body",
                                           "createdAt", "updatedAt", "author", "labels",
                                           "comments", "url"]},
    "PullRequest": {"kind": "OBJECT", "fields": ["id", "number", "title", "state", "body",
                                                 "headRefName", "baseRefName", "mergeable",
                                                 "merged", "files", "headRefOid", "baseRefOid",
                                                 "mergedAt", "mergeCommit", "author", "url"]},
    "Repository": {"kind": "OBJECT", "fields": ["id", "databaseId", "name", "nameWithOwner",
                                                "owner", "defaultBranchRef", "viewerPermission",
                                                "hasIssuesEnabled", "issue", "issues",
                                                "pullRequests", "pullRequest", "description",
                                                "isPrivate", "url"]},
    "User": {"kind": "OBJECT", "fields": ["id", "login", "name", "email"]},
    "IssueConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo", "totalCount"]},
    "PullRequestConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo", "totalCount"]},
    "PullRequestChangedFileConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo"]},
    "PullRequestChangedFile": {"kind": "OBJECT", "fields": ["path", "additions", "deletions", "changeType"]},
    "PageInfo": {"kind": "OBJECT", "fields": ["hasNextPage", "hasPreviousPage", "endCursor", "startCursor"]},
    "Ref": {"kind": "OBJECT", "fields": ["name", "target"]},
    "SearchType": {"kind": "ENUM", "enumValues": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"]},
    "IssueState": {"kind": "ENUM", "enumValues": ["OPEN", "CLOSED"]},
    "PullRequestState": {"kind": "ENUM", "enumValues": ["OPEN", "CLOSED", "MERGED"]},
    "MergeableState": {"kind": "ENUM", "enumValues": ["MERGEABLE", "CONFLICTING", "UNKNOWN"]},
    "PullRequestMergeMethod": {"kind": "ENUM", "enumValues": ["MERGE", "SQUASH", "REBASE"]},
    "RepositoryPermission": {"kind": "ENUM", "enumValues": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"]},
    "IssueOrderField": {"kind": "ENUM", "enumValues": ["CREATED_AT", "UPDATED_AT", "COMMENTS"]},
    "OrderDirection": {"kind": "ENUM", "enumValues": ["ASC", "DESC"]},
}

# Types whose fields the executor resolves; anything else -> validation error.
GQL_FIELDS = {
    "Query": {"viewer", "repository", "node", "__type"},
    "User": {"login", "id", "name"},
    "Repository": {"id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef",
                   "viewerPermission", "hasIssuesEnabled", "issue", "issues", "pullRequests",
                   "pullRequest", "description", "isPrivate"},
    "Issue": {"id", "number", "title", "state", "body"},
    "IssueConnection": {"nodes", "pageInfo", "totalCount"},
    "PullRequest": {"id", "number", "title", "state", "body", "headRefName", "baseRefName",
                    "mergeable", "merged", "files"},
    "PullRequestConnection": {"nodes", "pageInfo", "totalCount"},
    "PullRequestChangedFileConnection": {"nodes", "pageInfo"},
    "PullRequestChangedFile": {"path", "additions", "deletions"},
    "PageInfo": {"hasNextPage", "hasPreviousPage", "endCursor", "startCursor"},
    "Ref": {"name"},
    "Mutation": {"createIssue", "closeIssue", "createPullRequest", "mergePullRequest", "addComment"},
    "__Type": {"fields", "enumValues", "name", "kind"},
    "__Field": {"name"},
    "__EnumValue": {"name"},
    "CreateIssuePayload": {"issue"},
    "CloseIssuePayload": {"issue"},
    "CreatePullRequestPayload": {"pullRequest"},
    "MergePullRequestPayload": {"pullRequest"},
    "AddCommentPayload": {"commentEdge"},
    "IssueCommentEdge": {"node"},
    "IssueComment": {"id", "body"},
}

TOKEN_RE = re.compile(r'''
    (?P<ws>[\s,]+)
  | (?P<spread>\.\.\.)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?)
  | (?P<int>-?\d+)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<punct>[!$():=@\[\]{}.|&])
  | (?P<other>.)
''', re.VERBOSE)


def gql_lex(text):
    tokens = []
    i = 0
    while i < len(text):
        m = TOKEN_RE.match(text, i)
        if not m:
            raise ValueError("cannot lex at %d" % i)
        i = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        tokens.append((kind, m.group()))
    tokens.append(("eof", ""))
    return tokens


class GqlParser:
    def __init__(self, text):
        self.toks = gql_lex(text)
        self.i = 0

    def peek(self):
        return self.toks[self.i]

    def next(self):
        tok = self.toks[self.i]
        self.i += 1
        return tok

    def expect(self, kind, value=None):
        tok = self.next()
        if tok[0] != kind or (value is not None and tok[1] != value):
            raise ValueError("expected %s %s, got %r" % (kind, value, tok))
        return tok

    def parse(self):
        op = self.parse_operation()
        if self.peek()[0] != "eof":
            raise ValueError("trailing tokens")
        return op

    def parse_operation(self):
        kind, val = self.peek()
        op_type = "query"
        op_name = None
        if kind == "name" and val in ("query", "mutation", "subscription"):
            self.next()
            op_type = val
            if self.peek()[0] == "name":
                op_name = self.next()[1]
        elif kind == "punct" and val == "{":
            pass
        else:
            raise ValueError("expected an operation, got %r" % (val,))
        var_defs = {}
        if self.peek() == ("punct", "("):
            var_defs = self.parse_var_defs()
        return {"type": op_type, "name": op_name, "var_defs": var_defs,
                "selections": self.parse_selection_set()}

    def parse_var_defs(self):
        self.expect("punct", "(")
        defs = {}
        while self.peek() != ("punct", ")"):
            self.expect("punct", "$")
            name = self.expect("name")[1]
            self.expect("punct", ":")
            defs[name] = self.parse_type()
            if self.peek() == ("punct", "="):
                self.next()
                self.parse_value_literal()
        self.expect("punct", ")")
        return defs

    def parse_type(self):
        if self.peek() == ("punct", "["):
            self.next()
            inner = self.parse_type()
            self.expect("punct", "]")
            t = ("list", inner)
        else:
            t = ("named", self.expect("name")[1])
        if self.peek() == ("punct", "!"):
            self.next()
            t = ("nonnull", t)
        return t

    def parse_selection_set(self):
        self.expect("punct", "{")
        sels = []
        while self.peek() != ("punct", "}"):
            sels.append(self.parse_selection())
        self.expect("punct", "}")
        return sels

    def parse_selection(self):
        if self.peek()[0] == "spread":
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_name = self.expect("name")[1]
                return {"kind": "inline", "type": type_name,
                        "selections": self.parse_selection_set()}
            name = self.expect("name")[1]
            return {"kind": "fragment", "name": name}
        alias = None
        name = self.expect("name")[1]
        if self.peek() == ("punct", ":"):
            self.next()
            alias = name
            name = self.expect("name")[1]
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_args()
        directives = []
        while self.peek()[0] == "punct" and self.peek()[1] == "@":
            self.next()
            self.expect("name")
            if self.peek() == ("punct", "("):
                self.parse_args()
        sub = []
        if self.peek() == ("punct", "{"):
            sub = self.parse_selection_set()
        return {"kind": "field", "name": name, "alias": alias or name,
                "args": args, "selections": sub}

    def parse_args(self):
        self.expect("punct", "(")
        args = {}
        while self.peek() != ("punct", ")"):
            name = self.expect("name")[1]
            self.expect("punct", ":")
            args[name] = self.parse_value_literal()
        self.expect("punct", ")")
        return args

    def parse_value_literal(self):
        kind, val = self.peek()
        if kind == "punct" and val == "$":
            self.next()
            return ("var", self.expect("name")[1])
        if kind == "int":
            self.next()
            return ("lit", int(val))
        if kind == "float":
            self.next()
            return ("lit", float(val))
        if kind == "string":
            self.next()
            return ("lit", json.loads(val))
        if kind == "name":
            self.next()
            if val == "true":
                return ("lit", True)
            if val == "false":
                return ("lit", False)
            if val == "null":
                return ("lit", None)
            return ("enum", val)
        if kind == "punct" and val == "[":
            self.next()
            items = []
            while self.peek() != ("punct", "]"):
                items.append(self.parse_value_literal())
            self.expect("punct", "]")
            return ("list", items)
        if kind == "punct" and val == "{":
            self.next()
            obj = {}
            while self.peek() != ("punct", "}"):
                name = self.expect("name")[1]
                self.expect("punct", ":")
                obj[name] = self.parse_value_literal()
            self.expect("punct", "}")
            return ("obj", obj)
        raise ValueError("unexpected value %r" % (val,))


def gql_resolve_value(node, variables):
    kind = node[0]
    if kind == "var":
        return variables.get(node[1])
    if kind == "lit":
        return node[1]
    if kind == "enum":
        return node[1]
    if kind == "list":
        return [gql_resolve_value(v, variables) for v in node[1]]
    if kind == "obj":
        return {k: gql_resolve_value(v, variables) for k, v in node[1].items()}
    return None


class GqlError(Exception):
    pass


# -- value wrappers so the executor knows each node's GraphQL type --------------

class GVal:
    def __init__(self, gtype, value):
        self.gtype = gtype
        self.value = value


def _validate(selections, gtype, path):
    allowed = GQL_FIELDS.get(gtype)
    if allowed is None:
        raise GqlError('Cannot query field on type "%s"' % gtype)
    for sel in selections:
        if sel["kind"] == "field":
            if sel["name"] not in allowed:
                raise GqlError('Cannot query field "%s" on type "%s".' % (sel["name"], gtype))
            if sel["name"] == "__type":
                continue
            # recurse into known sub-selections
            sub = _subtype(gtype, sel["name"])
            if sub and sel["selections"]:
                _validate(sel["selections"], sub, path + [sel["name"]])
        elif sel["kind"] == "inline":
            if sel["type"] not in GQL_FIELDS and sel["type"] not in GQL_SCHEMA:
                raise GqlError('Unknown type "%s".' % sel["type"])
            _validate(sel["selections"], sel["type"], path)


def _subtype(gtype, field):
    mapping = {
        ("Query", "viewer"): "User",
        ("Query", "repository"): "Repository",
        ("Query", "node"): None,  # resolved by id; inline fragments carry the type
        ("Repository", "owner"): "User",
        ("Repository", "defaultBranchRef"): "Ref",
        ("Repository", "issue"): "Issue",
        ("Repository", "issues"): "IssueConnection",
        ("Repository", "pullRequests"): "PullRequestConnection",
        ("Repository", "pullRequest"): "PullRequest",
        ("IssueConnection", "nodes"): "Issue",
        ("IssueConnection", "pageInfo"): "PageInfo",
        ("PullRequestConnection", "nodes"): "PullRequest",
        ("PullRequestConnection", "pageInfo"): "PageInfo",
        ("PullRequest", "files"): "PullRequestChangedFileConnection",
        ("PullRequestChangedFileConnection", "nodes"): "PullRequestChangedFile",
        ("PullRequestChangedFileConnection", "pageInfo"): "PageInfo",
        ("Mutation", "createIssue"): "CreateIssuePayload",
        ("Mutation", "closeIssue"): "CloseIssuePayload",
        ("Mutation", "createPullRequest"): "CreatePullRequestPayload",
        ("Mutation", "mergePullRequest"): "MergePullRequestPayload",
        ("Mutation", "addComment"): "AddCommentPayload",
        ("CreateIssuePayload", "issue"): "Issue",
        ("CloseIssuePayload", "issue"): "Issue",
        ("CreatePullRequestPayload", "pullRequest"): "PullRequest",
        ("MergePullRequestPayload", "pullRequest"): "PullRequest",
        ("AddCommentPayload", "commentEdge"): "IssueCommentEdge",
        ("IssueCommentEdge", "node"): "IssueComment",
        ("__Type", "fields"): "__Field",
        ("__Type", "enumValues"): "__EnumValue",
    }
    return mapping.get((gtype, field))


def _cursor_for(number):
    return base64.b64encode(("cursor:%d" % number).encode("ascii")).decode("ascii")


def _cursor_num(cursor):
    try:
        raw = base64.b64decode("".join(str(cursor).split())).decode("ascii")
        if raw.startswith("cursor:"):
            return int(raw[7:])
    except Exception:
        return None
    return None


class GqlExecutor:
    def __init__(self):
        pass

    def execute(self, query_text, variables):
        try:
            op = GqlParser(query_text).parse()
        except Exception as e:
            return {"errors": [{"message": "Syntax Error: %s" % e}]}
        variables = variables or {}
        try:
            if op["type"] == "query":
                _validate(op["selections"], "Query", [])
                data = self._exec_selections(op["selections"], GVal("Query", None), variables)
            elif op["type"] == "mutation":
                _validate(op["selections"], "Mutation", [])
                data = self._exec_selections(op["selections"], GVal("Mutation", None), variables)
            else:
                return {"errors": [{"message": "Subscriptions are not supported"}]}
        except GqlError as e:
            return {"errors": [{"message": str(e)}]}
        except ApiError as e:
            return {"errors": [{"message": e.message}]}
        return {"data": data}

    # -- selection execution ---------------------------------------------------
    def _exec_selections(self, selections, gval, variables):
        out = {}
        for sel in selections:
            if sel["kind"] == "inline":
                if gval.gtype == sel["type"] or (gval.gtype is None and sel["type"] in GQL_FIELDS):
                    out.update(self._exec_selections(sel["selections"], gval, variables))
                elif gval.value is not None and isinstance(gval.value, dict) and gval.value.get("_gtype") == sel["type"]:
                    sub = GVal(sel["type"], gval.value)
                    out.update(self._exec_selections(sel["selections"], sub, variables))
                continue
            if sel["kind"] == "fragment":
                continue
            out[sel["alias"]] = self._exec_field(sel, gval, variables)
        return out

    def _args(self, sel, variables):
        return {k: gql_resolve_value(v, variables) for k, v in sel["args"].items()}

    def _exec_field(self, sel, gval, variables):
        name = sel["name"]
        args = self._args(sel, variables)
        gtype = gval.gtype
        if name == "__type":
            return self._introspect(args.get("name"), sel["selections"], variables)
        if gtype == "Query":
            return self._query_field(sel, args, variables)
        if gtype == "Mutation":
            return self._mutation_field(sel, args, variables)
        if gtype == "User":
            u = gval.value or {}
            return u.get("login") if name == "login" else u.get(name)
        if gtype == "Ref":
            return (gval.value or {}).get("name")
        if gtype == "Repository":
            return self._repo_field(sel, gval.value, args, variables)
        if gtype == "Issue":
            return self._issue_field(sel, gval.value, args, variables)
        if gtype == "IssueConnection":
            return self._issue_conn_field(sel, gval.value, args, variables)
        if gtype == "PullRequest":
            return self._pr_field(sel, gval.value, args, variables)
        if gtype == "PullRequestConnection":
            return self._pr_conn_field(sel, gval.value, args, variables)
        if gtype == "PullRequestChangedFileConnection":
            return self._pr_files_conn_field(sel, gval.value, args, variables)
        if gtype == "PullRequestChangedFile":
            return (gval.value or {}).get(name)
        if gtype == "PageInfo":
            return (gval.value or {}).get(name)
        if gtype == "__Type":
            t = gval.value or {}
            if name == "fields":
                inc = args.get("includeDeprecated", False)
                return [{"name": f} for f in t.get("fields", [])]
            if name == "enumValues":
                return [{"name": v} for v in t.get("enumValues", [])]
            return t.get(name)
        if gtype == "__Field" or gtype == "__EnumValue":
            return (gval.value or {}).get(name)
        if gtype in ("CreateIssuePayload", "CloseIssuePayload"):
            issue = (gval.value or {}).get("issue")
            return self._exec_selections(sel["selections"], GVal("Issue", issue), variables) if issue is not None else None
        if gtype in ("CreatePullRequestPayload", "MergePullRequestPayload"):
            pr = (gval.value or {}).get("pullRequest")
            return self._exec_selections(sel["selections"], GVal("PullRequest", pr), variables) if pr is not None else None
        if gtype == "AddCommentPayload":
            edge = (gval.value or {}).get("commentEdge")
            if edge is None:
                return None
            return self._exec_selections(sel["selections"], GVal("IssueCommentEdge", edge), variables)
        if gtype == "IssueCommentEdge":
            node = (gval.value or {}).get("node")
            return self._exec_selections(sel["selections"], GVal("IssueComment", node), variables) if node is not None else None
        if gtype == "IssueComment":
            if name == "id":
                return (gval.value or {}).get("node_id")
            return (gval.value or {}).get(name)
        return None

    def _introspect(self, type_name, selections, variables):
        info = GQL_SCHEMA.get(type_name)
        if info is None:
            return None
        gval = GVal("__Type", info)
        return self._exec_selections(selections, gval, variables)

    # -- Query root ------------------------------------------------------------
    def _query_field(self, sel, args, variables):
        name = sel["name"]
        if name == "viewer":
            return self._exec_selections(sel["selections"],
                                         GVal("User", {"login": VIEWER_LOGIN, "id": VIEWER_ID}),
                                         variables)
        if name == "repository":
            owner = args.get("owner")
            repo_name = args.get("name")
            if owner != VIEWER_LOGIN:
                return None
            repo = FORGE.get_repo(owner, repo_name)
            if repo is None:
                return None
            return self._exec_selections(sel["selections"], GVal("Repository", repo), variables)
        if name == "node":
            node_id = args.get("id")
            decoded = ungid(node_id)
            if decoded is None:
                return None
            kind, rest = decoded
            if kind == "Repository":
                parts = rest.split("/")
                if len(parts) != 2:
                    return None
                repo = FORGE.get_repo(parts[0], parts[1])
                if repo is None:
                    return None
                return self._exec_selections(sel["selections"],
                                             GVal("Repository", repo), variables)
            return None
        return None

    # -- Repository ------------------------------------------------------------
    def _repo_field(self, sel, repo, args, variables):
        name = sel["name"]
        if name == "id":
            return repo_gid(repo)
        if name == "databaseId":
            return repo.db_id
        if name == "name":
            return repo.name
        if name == "nameWithOwner":
            return "%s/%s" % (repo.owner, repo.name)
        if name == "owner":
            return self._exec_selections(sel["selections"],
                                         GVal("User", {"login": repo.owner}), variables)
        if name == "defaultBranchRef":
            if repo.head_oid() is None:
                return None
            return self._exec_selections(sel["selections"],
                                         GVal("Ref", {"name": repo.default_branch}), variables)
        if name == "viewerPermission":
            return "ADMIN"
        if name == "hasIssuesEnabled":
            return True
        if name == "description":
            return repo.description
        if name == "isPrivate":
            return repo.private
        if name == "issue":
            issue = repo.issues.get(args.get("number"))
            if issue is None:
                return None
            return self._exec_selections(sel["selections"], GVal("Issue", issue), variables)
        if name == "issues":
            return self._exec_selections(sel["selections"],
                                         GVal("IssueConnection", ("issues", repo, args)), variables)
        if name == "pullRequests":
            return self._exec_selections(sel["selections"],
                                         GVal("PullRequestConnection", ("pulls", repo, args)), variables)
        if name == "pullRequest":
            pr = repo.pulls.get(args.get("number"))
            if pr is None:
                return None
            return self._exec_selections(sel["selections"], GVal("PullRequest", pr), variables)
        return None

    def _issue_field(self, sel, issue, args, variables):
        name = sel["name"]
        if name == "id":
            return issue_gid(_repo_of_issue(issue), issue["number"])
        if name == "state":
            return issue["state"].upper()
        return issue.get(name)

    def _issue_conn_field(self, sel, value, args, variables):
        _, repo, qargs = value
        name = sel["name"]
        if name == "nodes":
            issues = self._filtered_issues(repo, qargs)
            return [self._exec_selections(sel["selections"], GVal("Issue", i), variables)
                    for i in issues]
        if name == "pageInfo":
            issues = self._filtered_issues(repo, qargs)
            return self._exec_selections(sel["selections"],
                                         GVal("PageInfo", self._page_info(repo, qargs, issues)),
                                         variables)
        if name == "totalCount":
            return len(self._filtered_issues(repo, qargs))
        return None

    def _filtered_issues(self, repo, qargs):
        issues = list(repo.issues.values())
        states = qargs.get("states")
        if states:
            wanted = {str(s).lower() for s in states}
            issues = [i for i in issues if i["state"] in wanted]
        order_by = qargs.get("orderBy") or {}
        field = order_by.get("field", "CREATED_AT")
        direction = order_by.get("direction", "DESC")
        reverse = direction != "ASC"
        issues.sort(key=lambda i: i["number"], reverse=reverse)
        first = qargs.get("first")
        after = qargs.get("after")
        if after:
            num = _cursor_num(after)
            if num is not None:
                issues = [i for i in issues if (i["number"] > num if not reverse else i["number"] < num)]
        if first is not None:
            issues = issues[:first]
        return issues

    def _page_info(self, repo, qargs, page_issues):
        # recompute the full filtered list to know whether more pages exist
        issues = list(repo.issues.values())
        states = qargs.get("states")
        if states:
            wanted = {str(s).lower() for s in states}
            issues = [i for i in issues if i["state"] in wanted]
        order_by = qargs.get("orderBy") or {}
        direction = order_by.get("direction", "DESC")
        reverse = direction != "ASC"
        issues.sort(key=lambda i: i["number"], reverse=reverse)
        after = qargs.get("after")
        if after:
            num = _cursor_num(after)
            if num is not None:
                issues = [i for i in issues if (i["number"] > num if not reverse else i["number"] < num)]
        first = qargs.get("first")
        has_next = False
        if first is not None and len(issues) > len(page_issues):
            has_next = True
        end_cursor = _cursor_for(page_issues[-1]["number"]) if page_issues else None
        return {"hasNextPage": has_next, "hasPreviousPage": False,
                "endCursor": end_cursor, "startCursor": None}

    def _pr_field(self, sel, pr, args, variables):
        name = sel["name"]
        if name == "id":
            return pull_gid(_repo_of_pull(pr), pr["number"])
        if name == "state":
            if pr["merged"]:
                return "MERGED"
            return pr["state"].upper()
        if name == "headRefName":
            return pr["head"]
        if name == "baseRefName":
            return pr["base"]
        if name == "mergeable":
            return pr_mergeable(_repo_of_pull(pr), pr)
        if name == "merged":
            return bool(pr["merged"])
        if name == "files":
            files = pr_files(_repo_of_pull(pr), pr)
            first = args.get("first")
            if first is not None:
                files = files[:first]
            nodes = [{"path": f["filename"], "additions": f["additions"],
                      "deletions": f["deletions"]} for f in files]
            return self._exec_selections(
                sel["selections"],
                GVal("PullRequestChangedFileConnection", ("files", nodes)), variables)
        return pr.get(name)

    def _pr_conn_field(self, sel, value, args, variables):
        _, repo, qargs = value
        name = sel["name"]
        if name == "nodes":
            pulls = [p for p in sorted(repo.pulls.values(), key=lambda p: p["number"])
                     if p["state"] == "open"]
            first = qargs.get("first")
            if first is not None:
                pulls = pulls[:first]
            return [self._exec_selections(sel["selections"], GVal("PullRequest", p), variables)
                    for p in pulls]
        if name == "pageInfo":
            return {"hasNextPage": False, "hasPreviousPage": False,
                    "endCursor": None, "startCursor": None}
        if name == "totalCount":
            return len([p for p in repo.pulls.values() if p["state"] == "open"])
        return None

    def _pr_files_conn_field(self, sel, value, args, variables):
        _, nodes = value
        name = sel["name"]
        if name == "nodes":
            return [self._exec_selections(sel["selections"],
                                          GVal("PullRequestChangedFile", n), variables)
                    for n in nodes]
        if name == "pageInfo":
            return {"hasNextPage": False, "hasPreviousPage": False,
                    "endCursor": None, "startCursor": None}
        return None

    # -- Mutation root ---------------------------------------------------------
    def _mutation_field(self, sel, args, variables):
        name = sel["name"]
        inp = args.get("input") or {}
        if name == "createIssue":
            repo = self._repo_by_gid(inp.get("repositoryId"))
            if repo is None:
                raise GqlError("Repository not found")
            title = inp.get("title", "")
            body = inp.get("body", "")
            number = repo.next_issue
            repo.next_issue += 1
            issue = {"number": number, "title": title, "body": body, "state": "open",
                     "labels": [], "comments": [], "db_id": 100000 + number, "_repo": repo}
            repo.issues[number] = issue
            return self._exec_selections(sel["selections"],
                                         GVal("CreateIssuePayload", {"issue": issue}), variables)
        if name == "closeIssue":
            repo, issue = self._issue_by_gid(inp.get("issueId"))
            if issue is None:
                raise GqlError("Issue not found")
            issue["state"] = "closed"
            return self._exec_selections(sel["selections"],
                                         GVal("CloseIssuePayload", {"issue": issue}), variables)
        if name == "createPullRequest":
            repo = self._repo_by_gid(inp.get("repositoryId"))
            if repo is None:
                raise GqlError("Repository not found")
            head = inp.get("headRefName", "")
            base = inp.get("baseRefName", "")
            title = inp.get("title", "")
            if repo.head_oid(head) is None or repo.head_oid(base) is None:
                raise GqlError("Head or base branch does not exist")
            number = repo.next_pull
            repo.next_pull += 1
            pr = {"number": number, "title": title, "body": "", "state": "open",
                  "merged": False, "merged_at": None, "merge_commit_sha": None,
                  "head": head, "base": base, "db_id": 200000 + number, "_repo": repo}
            repo.pulls[number] = pr
            return self._exec_selections(sel["selections"],
                                         GVal("CreatePullRequestPayload", {"pullRequest": pr}),
                                         variables)
        if name == "mergePullRequest":
            repo, pr = self._pull_by_gid(inp.get("pullRequestId"))
            if pr is None:
                raise GqlError("Pull request not found")
            if pr["state"] != "open":
                raise GqlError("Pull request is not open")
            method = (inp.get("mergeMethod") or "SQUASH").lower()
            merge_sha, conflict = do_merge(repo, pr, method)
            if conflict:
                raise GqlError("Merge conflict")
            return self._exec_selections(sel["selections"],
                                         GVal("MergePullRequestPayload", {"pullRequest": pr}),
                                         variables)
        if name == "addComment":
            repo, issue = self._issue_by_gid(inp.get("subjectId"))
            if issue is None:
                raise GqlError("Subject not found")
            body = inp.get("body", "")
            cid = repo.next_comment
            repo.next_comment += 1
            comment = {"id": cid, "node_id": comment_gid(repo, cid), "body": body,
                       "user": {"login": VIEWER_LOGIN}}
            issue["comments"].append(comment)
            edge = {"node": comment}
            return self._exec_selections(sel["selections"],
                                         GVal("AddCommentPayload", {"commentEdge": edge}),
                                         variables)
        return None

    # -- global-id lookups ------------------------------------------------------
    def _repo_by_gid(self, gid_value):
        decoded = ungid(gid_value)
        if decoded is None or decoded[0] != "Repository":
            return None
        parts = decoded[1].split("/")
        if len(parts) != 2:
            return None
        return FORGE.get_repo(parts[0], parts[1])

    def _issue_by_gid(self, gid_value):
        decoded = ungid(gid_value)
        if decoded is None or decoded[0] != "Issue":
            return None, None
        parts = decoded[1].split("/")
        if len(parts) != 3:
            return None, None
        repo = FORGE.get_repo(parts[0], parts[1])
        if repo is None:
            return None, None
        try:
            number = int(parts[2])
        except ValueError:
            return None, None
        return repo, repo.issues.get(number)

    def _pull_by_gid(self, gid_value):
        decoded = ungid(gid_value)
        if decoded is None or decoded[0] != "PullRequest":
            return None, None
        parts = decoded[1].split("/")
        if len(parts) != 3:
            return None, None
        repo = FORGE.get_repo(parts[0], parts[1])
        if repo is None:
            return None, None
        try:
            number = int(parts[2])
        except ValueError:
            return None, None
        return repo, repo.pulls.get(number)


# The executor needs the repo that owns an issue/PR for id fields; each
# issue/PR dict carries a "_repo" back-reference (the JSON helpers build
# fresh dicts, so it never leaks into a response).
def _repo_of_issue(issue):
    return issue.get("_repo")


def _repo_of_pull(pr):
    return pr.get("_repo")


GQL_EXECUTOR = GqlExecutor()


def handle_graphql(ctx):
    check_auth(ctx)
    try:
        body = ctx.json_body()
    except ApiError:
        raise
    if isinstance(body, list):
        out = []
        for entry in body:
            if not isinstance(entry, dict):
                out.append({"errors": [{"message": "Each operation must be an object"}]})
                continue
            out.append(GQL_EXECUTOR.execute(entry.get("query", ""),
                                            entry.get("variables") or {}))
        ctx.handler.send_json(200, out)
        return
    if not isinstance(body, dict):
        raise ApiError(400, "Request body must be a JSON object")
    result = GQL_EXECUTOR.execute(body.get("query", ""), body.get("variables") or {})
    ctx.handler.send_json(200, result)

# --------------------------------------------------------------------------------------------
# MCP (Model Context Protocol) at /mcp — modern 2026-07-28 + legacy handshake
# --------------------------------------------------------------------------------------------

MCP_REVISIONS = ["2026-07-28", "2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"]
MCP_SERVER_INFO = {"name": "github-core-clone-forge", "version": FORGE_VERSION}

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a repository owned by the authenticated user.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string", "description": "Repository name"},
                                    "description": {"type": "string", "description": "Repository description"},
                                    "private": {"type": "boolean", "description": "Whether the repository is private"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string", "description": "Repository owner login"},
                                    "repo": {"type": "string", "description": "Repository name"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string", "description": "Repository owner login"},
                                    "repo": {"type": "string", "description": "Repository name"},
                                    "title": {"type": "string", "description": "Issue title"},
                                    "body": {"type": "string", "description": "Issue body"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string", "description": "Repository owner login"},
                                    "repo": {"type": "string", "description": "Repository name"},
                                    "state": {"type": "string", "description": "Issue state: open, closed or all"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request from a head branch into a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string", "description": "Repository owner login"},
                                    "repo": {"type": "string", "description": "Repository name"},
                                    "title": {"type": "string", "description": "Pull request title"},
                                    "body": {"type": "string", "description": "Pull request body"},
                                    "head": {"type": "string", "description": "Head branch name"},
                                    "base": {"type": "string", "description": "Base branch name"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request with a squash commit.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string", "description": "Repository owner login"},
                                    "repo": {"type": "string", "description": "Repository name"},
                                    "pull_number": {"type": "integer", "description": "Pull request number"}},
                     "required": ["owner", "repo", "pull_number"]}},
]

MCP_TOOLS_BY_NAME = {t["name"]: t for t in MCP_TOOLS}


def _mcp_result(payload):
    text = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": payload}


def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": "error: " + message}], "isError": True}


def _mcp_repo_arg(args, key="repo"):
    owner = args.get("owner")
    name = args.get(key)
    if not isinstance(owner, str) or not owner:
        return None, "owner is required"
    if not isinstance(name, str) or not name:
        return None, "repo is required"
    if owner != VIEWER_LOGIN:
        return None, "Not Found"
    repo = FORGE.get_repo(owner, name)
    if repo is None:
        return None, "Not Found"
    return repo, None


def mcp_call_tool(name, args):
    """Returns (result_dict, is_error)."""
    tool = MCP_TOOLS_BY_NAME.get(name)
    if tool is None:
        return None, -32601, "Method not found: no tool named %s" % name
    missing = [p for p in tool["inputSchema"].get("required", []) if args.get(p) in (None, "")]
    if missing:
        return _mcp_error_result("missing required argument(s): %s" % ", ".join(missing)), 0, None
    try:
        if name == "create_repo":
            repo_name = args["name"]
            repo = FORGE.create_repo(VIEWER_LOGIN, repo_name, args.get("private", False),
                                     args.get("description", ""))
            if repo is None:
                return _mcp_error_result("Repository already exists"), 0, None
            return _mcp_result(repo_json(repo)), 0, None
        if name == "get_repo":
            repo, err = _mcp_repo_arg(args)
            if err:
                return _mcp_error_result(err), 0, None
            return _mcp_result(repo_json(repo)), 0, None
        if name == "create_issue":
            repo, err = _mcp_repo_arg(args)
            if err:
                return _mcp_error_result(err), 0, None
            title = args.get("title", "")
            body = args.get("body", "")
            number = repo.next_issue
            repo.next_issue += 1
            issue = {"number": number, "title": title, "body": body, "state": "open",
                     "labels": [], "comments": [], "db_id": 100000 + number, "_repo": repo}
            repo.issues[number] = issue
            return _mcp_result(issue_json(repo, issue)), 0, None
        if name == "list_issues":
            repo, err = _mcp_repo_arg(args)
            if err:
                return _mcp_error_result(err), 0, None
            state = str(args.get("state") or "open").lower()
            issues = list(repo.issues.values())
            if state != "all":
                issues = [i for i in issues if i["state"] == state]
            issues.sort(key=lambda i: i["number"])
            return _mcp_result([issue_json(repo, i) for i in issues]), 0, None
        if name == "create_pull_request":
            repo, err = _mcp_repo_arg(args)
            if err:
                return _mcp_error_result(err), 0, None
            head = args.get("head", "")
            base = args.get("base", "")
            if repo.head_oid(head) is None:
                return _mcp_error_result("Head branch '%s' does not exist" % head), 0, None
            if repo.head_oid(base) is None:
                return _mcp_error_result("Base branch '%s' does not exist" % base), 0, None
            for pr in repo.pulls.values():
                if pr["head"] == head and pr["state"] == "open":
                    return _mcp_error_result("A pull request already exists for %s" % head), 0, None
            number = repo.next_pull
            repo.next_pull += 1
            pr = {"number": number, "title": args.get("title", ""),
                  "body": args.get("body", ""), "state": "open",
                  "merged": False, "merged_at": None, "merge_commit_sha": None,
                  "head": head, "base": base, "db_id": 200000 + number, "_repo": repo}
            repo.pulls[number] = pr
            return _mcp_result(pull_json(repo, pr)), 0, None
        if name == "merge_pull_request":
            repo, err = _mcp_repo_arg(args)
            if err:
                return _mcp_error_result(err), 0, None
            try:
                number = int(args.get("pull_number"))
            except (TypeError, ValueError):
                return _mcp_error_result("pull_number is required"), 0, None
            pr = repo.pulls.get(number)
            if pr is None:
                return _mcp_error_result("Pull request not found"), 0, None
            if pr["state"] != "open":
                return _mcp_error_result("Pull request is not open"), 0, None
            merge_sha, conflict = do_merge(repo, pr, "squash")
            if conflict:
                return _mcp_error_result("Merge conflict"), 0, None
            return _mcp_result(pull_json(repo, pr)), 0, None
    except ApiError as e:
        return _mcp_error_result(e.message), 0, None
    return _mcp_error_result("unknown tool"), 0, None


def handle_mcp(ctx):
    """JSON-RPC over HTTP at /mcp. Auth first (401 without a token)."""
    if ctx.method == "DELETE":
        ctx.handler.send_no_content(204)
        return
    if ctx.method != "POST":
        raise ApiError(405, "Method Not Allowed")
    check_auth(ctx)
    # malformed JSON body -> HTTP 400, JSON-RPC -32700
    try:
        body = json.loads(ctx.body.decode("utf-8")) if ctx.body and ctx.body.strip() else None
    except Exception:
        err = {"jsonrpc": "2.0", "id": None,
               "error": {"code": -32700, "message": "Parse error"}}
        ctx.handler.send_json(400, err)
        return
    if body is None or not isinstance(body, dict):
        err = {"jsonrpc": "2.0", "id": None,
               "error": {"code": -32600, "message": "Invalid Request"}}
        ctx.handler.send_json(400, err)
        return
    method = body.get("method", "")
    req_id = body.get("id", None)
    params = body.get("params") or {}
    # notifications carry no id: acknowledge with 202 and no body
    if req_id is None and method.startswith("notifications/"):
        ctx.handler.send_no_content(202)
        return
    result, err_code, err_msg = _mcp_dispatch(method, params)
    if err_code:
        resp = {"jsonrpc": "2.0", "id": req_id,
                "error": {"code": err_code, "message": err_msg}}
    else:
        resp = {"jsonrpc": "2.0", "id": req_id, "result": result}
    ctx.handler.send_json(200, resp)


def _mcp_dispatch(method, params):
    """-> (result, error_code, error_message)."""
    if method == "server/discover":
        result = {
            "resultType": "discover",
            "supportedVersions": list(MCP_REVISIONS),
            "capabilities": {"tools": {}},
            "instructions": "A GitHub-compatible git forge.",
            "serverInfo": dict(MCP_SERVER_INFO),
            "_meta": {"io.modelcontextprotocol/serverInfo": dict(MCP_SERVER_INFO)},
        }
        return result, 0, None
    if method == "initialize":
        requested = params.get("protocolVersion")
        version = requested if requested in MCP_REVISIONS else MCP_REVISIONS[0]
        return {"protocolVersion": version,
                "capabilities": {"tools": {}},
                "serverInfo": dict(MCP_SERVER_INFO)}, 0, None
    if method == "tools/list":
        return {"tools": [dict(t) for t in MCP_TOOLS]}, 0, None
    if method == "tools/call":
        name = params.get("name", "")
        args = params.get("arguments") or {}
        if not isinstance(args, dict):
            return None, -32602, "Invalid params: arguments must be an object"
        result, code, msg = mcp_call_tool(name, args)
        if code:
            return None, code, msg
        return result, 0, None
    if method.startswith("notifications/"):
        return {}, 0, None
    return None, -32601, "Method not found: %s" % method


# --------------------------------------------------------------------------------------------
# router
# --------------------------------------------------------------------------------------------

def route(ctx):
    method = ctx.method
    path = ctx.path

    # health probe (no auth)
    if method == "GET" and path == "/healthz":
        ctx.handler.send_json(200, {"ok": True})
        return

    # git smart HTTP: /{owner}/{repo}.git/...
    m = re.match(r"^/([^/]+)/([^/]+)\.git/(info/refs|git-upload-pack|git-receive-pack)$", path)
    if m:
        owner, repo_name, service = m.group(1), unquote(m.group(2)), m.group(3)
        if service == "info/refs":
            svc = ctx.q("service", "")
            if svc not in ("git-upload-pack", "git-receive-pack"):
                raise ApiError(400, "service parameter is required")
            if method != "GET":
                raise ApiError(405, "Method Not Allowed")
            handle_info_refs(ctx, owner, repo_name, svc)
        elif service == "git-upload-pack":
            if method != "POST":
                raise ApiError(405, "Method Not Allowed")
            handle_upload_pack(ctx, owner, repo_name)
        else:
            if method != "POST":
                raise ApiError(405, "Method Not Allowed")
            handle_receive_pack(ctx, owner, repo_name)
        return

    # MCP
    if path == "/mcp":
        handle_mcp(ctx)
        return

    # GraphQL
    if path == "/api/graphql":
        if method != "POST":
            raise ApiError(405, "Method Not Allowed")
        handle_graphql(ctx)
        return

    # REST v3
    if path == "/api/v3" or path == "/api/v3/":
        if method != "GET":
            raise ApiError(405, "Method Not Allowed")
        rest_root(ctx)
        return
    if path.startswith("/api/v3/"):
        rest_route(ctx, path[len("/api/v3/"):])
        return

    # everything else: JSON 404 (never HTML)
    raise ApiError(404, "Not Found")


def rest_route(ctx, rest):
    method = ctx.method
    parts = [unquote(p) for p in rest.split("/") if p != ""]

    if parts == ["meta"] and method == "GET":
        rest_meta(ctx)
        return
    if parts == ["user"] and method == "GET":
        rest_user(ctx)
        return
    if parts == ["user", "repos"]:
        if method == "POST":
            rest_create_repo(ctx)
            return
        if method == "GET":
            rest_list_user_repos(ctx)
            return
        raise ApiError(405, "Method Not Allowed")

    if len(parts) >= 2 and parts[0] == "repos":
        owner, name = parts[1], parts[2] if len(parts) > 2 else ""
        tail = parts[3:]
        if not tail:
            if method == "GET":
                rest_get_repo(ctx, owner, name)
                return
            if method == "PATCH":
                rest_patch_repo(ctx, owner, name)
                return
            if method == "DELETE":
                rest_delete_repo(ctx, owner, name)
                return
            raise ApiError(405, "Method Not Allowed")
        if tail == ["branches"] and method == "GET":
            rest_list_branches(ctx, owner, name)
            return
        if len(tail) == 2 and tail[0] == "branches" and method == "GET":
            rest_get_branch(ctx, owner, name, tail[1])
            return
        if tail == ["commits"] and method == "GET":
            rest_list_commits(ctx, owner, name)
            return
        if tail == ["git", "refs"] and method == "POST":
            rest_create_ref(ctx, owner, name)
            return
        if len(tail) >= 3 and tail[0] == "git" and tail[1] == "refs" and method == "GET":
            rest_get_ref(ctx, owner, name, "/".join(tail[2:]))
            return
        if tail[0] == "contents":
            fpath = "/".join(tail[1:])
            if method == "GET":
                rest_get_contents(ctx, owner, name, fpath)
                return
            if method == "PUT":
                rest_put_contents(ctx, owner, name, fpath)
                return
            if method == "DELETE":
                rest_delete_contents(ctx, owner, name, fpath)
                return
            raise ApiError(405, "Method Not Allowed")
        if tail == ["labels"] and method == "POST":
            rest_create_label(ctx, owner, name)
            return
        if tail == ["issues"]:
            if method == "POST":
                rest_create_issue(ctx, owner, name)
                return
            if method == "GET":
                rest_list_issues(ctx, owner, name)
                return
            raise ApiError(405, "Method Not Allowed")
        if len(tail) == 2 and tail[0] == "issues" and tail[1].isdigit():
            number = int(tail[1])
            if method == "GET":
                rest_get_issue(ctx, owner, name, number)
                return
            if method == "PATCH":
                rest_patch_issue(ctx, owner, name, number)
                return
            raise ApiError(405, "Method Not Allowed")
        if len(tail) == 3 and tail[0] == "issues" and tail[1].isdigit() and tail[2] == "comments":
            number = int(tail[1])
            if method == "POST":
                rest_create_comment(ctx, owner, name, number)
                return
            if method == "GET":
                rest_list_comments(ctx, owner, name, number)
                return
            raise ApiError(405, "Method Not Allowed")
        if tail == ["pulls"]:
            if method == "POST":
                rest_create_pull(ctx, owner, name)
                return
            if method == "GET":
                rest_list_pulls(ctx, owner, name)
                return
            raise ApiError(405, "Method Not Allowed")
        if len(tail) == 2 and tail[0] == "pulls" and tail[1].isdigit():
            number = int(tail[1])
            if method == "GET":
                rest_get_pull(ctx, owner, name, number)
                return
            raise ApiError(405, "Method Not Allowed")
        if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() and tail[2] == "files":
            if method == "GET":
                rest_list_pull_files(ctx, owner, name, int(tail[1]))
                return
            raise ApiError(405, "Method Not Allowed")
        if len(tail) == 3 and tail[0] == "pulls" and tail[1].isdigit() and tail[2] == "merge":
            if method == "PUT":
                rest_merge_pull(ctx, owner, name, int(tail[1]))
                return
            raise ApiError(405, "Method Not Allowed")

    raise ApiError(404, "Not Found")


# --------------------------------------------------------------------------------------------
# lifecycle: bind, register, poll /done, exit 0
# --------------------------------------------------------------------------------------------

def http_json(url, method="GET", body=None, timeout=30):
    data = json_bytes(body) if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
            return resp.status, json.loads(raw.decode("utf-8")) if raw else {}
    except urllib.error.HTTPError as e:
        raw = e.read()
        try:
            return e.code, json.loads(raw.decode("utf-8")) if raw else {}
        except Exception:
            return e.code, {}
    except Exception:
        return None, {}


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=0)
    args = ap.parse_args()

    server = ForgeServer(("127.0.0.1", args.port), ForgeHandler)
    server.daemon_threads = True
    port = server.server_address[1]
    sys.stderr.write("[forge] listening on 127.0.0.1:%d\n" % port)
    sys.stderr.flush()

    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if not env_url:
        sys.stderr.write("[forge] MAKEFUN_ENV_URL is not set: serving without registering\n")
        sys.stderr.flush()
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        return 0

    # register: first wins; 409 means another entry already registered
    attempt = 0
    while True:
        status, _ = http_json(env_url + "/register", "POST", {"port": port}, timeout=30)
        if status in (200, 409):
            break
        if status in (400, 405):
            sys.stderr.write("[forge] register answered HTTP %s; exiting\n" % status)
            return 1
        time.sleep(min(2.0, 0.25 * (2 ** min(attempt, 3))))
        attempt += 1
    sys.stderr.write("[forge] registered port %d\n" % port)
    sys.stderr.flush()

    # poll /done until the trial is over
    attempt = 0
    while True:
        status, body = http_json(env_url + "/done", "GET", timeout=30)
        if status == 200 and isinstance(body, dict) and body.get("done") is True:
            break
        time.sleep(min(2.0, 0.25 * (2 ** min(attempt, 3))))
        attempt += 1

    server.shutdown()
    server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
