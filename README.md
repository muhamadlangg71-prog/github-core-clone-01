# github-core-clone-01 — a GitHub-compatible git forge

A standalone git forge in a single Python file (`main.py`, stdlib only, no
dependencies, no UI, no outside service). It serves, from its own in-memory
store:

- **git smart HTTP** — clone and push over `/{owner}/{repo}.git`, protocol v0
  and v2 (`ls-refs`, `fetch` with shallow/deepen and have/want negotiation,
  `receive-pack` with report-status, sideband framing, fast-forward rules,
  non-fast-forward refusal with reason `non-fast-forward`). Packs are built
  and read in-process (plain objects, OFS/REF delta resolution on read).
- **REST v3** (`/api/v3`) — repositories, branches, commits, git refs,
  contents (create/update/delete with real git blob/commit SHAs), labels,
  issues (+ comments), pull requests (+ files, squash merge with real
  three-way merge and conflict detection), pagination with `Link: rel="next"`.
- **GraphQL v4** (`/api/graphql`) — the documents `gh` and
  `github-mcp-server` send: `viewer`, `repository` (+ `issue(s)`,
  `pullRequest(s)`, `defaultBranchRef`, `viewerPermission`), `node(id:)`
  Relay round-trip, `__type` introspection, `createIssue` / `closeIssue` /
  `createPullRequest` / `mergePullRequest` / `addComment` mutations,
  cursor pagination, operation batching, invalid-field → HTTP 200 + `errors`.
- **MCP** (`/mcp`) — JSON-RPC 2.0, modern `server/discover` (2026-07-28)
  and legacy `initialize` handshake, `tools/list` and `tools/call` for
  `create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request`, `merge_pull_request` (all acting on the same store
  as REST/GraphQL).

## Auth

Any non-empty `Authorization: Bearer <token>` is the viewer `adaiversen`
(the scenario's viewer login — the token does not encode it; the scenario
seed is fixed). Missing token → 401. A repository belongs to the viewer;
the same name under another owner is 404, never 403.

## Run

```
python3 main.py [--port N]
```

Lifecycle (per the kit's `starter/main.ts`): with `MAKEFUN_ENV_URL` set the
process binds an ephemeral port, POSTs `{"port": N}` to
`$MAKEFUN_ENV_URL/register`, polls `GET $MAKEFUN_ENV_URL/done` until
`{"done": true}`, then exits 0. Without it, it just serves on the chosen
(or an ephemeral) port — handy for local runs with the kit's runner:

```
node --experimental-strip-types sdk/run.ts --url http://127.0.0.1:PORT --token TOK [--perf]
```

## Determinism

Server-created commits use a fixed author/committer (`ada iversen
<adaiversen@example.invalid>`) and a fixed timestamp; ids are counters;
no wall clock or randomness reaches stored state (the `X-GitHub-Request-Id`
header is a per-process counter). Two runs over the same request sequence
produce the same state.
