# Handoff Snapshot

Snapshot date: 2026-07-19 (America/Los_Angeles)

## Project Truth

- Mac integration repository: `/Users/mjkang/Develop/poincare`, branch `main`.
- Harness v2 pivot base: `7ce913d87be973256517ea862fb4d3dbfae7cb82`,
  equal to `origin/main` before the implementation. Inspect the current commit
  and working tree before acting; preserve any later changes.
- An exact stdin probe at the pivot base failed with `Unknown identifier
  Poincare.poincare_conjecture`.
- The repository is still incomplete. Completion means Lean checks exactly
  `Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`, its
  axiom footprint is allowed, and the full completion audit passes in a clean,
  stable integration checkout.

`CURRENT_STATUS.md` was generated on 2026-06-30 and `harness/ledger.json` ends
with the 2026-07-07 legacy selector-assembly work. Both are historical until
regenerated or revalidated against the current commit. Lean and the current
diff remain authoritative.

## Current Theorem-Shaped Task

The first Harness v2 exercise is
`automatic-scalar-derivative-constructor` revision 1, attempt Job
`automatic-scalar-derivative-constructor-a01`, frozen at
`7ce913d87be973256517ea862fb4d3dbfae7cb82`.

Its single allowed source file is:

```text
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean
```

The objective is to add the frozen `ofReactionFields` constructor and derive
`scalarTimeDerivativeJointContinuous` from `reaction.jointMetricEntries` via
the existing theorem
`scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three`.
The constructor may not add `ScalarTimeDerivativeJointContinuous` or scalar
domination as a replacement argument. The Task and Job source records are
staged in ignored `harness/v2/state/tasks/` and `harness/v2/state/queue/`; they
must be transferred separately into an owner-only import directory on
`mj-zima`, given a fresh future lease expiry, and imported into the runtime
store rather than committed as queue state. Transfer only the current Task and
queue Job JSON. Do not copy the Mac SQLite database, `state/staging/**`, or
`state/jobs/**`; those are stale interrupted dry-run evidence.

The previous broad positive-time-overlap and compact-history surfaces remain
important context, but this narrower constructor is the selected first
dependency reduction. Do not redispatch the last legacy ledger entry.

## Executable Harness Boundary

The primary path is:

```text
Codex GPT on mj-zima
  -> Harness v2 Task/Job SQLite, leases, artifacts, worktrees, and gates
  -> one fresh bounded Pi JSON Job session
  -> Leanstral on the existing private vLLM endpoint
```

Codex is the only frontier selector, worktree allocator, reviewer, gate owner,
Task acceptance authority, and commit authority. Each Job gets a new Pi
process/session. Pi built-ins are disabled, and Leanstral receives exactly:

- `read_context`
- `search_symbol`
- `apply_patch_scoped`
- `lean_check`
- `git_diff`
- `report_blocked`

There is no worker access to an unrestricted shell, SSH, arbitrary filesystem
or network tools, Git mutation, worktree deletion, Docker, Ray, tmux, or model
service management. `harness/v2/worker/` is fallback-only: keep its endpoint
health check, deterministic prompt snapshot, and explicit one-shot inference
path, but do not extend it into another agent loop.

The control plane stores validated Task/Job transitions and fenced leases in
SQLite and keeps prompts, Pi JSON events, tool results, diffs, compiler output,
blocked reports, gates, and reviews append-only under ignored Job artifacts. A
passed Job never accepts its Task; Codex must inspect the diff and independently
rerun the frozen gate first.

## Verified Live Deployment Facts

Read-only checks on 2026-07-19 found:

- `mj-zima` has the repository cloned at `/srv/projects/poincare` at
  `7ce913d87be973256517ea862fb4d3dbfae7cb82`.
- The project toolchain reports Lean `4.30.0-rc2` on `mj-zima`.
- Pi has a dedicated npm installation under `/srv/data/poincare-harness/pi`,
  pinned by the committed lockfile at version `0.80.10`. Production Jobs must
  attest the complete install and launch the manifest-bound Node/CLI entrypoint;
  the `.bin/pi` wrapper and version output alone are not a trust boundary.
- The existing private vLLM API is healthy, serves model ID `leanstral-1.5`,
  and reports a 200,000-token model limit.
- The model artifact is `mistralai/Leanstral-1.5-119B-A6B`, revision
  `81592da95d94ab0439bfce16df1d55b402e598b6`.
- The exact-base root bootstrap completed successfully: 4,064/4,064 jobs,
  `exit_code=0`, at `2026-07-20T00:39:27Z`. The focused automatic scalar-time
  derivative module then completed 3,382/3,382 jobs, `exit_code=0`, at
  `2026-07-20T00:40:20Z`. No overlapping Lean build or owned bootstrap tmux
  session remained at the subsequent read-only check.

The private endpoint URL belongs only in ignored configuration and Job
evidence. Do not restart or modify the live vLLM/Ray service, inspect or manage
its GPU processes, change model files, or take ownership of the Spark runtime.

The Mac tldraw offline canvas is titled inside the drawing `Poincare Proof
Orchestration`, stable document ID `nPBFgUN4xNLuW1nWbbtkE` (the app currently
lists the unsaved canvas as `Untitled`). It shows the Pi-centered chain, exact
six tools, Codex-only authority, and the exact long-term Harness completion
terminal. The Mac lane records the final setup-thread handoff and future
on-demand inspection; it does not imply that this thread remains alive. The
`mj-zima` observe process produces durable evidence every 10,800 seconds.

## Exact Next Action

Transfer the clean control-plane commit containing this handoff plus only the
refreshed Task/Job source records to `mj-zima`; do not copy the Mac SQLite
database, WAL, prior staging, or prior Job artifacts. The local runtime,
fallback-worker, Pi, deploy, TypeScript, syntax, and schema gates were green
before that commit was made.

After that exact first action, seal a fresh Pi install, publish and verify the
separate old-base and control-HEAD Lean caches, initialize fresh runtime state,
and run `automatic-scalar-derivative-constructor-a01` through one fresh
`harness/v2/deploy/run-job-supervised.sh` Pi session. Preserve the complete Pi
event stream even on failure. Codex must rerun the Task's exact Lean, hygiene,
scope, and declaration gates before accepting or committing anything.

Launch the owned Codex-control/Pi-supervisor/observe tmux topology only after
preflight and the single-Job exercise are sound. The `mj-zima` observe loop
emits one immediate evidence snapshot and continues every 10,800 seconds. This
Mac setup thread reports the final deployed state once and ends; future
operators inspect that durable evidence from the Mac on demand. The long-term
Harness may report proof completion only after the exact declaration probe,
allowed-axiom check, clean stable HEAD, and full completion audit all pass.
