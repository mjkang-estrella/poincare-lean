# Handoff Snapshot

Snapshot date: 2026-07-20 (America/Los_Angeles)

## Project Truth

- Mac integration repository: `/Users/mjkang/Develop/poincare`, branch `main`.
- Harness v2 pivot base: `7ce913d87be973256517ea862fb4d3dbfae7cb82`,
  equal to `origin/main` before the implementation. The Mac control-plane
  commit is `8114cfe2a592d22ea1973441c0fb086c72e8826d`; the bounded proof Job
  commit is `f266c2fd4a8c23ca55bad0a09f35cc638e6842c0`. Inspect the current
  commit and working tree before acting; preserve any later changes.
- An exact stdin probe at the pivot base and again at the deployed release
  candidate failed with `Unknown identifier Poincare.poincare_conjecture`.
- The repository is still incomplete. Completion means Lean checks exactly
  `Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`, its
  axiom footprint is allowed, and the full completion audit passes in a clean,
  stable integration checkout.

`CURRENT_STATUS.md` was generated on 2026-06-30 and `harness/ledger.json` ends
with the 2026-07-07 legacy selector-assembly work. Both are historical until
regenerated or revalidated against the current commit. Lean and the current
diff remain authoritative.

## Completed Bounded Deployment Exercise

The first Harness v2 exercise was
`automatic-scalar-derivative-constructor` revision 4, accepted from Job
`automatic-scalar-derivative-constructor-r4-a03`, frozen at
`7ce913d87be973256517ea862fb4d3dbfae7cb82`. Attempts `r4-a01` and `r4-a02`
were terminalized and preserved; neither immutable Job was relaunched after a
supervisor record existed.

Its single allowed source file is:

```text
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean
```

The accepted edit adds the frozen `ofReactionFields` constructor and derives
`scalarTimeDerivativeJointContinuous` from `reaction.jointMetricEntries` via
the existing theorem
`scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three`.
The constructor may not add `ScalarTimeDerivativeJointContinuous` or scalar
domination as a replacement argument. Leanstral made the one-file edit through
Pi's scoped patch tool, its worker `lean_check` passed, and Codex independently
reran all six frozen acceptance commands plus the canonical exact-type
declaration probe before committing and accepting it. The accepted Job gate is
`harness/v2/state/jobs/automatic-scalar-derivative-constructor-r4-a03/gate.json`
on `mj-zima`.

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

As of 2026-07-20 the executable worker plane can fill up to four fixed Pi
execution slots from fully prepared queued Jobs with disjoint SQLite file
leases. The supervisor renews each running lease, releases its execution slot
when Pi exits, and routes a sealed successful result to Codex-owned
`reviewing`. Blocked or unsuccessful runs keep immutable evidence; only Codex
may create a fresh attempt. Reviewing Jobs do not consume Leanstral execution
capacity, so independent serial review can overlap another disjoint proof Job.

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

Checks and the bounded release exercise on 2026-07-20 established:

- The integration checkout is `/srv/projects/poincare`; the committed control
  checkout is `/srv/data/poincare-harness/control`; Job worktrees are beneath
  `/srv/projects/poincare-worktrees`.
- The project toolchain reports Lean `4.30.0-rc2` on `mj-zima`.
- Production Pi is the fresh sealed installation
  `/srv/data/poincare-harness/pi-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`,
  with owner-only attestations under
  `/srv/data/poincare-harness/pi-attestation-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`.
  The legacy unsealed `/srv/data/poincare-harness/pi` tree was not mutated or
  reused.
- Fresh runtime state is
  `/srv/projects/poincare/harness/v2/state/harness.sqlite3`; no Mac SQLite,
  WAL, staging directory, or prior Mac Job artifact was transferred.
- The existing private vLLM API is healthy, serves model ID `leanstral-1.5`,
  and reports a 200,000-token model limit.
- The model artifact is `mistralai/Leanstral-1.5-119B-A6B`, revision
  `81592da95d94ab0439bfce16df1d55b402e598b6`.
- The exact-base root bootstrap completed successfully: 4,064/4,064 jobs,
  `exit_code=0`, at `2026-07-20T00:39:27Z`. The focused automatic scalar-time
  derivative module then completed 3,382/3,382 jobs, `exit_code=0`, at
  `2026-07-20T00:40:20Z`. No overlapping Lean build or owned bootstrap tmux
  session remained at the subsequent read-only check.
- The bounded accepted Job used a fresh Pi JSON session, exactly the six scoped
  tools, dispatch generation 1 and lease token 1. Its sealed Pi run reported
  success with 8 tool events; Codex's clean accepted tree is
  `0581d0c497d584406dbfd75386214e1ed67426b6`.
- Serial integration verification passed root elaboration plus the interface,
  semantic-surface, theorem-contract, and axiom audits. The portable
  root-import audit then reported five pre-existing direct-import ledger gaps,
  so the root-import and full completion audits correctly remain non-green.

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

## Operator Handoff

The persistent deployment owns exactly `poincare-control`,
`poincare-workers`, and `poincare-observe`. From the Mac, use:

```sh
ssh -i ~/.ssh/id_ed25519_zimaboard_ai_lab -o IdentitiesOnly=yes \
  mj-kang@192.168.30.227 \
  '/srv/data/poincare-harness/control/harness/v2/deploy/status.sh /srv/data/poincare-harness/private/deploy.env'
```

Durable three-hour evidence is under
`/srv/projects/poincare/harness/v2/state/deploy/`, especially
`observe/heartbeats.jsonl` and `observe/snapshots/`. To request a graceful
drain without deleting state:

```sh
/srv/data/poincare-harness/control/harness/v2/deploy/stop.sh \
  /srv/data/poincare-harness/private/deploy.env
```

Restart with the corresponding `launch.sh` command. The SQLite store and Job
artifacts, not tmux scrollback, are recovery state. This Mac setup thread ends
after its one deployment report; it does not remain alive for the three-hour
loop. The long-term Harness may report proof completion only after the exact
declaration probe, allowed-axiom check, clean stable HEAD, and full completion
audit all pass.

Known non-blocking release follow-ups are bounded: Pi 0.80.10 emits harmless
read-only global-settings lock warnings in the sealed namespace, and its
cumulative JSON message updates made this successful 7,116-token Job's event
files large. Both are retained as evidence and remain within the Job disk
budget; neither expands Leanstral's authority or blocks restart/recovery. The
root-import ledger also needs direct `Poincare.lean` imports for the two Cartan
tail-overlap reductions, the automatic scalar-time-derivative module, the
scalar-variation continuity reduction, and the automatic finite-nerve compact-
history boundary module. Their current transitive visibility is sufficient for
the accepted constructor's exact `import Poincare` type probe, so this bounded
deployment does not widen into unrelated root wiring.
