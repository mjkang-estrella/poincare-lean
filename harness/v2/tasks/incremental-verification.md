# Incremental verification implementation

Date: 2026-09-29. Base: `6c28d8eafa69b8ebb354a2b7506c57e62b7bbf2d`.
Objective: reduce repeated verification cost while retaining exact theorem
contracts, independent fresh acceptance, scoped worker tools, immutable evidence,
and the existing completion boundary.

Context: `README.md`, `HANDOFF.md`, `docs/PROJECT_MAP.md`, `AGENTS.md`,
`harness/v2/SPEC.md`, and the existing source/tests of the owned component.

Disjoint ownership leases for this attempt:

- Lean import worker: `Poincare/Global/ClosedLaplacianStokesProducer.lean`,
  `FiniteAtlasParabolicTensorSpace.lean`, `BufferedFrozenParabolicSolver.lean`.
  Separate `codex/minimal-stokes-imports` worktree. Preserve all declarations.
- Probe worker: `harness/gate.sh`, `harness/v2/deploy/focused_review.py`,
  and a new focused-probe test module under `harness/v2/deploy/tests`.
- Session worker: `harness/v2/pi/broker.py`, a new persistent Lean session module,
  and session tests. Coordinate security API additions with the cache worker.
- Cache worker: `harness/v2/pi/security.py`, isolated security tests and
  protected-cache support. No weakening of the default integrity path.
- Receipt worker: new `scripts/verification_receipts.py`,
  `scripts/read_status_summary.sh`, `scripts/write_status_summary.sh`,
  and receipt tests. Cached status never certifies completion.
- Negative-probe worker: `harness/v2/deploy/exact-completion-probe.sh`,
  new negative-probe cache and compiled-import identity helpers, and tests.
  Only a verified absent result may be reused; positive probes remain fresh.
- Orchestrator: documentation, task evidence, independent review/integration,
  and changes needed to connect these disjoint components after review.

No other Lean proof changes, frozen-target changes, placeholders, or model
service changes are allowed. Workers never accept, merge, or modify main.

Acceptance: focused Python unit suites; fail-closed mutation/invalidation and
multi-symbol probe regression tests; real incremental Lean session smoke check;
`LEAN_NUM_THREADS=1 lake env lean` for each changed Lean file; forbidden-token
scan; `git diff --check`; one serialized integration build, root elaboration,
interface/semantic/theorem-contract/root-import/axiom audits, payload equivalence,
and the exact final theorem probe. Completion is expected to remain absent.

Record timings separately for cache validation, import/load and elaboration,
probe execution, and audits. A platform-specific smoke check that cannot run on
this Mac must be reported explicitly; never replace it with a success claim.
Stop for a precise resisting Lean type or unavailable required isolation primitive
after preserving verified changes and diagnostics. Infrastructure acceptance
requires tests that demonstrate unchanged acceptance and rejection behavior.
