# Incremental verification acceptance

Date: 2026-09-29. Base: `6c28d8eafa69b8ebb354a2b7506c57e62b7bbf2d`.
Implementation: `c73438b0`, `9d08a24b`, and `4a6ec16a` on
`codex/incremental-verification`.

## Result

Import direction, proof iteration and verification evidence have changed.
No theorem bodies or frozen statements changed. Independent fresh acceptance
and the exact completion boundary are retained.

- Transitive local imports: Stokes 626 to 147, tensor carrier 630 to 110,
  buffered solver 641 to 196, Hamilton gradient 635 to 363.
- Three changed files compiled independently; 258 declaration type fingerprints
  and their allowed axiom footprints matched the base. All non-import source
  bytes matched.
- The actual solver's LSP check took 61.047 seconds initially, 0.721 seconds
  after an appended existing-declaration check, and 0.000101 seconds for
  identical input. Fresh whole-file compilation took 59.31 seconds. This is
  a local compiler measurement, excluding Linux sandbox/integrity overhead.
- The first integration build reported 4,202 jobs but rebuilt only seven
  targets in 38.547 seconds. The unchanged-source check rebuilt zero targets
  in 2.220 seconds. Job count includes cached dependencies and artifacts.

## Acceptance evidence

The final complete Python suite ran 416 tests: 400 passed, 16 skipped.
Actual Lean fixtures checked multi-symbol type/axiom rejection, versioned
diagnostics and command snapshot reuse. Dirty helper, hidden Git-index,
compiler-library, archive corruption and import-artifact race tests passed.

The full build, interface, mathlib, shape, theorem-contract, semantic,
root-import and axiom gates passed. The completion audit failed only because
`Poincare.poincare_conjecture` is absent. Audit payload equivalence passed.

Final sealed checkpoint:
`harness/v2/state/verification/checkpoints/20260929T190243Z-5605c7645b0b44fc92bb58fcdda9c7bc`.
Raw worker failures, compiler output, root review checks, benchmarks and test
output remain under ignored `harness/v2/state/incremental-verification`.

## Limits

No live model service or remote deployment was changed. Protected Linux mounts,
Bubblewrap and cgroup integration for persistent sessions were not exercised
on this Mac. Ordinary caches retain full content validation. Exact declaration
probes default to minimal fresh execution; negative reuse requires explicit
`--reuse-negative`. A status receipt never certifies proof completion.

First inspection: `sh scripts/read_status_summary.sh`. Freshness describes
source-matching historical evidence and retains the original verified HEAD.
