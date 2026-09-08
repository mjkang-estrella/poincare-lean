# Worker contract

You are an analysis worker on the Poincaré Lean project (toolchain leanprover/lean4:v4.30.0-rc2). Isolated
worktree on branch `worker/parametrization-plan-2`, cloned `.lake` cache. READ-ONLY on Lean sources: do not edit
any `.lean` file or `Poincare.lean`. Deliver ONLY `harness/reports/parametrization-plan-2.md` (commit it on the
branch). Every claim must cite a file and declaration you verified with grep or a `lake env lean` scratch probe
under `/tmp`; type-check every proposed target statement in a scratch file (declaration/type checks only).

# Task: specify the next five bounded tasks of the chain parametrization

Read first: `harness/reports/chain-parametrization-inventory.md` (the plan; its first five tasks are now landed
on `main` as `CartanSuppliedSourceMap.lean`, `CartanSuppliedSourceGermTransfer.lean`, `FixedChartEndpointSlices.lean`,
`FixedChartUniformSourceNormal.lean`, `FixedChartUniformPreferredGermAgreement.lean` — read all five and their
reports `harness/reports/{supplied-source-map,supplied-source-germ-transfer,fixed-chart-endpoint-slices,fixed-chart-uniform-source-normal,parametrization-task-5}_done.md`),
then HANDOFF.md "2026-09-08 Repair track and audit payload caching".

The plan's remaining files are described only in outline: two successor/differential files, two local
quantitative existence/equality files, three chain/mesh/overlap files, one restricted-atlas file, one final
development adapter. Specify the NEXT FIVE of them with the same exactness as the inventory's first five: for each
task, the single new file name, namespace, definitions with full Lean text, theorem targets with full Lean
statements (type-checked in a scratch file against the current `main`), the existing declarations to reuse
(cite them), the gate command, and the exact stop condition. Order them by dependency. Where a supplied-source
version of `DifferentialInducedSuccessor.Data` is defined, keep every field that the downstream consumers
(`DifferentialSuccessorIntervalNaturality`, `DifferentialSuccessorAdjacentContinuation`,
`CartanCanonicalRootedDirectGenericNeighborhoodRecognition`) actually use, and say which consumer theorems can be
reused as instances (via `generic_map_eq` and `normal_eventuallyEq_generic_in_anchor_frame`) versus re-proved.
State plainly which of the new local quantitative statements are the well-posed replacements of H1 and H2 on the
patch, and give their exact Lean statements. No implementation; no claims of provability beyond what the cited
existing theorems support.
