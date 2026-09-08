# Worker contract

You are an analysis worker on the Poincaré Lean project (toolchain leanprover/lean4:v4.30.0-rc2). Isolated
worktree on branch `worker/chain-parametrization-inventory`, cloned `.lake` cache. READ-ONLY on Lean sources: do
not edit any `.lean` file or `Poincare.lean`. Deliver ONLY `harness/reports/chain-parametrization-inventory.md`
(commit it on the branch). Every claim must cite a file and declaration you verified with grep or a
`lake env lean` scratch probe under `/tmp`; no speculation.

# Task: inventory the Cartan chain's dependence on the per-anchor exponential, and propose the minimal parametrization

Context, read first: HANDOFF.md sections "2026-09-08 Repair track and audit payload caching" and
"2026-09-08 H1 and H2 are atlas-dependent as stated"; `harness/reports/M5-glob-72_statement_refutation.md`;
`Poincare/Global/ControlledChartInstance.lean`; `Poincare/Global/ConnectionInstanceNaturality.lean`
(`exists_controlled_recognition_reduction'`); `Poincare/Global/GeodesicFlowJointDerivative.lean` and
`Poincare/Global/FixedChartUniformNormalRadius.lean` (the uniform fixed-chart exponential:
`exists_uniform_local_geodesic_chart_flow_normal_neighborhoods`); `Poincare/Global/CartanSourceExponentialFamily.lean`
(`Family`, `Family.JointlyRegular`, `genericFamily`, `LocalFamily` if present) and
`Poincare/Global/CartanGenericSuccessorDataLocalCover.lean` (`LocalFamily`, `FixedChartAnchorEndpointPackage`).

Facts: `GeodesicTransport.expAt g x`, `expAtChartOpenPartialHomeomorph g x`, and `cutoff x` are per-anchor
`Classical.choose` selections with no radius control, so no statement that is joint in the anchor can be proved
about them. The uniform exponential of a fixed chart now exists with joint C¹ dependence and a uniform normal
radius on compact regions of the chart's initial-position ball. A globally jointly regular `Family` cannot in
general be continuous across chart switches of a finite atlas; the usable notion is local: near every anchor, one
fixed chart and one uniform exponential.

Deliverables in the report:
1. The dependency inventory: every module on the path from `CartanMap.openPartialHomeomorph` through
   `CartanChain.ChainState`, `DifferentialInducedSuccessor.Data`, `DifferentialSuccessor*`, `CartanCanonical*`,
   `CartanGeneric*`, `CartanRestrictedOverlapCompatibility`, `UnitRecognitionNext`, to
   `CartanTwoNeighborhoodDevelopment`, classified as (a) hardwired to `expAtChartOpenPartialHomeomorph`/`expAt`/
   `cutoff`/`chartAt` (list the exact declarations and fields), (b) parametric over a `Family`/`LocalFamily`
   already, or (c) purely topological/combinatorial (chain bookkeeping, covering skeleton) and independent of the
   exponential. Give counts and the list of (a).
2. For the theorems that the final consumers actually need (list them: local isometry of the germ, F-transition
   law, successor data existence, successor equality near the new anchor, chain realization with mesh control,
   restricted compatible atlas, global local development), state for each whether it is a germ-level (pointwise
   at the anchor) property — which would transfer from `expAt` to the uniform exponential by per-anchor agreement
   (ODE uniqueness on the cutoff-one zone) — or a joint-in-anchor property that must be re-proved for the uniform
   exponential. Cite the exact statements.
3. The minimal parametrization proposal: the smallest set of definitions to generalize (e.g. a structure bundling
   `normalChart : M → OpenPartialHomeomorph E E`-style exponential charts with the properties the chain uses,
   with `genericFamily` and the uniform family as instances), which existing theorems become lemmas about the
   parameter, and the estimated size (files, theorems) of the re-run. Prefer a plan where the existing generic
   proofs are reused as instances, and identify any theorem whose proof genuinely uses the specific
   `Classical.choose` selector (those must be re-proved).
4. An ordered list of the first five bounded tasks (each one new file, gate-checkable), with exact target
   statements, to execute the plan.
