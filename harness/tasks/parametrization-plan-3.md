# Worker contract

You are an analysis worker on the Poincaré Lean project (toolchain leanprover/lean4:v4.30.0-rc2). Isolated
worktree on branch `worker/parametrization-plan-3`, cloned `.lake` cache. READ-ONLY on Lean sources: do not edit
any `.lean` file or `Poincare.lean`. Deliver ONLY `harness/reports/parametrization-plan-3.md` (commit it on the
branch). Every claim must cite a file and declaration you verified with grep or a `lake env lean` scratch probe
under `/tmp`; type-check every proposed target statement in a scratch file (declaration/type checks only).

# Task: specify the final files of the chain parametrization, from the patch H1/H2 theorems to the global developing map

Read first: `harness/reports/chain-parametrization-inventory.md` and `harness/reports/parametrization-plan-2.md`
(tasks 6-10, all landed), then the landed modules in order: `CartanSuppliedDifferentialSuccessor.lean`,
`CartanSuppliedDifferentialTransfer.lean`, `FixedChartLocalSuccessorExistence.lean`,
`FixedChartLocalSuccessorEquality.lean`, `FixedChartMovingPositionJacobi.lean`,
`FixedChartMappedGeodesicAssembly.lean` (`FixedChartLocalSuccessorEquality.exists_radii`: the patch H1/H2
theorem — one step radius and one evaluation radius for compact anchor sets on a fixed-chart patch),
`CartanSuppliedReachableChain.lean` (task 10: `ReachableChain`, `StepAvailable`, `exists_reachableChain`,
`state_eq`, `state_eq_of_open_agreement`), `FixedChartUniformSourceNormal.lean` (`Patch`, `exists_patch`),
`ControlledChartInstance.lean`, `ConnectionInstanceNaturality.lean` (`exists_controlled_recognition_reduction'`),
and the legacy consumers to be replaced or reused: `CartanCanonicalRootedDirectGenericNeighborhoodRecognition.lean`
(`exists_genericRootedRealization_with_wholeCellMesh_of_certificate`,
`restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry`), `CartanAtlasRootedPathSkeleton.lean`,
`DifferentialSuccessorAdjacentContinuation.lean` (`differentialHomotopyGrid_chain_endpoint_eq_of_metricBall_patches`,
`reachableChains_endpoint_eq`), `CartanRestrictedOverlapCompatibility.lean` (`RestrictedCompatibleCartanAtlasData3`,
`isLocalHomeomorph_diagonalDevelopment`, `globalLocalDevelopment_of_restrictedCompatibleCartanAtlas`),
`UnitRecognitionNext.lean`, `RoundSphereSimpleConnected.lean`, `CartanTwoNeighborhoodDevelopment.lean`.

Goal of the remaining program: prove, for a controlled `ChartedSpace` instance (finite atlas with uniform-ball
chart sources) and a unit-curvature metric, `UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3` (a total
local homeomorphism `M → RoundSphere3`), hence via the landed reductions `UnitConstantCurvatureSphereRecognition3`
for the original instance. The available inputs are: one patch per chart of the finite atlas (source) and per
chart of the sphere (target), each with the patch H1/H2 theorem on compact anchor sets; chains along paths
(task 10) with a per-step interpretation policy; the covering skeleton and simple-connectivity endgame.

Specify the remaining tasks (as many as needed, ordered by dependency, each one new file) with the same
exactness as plan 2: full Lean text for definitions, type-checked theorem targets, existing declarations to
reuse (cite), gate command, exact stop condition. They must cover: (a) the finite patch cover: choosing, for the
controlled instance, finitely many source patches whose anchor sets cover `M` with a Lebesgue number, and
finitely many sphere patches covering `RoundSphere3`, and a policy `ℕ → ChainState → Interpretation` selecting
the patch containing the current anchor and target (state exactly how the policy is defined and why `StepAvailable`
holds for mesh below the uniform step radius); (b) chain realization along every path with mesh control from the
uniform radii (the supplied analogue of `exists_genericRootedRealization_with_wholeCellMesh_of_certificate`);
(c) homotopy invariance of chain endpoints via the uniform evaluation radius and `state_eq_of_open_agreement`
(the supplied analogue of the metric-ball-patch grid argument), using `SimplyConnectedSpace M`;
(d) the restricted compatible atlas from the rooted chains (the supplied analogue of
`restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry`), or a direct construction of the total
map and its local-homeomorphism property from the chain germs and `isLocalHomeomorph_diagonalDevelopment`;
(e) the final adapter: `UnitCurvatureGlobalLocalDevelopment3` for the controlled instance, then
`UnitConstantCurvatureSphereRecognition3` for the original instance through
`ConnectionInstanceNaturality.exists_controlled_recognition_reduction'`, and the universal statement feeding
`poincareConjecture_of_hamiltonConvergence_of_unitRecognition`. For each task state which legacy theorem's proof
can be reused as a template and which parts are genuinely new. Be explicit about where the patch interpretation
changes between steps (the chain re-anchors inside one patch until it leaves its anchor set, then switches
patch) and what the germ-agreement theorems (`CartanSuppliedSourceGermTransfer`,
`FixedChartUniformPreferredGermAgreement`, `CartanSuppliedDifferentialTransfer.patch_germ_eventuallyEq_generic`)
give at a patch switch. No implementation; no claims of provability beyond what the cited theorems support.
