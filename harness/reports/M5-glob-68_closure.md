# M5-glob-68 closure record: the F-transition boundary is closed; the live boundary is H1 and H2

Date: 2026-09-07. Author: orchestrator (Claude Fable 5.1), verified in Lean in
worktree `worker/unit-recognition-boundary` on top of `main` (`b2b96fc2`).

## What the reports through M5-glob-67 got wrong

`harness/ledger.json` and `harness/reports/M5-glob-21_*.md` .. `M5-glob-67_*.md`
record the Cartan chart-map "F-transition law" and the old-germ-vs-successor
`EqOn` as blocked on an indexed endpoint Grönwall package. Lean disagrees.
Commit `d8f2e43c` (2026-07-17, "add fix", 517 files, no harness report) closed
both curvature-only, and no report or ledger entry recorded it:

```text
'Poincare.UniformAnchoredFTransition.exists_cartanChartMap_christoffelAt_F_transition_law_curvature_only' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Files: `Poincare/Global/UniformAnchoredFTransition.lean`,
`Poincare/Global/UniformAnchoredGeodesicTransition.lean`,
`Poincare/Global/DifferentialSuccessorIntervalNaturality.lean`.

The closing route is the second-variation package
(`UniformAnchoredSecondVariation.exists_expAtChart_fderiv_contDiffAt_one_on_smallBall`,
`exists_cartanChartMap_contDiffAt_two_on_small_normal_balls`) giving
`ContDiffAt ℝ 2` of the Cartan chart map directly. The third-variation and
selector tower built in M5-glob-49..67 (`FlowSmoothness`, `ThirdVariation`,
`FieldC1`, `DoublyResidual`, `TowerClosed`, `ThirdFamily`, `OmegaGronwall`,
`HostedCLM`, `TheSelector`, `TwoConnectors`, `OmegaRescale`,
`CenteredMembership`, `SelectorAssembly`, `IndexedSelection`,
`ContinuityPackages`) is not on the closing path except for
`ContinuityPackages.normedField_continuousOn_of_norm_sub_le`, an import of
`TowerClosed` in `EndpointCurry`, and `TwoConnectors` in
`SecondVariationRescale`. Do not dispatch tasks against the M5-glob-67
"resisting shape"; it is moot.

## The live boundary

`Poincare/Global/CartanTwoNeighborhoodDevelopment.lean` (this checkpoint)
proves, with the standard axiom footprint, that two joint-uniformity
statements discharge the total developing map:

```text
'Poincare.CartanTwoNeighborhoodDevelopment.globalLocalDevelopment_of_two_neighborhoods' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CartanTwoNeighborhoodDevelopment.unitConstantCurvatureSphereRecognition3_of_two_neighborhoods' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods' depends on axioms: [propext, Classical.choice, Quot.sound]
```

H1 = `UnitCurvatureSuccessorDataNeighborhood3`: for every unit-curvature `g`,
`CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood g`, i.e.

```lean
UniversalSuccessorDataLocus g ∈ 𝓝ˢ successorParameterDiagonal
UniversalSuccessorDataLocus g =
  {q : (M × RoundSphere3) × M |
    ∀ L : CartanMap.TangentAlignment g q.1.1 q.1.2,
      Nonempty (DifferentialInducedSuccessor.Data ⟨q.1.1, q.1.2, L⟩ q.2)}
```

H2 = `UnitCurvatureSuccessorEqualityNeighborhood3`: for every unit-curvature `g`,
`DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityNeighborhood g`, i.e.

```lean
UniversalSuccessorEqualityLocus g ∈ 𝓝ˢ successorEqualityParameterDiagonal
UniversalSuccessorEqualityLocus g =
  {q | ∀ (L : CartanMap.TangentAlignment g q.1.1.1 q.1.1.2)
        (d : DifferentialInducedSuccessor.Data ⟨q.1.1.1, q.1.1.2, L⟩ q.1.2),
        (⟨q.1.1.1, q.1.1.2, L⟩ : ChainState g).germ q.2 = d.successor.germ q.2}
```

What curvature already proves (fixed anchors `(x, p)`):

- `CartanAtlasRootedPathCurvatureSuccessorRadius.universalSuccessorDataLocus_vertical_mem_nhds_of_curvature`:
  `{z | ((x, p), z) ∈ UniversalSuccessorDataLocus g} ∈ 𝓝 x`.
- `DifferentialSuccessorEqualityStabilityReduction.fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature`:
  `FixedAnchorActualSuccessorEqualityNeighborhood g x p`.

What is missing in each: the neighborhood must be uniform as `(x, p)` and the
alignment move on the compact diagonal. Equivalent forms already in the repo:
H1 ↔ `CartanGenericSuccessorDataLocalCover.LocalGenericSuccessorDataCover g`
(`localGenericSuccessorDataCover_iff_universalSuccessorDataNeighborhood`);
H2 ↔ `DifferentialUniformSuccessorMesh.UniformSuccessorEqOnBall` with one
radius (`exists_uniformSuccessorEqOnBall_of_jointNeighborhood`) ↔
`DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence g`.

## Also stale in HANDOFF.md

The "exact next analytic action" of the 2026-09-04 section was completed by
commit `723b4132` before that section was written:

```text
'Poincare.CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and `NormalizedFlowFormalProfilePositiveEinstein.lean` already exposes the
`...OfCompactTensorControl` constructors without the `gref c hLower` inputs.

## Verification

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanTwoNeighborhoodDevelopment.lean
lake build Poincare.Global.CartanTwoNeighborhoodDevelopment   # Built (3584 jobs)
# #print axioms on the four new theorems: [propext, Classical.choice, Quot.sound]
```
