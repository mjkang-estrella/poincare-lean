# M5-glob-72: H1 and H2 as stated depend on the preferred charts and are refuted

Date: 2026-09-08. Orchestrator record consolidating three independent codex
worker results (M5-glob-69, M5-glob-70, M5-glob-71), each re-gated on `main`.

## Finding

The successor-data and successor-equality obligations H1 and H2 of
`harness/v2/missions/unit-recognition.json`, and the joint-regularity interface
`CartanSourceExponential.GenericJointRegularity`, are formulated for the
preferred charts `chartAt E x` of the ambient `ChartedSpace` instance. Mathlib's
`ChartedSpace` lets the instance choose, at every point other than a fixed
`x₀`, a chart whose source excludes `x₀`; the atlas stays smooth. Every one of
the three statements then fails, before any analysis is involved:

- `GenericJointRegularity g` is false for every `g` on
  `ClosedSmoothModel 3` with the punctured atlas (module
  `Poincare/Global/GenericJointRegularityCounterexample.lean`,
  `not_forall_genericJointRegularity`, axioms propext/Classical.choice/Quot.sound).
- H1 implies `FixedChartSuccessorDataPersistence.PreferredChartSourcePersistence x₀`
  (`{y | x₀ ∈ (extChartAt I y).source} ∈ 𝓝 x₀`) through the
  `source_mem_oldChart` field of every `DifferentialInducedSuccessor.Data`;
  the punctured selection violates it (module
  `Poincare/Global/FixedChartSuccessorDataPersistence.lean`, ten theorems).
- H2 (via `ActualSuccessorEqualityRadiusLocalPersistence`) forces the preferred
  chart at every nearby anchor to be injective on a common neighborhood,
  because `EqOn` is required on a whole metric ball for the total functions
  of the germs, which factor through the total chart extension
  (`Poincare/Global/SuccessorEqualityRadiusPersistence.lean`, six theorems;
  the obstruction `PreferredChartCollisionAccumulation` excludes every
  positive admissible radius).

What is not claimed: a Lean counterexample to the universal statements with
the compactness, simple-connectivity, and unit-curvature hypotheses. That
needs the round metric transported to a re-charted sphere; the workers
stopped under the contract's invalid-statement rule instead. The
mathematical construction (restrict every chart except one to exclude a point,
or to a ball of half its distance to the point) applies verbatim to the sphere.

## Consequence

The Cartan development chain, from `CartanMap.openPartialHomeomorph` through
`DifferentialInducedSuccessor.Data` to the H1/H2 boundary, is pinned to the
arbitrary preferred-chart selection and to total off-source extensions of
charts. Joint statements in the anchor cannot be proved in that generality.
The boundary must be reformulated:

1. germ equalities must be stated on `source ∩ ball`, never on the total
   functions of `OpenPartialHomeomorph`;
2. the chart family used by the germs must be controlled: on a compact
   manifold, a finite subatlas with a Lebesgue number `δ` gives a selection
   `x ↦ c (i x)` whose source contains `ball x δ`, so
   `{y | x ∈ source (c (i y))} ⊇ ball x δ` for every `x`. The repository's
   `CartanSourceExponential.Family` abstraction is the place for such a
   family; the chain must be run over an arbitrary family satisfying the
   controlled-source property rather than over `genericFamily`.

The first bounded step is task `controlled-chart-instance`: existence of a
`ChartedSpace` instance on a compact manifold, with the same smooth structure,
whose preferred charts satisfy the source-persistence clause. The remaining
steps are transport of `ClosedSmoothRiemannianMetric` and
`HasConstantSectionalCurvature3` across instances with the same maximal atlas,
and re-running the chain on the controlled instance, after which the H1/H2
analysis (persistence of the Picard–Lindelöf radii under motion of the
anchors) becomes a well-posed problem.

## Evidence

Gate results on `main` for the three modules: build success and every theorem
with axioms `[propext, Classical.choice, Quot.sound]`; the counterexample block
of `M5-glob-71_blocked.md` re-elaborated verbatim by the orchestrator.
