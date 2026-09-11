# Closed Laplacian Stokes producer: blocked with verified partial constructor

Date: 2026-09-11. Base: `3bdabbc9806d413b0f71c939d8d0e1a96394c6c5`.
Branch: `worker/closed-laplacian-stokes-producer`.
Proof head: `eb0c39b9f4a9da143233000f64cc3a820e36afde`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The unconditional `closedLaplacianStokes_of_contMDiff_two` and its unconditional
forward-flow corollary are **not proved or declared**. The blocked stop condition
is used. The committed partial constructor is
`Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients`.
The new module contains ten theorems and two definitions. All twelve compile
and print exactly `[propext, Classical.choice, Quot.sound]`, allowing only
whitespace differences in Lean's line wrapping.

## What is proved

The module constructs the full open-chart Hausdorff measure formula and
proves density integrability there from finite Riemannian volume. This matters
because the landed finite atlas's `coordinateDomain` disjointizes the cover;
those pieces are not the open regions needed by a smooth subordinate partition.
The new constructor uses the selected charts' entire targets and open sources.
It does not reuse the disjoint pieces as open chart regions.

A smooth partition exists subordinate to the finite genuine source cover.
For a scalar supported inside a chart source, its inverse-chart pullback,
extended by zero off the target, has compact support inside the target and
is globally C². The compact support proof uses the compact image of the
manifold scalar's topological support, including control at the chart boundary.
The global regularity proof uses composition on the target and local zero
values off the coordinate support.

Given the two coordinate coefficient identities and a positive continuous
weight, the localized intrinsic Laplacian is continuous. Thus the constructor
supplies `localizedLaplacian_aestronglyMeasurable`; that field is not an extra
analytic argument. Christoffel contraction is defined by the actual negative
double sum, so `contractedChristoffel_eq` is also discharged.

The genuine density weight and inverse Gram-matrix entries are proved smooth
**on the chart target** from the fixed smooth metric. The determinant proof
uses its finite permutation expansion. Density smoothness uses positive
determinant and square root; inverse-matrix smoothness uses the determinant
and adjugate. No flow or joint-in-time hypothesis enters these results.

## Exact target and residual fields

The initial successful `#print` confirms that `ClosedLaplacianStokes g f` is

```lean
Integrable (fun x : M ↦ g.laplacianAt f x) (volumeMeasure g) ∧
  (∫ x, g.laplacianAt f x ∂(volumeMeasure g)) = 0
```

The complete original record print is in the command transcript below.
`geometry_of_coordinate_coefficients` constructs that original record. Its
result can be passed directly to the landed `.closedLaplacianStokes` theorem.
It does not replace the target or introduce a new predicate.

| Original record fields | Producer or remaining obligation |
| --- | --- |
| `chartCount`, `coordinateDomain`, `inverseChart`, `chartRegion` | Selected genuine charts, full targets and open sources |
| `coordinateDomain_measurable`, `inverseChart_measurable`, `chartRegion_isOpen` | Existing chart openness and inverse-chart embedding |
| `density`, `density_nonneg` | Actual inverse-chart Gram density and landed positivity |
| `density_integrable` | New `openChart_density_integrable` |
| `chartMeasure` | New `openChart_measure`, using the landed full area formula |
| `partition`, `partition_subordinate` | New `exists_subordinate_partition`; the constructor takes its witnesses explicitly |
| `f_contMDiff_two` | Original scalar hypothesis |
| `coordinateRepresentative`, `coordinateRepresentative_eq` | New `coordinateScalar`, the target indicator of the inverse-chart pullback |
| `coordinateRepresentative_contDiff_two` | New `coordinateScalar_contDiff_two` |
| `coordinateRepresentative_hasCompactSupport`, `coordinateRepresentative_tsupport_subset_coordinateDomain` | New `coordinateScalar_support` |
| `weight`, `weight_eq_density` | Genuine formula verified on targets by `chartWeight_regular`; a chosen global weight and its agreement remain explicit constructor arguments |
| `weight_contDiff_one` | **Remaining global extension obligation**; targetwise smoothness is proved |
| `inverseMetric`, `inverseMetric_contDiff_one` | **Remaining global extension obligation**; genuine inverse coefficients are smooth on targets by `chartInverseMetric_contDiffOn` |
| `christoffel` | Explicit coefficient array argument; the diagnostic uses the usual formula from inverse Gram entries and first Gram derivatives |
| `contractedChristoffel`, `contractedChristoffel_eq` | Defined negative double contraction, equality proved by reduction |
| `density_inverseMetric_compatibility` | **Unproved**; explicit `hcompat` argument |
| `intrinsicCoordinateLaplacian_eq` | **Unproved**; explicit `hcoord` argument |
| `localizedLaplacian_aestronglyMeasurable` | New `localizedLaplacian_continuous_of_coefficients`, conditional on the remaining coefficient arguments |

The strongest partial constructor retains five proof arguments: global C¹
weight, global C¹ inverse entries, agreement of weight with genuine density,
density compatibility, and intrinsic coordinate equality. The coefficient
arrays themselves are also explicit. All these assumptions appear in its
type; none are hidden in a definition or a typeclass.

There are more resisting fields than the task's anticipated single identity.
The full-field fallback with only `intrinsicCoordinateLaplacian_eq` remaining
was not reached. In particular, smoothness on an arbitrary full chart target
does not by itself produce a smooth extension to all Euclidean space agreeing
on that target. No impossibility theorem is claimed. A refined cover of
smaller regions and compatible coefficient extensions is a possible next
construction. The existing `CovariantDerivative.exists_blending_cutoff`,
`exists_global_chart_metric`, and `contDiff_blendedChartMetric_scalar` support
that route, but their local agreement has not been assembled into the needed
finite subordinate geometry here.

With `G` the genuine chart Gram field, `a = G⁻¹`,
`w = rawHausdorffLebesgueScale n * sqrt(abs(det G))`, and the standard
Christoffel coefficient formula shown in the diagnostic source, the two exact
resisting identities are

```lean
(∑ k : Fin n,
  fderiv ℝ (fun y ↦ w i y * a i y k j) z
    (EuclideanSpace.single k (1 : ℝ))) =
  w i z * (-(∑ k : Fin n, ∑ l : Fin n, a i z k l * Γ i z j k l))
```

and

```lean
g.laplacianAt (fun x ↦ ρ i x * f x)
    (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
  christoffelCoordinateLaplacian (a i) (Γ i)
    (coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z
```

Rewriting the second with `g.laplacianAt_eq_trace_hessianContinuousAt`
leaves the metric-dual trace of the intrinsic Hessian equal to the
coordinate derivative expression. The final diagnostic prints this exact
resisting type with a fully constructed cover. The coefficient regularity
attempts separately fail with `ContDiffOn ℝ 1 ... target` versus
`ContDiff ℝ 1 ...`; those are mathematical interface differences, not
successful extension proofs.

## Verification and flow boundary

The final focused module check exits 0. The source token scan is empty and
exits 1. `git diff --check` exits 0, including the complete proof diff from
the recorded base. All twelve declaration dependency prints pass. There is
one harmless unused-section-variable warning in `coordinateScalar_contDiff_two`.
Each new theorem was compiled and dependency-checked before its commit.
The later assumption-cleanup commit was also checked.

A separate successful probe checks the forward-flow conclusion **assuming**
the static Stokes producer explicitly. It obtains scalar C² regularity using
`scalarAt_contMDiffAt_two_of_normalizedRicciFlow` and
`timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three`.
It works in arbitrary dimension, so applies in dimension 3 with the Hamilton
context. This verifies the corollary step, not its missing Stokes premise.
No conditional theorem is given the frozen unconditional target's name.

All compiler probe output, including failures, is preserved below. Early
support/regularity attempts needed a dimension annotation, controlled
indicator reduction, and correct implicit model inference. The coefficient
continuity proof needed an explicit contracted-Christoffel function.
The inverse-matrix proof needed a nondependent type for `Pi.single`.
The first final diagnostic omitted second countability required by the
canonical finite-cover choice; the next used an ambiguous infinity notation.
Both were corrected before the final resisting goals were recorded. Compiler
recovery terms printed in those failed diagnostic contexts are not source
proofs. They are not present in the committed module. The dependency checker
initially rejected multiline pretty-printing; normalizing whitespace fixed
that checker, without changing the printed dependency set.

Before edits, HANDOFF's top section, README, PROJECT_MAP, the task context,
the requested reports, and the named definitions/imports were read. Initial
status was clean on the assigned worker branch at the base above, and the
worktree inventory was checked. The specific worker contract keeps HANDOFF,
all existing Lean files, root imports and frozen contracts read-only. Only
the requested new Lean module and this report are added. No full build,
root integration audit, merge, or task acceptance was performed.

First action for the orchestrator:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Then independently review `geometry_of_coordinate_coefficients` and rerun
the dependency prints. The next proof objective is to transport the intrinsic
Hessian trace into the genuine inverse-chart frame and identify its second
derivative and Christoffel correction. The exact diagnostic below supplies
the coordinate choices and remaining equality.

## Diagnostic sources

These tails were appended before the final namespace end of the committed
module, so the probes use the actual source and imports without a stale
new-module cache.

### Final resisting constructor attempt

```lean
example [SecondCountableTopology M] (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
    (hreg : ContMDiff I 𝓘(ℝ) 2 f) : ClosedLaplacianStokes g f := by
  let C := compactFiniteExtendedChartCover (n := n) (M := M)
  obtain ⟨ρ, hρ⟩ := exists_subordinate_partition C
  let G := fun i : Fin C.chartCount ↦ inverseChartPullbackGramMatrixField g (C.anchor i)
  let w := fun (i : Fin C.chartCount) (z : E) ↦
    (rawHausdorffLebesgueScale n : ℝ) * VolumeDensity.chartVolumeDensity (G i z)
  let a := fun (i : Fin C.chartCount) (z : E) ↦ (G i z)⁻¹
  let Γ := fun (i : Fin C.chartCount) (z : E) (k j l : Fin n) ↦
    (1 / 2 : ℝ) * ∑ m : Fin n, a i z k m *
      (coordinateDirectionalDerivative (fun y ↦ G i y l m) j z +
       coordinateDirectionalDerivative (fun y ↦ G i y j m) l z -
       coordinateDirectionalDerivative (fun y ↦ G i y j l) m z)
  refine (geometry_of_coordinate_coefficients g f hreg C ρ hρ w a Γ ?_ ?_ ?_ ?_ ?_).closedLaplacianStokes
  · intro i
    have H := (chartWeight_regular g (C.anchor i)).1
    exact H.of_le (m := (1 : ℕ∞ω)) (by norm_num)
  · intro i j k
    have H := chartInverseMetric_contDiffOn g (C.anchor i) j k
    exact H.of_le (m := (1 : ℕ∞ω)) (by norm_num)
  · intro i z
    exact (chartWeight_regular g (C.anchor i)).2 z
  · intro i z j
    trace_state
  · intro i z
    rw [g.laplacianAt_eq_trace_hessianContinuousAt]
    trace_state
```

### Successful conditional flow probe

```lean
/-- This probe assumes the unproved static producer explicitly. -/
example
    (hStokes : ∀ (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ),
      ContMDiff I 𝓘(ℝ) 2 f → ClosedLaplacianStokes g f)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x) := by
  intro t ht
  apply hStokes
  intro x
  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow (hFlow t ht)
    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hJoint t y)) x

#check geometry_of_coordinate_coefficients
#check FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
```

## Actual command output, dependency prints, and final diff

Trailing spaces on blank diagnostic lines are removed for the whitespace gate.


### Command

```sh
rg -n 'laplacianAt.*(continuous|Continuous|contMDiff)|continuous.*laplacianAt|inverseExtendedChart.*(Formula|Density)|hausdorffChartDensityEquality|contDiff.*extend|contMDiff.*extend' Poincare/Global/Hausdorff* Poincare/Global/*Laplacian* .lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean
```

Exit: 0

```text
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:124:theorem FiniteExtendedChartCover.hausdorffChartDensityEquality
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:131:  C.hausdorffChartDensityEquality_of_restrictedAreaFormula g i
Poincare/Global/Laplacian.lean:495:theorem laplacianAt_eq_trace_hessianContinuousAt
Poincare/Global/Laplacian.lean:507:  unfold laplacianAt hessianContinuousAt
Poincare/Global/Laplacian.lean:822:  rw [g.laplacianAt_eq_trace_hessianContinuousAt (f * h) x,
Poincare/Global/Laplacian.lean:823:    g.laplacianAt_eq_trace_hessianContinuousAt h x,
Poincare/Global/Laplacian.lean:824:    g.laplacianAt_eq_trace_hessianContinuousAt f x]
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:270:theorem hausdorffChartDensityEquality_of_restrictedAreaFormula
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:278:  exact hausdorffChartDensityEquality_of_pullbackMetricFormula
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:332:    C.hausdorffChartDensityEquality_of_restrictedAreaFormula
Poincare/Global/HausdorffCoordinateDensityVariation.lean:110:theorem hausdorffChartDensityEquality_one_of_isometry
Poincare/Global/HausdorffInverseChartAreaFormula.lean:149:theorem inverseChart_hausdorffChartDensityEquality
Poincare/Global/HausdorffInverseChartAreaFormula.lean:156:  inverseChart_hausdorffChartDensityEquality_of_areaFormula
Poincare/Global/HausdorffInverseChartAreaFormula.lean:161:theorem inverseChart_hausdorffChartDensityEquality_chartFrame_auto
Poincare/Global/HausdorffInverseChartAreaFormula.lean:169:  inverseChart_hausdorffChartDensityEquality_chartFrame gt t x₀
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:77:theorem hausdorffChartDensityEquality_range_of_pullbackMetricFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:102:theorem hausdorffChartDensityEquality_of_pullbackMetricFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:109:  exact hausdorffChartDensityEquality_range_of_pullbackMetricFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:226:theorem inverseChart_hausdorffChartDensityEquality_of_areaFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:234:  exact hausdorffChartDensityEquality_range_of_pullbackMetricFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:243:theorem inverseChart_hausdorffChartDensityEquality_chartFrame
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:252:  have hlocal := inverseChart_hausdorffChartDensityEquality_of_areaFormula
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:287:theorem inverseChart_hausdorffChartDensityEquality_coordinateGram
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:297:  have hlocal := inverseChart_hausdorffChartDensityEquality_of_areaFormula
```

### Command

```sh
rg -n 'extend.*(contDiff|contMDiff|tsupport|support)|contDiff.*extend|tsupport.*extend|contMDiff.*extend|contDiff.*indicator' .lake/packages/mathlib/Mathlib/Geometry/Manifold .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/Topology/PartialHomeomorph*
```

Exit: 1

```text
zsh:1: no matches found: .lake/packages/mathlib/Mathlib/Topology/PartialHomeomorph*
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/inspect.lean
```

Exit: 0

```text
def Poincare.ClosedLaplacianStokes.{u} : {n : ℕ} →
  {M : Type u} →
    [inst : TopologicalSpace M] →
      [T2Space M] →
        [CompactSpace M] →
          [ConnectedSpace M] →
            [inst_4 : MeasurableSpace M] →
              [BorelSpace M] →
                [inst_6 : ChartedSpace (Poincare.ClosedSmoothModel n) M] →
                  [inst_7 : IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] →
                    Poincare.ClosedSmoothRiemannianMetric n M → (M → ℝ) → Prop :=
fun {n} {M} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] g f =>
  MeasureTheory.Integrable (fun x => g.laplacianAt f x) (Poincare.volumeMeasure g) ∧
    ∫ (x : M), g.laplacianAt f x ∂Poincare.volumeMeasure g = 0
structure Poincare.FiniteSubordinateHausdorffLaplacianGeometry.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (f : M → ℝ) : Type u
number of parameters: 12
fields:
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.chartCount : ℕ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateDomain : Fin self.chartCount →
      Set (Poincare.ClosedSmoothModel n)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateDomain_measurable : ∀ (i : Fin self.chartCount),
      MeasurableSet (self.coordinateDomain i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.inverseChart : (i : Fin self.chartCount) →
      ↑(self.coordinateDomain i) → M
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.inverseChart_measurable : ∀ (i : Fin self.chartCount),
      Measurable (self.inverseChart i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.chartRegion : Fin self.chartCount → Set M
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.chartRegion_isOpen : ∀ (i : Fin self.chartCount),
      IsOpen (self.chartRegion i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.density : (i : Fin self.chartCount) →
      ↑(self.coordinateDomain i) → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.density_nonneg : ∀ (i : Fin self.chartCount),
      0 ≤ᵐ[Poincare.coordinateLebesgueMeasure (self.coordinateDomain i)] self.density i
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.density_integrable : ∀ (i : Fin self.chartCount),
      MeasureTheory.Integrable (self.density i) (Poincare.coordinateLebesgueMeasure (self.coordinateDomain i))
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.chartMeasure : ∀ (i : Fin self.chartCount),
      Poincare.HausdorffChartDensityEquality g (self.coordinateDomain i) (self.inverseChart i) (self.chartRegion i)
        (self.density i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.partition : SmoothPartitionOfUnity (Fin self.chartCount)
      (Poincare.closedSmoothModelWithCorners n) M
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.partition_subordinate : self.partition.IsSubordinate
      self.chartRegion
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.f_contMDiff_two : ContMDiff
      (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 f
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateRepresentative : Fin self.chartCount →
      Poincare.ClosedSmoothModel n → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateRepresentative_eq : ∀ (i : Fin self.chartCount)
      (z : ↑(self.coordinateDomain i)),
      self.coordinateRepresentative i ↑z = (self.partition i) (self.inverseChart i z) * f (self.inverseChart i z)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateRepresentative_contDiff_two : ∀
      (i : Fin self.chartCount), ContDiff ℝ 2 (self.coordinateRepresentative i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateRepresentative_hasCompactSupport : ∀
      (i : Fin self.chartCount), HasCompactSupport (self.coordinateRepresentative i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.coordinateRepresentative_tsupport_subset_coordinateDomain : ∀
      (i : Fin self.chartCount), tsupport (self.coordinateRepresentative i) ⊆ self.coordinateDomain i
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.weight : Fin self.chartCount → Poincare.ClosedSmoothModel n → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.weight_contDiff_one : ∀ (i : Fin self.chartCount),
      ContDiff ℝ 1 (self.weight i)
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.weight_eq_density : ∀ (i : Fin self.chartCount)
      (z : ↑(self.coordinateDomain i)), self.weight i ↑z = ↑(Poincare.rawHausdorffLebesgueScale n) * self.density i z
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.inverseMetric : Fin self.chartCount →
      Poincare.ClosedSmoothModel n → Fin n → Fin n → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.inverseMetric_contDiff_one : ∀ (i : Fin self.chartCount)
      (a b : Fin n), ContDiff ℝ 1 fun z => self.inverseMetric i z a b
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.christoffel : Fin self.chartCount →
      Poincare.ClosedSmoothModel n → Fin n → Fin n → Fin n → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.contractedChristoffel : Fin self.chartCount →
      Poincare.ClosedSmoothModel n → Fin n → ℝ
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.contractedChristoffel_eq : ∀ (i : Fin self.chartCount)
      (z : ↑(self.coordinateDomain i)) (k : Fin n),
      self.contractedChristoffel i (↑z) k = -∑ a, ∑ b, self.inverseMetric i (↑z) a b * self.christoffel i (↑z) k a b
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.density_inverseMetric_compatibility : ∀ (i : Fin self.chartCount)
      (z : ↑(self.coordinateDomain i)) (j : Fin n),
      ∑ a, (fderiv ℝ (fun y => self.weight i y * self.inverseMetric i y a j) ↑z) (EuclideanSpace.single a 1) =
        self.weight i ↑z * self.contractedChristoffel i (↑z) j
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.intrinsicCoordinateLaplacian_eq : ∀ (i : Fin self.chartCount)
      (z : ↑(self.coordinateDomain i)),
      g.laplacianAt (fun x => (self.partition i) x * f x) (self.inverseChart i z) =
        Poincare.christoffelCoordinateLaplacian (self.inverseMetric i) (self.christoffel i)
          (self.coordinateRepresentative i) ↑z
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.localizedLaplacian_aestronglyMeasurable : ∀
      (i : Fin self.chartCount),
      MeasureTheory.AEStronglyMeasurable (fun x => g.laplacianAt (fun y => (self.partition i) y * f y) x)
        (Poincare.volumeMeasure g)
constructor:
  Poincare.FiniteSubordinateHausdorffLaplacianGeometry.mk.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (Poincare.ClosedSmoothModel n) M] [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M]
    {g : Poincare.ClosedSmoothRiemannianMetric n M} {f : M → ℝ} (chartCount : ℕ)
    (coordinateDomain : Fin chartCount → Set (Poincare.ClosedSmoothModel n))
    (coordinateDomain_measurable : ∀ (i : Fin chartCount), MeasurableSet (coordinateDomain i))
    (inverseChart : (i : Fin chartCount) → ↑(coordinateDomain i) → M)
    (inverseChart_measurable : ∀ (i : Fin chartCount), Measurable (inverseChart i))
    (chartRegion : Fin chartCount → Set M) (chartRegion_isOpen : ∀ (i : Fin chartCount), IsOpen (chartRegion i))
    (density : (i : Fin chartCount) → ↑(coordinateDomain i) → ℝ)
    (density_nonneg : ∀ (i : Fin chartCount), 0 ≤ᵐ[Poincare.coordinateLebesgueMeasure (coordinateDomain i)] density i)
    (density_integrable :
      ∀ (i : Fin chartCount),
        MeasureTheory.Integrable (density i) (Poincare.coordinateLebesgueMeasure (coordinateDomain i)))
    (chartMeasure :
      ∀ (i : Fin chartCount),
        Poincare.HausdorffChartDensityEquality g (coordinateDomain i) (inverseChart i) (chartRegion i) (density i))
    (partition : SmoothPartitionOfUnity (Fin chartCount) (Poincare.closedSmoothModelWithCorners n) M)
    (partition_subordinate : partition.IsSubordinate chartRegion)
    (f_contMDiff_two : ContMDiff (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 f)
    (coordinateRepresentative : Fin chartCount → Poincare.ClosedSmoothModel n → ℝ)
    (coordinateRepresentative_eq :
      ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
        coordinateRepresentative i ↑z = (partition i) (inverseChart i z) * f (inverseChart i z))
    (coordinateRepresentative_contDiff_two : ∀ (i : Fin chartCount), ContDiff ℝ 2 (coordinateRepresentative i))
    (coordinateRepresentative_hasCompactSupport :
      ∀ (i : Fin chartCount), HasCompactSupport (coordinateRepresentative i))
    (coordinateRepresentative_tsupport_subset_coordinateDomain :
      ∀ (i : Fin chartCount), tsupport (coordinateRepresentative i) ⊆ coordinateDomain i)
    (weight : Fin chartCount → Poincare.ClosedSmoothModel n → ℝ)
    (weight_contDiff_one : ∀ (i : Fin chartCount), ContDiff ℝ 1 (weight i))
    (weight_eq_density :
      ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
        weight i ↑z = ↑(Poincare.rawHausdorffLebesgueScale n) * density i z)
    (inverseMetric : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → Fin n → ℝ)
    (inverseMetric_contDiff_one : ∀ (i : Fin chartCount) (a b : Fin n), ContDiff ℝ 1 fun z => inverseMetric i z a b)
    (christoffel : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → Fin n → Fin n → ℝ)
    (contractedChristoffel : Fin chartCount → Poincare.ClosedSmoothModel n → Fin n → ℝ)
    (contractedChristoffel_eq :
      ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)) (k : Fin n),
        contractedChristoffel i (↑z) k = -∑ a, ∑ b, inverseMetric i (↑z) a b * christoffel i (↑z) k a b)
    (density_inverseMetric_compatibility :
      ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)) (j : Fin n),
        ∑ a, (fderiv ℝ (fun y => weight i y * inverseMetric i y a j) ↑z) (EuclideanSpace.single a 1) =
          weight i ↑z * contractedChristoffel i (↑z) j)
    (intrinsicCoordinateLaplacian_eq :
      ∀ (i : Fin chartCount) (z : ↑(coordinateDomain i)),
        g.laplacianAt (fun x => (partition i) x * f x) (inverseChart i z) =
          Poincare.christoffelCoordinateLaplacian (inverseMetric i) (christoffel i) (coordinateRepresentative i) ↑z)
    (localizedLaplacian_aestronglyMeasurable :
      ∀ (i : Fin chartCount),
        MeasureTheory.AEStronglyMeasurable (fun x => g.laplacianAt (fun y => (partition i) y * f y) x)
          (Poincare.volumeMeasure g)) :
    Poincare.FiniteSubordinateHausdorffLaplacianGeometry g f
SmoothPartitionOfUnity.exists_isSubordinate.{uι, uE, uH, uM} {ι : Type uι} {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [FiniteDimensional ℝ E] [IsManifold I (↑⊤) M] [T2Space M] [SigmaCompactSpace M] {s : Set M}
  (hs : IsClosed s) (U : ι → Set M) (ho : ∀ (i : ι), IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f, f.IsSubordinate U
Poincare.inverseChart_hausdorffChartDensityEquality.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] (g : Poincare.ClosedSmoothRiemannianMetric n M)
  (x₀ : M) :
  Poincare.HausdorffChartDensityEquality g (extChartAt (Poincare.closedSmoothModelWithCorners n) x₀).target
    (Poincare.inverseExtendedChartParametrization x₀) (Set.range (Poincare.inverseExtendedChartParametrization x₀))
    (Poincare.inverseChartPullbackVolumeDensity g x₀)
Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} (hFlow : ∀ (y : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
  (hEntries : ∀ (y : M), Poincare.TimeVariationExtContMDiffAt gt t₀ y 2) (x : M) :
  ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt t₀).scalarAt y) x
```

### Command

```sh
rg -n 'extend.*(contDiff|contMDiff|tsupport|support)|contDiff.*extend|tsupport.*extend|contMDiff.*extend|contDiff.*indicator|contDiff_of_tsupport' .lake/packages/mathlib/Mathlib/Geometry/Manifold .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/Topology
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/Basic.lean:789:    extends HasGroupoid M (contDiffGroupoid n I)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:30:* `ModelWithCorners.contDiffOn_extendCoordChange`: if `f` and `f'` lie in the maximal atlas on `M`,
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:372:lemma contDiffOn_extendCoordChange (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:377:lemma contDiffWithinAt_extendCoordChange (he : e ∈ maximalAtlas I n M)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:380:  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:385:lemma contDiffWithinAt_extendCoordChange' (he : e ∈ maximalAtlas I n M)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:388:  refine I.contDiffWithinAt_extendCoordChange he he' ?_
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:392:lemma contDiffOn_extendCoordChange_symm (he : e ∈ maximalAtlas I n M)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:395:  I.contDiffOn_extendCoordChange he' he
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:403:  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:404:  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:436:alias contDiffOn_extend_coord_change := ModelWithCorners.contDiffOn_extendCoordChange
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:439:alias contDiffWithinAt_extend_coord_change := ModelWithCorners.contDiffWithinAt_extendCoordChange
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:442:alias contDiffWithinAt_extend_coord_change' := ModelWithCorners.contDiffWithinAt_extendCoordChange'
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:790:  I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:795:  I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean:265:  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:45:in terms of extended charts in `contMDiffOn_iff` and `contMDiff_iff`.
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:335:    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtProp_self_source,
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:89:theorem contMDiffAt_extend {x : M} (he : e ∈ maximalAtlas I n M) (hx : x ∈ e.source) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:93:theorem contMDiffOn_extend (he : e ∈ maximalAtlas I n M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:95:  fun _x' hx' ↦ (contMDiffAt_extend he hx').contMDiffWithinAt
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:99:  contMDiffAt_extend (chart_mem_maximalAtlas x) h
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:111:theorem contMDiffOn_extend_symm (he : e ∈ maximalAtlas I n M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:120:  convert contMDiffOn_extend_symm (chart_mem_maximalAtlas (I := I) x)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:68:  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:114:    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas j.2)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:116:    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas i.2)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/MDifferentiable.lean:680:lemma exists_contMDiffOn_extend [(x : M) → Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/MDifferentiable.lean:695:lemma contMDiffAt_extend' {x : M} (σ₀ : V x) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/MDifferentiable.lean:711:  obtain ⟨s, hs, hsσ⟩ := exists_contMDiffOn_extend (k := 1) I F σ₀
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/MDifferentiable.lean:716:  (contMDiffAt_extend' (k := 1) I F σ₀).mdifferentiableAt one_ne_zero
```

### Command

```sh
rg -n 'contDiff.*(tsupport|support)|HasCompactSupport.*comp|tsupport.*comp|contMDiffOn_extChartAt_symm|contMDiffAt_extChartAt_symm' .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff .lake/packages/mathlib/Mathlib/Topology/Algebra/Support*
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:118:theorem contMDiffOn_extChartAt_symm (x : M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean:128:  contMDiffOn_extChartAt_symm x y hy
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:74:        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) g (by fun_prop) ht
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:79:        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) f (by fun_prop) ht
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:158:      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:167:      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:21:in `IsOpen.exists_contDiff_support_eq`.
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:45:theorem exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : ℕ∞} (hs : s ∈ 𝓝 x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:78:alias exists_smooth_tsupport_subset := exists_contDiff_tsupport_subset
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:82:theorem IsOpen.exists_contDiff_support_eq {n : ℕ∞} {s : Set E} (hs : IsOpen s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:100:      rcases exists_contDiff_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:140:        apply HasCompactSupport.comp_left _ norm_zero
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:199:alias IsOpen.exists_smooth_support_eq := IsOpen.exists_contDiff_support_eq
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:224:    A.exists_contDiff_support_eq
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:399:  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:386:  (tsupport_comp_subset (g := fun L : E →L[𝕜] F ↦ L v) rfl _).trans (tsupport_fderiv_subset 𝕜)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:20:  `HasCompactSupport.hasFDerivAt_convolution_left`: we can compute the total derivative
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:215:    apply (HasCompactSupport.convolutionExists_right (L.precompR (P × G) :) T hf _ q₀.2).1
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:785:    refine tsupport_comp_eq (g := ContinuousMultilinearMap.curryLeft) (fun {x} ↦ ?_) _ |>.symm
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:793:  refine tsupport_comp_eq (g := ContinuousMultilinearMap.curry0) (fun {x} ↦ ?_) _ |>.symm
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove the Hausdorff measure formula on full open chart sources"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer f13f4667] Prove the Hausdorff measure formula on full open chart sources
 1 file changed, 44 insertions(+)
 create mode 100644 Poincare/Global/ClosedLaplacianStokesProducer.lean
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n 'laplacian.*(cont|meas)|((cont|meas)[A-Za-z_]*).*laplacian|contMDiff.*gradient|contMDiff.*hessian|continuous.*hessian|continuous.*covariant|contMDiff.*covDeriv' Poincare/Global/Laplacian.lean Poincare/ModelLaplacian.lean Poincare/CovariantDerivative*.lean
```

Exit: 1

```text
zsh:1: no matches found: Poincare/CovariantDerivative*.lean
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove density integrability on full inverse charts"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 60c4f99b] Prove density integrability on full inverse charts
 1 file changed, 28 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'contMDiff.*gradient|contMDiff.*hessian|continuous.*hessian|continuous.*covariant|contMDiff.*covDeriv|contMDiff.*leviCivita|laplacian.*measurable' Poincare .lake/packages/mathlib/Mathlib/Geometry/Manifold
```

Exit: 0

```text
Poincare/ModelChristoffel.lean:1025:    @leviCivitaConnection_contMDiff = @leviCivitaConnection_contMDiff :=
Poincare/ModelLaplacian.lean:13198:is built from continuous-linear maps in `z`. Infrastructure for the covariant-level
Poincare/ModelLaplacian.lean:28808:`w`-slot continuously — the inner factor of the CLM-valued Hessian field `covariantHessianForm`. -/
Poincare/ModelLaplacian.lean:28821:continuous bilinear form `(v,w) ↦ D²f(v,w) − df(Γ(v,w))`, built from `covariantHessianInnerCLM` made linear
Poincare/Global/ConnectionInstanceNaturality.lean:432:    fun V hV ↦ CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt g.leviCivita hZold hV
Poincare/Global/MetricFamilyCovRicciEntryContinuity.lean:467:/-- Chart data sufficient to construct continuous coordinate covariant-Ricci
Poincare/Global/ScalarVariation.lean:6517:        (FiberBundle.contMDiffAt_extend' (k := 2) I E (g.leviCivita Z x v))
Poincare/Global/HeatCauchyNext2.lean:713:      continuous_const.smul (hhessian.continuous.comp hsub)
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:178:theorem continuous_hessian_pos :
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:222:    continuous_hessian_pos.comp
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:349:theorem continuous_duhamel_hessian {α T t M K : ℝ}
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:415:  exact continuous_duhamel_hessian hα hα1 ht hf hM hK
```

### Command

```sh
rg -n 'laplacianAt.*eq|eq.*laplacianAt|chart.*[Ll]aplacian|[Ll]aplacian.*chart' Poincare/Global/Laplacian.lean Poincare/Global/Scalar*.lean Poincare/Global/*Laplacian*.lean Poincare/ModelLaplacian.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:5:# Open-chart data for closed Laplacian Stokes
Poincare/Global/Laplacian.lean:495:theorem laplacianAt_eq_trace_hessianContinuousAt
Poincare/Global/Laplacian.lean:822:  rw [g.laplacianAt_eq_trace_hessianContinuousAt (f * h) x,
Poincare/Global/Laplacian.lean:823:    g.laplacianAt_eq_trace_hessianContinuousAt h x,
Poincare/Global/Laplacian.lean:824:    g.laplacianAt_eq_trace_hessianContinuousAt f x]
Poincare/Global/Laplacian.lean:495:theorem laplacianAt_eq_trace_hessianContinuousAt
Poincare/Global/Laplacian.lean:822:  rw [g.laplacianAt_eq_trace_hessianContinuousAt (f * h) x,
Poincare/Global/Laplacian.lean:823:    g.laplacianAt_eq_trace_hessianContinuousAt h x,
Poincare/Global/Laplacian.lean:824:    g.laplacianAt_eq_trace_hessianContinuousAt f x]
Poincare/Global/ScalarEvolution.lean:20:single-chart analogues already live in `ModelLaplacian.lean`; this file adds
Poincare/Global/ScalarEvolution.lean:589:  rw [laplacianAt_eq_sum_hessianAt (g := g)
Poincare/Global/ScalarEvolution.lean:591:  rw [laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x)]
Poincare/Global/ScalarEvolution.lean:1441:theorem laplacianAt_tracelessRicciNormSqAt_eq
Poincare/Global/ScalarEvolution.lean:1540:theorem laplacianAt_quotient_eq_of_eventually_product_rule
Poincare/Global/ScalarEvolution.lean:1671:      (g.laplacianAt_quotient_eq_of_eventually_product_rule
Poincare/Global/ScalarEvolution.lean:1938:    g.laplacianAt_quotient_eq_of_eventually_product_rule
Poincare/Global/ScalarEvolution.lean:2091:theorem hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
Poincare/Global/ScalarEvolution.lean:2155:      laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq
Poincare/Global/ScalarEvolution.lean:2167:theorem hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_scalarGrad_add_tracelessReactionTrace3
Poincare/Global/ScalarEvolution.lean:2249:      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
Poincare/Global/ScalarEvolution.lean:2274:      g.laplacianAt_tracelessRicciNormSqAt_eq
Poincare/Global/ScalarEvolution.lean:2369:      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
Poincare/Global/ScalarEvolution.lean:2685:      hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_scalarGrad_add_tracelessReactionTrace3
Poincare/Global/ScalarEvolution.lean:2827:theorem laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero
Poincare/Global/ScalarEvolution.lean:2866:    g.laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero hric x
Poincare/Global/ScalarEvolution.lean:2900:uses only `laplacianAt_eq_sum_hessianAt`.
Poincare/Global/ScalarEvolution.lean:3946:  rw [g.laplacianAt_eq_trace_hessianContinuousAt f x]
Poincare/Global/ScalarVariation.lean:2108:theorem laplacianAt_eq_sum_hessianAt
Poincare/Global/ScalarVariation.lean:2124:/-- Basis-invariant form of `laplacianAt_eq_sum_hessianAt`. -/
Poincare/Global/ScalarVariation.lean:2125:theorem laplacianAt_eq_sum_hessianAt_basis
Poincare/Global/ScalarVariation.lean:16501:theorem laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub
Poincare/Global/ScalarVariation.lean:16526:  rw [laplacianAt_eq_sum_hessianAt (g := g)
Poincare/Global/ScalarVariation.lean:19403:          rw [laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x)]
Poincare/Global/ScalarVariation.lean:20688:theorem laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq
Poincare/Global/ScalarVariation.lean:20713:      laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub
Poincare/Global/ScalarVariation.lean:24219:      laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x)
Poincare/Global/ScalarVariation.lean:24683:      laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq
Poincare/Global/ScalarVariation.lean:25309:theorem laplacianAt_quotient_eq_of_product_rule
Poincare/Global/ScalarVariation.lean:25551:separate and already proved by `laplacianAt_eq_sum_hessianAt`.
Poincare/Global/ScalarVariation.lean:26415:      (laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x))
Poincare/Global/ScalarVariation.lean:26442:      (laplacianAt_eq_sum_hessianAt (g := g) (f := f) (x := x))
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Construct a smooth partition subordinate to the finite genuine chart cover"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 9fb0f22b] Construct a smooth partition subordinate to the finite genuine chart cover
 1 file changed, 8 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:87:23: error: typeclass instance problem is stuck
  ChartedSpace (ClosedSmoothModel ?m.41) M

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `ChartedSpace` contain metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

### Command

```sh
rg -n 'euclideanCoordinateDivergence.*continuous|continuous.*euclideanCoordinateDivergence|theorem.*euclideanCoordinateDivergence|notMem_tsupport_iff_eventuallyEq|contMDiffAt.*contDiffAt|contDiffOn.*contDiffAt' Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean .lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean
```

Exit: 0

```text
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:71:theorem euclideanCoordinateDivergence_integrable
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:83:theorem integral_euclideanCoordinateDivergence_eq_zero
Poincare/Global/NormalizedFlowHausdorffAutomaticStokes.lean:100:theorem euclideanCoordinateDivergence_eq_zero_of_not_mem
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:51:theorem contMDiffAt_iff_contDiffAt {f : E → E'} {x : E} :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean:55:alias ⟨ContMDiffAt.contDiffAt, ContDiffAt.contMDiffAt⟩ := contMDiffAt_iff_contDiffAt
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:99:28: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
p : M
f : M → ℝ
hf : tsupport f ⊆ (extChartAt I p).source
hcompact : IsCompact (↑(extChartAt I p) '' tsupport f)
z : E
hz : z ∈ Function.support (coordinateScalar p f)
hzt : z ∉ (extChartAt I p).target
⊢ z ∈ (chartAt E p).target → f (↑(chartAt E p).symm z) = 0
Poincare/Global/ClosedLaplacianStokesProducer.lean:99:55: warning: This simp argument is unused:
  indicator_of_notMem hzt

Hint: Omit it from the simp argument list.
  simp [coordinateScalar,̵ ̵i̵n̵d̵i̵c̵a̵t̵o̵r̵_̵o̵f̵_̵n̵o̵t̵M̵e̵m̵ ̵h̵z̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Command

```sh
rg -n 'contDiff.*inv|ContDiff.*inv|contDiff.*det|ContDiff.*det' .lake/packages/mathlib/Mathlib/Analysis/Matrix .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff; rg -n 'chartVolumeDensity|contDiff.*sqrt|ContDiff.*sqrt' Poincare/VolumeDensity.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean; rg -n 'density_inverseMetric_compatibility|intrinsicCoordinateLaplacian_eq|sqrt.*christoffel|density.*Christoffel' Poincare
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:541:    ContDiff 𝕜 n fun x => f x / c := by simpa only [div_eq_mul_inv] using hf.mul contDiff_const
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:780:    ContDiffAt 𝕜 n Ring.inverse (x : R) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:781:  have := AnalyticOnNhd.contDiffOn (analyticOnNhd_inverse (𝕜 := 𝕜) (A := R)) (n := n)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:788:theorem contDiffAt_inv {x : 𝕜'} (hx : x ≠ 0) {n} : ContDiffAt 𝕜 n Inv.inv x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:792:theorem contDiffOn_inv {n} : ContDiffOn 𝕜 n (Inv.inv : 𝕜' → 𝕜') {0}ᶜ := fun _ hx =>
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:793:  (contDiffAt_inv 𝕜 hx).contDiffWithinAt
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:798:theorem ContDiffWithinAt.inv {f : E → 𝕜'} {n} (hf : ContDiffWithinAt 𝕜 n f s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:800:  (contDiffAt_inv 𝕜 hx).comp_contDiffWithinAt x hf
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:803:theorem ContDiffOn.inv {f : E → 𝕜'} (hf : ContDiffOn 𝕜 n f s) (h : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:804:    ContDiffOn 𝕜 n (fun x => (f x)⁻¹) s := fun x hx => (hf.contDiffWithinAt hx).inv (h x hx)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:807:nonrec theorem ContDiffAt.inv {f : E → 𝕜'} (hf : ContDiffAt 𝕜 n f x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:812:theorem ContDiff.inv {f : E → 𝕜'} (hf : ContDiff 𝕜 n f) (h : ∀ x, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:814:  rw [contDiff_iff_contDiffAt]; exact fun x => hf.contDiffAt.inv (h x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:855:theorem contDiffAt_map_inverse [CompleteSpace E] (e : E ≃L[𝕜] F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:856:    ContDiffAt 𝕜 n inverse (e : E →L[𝕜] F) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:874:theorem ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse [CompleteSpace E] {e : E →L[𝕜] F}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:875:    (he : e.IsInvertible) : ContDiffAt 𝕜 n inverse e := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:877:  exact _root_.contDiffAt_map_inverse M
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:935:        have h_deriv₁ : ContDiffAt 𝕜 n inverse (f' (f.symm a)) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:937:          exact contDiffAt_map_inverse _
rg: Poincare/VolumeDensity.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:65:theorem contDiffAt_sqrt {x : ℝ} {n : WithTop ℕ∞} (hx : x ≠ 0) : ContDiffAt ℝ n (√·) x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:150:theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:152:  (contDiffAt_sqrt hx).comp x hf
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:155:theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:157:  (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:160:theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:161:    ContDiffOn ℝ n (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:164:theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => √(f y) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:165:  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:386:coordinate formula and the density/contracted-Christoffel compatibility
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:431:  density_inverseMetric_compatibility : ∀ i
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:437:  intrinsicCoordinateLaplacian_eq : ∀ i
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:560:      (A.density_inverseMetric_compatibility i z)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:571:              (A.intrinsicCoordinateLaplacian_eq i z)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'contDiff.*(det|matrix_inv|matrixInv)|ContDiff.*(det|matrix_inv|matrixInv)' .lake/packages/mathlib/Mathlib; rg -n 'def chartVolumeDensity|contDiff.*chartVolumeDensity' Poincare; rg -n 'theorem.*(contDiffOn|contDiffAt).*chartMetric|density.*[Cc]hristoffel|[Cc]hristoffel.*density|contracted.*[Cc]hristoffel' Poincare/ModelChristoffel.lean Poincare/Global/Coordinate*.lean
```

Exit: 1

```text
Poincare/Global/VolumeDensity.lean:74:def chartVolumeDensity (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
Poincare/Global/VolumeDensity.lean:81:def chartVolumeDensityOfBilinear
```

### Command

```sh
rg -n 'contDiffWithinAt.*contDiffAt|theorem ContMDiffWithinAt.contMDiffAt|notMem_tsupport_iff_eventuallyEq|continuousOn_extChartAt' .lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Support* .lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:510:theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:630:theorem continuousOn_extChartAt_symm (x : M) :
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:919:    hcom.image_of_continuousOn <| (continuousOn_extChartAt x).mono hss
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:944:theorem contDiffWithinAt_iff_contDiffAt (h : s ∈ 𝓝 x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:950:  forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:511:  apply (continuousOn_extChartAt _).comp
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:512:  · apply h.comp ((continuousOn_extChartAt_symm _).mono inter_subset_left) (fun z hz ↦ ?_)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiff/Defs.lean:704:protected theorem ContMDiffWithinAt.contMDiffAt
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove compact support of zero-extended chart scalars"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer d6e6c382] Prove compact support of zero-extended chart scalars
 1 file changed, 23 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:111:48: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/ClosedLaplacianStokesProducer.lean:111:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace (ModelWithCorners ℝ E E)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ClosedLaplacianStokesProducer.lean:107:52: error: unsolved goals
case neg
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
p : M
f : M → ℝ
hf : tsupport f ⊆ (extChartAt I p).source
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
z : E
hz : z ∉ (extChartAt I p).target
⊢ ContDiffAt ℝ 2 (coordinateScalar p f) z
```

### Command

```sh
rg -n 'mdifferentiableAt_gradient|laplacianAt_const|laplacianAt_congr_of_eventuallyEq' Poincare/Global/Laplacian.lean; rg -n 'theorem ContinuousAt.congr_of_eventuallyEq|theorem.*sum' .lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean; rg -n 'tsupport.*eventuallyEq|eventuallyEq.*tsupport' .lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Support*/*.lean
```

Exit: 1

```text
213:theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
510:theorem laplacianAt_congr_of_eventuallyEq
700:  g.hessianAt_symm hf (g.mdifferentiableAt_gradient hf) v w
756:    (g.mdifferentiableAt_gradient (hf x))
757:    (g.mdifferentiableAt_gradient (hh x))
765:theorem laplacianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
778:theorem laplacianAt_const_smul' (g : ClosedSmoothRiemannianMetric n M)
782:  g.laplacianAt_const_smul c
784:    (g.mdifferentiableAt_gradient (hf x))
861:    (g.mdifferentiableAt_gradient (hf x))
862:    (g.mdifferentiableAt_gradient (hh x))
876:theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:436:theorem ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) :
zsh:1: no matches found: .lake/packages/mathlib/Mathlib/Topology/Algebra/Support*/*.lean
```

### Command

```sh
rg -n 'contMDiffOn_extChartAt_symm' Poincare | head -20
```

Exit: 0

```text
Poincare/ChartTransport.lean:227:      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm x₀
Poincare/ChartTransport.lean:440:    (contMDiffOn_extChartAt_symm x₀).of_le (le_trans le_self_add hm)
Poincare/Global/VolumeFinitenessComparison.lean:94:      ((contMDiffOn_extChartAt_symm x).comp η_smooth hη.1)
Poincare/Global/MetricFlowJointRegularity.lean:230:    simpa [e] using (contMDiffOn_extChartAt_symm (I := Iₘ) x)
Poincare/Global/ClosedLaplacianStokesProducer.lean:111:  · have hinv := (contMDiffOn_extChartAt_symm (I := I) (n := 2) p z hz).contMDiffAt
Poincare/Global/DeTurckCoordinateJointRegularityThree.lean:98:    simpa [e] using (contMDiffOn_extChartAt_symm (I := Iₘ) x)
Poincare/Global/HausdorffInverseChartLocalFrozenUpper.lean:134:    exact (contMDiffOn_extChartAt_symm x₀).comp hηsmooth hηtarget
Poincare/Global/GeodesicPathLength.lean:114:  exact (contMDiffOn_extChartAt_symm x₀).comp hposM
Poincare/Global/DeTurckCoordinateJointRegularityFour.lean:98:    simpa [e] using (contMDiffOn_extChartAt_symm (I := Iₘ) x)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:111:59: error: Application type mismatch: The argument
  z
has type
  E
of sort `Type` but is expected to have type
  p ∈ (extChartAt ?m.123 I).target
of sort `Prop` in the application
  contMDiffOn_extChartAt_symm I p z
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'continuous_iff_continuousAt|ContinuousAt.div|ContinuousAt.comp|ContinuousAt.congr_of_eventuallyEq|isOpen_compl|eq_div_iff' .lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean | head -25
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:61:nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:126:  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).inv₀ (h0 x)
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:213:nonrec theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:230:theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:231:    ContinuousAt (fun x => f x / g x) a := ContinuousAt.div hf hg h₀
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:242:theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:254:  `0`. See docstring of `ContinuousAt.comp_div_cases`. -/
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:259:  continuous_iff_continuousAt.mpr fun a =>
.lake/packages/mathlib/Mathlib/Topology/Algebra/GroupWithZero.lean:373:  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).zpow₀ m (h0 x)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:49:  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:104:  rw [ContinuousOn, continuous_iff_continuousAt]; constructor
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:152:  continuous_iff_continuousAt.mpr fun x ↦ let ⟨i, hi⟩ := hs x; by
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:436:theorem ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:485:@[fun_prop] theorem ContinuousAt.comp_continuousWithinAt {g : β → γ}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:489:theorem ContinuousAt.comp_continuousWithinAt_of_eq {g : β → γ} {y : β}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:532:theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:536:  ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)
.lake/packages/mathlib/Mathlib/Topology/ContinuousOn.lean:538:theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ → δ} {g : α → β}
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove C2 regularity of zero-extended chart scalars"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer c2a6890b] Prove C2 regularity of zero-extended chart scalars
 1 file changed, 19 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'contDiff|ContDiff|hasFDeriv|chartVolumeDensity' Poincare/Global/VolumeDensity.lean | head -65; rg -n 'Matrix.*contDiff|matrix.*[Cc]ontDiff|contDiff.*matrix|ContDiff.*matrix' Poincare/Global/MetricFlowJointRegularity.lean Poincare/ModelChristoffel.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean
```

Exit: 1

```text
74:def chartVolumeDensity (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
81:def chartVolumeDensityOfBilinear
84:  chartVolumeDensity (bilinearFormMatrix B)
91:theorem chartVolumeDensity_nonneg (G : Matrix (Fin n) (Fin n) ℝ) :
92:    0 ≤ chartVolumeDensity G :=
96:theorem chartVolumeDensity_pos_of_posDef {G : Matrix (Fin n) (Fin n) ℝ}
98:    0 < chartVolumeDensity (n := n) G := by
103:theorem chartVolumeDensityOfBilinear_pos_of_posDef
107:    0 < chartVolumeDensityOfBilinear (n := n) B :=
108:  chartVolumeDensity_pos_of_posDef hB
123:theorem chartVolumeDensity_conformalGram_sq (c : ℝ) (hc : 0 ≤ c) :
124:    chartVolumeDensity (n := n) (conformalGram (n := n) c) ^ 2 = c ^ n := by
125:  rw [chartVolumeDensity, chartGramDet_conformalGram,
133:theorem chartVolumeDensityOfBilinear_conformal_sq
138:    chartVolumeDensityOfBilinear (n := n) B ^ 2 = c ^ n := by
139:  rw [chartVolumeDensityOfBilinear, hB]
140:  exact chartVolumeDensity_conformalGram_sq c hc
143:theorem chartVolumeDensityOfBilinear_conformalInnerScale_sq (c : ℝ)
145:    chartVolumeDensityOfBilinear (n := n)
148:  exact chartVolumeDensityOfBilinear_conformal_sq
158:theorem continuous_chartVolumeDensity {X : Type*} [TopologicalSpace X]
160:    Continuous fun z => chartVolumeDensity (n := n) (G z) := by
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Derive Laplacian continuity from positive-density coordinate divergence"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 07a16b64] Derive Laplacian continuity from positive-density coordinate divergence
 1 file changed, 38 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:186:10: warning: `continuous_finset_sum` has been deprecated: Use `continuous_finsetSum` instead
Poincare/Global/ClosedLaplacianStokesProducer.lean:199:6: error: Application type mismatch: The argument
  hcompat z
has type
  ∀ (j : Fin n),
    ∑ i, (fderiv ℝ (fun y => w y * a y i j) ↑z) (EuclideanSpace.single i 1) =
      w ↑z * -∑ i, ∑ k, a (↑z) i k * Γ (↑z) j i k
but is expected to have type
  ∀ (j : Fin n), ∑ i, (fderiv ℝ (fun y => w y * a y i j) ↑z) (EuclideanSpace.single i 1) = w ↑z * ?m.379 (↑z) j
in the application
  euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq (ContDiff.differentiable hw one_ne_zero ↑z)
    (fun i j => ContDiff.differentiable (ha i j) one_ne_zero ↑z)
    (fun j => ContDiff.differentiable (coordinateDirectionalDerivative_contDiff_one hu j) one_ne_zero ↑z) (hcompat z)
```

### Command

```sh
rg -n 'theorem det_apply|def det |theorem ContDiffOn.prod|theorem ContDiffOn.sum|theorem ContDiffOn.congr|theorem PosDef.det_pos|lemma PosDef.det_pos|inv_def|inv_apply' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:338:  · rw [nonsing_inv_apply_not_isUnit _ h]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:59:def det (M : Matrix n n R) : R :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:62:theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:66:theorem det_apply' (M : Matrix n n R) : M.det = ∑ σ : Perm n, ε σ * ∏ i, M (σ i) i := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:71:  simp_rw [inv_apply, sign_inv, sub_eq_add_neg, detp, ← sum_neg_distrib]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:648:      have mk_inv_apply_eq : ∀ k x, ((σ.symm (x, k)).fst, k) = σ.symm (x, k) := by grind
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:653:        simp [mk_inv_apply_eq]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:555:theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean:564:theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:172:theorem inv_def (A : Matrix n n α) : A⁻¹ = A.det⁻¹ʳ • A.adjugate :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:175:theorem nonsing_inv_apply_not_isUnit (h : ¬IsUnit A.det) : A⁻¹ = 0 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:176:  rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:178:theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = (↑h.unit⁻¹ : α) • A.adjugate := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:179:  rw [inv_def, ← Ring.inverse_unit h.unit, IsUnit.unit_spec]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:185:  rw [inv_def, Ring.inverse_invertible, invOf_eq]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:200:    rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit A h_det]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:203:  rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:206:  rw [inv_def, inv_def, conjTranspose_smul, det_conjTranspose, adjugate_conjTranspose,
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:406:  · exact Or.inr (nonsing_inv_apply_not_isUnit _ h)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:419:  · rw [Ring.inverse_non_unit _ h, nonsing_inv_apply_not_isUnit _ h, det_zero ‹_›]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:502:    refine nonsing_inv_apply_not_isUnit _ ?_
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:592:  rw [inv_def, adjugate_subsingleton, smul_one_eq_diagonal]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:630:  · simp [nonsing_inv_apply_not_isUnit _ h]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:643:  simp only [inv_def]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:658:  rw [cramer_eq_adjugate_mulVec, A.nonsing_inv_apply h, ← smul_mulVec, smul_smul,
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:749:    rw [nonsing_inv_apply_not_isUnit _ hA, zero_kronecker, nonsing_inv_apply_not_isUnit _ hAB]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:757:    rw [nonsing_inv_apply_not_isUnit _ hB, kronecker_zero, nonsing_inv_apply_not_isUnit _ hAB]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:381:theorem ContDiffOn.sum {ι : Type*} {f : ι → E → F} {s : Finset ι} {t : Set E}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:727:theorem ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'theorem.*ContDiff.*abs|lemma.*ContDiff.*abs|PosDef.det_pos|theorem.*ContDiffOn.prod|lemma.*ContDiffOn.prod|matrix.*[Ii]nv|adjugate_apply' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean | head -45
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:194:theorem adjugate_apply (A : Matrix n n α) (i j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:200:  rw [transpose_apply, adjugate_apply, adjugate_apply, updateRow_transpose, det_transpose]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:236:  rw [adjugate_apply, submatrix_apply, adjugate_apply, ← det_submatrix_equiv_self e,
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:258:theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:267:  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, Pi.single_apply, eq_comm]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:289:  simp [Subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:328:  rw [adjugate_apply, RingHom.mapMatrix_apply, map_apply, RingHom.mapMatrix_apply, this, ←
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:329:    map_updateRow, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← adjugate_apply]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Adjugate.lean:364:  simp_rw [adjugate_apply, det_succ_row _ j, updateRow_self, submatrix_updateRow_succAbove]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean:727:theorem ContDiffOn.prodMap {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F' : Type*}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean:573:theorem ContDiffOn.prodMk {s : Set E} {f : E → F} {g : E → G} (hf : ContDiffOn 𝕜 n f s)
```

### Command

```sh
rg -n 'det_pos|contDiffOn_abs|ContDiffOn.*norm|ContDiff.*norm' .lake/packages/mathlib/Mathlib/Analysis/Matrix .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Norm.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean
```

Exit: 2

```text
rg: .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Norm.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/Analysis/Matrix/PosDef.lean:85:lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A := by
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Derive localized Laplacian measurability from the coefficient identities"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer dcf8ccb9] Derive localized Laplacian measurability from the coefficient identities
 1 file changed, 47 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'PosDef.det_pos|\.det_pos|det_apply.*ContDiff|simp.*det_apply' Poincare/Global/Hausdorff* Poincare/Global/Volume* Poincare/Global/Metric* | head -20
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Construct finite Hausdorff Stokes geometry from explicit residual coefficients"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer ffad15f4] Construct finite Hausdorff Stokes geometry from explicit residual coefficients
 1 file changed, 77 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:73:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:85:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:124:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.contDiffOn_matrix_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove determinant smoothness from coordinate entries"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 5f760102] Prove determinant smoothness from coordinate entries
 1 file changed, 13 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:86:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:125:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:86:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:125:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.contDiffOn_matrix_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.chartWeight_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
rg -n 'theorem updateRow_apply|lemma updateRow_apply|theorem inverse_eq_inv|lemma inverse_eq_inv' .lake/packages/mathlib/Mathlib; rg -n '^(noncomputable )?(def|theorem) .*([Cc]hristoffel|chartMetric)' Poincare/ModelChristoffel.lean Poincare/ChartTransport.lean | head -45
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/RowCol.lean:227:theorem updateRow_apply [DecidableEq m] {i' : m} :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:315:lemma inverse_eq_inverse' (f : X →[M] Y₁) (g : Y₁ → X)
Poincare/ChartTransport.lean:28:def chartMetric [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:49:theorem chartMetric_apply [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:62:theorem chartMetric_apply_chart [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:91:theorem chartMetric_symm [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:109:theorem chartMetric_nondegenerate [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:135:theorem chartMetric_posDef [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:154:theorem chartMetric_nondegenerate_center [FiniteDimensional ℝ E]
Poincare/ChartTransport.lean:168:theorem chartMetric_model_space
Poincare/ChartTransport.lean:196:theorem contDiff_chartMetric_iff
Poincare/ChartTransport.lean:286:theorem blendedChartMetric_eq_chartMetric_of_eq_one (χ : E → ℝ)
Poincare/ChartTransport.lean:428:theorem contMDiffOn_chartMetric_pairing
Poincare/ChartTransport.lean:730:theorem chartMetric_eq :
Poincare/ChartTransport.lean:747:theorem contMDiffOn_chartMetric_pairing_eq :
Poincare/ChartTransport.lean:785:theorem chartMetric_apply_eq :
Poincare/ChartTransport.lean:790:theorem chartMetric_apply_chart_eq :
Poincare/ChartTransport.lean:795:theorem chartMetric_symm_eq :
Poincare/ChartTransport.lean:800:theorem chartMetric_nondegenerate_eq :
Poincare/ChartTransport.lean:805:theorem chartMetric_posDef_eq :
Poincare/ChartTransport.lean:810:theorem chartMetric_nondegenerate_center_eq :
Poincare/ChartTransport.lean:815:theorem chartMetric_model_space_eq :
Poincare/ChartTransport.lean:820:theorem contDiff_chartMetric_iff_eq :
Poincare/ChartTransport.lean:840:theorem blendedChartMetric_eq_chartMetric_of_eq_one_eq :
Poincare/ModelChristoffel.lean:32:noncomputable def christoffelFunctional (x u v : F) :
Poincare/ModelChristoffel.lean:46:noncomputable def christoffelAt (x : F)
Poincare/ModelChristoffel.lean:51:theorem b_christoffelAt (x : F) (b : LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:87:theorem christoffelAt_symm {x : F} (b : LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:101:noncomputable def christoffelLinear (x : F) (b : LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:141:noncomputable def christoffelOneForm (b : Π x : F, LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:152:theorem christoffelOneForm_apply (b : Π x : F, LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:342:theorem christoffelAt_eq_inverse {x : F} (b : LinearMap.BilinForm ℝ F)
Poincare/ModelChristoffel.lean:368:theorem contDiffAt_christoffelAt {k : ℕ∞ω} {x : F}
Poincare/ModelChristoffel.lean:418:theorem contDiff_christoffel_apply_section {k : ℕ∞ω}
Poincare/ModelChristoffel.lean:624:theorem christoffelAt_const (G₀ : F →L[ℝ] F →L[ℝ] ℝ) (x : F)
Poincare/ModelChristoffel.lean:952:theorem christoffelFunctional_eq :
Poincare/ModelChristoffel.lean:957:theorem christoffelAt_eq :
Poincare/ModelChristoffel.lean:962:theorem christoffelLinear_eq :
Poincare/ModelChristoffel.lean:967:theorem christoffelOneForm_eq :
Poincare/ModelChristoffel.lean:1004:theorem christoffelAt_eq_inverse_eq :
Poincare/ModelChristoffel.lean:1009:theorem contDiffAt_christoffelAt_eq :
Poincare/ModelChristoffel.lean:1014:theorem contDiff_christoffel_apply_section_eq :
Poincare/ModelChristoffel.lean:1039:theorem christoffelAt_const_eq :
Poincare/ModelChristoffel.lean:1067:theorem b_christoffelAt_eq :
Poincare/ModelChristoffel.lean:1077:theorem christoffelAt_symm_eq :
Poincare/ModelChristoffel.lean:1082:theorem christoffelOneForm_apply_eq :
```

### Command

```sh
rg -n 'inverse_eq_inv' .lake/packages/mathlib/Mathlib/Algebra .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix | head -20; rg -n 'updateRow_apply' .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/RowCol.lean
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:586:`Matrix.diagonal_unique` can be used to reach this form, while `Ring.inverse_eq_inv` can be used
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:427:theorem Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹ := by
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:433:theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean:434:  funext Ring.inverse_eq_inv
227:theorem updateRow_apply [DecidableEq m] {i' : m} :
254:  rw [updateRow_apply, map_apply, map_apply, updateRow_apply]
265:  rw [transpose_apply, updateRow_apply, updateCol_apply]
270:  rw [transpose_apply, updateRow_apply, updateCol_apply]
345:  simp only [submatrix_apply, updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove smoothness of the genuine Hausdorff weight on chart targets"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 884ee1b2] Prove smoothness of the genuine Hausdorff weight on chart targets
 1 file changed, 28 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:86:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:125:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:345:6: error: Type mismatch
  contDiffOn_const
has type
  ContDiffOn ?m.229 ?m.237 (fun x => ?m.238) ?m.239
but is expected to have type
  ContDiffOn ℝ ∞ (fun x => Pi.single i ?m.213 l) (extChartAt I p).target
```

### Command

```sh
rg -n 'timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|laplacianAt_eq_trace_hessianContinuousAt|blendedChartMetric|contDiff_blended' Poincare/Global/MetricFlowJointRegularity.lean Poincare/Global/NormalizedFlowScalarRegularity.lean Poincare/Global/Laplacian.lean Poincare/ChartTransport.lean | head -35
```

Exit: 0

```text
Poincare/ChartTransport.lean:273:def blendedChartMetric (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ChartTransport.lean:278:theorem blendedChartMetric_apply (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ChartTransport.lean:281:    blendedChartMetric χ G₀ g x₀ z v w =
Poincare/ChartTransport.lean:283:  simp [blendedChartMetric]
Poincare/ChartTransport.lean:286:theorem blendedChartMetric_eq_chartMetric_of_eq_one (χ : E → ℝ)
Poincare/ChartTransport.lean:290:    blendedChartMetric χ G₀ g x₀ z = chartMetric g x₀ z := by
Poincare/ChartTransport.lean:292:  rw [blendedChartMetric_apply, hz]
Poincare/ChartTransport.lean:295:theorem blendedChartMetric_symm (χ : E → ℝ) (G₀ : E →L[ℝ] E →L[ℝ] ℝ)
Poincare/ChartTransport.lean:300:    blendedChartMetric χ G₀ g x₀ z v w =
Poincare/ChartTransport.lean:301:      blendedChartMetric χ G₀ g x₀ z w v := by
Poincare/ChartTransport.lean:302:  rw [blendedChartMetric_apply, blendedChartMetric_apply,
Poincare/ChartTransport.lean:309:theorem blendedChartMetric_posDef (χ : E → ℝ)
Poincare/ChartTransport.lean:318:    0 < blendedChartMetric χ G₀ g x₀ z v v := by
Poincare/ChartTransport.lean:319:  rw [blendedChartMetric_apply]
Poincare/ChartTransport.lean:332:theorem blendedChartMetric_nondegenerate (χ : E → ℝ)
Poincare/ChartTransport.lean:340:    (v : E) (hv : ∀ w, blendedChartMetric χ G₀ g x₀ z v w = 0) : v = 0 := by
Poincare/ChartTransport.lean:342:  have hpos := blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀ hχ0 hχ1
Poincare/ChartTransport.lean:350:with which `blendedChartMetric` satisfies all its hypotheses.  When the chart
Poincare/ChartTransport.lean:399:  refine ⟨blendedChartMetric χ G₀ g x₀,
Poincare/ChartTransport.lean:400:    fun z v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z v w,
Poincare/ChartTransport.lean:401:    fun z v hv ↦ blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀
Poincare/ChartTransport.lean:408:  rw [blendedChartMetric_apply, hz]
Poincare/ChartTransport.lean:495:  LinearMap.mk₂ ℝ (fun v w ↦ blendedChartMetric χ G₀ g x₀ z v w)
Poincare/ChartTransport.lean:512:    exact blendedChartMetric_nondegenerate χ G₀ hG₀pos g hgpos x₀
Poincare/ChartTransport.lean:516:    have hpos := blendedChartMetric_posDef χ G₀ hG₀pos g hgpos x₀
Poincare/ChartTransport.lean:538:  modelLeviCivita (blendedChartMetric χ G₀ g x₀)
Poincare/ChartTransport.lean:552:    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
Poincare/ChartTransport.lean:559:    (fun z' v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z' v w) z
Poincare/ChartTransport.lean:570:    (hbl : Differentiable ℝ (blendedChartMetric χ G₀ g x₀))
Poincare/ChartTransport.lean:574:    MetricCompatibleAt (blendedChartMetric χ G₀ g x₀)
Poincare/ChartTransport.lean:577:    (fun z' v w ↦ blendedChartMetric_symm χ G₀ hG₀symm g hgsymm x₀ z' v w)
Poincare/ChartTransport.lean:597:theorem contDiff_blendedChartMetric_scalar
Poincare/ChartTransport.lean:608:    ContDiff ℝ m (fun z ↦ blendedChartMetric χ G₀ g x₀ z v w) := by
Poincare/ChartTransport.lean:624:      fun z ↦ blendedChartMetric_apply χ G₀ g x₀ z v w)
Poincare/ChartTransport.lean:634:    rw [blendedChartMetric_apply, hz]
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:86:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ClosedLaplacianStokesProducer.lean:125:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:74:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition`:
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:86:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
  [IsManifold I ∞ M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold I ∞ M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/dependencies.lean:125:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence`:
  [CompactSpace M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.contDiffOn_matrix_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.chartWeight_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Prove smoothness of genuine inverse-metric entries on chart targets"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer 6e78c95e] Prove smoothness of genuine inverse-metric entries on chart targets
 1 file changed, 24 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
Poincare/Global/ClosedLaplacianStokesProducer.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/dependencies.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/dependencies.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.ClosedLaplacianStokesProducer.openChart_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.openChart_density_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.exists_subordinate_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.laplacian_continuous_of_coordinate_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.localizedLaplacian_continuous_of_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.contDiffOn_matrix_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.chartWeight_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 1

```text
```

### Command

```sh
git diff --check
```

Exit: 0

```text
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/resisting.lean
```

Exit: 1

```text
/tmp/closed-laplacian-stokes-producer/resisting.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/resisting.lean:355:11: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  SecondCountableTopology M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/closed-laplacian-stokes-producer/resisting.lean:369:19: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
H :
  ContDiffOn ℝ ∞
    (fun z =>
      ↑(rawHausdorffLebesgueScale n) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) z))
    (extChartAt I (C.anchor i)).target
⊢ ?m.223 ≤ ∞
/tmp/closed-laplacian-stokes-producer/resisting.lean:372:19: error: unsolved goals
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
j k : Fin n
H :
  ContDiffOn ℝ ∞ (fun z => (inverseChartPullbackGramMatrixField g (C.anchor i) z)⁻¹ j k)
    (extChartAt I (C.anchor i)).target
⊢ ?m.259 ≤ ∞
/tmp/closed-laplacian-stokes-producer/resisting.lean:375:2: error: unsolved goals
case refine_4
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
/tmp/closed-laplacian-stokes-producer/resisting.lean:377:2: error: unsolved goals
case refine_5
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
case refine_4
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
case refine_5
n : ℕ
M : Type u
inst✝⁷ : TopologicalSpace M
inst✝⁶ : T2Space M
inst✝⁵ : CompactSpace M
inst✝⁴ : ConnectedSpace M
inst✝³ : MeasurableSpace M
inst✝² : BorelSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := sorry
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
```

### Command

```sh
git add Poincare/Global/ClosedLaplacianStokesProducer.lean && git commit -m "Remove unused geometric assumptions from support and continuity lemmas"
```

Exit: 0

```text
[worker/closed-laplacian-stokes-producer eb0c39b9] Remove unused geometric assumptions from support and continuity lemmas
 1 file changed, 4 insertions(+)
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/flow.lean
```

Exit: 0

```text
/tmp/closed-laplacian-stokes-producer/flow.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare.ClosedLaplacianStokesProducer.geometry_of_coordinate_coefficients.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M] (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ) (hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
  (C : FiniteExtendedChartCover) (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M)
  (hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source) (w : Fin C.chartCount → E → ℝ)
  (a : Fin C.chartCount → E → Fin n → Fin n → ℝ) (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
  (hw : ∀ (i : Fin C.chartCount), ContDiff ℝ 1 (w i))
  (ha : ∀ (i : Fin C.chartCount) (j k : Fin n), ContDiff ℝ 1 fun z => a i z j k)
  (hweight :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target),
      w i ↑z = ↑(rawHausdorffLebesgueScale n) * inverseChartPullbackVolumeDensity g (C.anchor i) z)
  (hcompat :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target) (j : Fin n),
      ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
        w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l)
  (hcoord :
    ∀ (i : Fin C.chartCount) (z : ↑(extChartAt I (C.anchor i)).target),
      g.laplacianAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z) =
        christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z) :
  FiniteSubordinateHausdorffLaplacianGeometry g f
Poincare.FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M] {g : ClosedSmoothRiemannianMetric n M} {f : M → ℝ}
  (A : FiniteSubordinateHausdorffLaplacianGeometry g f) : ClosedLaplacianStokes g f
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/resisting.lean
```

Exit: 1

```text
/tmp/closed-laplacian-stokes-producer/resisting.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/resisting.lean:369:36: error: Ambiguous term
  ∞
Possible interpretations:
  ∞ : ℝ≥0∞

  ∞ : ℕ∞ω
/tmp/closed-laplacian-stokes-producer/resisting.lean:369:19: error: unsolved goals
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
H :
  ContDiffOn ℝ ∞
    (fun z =>
      ↑(rawHausdorffLebesgueScale n) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) z))
    (extChartAt I (C.anchor i)).target
⊢ 1 ≤ sorry ()
/tmp/closed-laplacian-stokes-producer/resisting.lean:372:36: error: Ambiguous term
  ∞
Possible interpretations:
  ∞ : ℝ≥0∞

  ∞ : ℕ∞ω
/tmp/closed-laplacian-stokes-producer/resisting.lean:372:19: error: unsolved goals
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
j k : Fin n
H :
  ContDiffOn ℝ ∞ (fun z => (inverseChartPullbackGramMatrixField g (C.anchor i) z)⁻¹ j k)
    (extChartAt I (C.anchor i)).target
⊢ 1 ≤ sorry ()
/tmp/closed-laplacian-stokes-producer/resisting.lean:375:2: error: unsolved goals
case refine_4
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
/tmp/closed-laplacian-stokes-producer/resisting.lean:377:2: error: unsolved goals
case refine_5
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
case refine_4
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
case refine_5
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
```

### Command

```sh
rg -n '(^|[ .])(ClosedLaplacianStokes|FiniteSubordinateHausdorffLaplacianGeometry|FiniteExtendedChartCover|inverseExtendedChartParametrization|inverseExtendedChartParametrization_isEmbedding|inverseChart_hausdorffChartDensityEquality|continuous_inverseChartPullbackVolumeDensity|inverseChartPullbackVolumeDensity_pos|inverseChartPullbackGramMatrixField|inverseChartPullbackGramMatrix_eq_field|inverseChartPullbackGramMatrix_posDef|contDiffOn_inverseChartPullbackGramMatrixField_entry|exists_isSubordinate|coordinateMetricFluxComponent_contDiff_one|coordinateDirectionalDerivative_contDiff_one|euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq|contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian|laplacianAt_congr_of_eventuallyEq|mdifferentiableAt_gradient|laplacianAt_const|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|chartVolumeDensity|rawHausdorffLebesgueScale|coordinateLebesgueMeasure|volumeMeasure_isFiniteMeasure)\b' Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean Poincare/Global/HausdorffInverseChartAreaFormula.lean Poincare/Global/HausdorffInverseChartGramContinuity.lean Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean Poincare/Global/Laplacian.lean Poincare/Global/MetricFlowJointRegularity.lean Poincare/Global/NormalizedFlowScalarRegularity.lean Poincare/Global/VolumeDensity.lean Poincare/Global/Volume.lean .lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean
```

Exit: 2

```text
rg: Poincare/Global/Volume.lean: No such file or directory (os error 2)
Poincare/Global/NormalizedFlowScalarRegularity.lean:91:theorem scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowScalarRegularity.lean:142:      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
Poincare/Global/NormalizedFlowScalarRegularity.lean:152:      (fun t ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean:89:theorem inverseChartPullbackGramMatrix_posDef
Poincare/Global/HausdorffFrozenInverseChartAreaFormula.lean:111:  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
Poincare/Global/HausdorffInverseChartAreaFormula.lean:47:    inverseExtendedChartParametrization (n := n) (M := M) x₀
Poincare/Global/HausdorffInverseChartAreaFormula.lean:50:    inverseExtendedChartParametrization_isEmbedding
Poincare/Global/HausdorffInverseChartAreaFormula.lean:149:theorem inverseChart_hausdorffChartDensityEquality
Poincare/Global/VolumeDensity.lean:74:def chartVolumeDensity (G : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
Poincare/Global/VolumeDensity.lean:84:  chartVolumeDensity (bilinearFormMatrix B)
Poincare/Global/VolumeDensity.lean:92:    0 ≤ chartVolumeDensity G :=
Poincare/Global/VolumeDensity.lean:98:    0 < chartVolumeDensity (n := n) G := by
Poincare/Global/VolumeDensity.lean:124:    chartVolumeDensity (n := n) (conformalGram (n := n) c) ^ 2 = c ^ n := by
Poincare/Global/VolumeDensity.lean:160:    Continuous fun z => chartVolumeDensity (n := n) (G z) := by
Poincare/Global/MetricFlowJointRegularity.lean:320:theorem timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointRegularity.lean:417:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/HausdorffInverseChartGramContinuity.lean:44:noncomputable def inverseChartPullbackGramMatrixField
Poincare/Global/HausdorffInverseChartGramContinuity.lean:55:theorem inverseChartPullbackGramMatrix_eq_field
Poincare/Global/HausdorffInverseChartGramContinuity.lean:59:      inverseChartPullbackGramMatrixField g x₀ z := by
Poincare/Global/HausdorffInverseChartGramContinuity.lean:76:theorem contDiffOn_inverseChartPullbackGramMatrixField_entry
Poincare/Global/HausdorffInverseChartGramContinuity.lean:79:      (fun z ↦ inverseChartPullbackGramMatrixField g x₀ z i j)
Poincare/Global/HausdorffInverseChartGramContinuity.lean:95:    (fun z i ↦ inverseChartPullbackGramMatrixField g x₀ z i)
Poincare/Global/HausdorffInverseChartGramContinuity.lean:103:  exact contDiffOn_inverseChartPullbackGramMatrixField_entry g x₀ i j
Poincare/Global/HausdorffInverseChartGramContinuity.lean:115:          inverseChartPullbackGramMatrixField g x₀ z) :=
Poincare/Global/HausdorffInverseChartGramContinuity.lean:124:theorem continuous_inverseChartPullbackVolumeDensity
Poincare/Global/HausdorffInverseChartGramContinuity.lean:135:theorem inverseChartPullbackVolumeDensity_pos
Poincare/Global/HausdorffInverseChartGramContinuity.lean:202:    inverseChartPullbackVolumeDensity_pos g x₀ z₀
Poincare/Global/Laplacian.lean:213:theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:510:theorem laplacianAt_congr_of_eventuallyEq
Poincare/Global/Laplacian.lean:700:  g.hessianAt_symm hf (g.mdifferentiableAt_gradient hf) v w
Poincare/Global/Laplacian.lean:756:    (g.mdifferentiableAt_gradient (hf x))
Poincare/Global/Laplacian.lean:757:    (g.mdifferentiableAt_gradient (hh x))
Poincare/Global/Laplacian.lean:784:    (g.mdifferentiableAt_gradient (hf x))
Poincare/Global/Laplacian.lean:861:    (g.mdifferentiableAt_gradient (hf x))
Poincare/Global/Laplacian.lean:862:    (g.mdifferentiableAt_gradient (hh x))
Poincare/Global/Laplacian.lean:876:theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:125:def inverseExtendedChartParametrization (x₀ : M) :
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:133:theorem inverseExtendedChartParametrization_isEmbedding (x₀ : M) :
Poincare/Global/HausdorffPullbackAreaFormulaReduction.lean:160:  VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrix g x₀ z)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:45:def ClosedLaplacianStokes
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:114:    g.laplacianAt_const (2 * meanScalar g) x,
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:448:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:477:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:509:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:560:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:591:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:627:    (hStokes : ClosedLaplacianStokes (gt t₀)
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:54:structure FiniteExtendedChartCover where
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:86:    FiniteExtendedChartCover (n := n) (M := M) :=
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:89:namespace FiniteExtendedChartCover
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:92:def chartSource (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:97:def manifoldPiece (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:104:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:111:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:121:    (C : FiniteExtendedChartCover (n := n) (M := M)) :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:128:    (C : FiniteExtendedChartCover (n := n) (M := M)) :
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:137:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:145:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:153:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:161:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:163:  fun z ↦ inverseExtendedChartParametrization
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:169:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:180:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:205:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:210:    inverseExtendedChartParametrization
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:236:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:244:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:252:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:261:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:271:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:286:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:297:end FiniteExtendedChartCover
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:302:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:314:    {C : FiniteExtendedChartCover (n := n) (M := M)}
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:338:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:348:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:373:    {C : FiniteExtendedChartCover (n := n) (M := M)}
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:392:    (C : FiniteExtendedChartCover (n := n) (M := M))
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:404:    {C : FiniteExtendedChartCover (n := n) (M := M)}
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:45:unity, see `SmoothPartitionOfUnity.exists_isSubordinate`.
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:100:subordinate to `U`, see `SmoothBumpCovering.exists_isSubordinate`.
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:364:theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:495:  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:563:theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:579:  apply exists_isSubordinate _ hs _ (fun i ↦ (chartAt H _).open_source) (fun x hx ↦ ?_)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:585:  apply exists_isSubordinate _ isClosed_univ _ (fun i ↦ (chartAt H _).open_source) (fun x _ ↦ ?_)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:618:    SmoothPartitionOfUnity.exists_isSubordinate
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:92:theorem coordinateDirectionalDerivative_contDiff_one
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:101:theorem coordinateMetricFluxComponent_contDiff_one
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:201:theorem euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:279:theorem contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:388:structure FiniteSubordinateHausdorffLaplacianGeometry
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:451:noncomputable def FiniteSubordinateHausdorffLaplacianGeometry.localizedScalar
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:453:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:458:theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedScalar_contMDiff_two
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:460:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:473:theorem FiniteSubordinateHausdorffLaplacianGeometry.tsupport_localizedScalar_subset_chartRegion
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:475:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:483:theorem FiniteSubordinateHausdorffLaplacianGeometry.laplacian_localizedScalar_eq_zero_of_not_mem
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:485:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:494:      g.laplacianAt_congr_of_eventuallyEq hxt
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:495:        (g.mdifferentiableAt_gradient
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:497:        (g.mdifferentiableAt_gradient contMDiffAt_const)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:498:    _ = 0 := g.laplacianAt_const 0 x
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:502:noncomputable def FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:504:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:511:theorem FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent_contDiff_one
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:513:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:516:  coordinateMetricFluxComponent_contDiff_one
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:522:theorem FiniteSubordinateHausdorffLaplacianGeometry.fluxComponent_hasCompactSupport
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:524:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:532:theorem FiniteSubordinateHausdorffLaplacianGeometry.tsupport_fluxComponent_subset_coordinateDomain
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:534:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:544:theorem FiniteSubordinateHausdorffLaplacianGeometry.coordinateLaplacianDensity_eq_divergence
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:546:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:552:    euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:584:theorem FiniteSubordinateHausdorffLaplacianGeometry.coordinateLaplacianDensity_integrable
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:586:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:614:theorem FiniteSubordinateHausdorffLaplacianGeometry.pulledBackLaplacian_integrable
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:616:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:624:  let μU := coordinateLebesgueMeasure U
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:625:  let c : ℝ := rawHausdorffLebesgueScale n
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:647:theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedLaplacian_integrableOn_chartRegion
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:649:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:673:theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedLaplacian_integrable
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:675:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:685:theorem FiniteSubordinateHausdorffLaplacianGeometry.localizedClosedLaplacianStokes
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:687:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:689:    ClosedLaplacianStokes g (A.localizedScalar i) := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:743:      simpa only [Finset.sum_empty] using g.laplacianAt_const 0 x
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:765:theorem FiniteSubordinateHausdorffLaplacianGeometry.sum_localizedScalar_eq
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:767:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) :
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:782:theorem FiniteSubordinateHausdorffLaplacianGeometry.laplacian_eq_sum_localized
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:784:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) (x : M) :
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:802:theorem FiniteSubordinateHausdorffLaplacianGeometry.closedLaplacianStokes
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:804:    (A : FiniteSubordinateHausdorffLaplacianGeometry g f) :
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:805:    ClosedLaplacianStokes g f := by
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:856:    FiniteSubordinateHausdorffLaplacianGeometry (gt t) (f t)
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:865:    ClosedLaplacianStokes (gt t) (f t) :=
```

### Command

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/closed-laplacian-stokes-producer/resisting.lean
```

Exit: 1

```text
/tmp/closed-laplacian-stokes-producer/resisting.lean:108:0: warning: automatically included section variable(s) unused in theorem `Poincare.ClosedLaplacianStokesProducer.coordinateScalar_contDiff_two`:
  [T2Space M]
  [ConnectedSpace M]
  [MeasurableSpace M]
  [BorelSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/closed-laplacian-stokes-producer/resisting.lean:369:4: error: Type mismatch
  ContDiffOn.of_le H (of_eq_true (Eq.trans WithTop.one_le_coe._simp_2 (Eq.trans le_top._simp_2 (eq_true True.intro))))
has type
  ContDiffOn ℝ 1
    (fun z =>
      ↑(rawHausdorffLebesgueScale n) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g (C.anchor i) z))
    (extChartAt I (C.anchor i)).target
but is expected to have type
  ContDiff ℝ 1 (w i)
/tmp/closed-laplacian-stokes-producer/resisting.lean:372:4: error: Type mismatch
  ContDiffOn.of_le H (of_eq_true (Eq.trans WithTop.one_le_coe._simp_2 (Eq.trans le_top._simp_2 (eq_true True.intro))))
has type
  ContDiffOn ℝ 1 (fun z => (inverseChartPullbackGramMatrixField g (C.anchor i) z)⁻¹ j k)
    (extChartAt I (C.anchor i)).target
but is expected to have type
  ContDiff ℝ 1 fun z => a i z j k
/tmp/closed-laplacian-stokes-producer/resisting.lean:375:2: error: unsolved goals
case refine_4
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
/tmp/closed-laplacian-stokes-producer/resisting.lean:377:2: error: unsolved goals
case refine_5
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
case refine_4
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
j : Fin n
⊢ ∑ k, (fderiv ℝ (fun y => w i y * a i y k j) ↑z) (EuclideanSpace.single k 1) =
    w i ↑z * -∑ k, ∑ l, a i (↑z) k l * Γ i (↑z) j k l
case refine_5
n : ℕ
M : Type u
inst✝⁸ : TopologicalSpace M
inst✝⁷ : T2Space M
inst✝⁶ : CompactSpace M
inst✝⁵ : ConnectedSpace M
inst✝⁴ : MeasurableSpace M
inst✝³ : BorelSpace M
inst✝² : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst✝ : SecondCountableTopology M
g : ClosedSmoothRiemannianMetric n M
f : M → ℝ
hreg : ContMDiff I 𝓘(ℝ, ℝ) 2 f
C : FiniteExtendedChartCover := compactFiniteExtendedChartCover
ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M
hρ : ρ.IsSubordinate fun i => (extChartAt I (C.anchor i)).source
G : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i => inverseChartPullbackGramMatrixField g (C.anchor i)
w : Fin C.chartCount → E → ℝ := fun i z => ↑(rawHausdorffLebesgueScale n) * VolumeDensity.chartVolumeDensity (G i z)
a : Fin C.chartCount → E → Matrix (Fin n) (Fin n) ℝ := fun i z => (G i z)⁻¹
Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ :=
  fun i z k j l =>
    1 / 2 *
      ∑ m,
        a i z k m *
          (coordinateDirectionalDerivative (fun y => G i y l m) j z +
              coordinateDirectionalDerivative (fun y => G i y j m) l z -
            coordinateDirectionalDerivative (fun y => G i y j l) m z)
i : Fin C.chartCount
z : ↑(extChartAt I (C.anchor i)).target
⊢ (LinearMap.trace ℝ (TangentSpace I (inverseExtendedChartParametrization (C.anchor i) z)))
      (↑((g.metricBilinAt (inverseExtendedChartParametrization (C.anchor i) z)).toDual ⋯).symm ∘ₗ
        ↑LinearMap.toContinuousLinearMap.symm ∘ₗ
          ↑(g.hessianContinuousAt (fun x => (ρ i) x * f x) (inverseExtendedChartParametrization (C.anchor i) z))) =
    christoffelCoordinateLaplacian (a i) (Γ i) (coordinateScalar (C.anchor i) fun x => (ρ i) x * f x) ↑z
```

### Command

```sh
rg -n '^(noncomputable )?(def|theorem|instance) (rawHausdorffLebesgueScale|coordinateLebesgueMeasure|volumeMeasure_isFiniteMeasure)\b' Poincare
```

Exit: 0

```text
Poincare/Global/VolumeFinitenessComparison.lean:146:theorem volumeMeasure_isFiniteMeasure
Poincare/Global/HausdorffCoordinateDensityVariation.lean:47:noncomputable def rawHausdorffLebesgueScale (n : ℕ) : ℝ≥0 :=
Poincare/Global/HausdorffCoordinateDensityVariation.lean:67:noncomputable def coordinateLebesgueMeasure
```

### Command

```sh
git status --short --branch
```

Exit: 0

```text
## worker/closed-laplacian-stokes-producer
```

### Command

```sh
git log --oneline 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..HEAD
```

Exit: 0

```text
eb0c39b9 Remove unused geometric assumptions from support and continuity lemmas
6e78c95e Prove smoothness of genuine inverse-metric entries on chart targets
884ee1b2 Prove smoothness of the genuine Hausdorff weight on chart targets
5f760102 Prove determinant smoothness from coordinate entries
ffad15f4 Construct finite Hausdorff Stokes geometry from explicit residual coefficients
dcf8ccb9 Derive localized Laplacian measurability from the coefficient identities
07a16b64 Derive Laplacian continuity from positive-density coordinate divergence
c2a6890b Prove C2 regularity of zero-extended chart scalars
d6e6c382 Prove compact support of zero-extended chart scalars
9fb0f22b Construct a smooth partition subordinate to the finite genuine chart cover
60c4f99b Prove density integrability on full inverse charts
f13f4667 Prove the Hausdorff measure formula on full open chart sources
```

### Command

```sh
git diff --stat 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..HEAD
```

Exit: 0

```text
 Poincare/Global/ClosedLaplacianStokesProducer.lean | 353 +++++++++++++++++++++
 1 file changed, 353 insertions(+)
```

### Command

```sh
git diff --check 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..HEAD
```

Exit: 0

```text
```

### Command

```sh
cat lean-toolchain
```

Exit: 0

```text
leanprover/lean4:v4.30.0-rc2
```

### Command

```sh
git diff 3bdabbc9806d413b0f71c939d8d0e1a96394c6c5..HEAD -- Poincare/Global/ClosedLaplacianStokesProducer.lean
```

Exit: 0

```text
diff --git a/Poincare/Global/ClosedLaplacianStokesProducer.lean b/Poincare/Global/ClosedLaplacianStokesProducer.lean
new file mode 100644
index 00000000..0c549094
--- /dev/null
+++ b/Poincare/Global/ClosedLaplacianStokesProducer.lean
@@ -0,0 +1,353 @@
+import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
+import Poincare.Global.HamiltonChartDensityLocalDomination
+import Mathlib.Analysis.Matrix.PosDef
+
+/-!
+# Open-chart data for closed Laplacian Stokes
+
+The constructors below supply genuine chart measures and compactly supported
+coordinate scalars. Coordinate coefficient identities remain explicit inputs
+to the final partial constructor.
+-/
+
+noncomputable section
+open Bundle FiberBundle Filter MeasureTheory Set
+open scoped Manifold ContDiff Topology ENNReal NNReal
+set_option autoImplicit false
+universe u
+namespace Poincare.ClosedLaplacianStokesProducer
+
+variable {n : ℕ} {M : Type u}
+variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
+variable [MeasurableSpace M] [BorelSpace M]
+variable [ChartedSpace (ClosedSmoothModel n) M]
+variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
+
+local notation "I" => closedSmoothModelWithCorners n
+local notation "E" => ClosedSmoothModel n
+
+/-- The full inverse-chart measure is the Riemannian measure on its open source. -/
+theorem openChart_measure (g : ClosedSmoothRiemannianMetric n M) (p : M) :
+    HausdorffChartDensityEquality g (extChartAt I p).target
+      (inverseExtendedChartParametrization (n := n) p)
+      (extChartAt I p).source (inverseChartPullbackVolumeDensity g p) := by
+  have hrange : Set.range (inverseExtendedChartParametrization (n := n) p) =
+      (extChartAt I p).source := by
+    ext x
+    constructor
+    · rintro ⟨z, rfl⟩
+      exact (extChartAt I p).map_target z.2
+    · intro hx
+      refine ⟨⟨extChartAt I p x, (extChartAt I p).map_source hx⟩, ?_⟩
+      exact (extChartAt I p).left_inv hx
+  simpa only [hrange] using inverseChart_hausdorffChartDensityEquality g p
+
+/-- Finite Riemannian volume gives integrability of the density on the full chart. -/
+theorem openChart_density_integrable (g : ClosedSmoothRiemannianMetric n M) (p : M) :
+    Integrable (inverseChartPullbackVolumeDensity g p)
+      (coordinateLebesgueMeasure (extChartAt I p).target) := by
+  have hcont := continuous_inverseChartPullbackVolumeDensity g p
+  have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+      (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+  have hmeas := (inverseExtendedChartParametrization_isEmbedding (n := n) p).continuous.measurable
+  have hmass := congrArg (fun μ : Measure M ↦ μ univ) (openChart_measure g p)
+  dsimp only at hmass
+  rw [Measure.map_apply hmeas MeasurableSet.univ, preimage_univ,
+    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hmass
+  have hfinite :
+      ∫⁻ z, ENNReal.ofReal ((rawHausdorffLebesgueScale n : ℝ) *
+        inverseChartPullbackVolumeDensity g p z)
+        ∂(coordinateLebesgueMeasure (extChartAt I p).target) ≠ (⊤ : ℝ≥0∞) := by
+    rw [rawHausdorffCoordinateDensityMeasure, withDensity_apply _ MeasurableSet.univ,
+      Measure.restrict_univ] at hmass
+    rw [hmass]
+    letI := volumeMeasure_isFiniteMeasure g
+    exact measure_ne_top (volumeMeasure g) _
+  have hint := (lintegral_ofReal_ne_top_iff_integrable
+    (hcont.const_mul (rawHausdorffLebesgueScale n : ℝ)).aestronglyMeasurable
+    (Eventually.of_forall fun z ↦ mul_nonneg hscale.le
+      (inverseChartPullbackVolumeDensity_pos g p z).le)).mp hfinite
+  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hscale.ne') _).mp hint
+
+omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
+/-- The compact finite chart cover has a smooth subordinate partition. -/
+theorem exists_subordinate_partition (C : FiniteExtendedChartCover (n := n) (M := M)) :
+    ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ,
+      ρ.IsSubordinate (fun i ↦ (extChartAt I (C.anchor i)).source) := by
+  apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ _
+    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
+  rw [C.sources_cover]
+
+/-- The coordinate scalar is extended by zero off the genuine target. -/
+def coordinateScalar (p : M) (f : M → ℝ) : E → ℝ :=
+  (extChartAt I p).target.indicator (fun z ↦ f ((extChartAt I p).symm z))
+
+omit [T2Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
+  [IsManifold I ∞ M] in
+/-- A scalar supported inside a chart has a compactly supported coordinate extension. -/
+theorem coordinateScalar_support (p : M) (f : M → ℝ)
+    (hf : tsupport f ⊆ (extChartAt I p).source) :
+    HasCompactSupport (coordinateScalar (n := n) p f) ∧
+      tsupport (coordinateScalar (n := n) p f) ⊆ (extChartAt I p).target := by
+  have hcompact : IsCompact ((extChartAt I p) '' tsupport f) :=
+    (isClosed_tsupport f).isCompact.image_of_continuousOn
+      ((continuousOn_extChartAt p).mono hf)
+  have hsub : tsupport (coordinateScalar (n := n) p f) ⊆ (extChartAt I p) '' tsupport f := by
+    apply closure_minimal _ hcompact.isClosed
+    intro z hz
+    by_cases hzt : z ∈ (extChartAt I p).target
+    · refine ⟨(extChartAt I p).symm z, ?_, (extChartAt I p).right_inv hzt⟩
+      apply subset_tsupport
+      simpa only [Function.mem_support, coordinateScalar, indicator_of_mem hzt] using hz
+    · exact False.elim (hz (indicator_of_notMem hzt _))
+  exact ⟨hcompact.of_isClosed_subset (isClosed_tsupport _) hsub,
+    hsub.trans (image_subset_iff.mpr fun x hx ↦ (extChartAt I p).map_source (hf hx))⟩
+
+/-- Zero extension preserves C² regularity for scalars supported inside the source. -/
+theorem coordinateScalar_contDiff_two (p : M) (f : M → ℝ)
+    (hf : tsupport f ⊆ (extChartAt I p).source)
+    (hreg : ContMDiff I 𝓘(ℝ) 2 f) :
+    ContDiff ℝ 2 (coordinateScalar (n := n) p f) := by
+  apply contDiff_iff_contDiffAt.mpr
+  intro z
+  by_cases hz : z ∈ (extChartAt I p).target
+  · have hinv := (contMDiffOn_extChartAt_symm (n := 2) p z hz).contMDiffAt
+      ((isOpen_extChartAt_target p).mem_nhds hz)
+    have hcomp := (hreg.contMDiffAt.comp z hinv).contDiffAt
+    apply hcomp.congr_of_eventuallyEq
+    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz] with y hy
+    exact indicator_of_mem hy _
+  · have hout : z ∉ tsupport (coordinateScalar (n := n) p f) :=
+      fun h ↦ hz ((coordinateScalar_support p f hf).2 h)
+    exact contDiffAt_const.congr_of_eventuallyEq
+      (notMem_tsupport_iff_eventuallyEq.mp hout)
+
+omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
+/-- A positive continuous density and a continuous coordinate divergence imply
+continuity of the intrinsic Laplacian of a chart-supported C² scalar. -/
+theorem laplacian_continuous_of_coordinate_divergence
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    (hf : tsupport f ⊆ (extChartAt I p).source)
+    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
+    (w D : E → ℝ) (hw : Continuous w) (hD : Continuous D)
+    (hwpos : ∀ z ∈ (extChartAt I p).target, 0 < w z)
+    (hcoord : ∀ z : (extChartAt I p).target,
+      w z * g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) = D z) :
+    Continuous (fun x ↦ g.laplacianAt f x) := by
+  have hformula (x : M) (hx : x ∈ (extChartAt I p).source) :
+      g.laplacianAt f x = D (extChartAt I p x) / w (extChartAt I p x) := by
+    let z : (extChartAt I p).target := ⟨extChartAt I p x, (extChartAt I p).map_source hx⟩
+    have hinv : inverseExtendedChartParametrization (n := n) p z = x :=
+      (extChartAt I p).left_inv hx
+    apply (eq_div_iff (hwpos z z.2).ne').mpr
+    simpa only [hinv, mul_comm] using hcoord z
+  apply continuous_iff_continuousAt.mpr
+  intro x
+  by_cases hx : x ∈ (extChartAt I p).source
+  · have hc := (continuousOn_extChartAt p x hx).continuousAt
+      ((isOpen_extChartAt_source p).mem_nhds hx)
+    have hquot := (hD.continuousAt.div hw.continuousAt
+      (hwpos _ ((extChartAt I p).map_source hx)).ne').comp hc
+    apply hquot.congr_of_eventuallyEq
+    filter_upwards [(isOpen_extChartAt_source p).mem_nhds hx] with y hy
+    exact hformula y hy
+  · have hxt : x ∉ tsupport f := fun h ↦ hx (hf h)
+    apply continuousAt_const.congr_of_eventuallyEq
+    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxt] with y hy
+    calc
+      g.laplacianAt f y = g.laplacianAt (fun _ : M ↦ (0 : ℝ)) y :=
+        g.laplacianAt_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
+          (g.mdifferentiableAt_gradient hreg.contMDiffAt)
+          (g.mdifferentiableAt_gradient contMDiffAt_const)
+      _ = 0 := g.laplacianAt_const 0 y
+
+/-- The coefficient identities supply continuity, so measurability need not
+be a separate input to the Stokes constructor. -/
+theorem localizedLaplacian_continuous_of_coefficients
+    (g : ClosedSmoothRiemannianMetric n M) (p : M) (f : M → ℝ)
+    (hf : tsupport f ⊆ (extChartAt I p).source)
+    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
+    (w : E → ℝ) (a : E → Fin n → Fin n → ℝ)
+    (Γ : E → Fin n → Fin n → Fin n → ℝ)
+    (hw : ContDiff ℝ 1 w) (ha : ∀ i j, ContDiff ℝ 1 (fun z ↦ a z i j))
+    (hweight : ∀ z : (extChartAt I p).target,
+      w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z)
+    (hcompat : ∀ z : (extChartAt I p).target, ∀ j : Fin n,
+      (∑ i : Fin n, fderiv ℝ (fun y ↦ w y * a y i j) z
+        (EuclideanSpace.single i (1 : ℝ))) =
+        w z * (-(∑ i : Fin n, ∑ k : Fin n, a z i k * Γ z j i k)))
+    (hcoord : ∀ z : (extChartAt I p).target,
+      g.laplacianAt f (inverseExtendedChartParametrization (n := n) p z) =
+        christoffelCoordinateLaplacian a Γ (coordinateScalar (n := n) p f) z) :
+    Continuous (fun x ↦ g.laplacianAt f x) := by
+  let u := coordinateScalar (n := n) p f
+  have hu : ContDiff ℝ 2 u := coordinateScalar_contDiff_two p f hf hreg
+  let F := coordinateMetricFluxComponent w a u
+  have hF (i : Fin n) : ContDiff ℝ 1 (F i) :=
+    coordinateMetricFluxComponent_contDiff_one hw ha hu i
+  apply laplacian_continuous_of_coordinate_divergence g p f hf hreg w
+    (euclideanCoordinateDivergence F) hw.continuous
+  · exact continuous_finsetSum _ fun i _ ↦
+      ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const
+  · intro z hz
+    rw [hweight ⟨z, hz⟩]
+    have hscale : 0 < (rawHausdorffLebesgueScale n : ℝ) := by
+      exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
+        (Measure.hausdorffMeasure (Module.finrank ℝ E : ℝ)) (volume : Measure E)
+    exact mul_pos hscale (inverseChartPullbackVolumeDensity_pos g p ⟨z, hz⟩)
+  · intro z
+    have hdiv := euclideanCoordinateDivergence_coordinateMetricFluxComponent_eq
+      (contractedChristoffel := fun y j ↦ -(∑ i : Fin n, ∑ k : Fin n, a y i k * Γ y j i k))
+      (hw.differentiable one_ne_zero z)
+      (fun i j ↦ (ha i j).differentiable one_ne_zero z)
+      (fun j ↦ (coordinateDirectionalDerivative_contDiff_one hu j).differentiable one_ne_zero z)
+      (hcompat z)
+    rw [contractedCoordinateLaplacian_eq_christoffelCoordinateLaplacian
+      a Γ (fun y j ↦ -(∑ i : Fin n, ∑ k : Fin n, a y i k * Γ y j i k)) u z
+      (fun _ ↦ rfl)] at hdiv
+    rw [hcoord z]
+    exact hdiv.symm
+
+/-- A partial producer with every residual coefficient obligation stated as
+an argument. Chart measures, partitioned scalar extensions and Laplacian
+measurability are constructed rather than supplied. -/
+def geometry_of_coordinate_coefficients
+    (g : ClosedSmoothRiemannianMetric n M) (f : M → ℝ)
+    (hreg : ContMDiff I 𝓘(ℝ) 2 f)
+    (C : FiniteExtendedChartCover (n := n) (M := M))
+    (ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ)
+    (hρ : ρ.IsSubordinate (fun i ↦ (extChartAt I (C.anchor i)).source))
+    (w : Fin C.chartCount → E → ℝ)
+    (a : Fin C.chartCount → E → Fin n → Fin n → ℝ)
+    (Γ : Fin C.chartCount → E → Fin n → Fin n → Fin n → ℝ)
+    (hw : ∀ i, ContDiff ℝ 1 (w i))
+    (ha : ∀ i j k, ContDiff ℝ 1 (fun z ↦ a i z j k))
+    (hweight : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      w i z = (rawHausdorffLebesgueScale n : ℝ) *
+        inverseChartPullbackVolumeDensity g (C.anchor i) z)
+    (hcompat : ∀ i (z : (extChartAt I (C.anchor i)).target) (j : Fin n),
+      (∑ k : Fin n, fderiv ℝ (fun y ↦ w i y * a i y k j) z
+        (EuclideanSpace.single k (1 : ℝ))) =
+        w i z * (-(∑ k : Fin n, ∑ l : Fin n, a i z k l * Γ i z j k l)))
+    (hcoord : ∀ i (z : (extChartAt I (C.anchor i)).target),
+      g.laplacianAt (fun x ↦ ρ i x * f x)
+        (inverseExtendedChartParametrization (n := n) (C.anchor i) z) =
+        christoffelCoordinateLaplacian (a i) (Γ i)
+          (coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)) z) :
+    FiniteSubordinateHausdorffLaplacianGeometry g f := by
+  have hsupport (i : Fin C.chartCount) :
+      tsupport (fun x ↦ ρ i x * f x) ⊆ (extChartAt I (C.anchor i)).source :=
+    tsupport_mul_subset_left.trans (hρ i)
+  have htwo : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
+    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
+      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
+    exact WithTop.coe_le_coe.mpr le_top
+  have hlocal (i : Fin C.chartCount) :
+      ContMDiff I 𝓘(ℝ) 2 (fun x ↦ ρ i x * f x) :=
+    ((ρ i).contMDiff.of_le htwo).mul hreg
+  exact {
+    chartCount := C.chartCount
+    coordinateDomain := fun i ↦ (extChartAt I (C.anchor i)).target
+    coordinateDomain_measurable := fun i ↦ (isOpen_extChartAt_target (C.anchor i)).measurableSet
+    inverseChart := fun i ↦ inverseExtendedChartParametrization (n := n) (C.anchor i)
+    inverseChart_measurable := fun i ↦
+      (inverseExtendedChartParametrization_isEmbedding (n := n) (C.anchor i)).continuous.measurable
+    chartRegion := fun i ↦ (extChartAt I (C.anchor i)).source
+    chartRegion_isOpen := fun i ↦ isOpen_extChartAt_source (C.anchor i)
+    density := fun i ↦ inverseChartPullbackVolumeDensity g (C.anchor i)
+    density_nonneg := fun i ↦ Eventually.of_forall fun z ↦
+      (inverseChartPullbackVolumeDensity_pos g (C.anchor i) z).le
+    density_integrable := fun i ↦ openChart_density_integrable g (C.anchor i)
+    chartMeasure := fun i ↦ openChart_measure g (C.anchor i)
+    partition := ρ
+    partition_subordinate := hρ
+    f_contMDiff_two := hreg
+    coordinateRepresentative := fun i ↦
+      coordinateScalar (n := n) (C.anchor i) (fun x ↦ ρ i x * f x)
+    coordinateRepresentative_eq := fun i z ↦ indicator_of_mem z.2 _
+    coordinateRepresentative_contDiff_two := fun i ↦
+      coordinateScalar_contDiff_two (C.anchor i) _ (hsupport i) (hlocal i)
+    coordinateRepresentative_hasCompactSupport := fun i ↦
+      (coordinateScalar_support (C.anchor i) _ (hsupport i)).1
+    coordinateRepresentative_tsupport_subset_coordinateDomain := fun i ↦
+      (coordinateScalar_support (C.anchor i) _ (hsupport i)).2
+    weight := w
+    weight_contDiff_one := hw
+    weight_eq_density := hweight
+    inverseMetric := a
+    inverseMetric_contDiff_one := ha
+    christoffel := Γ
+    contractedChristoffel := fun i z j ↦ -(∑ k : Fin n, ∑ l : Fin n, a i z k l * Γ i z j k l)
+    contractedChristoffel_eq := fun _ _ _ ↦ rfl
+    density_inverseMetric_compatibility := hcompat
+    intrinsicCoordinateLaplacian_eq := hcoord
+    localizedLaplacian_aestronglyMeasurable := fun i ↦
+      (localizedLaplacian_continuous_of_coefficients g (C.anchor i) _ (hsupport i) (hlocal i)
+        (w i) (a i) (Γ i) (hw i) (ha i) (hweight i) (hcompat i) (hcoord i)).aestronglyMeasurable }
+
+/-- Entrywise smoothness suffices for smoothness of a determinant on an open chart. -/
+theorem contDiffOn_matrix_det (G : E → Matrix (Fin n) (Fin n) ℝ) (U : Set E)
+    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
+    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
+  classical
+  simp only [Matrix.det_apply']
+  apply ContDiffOn.sum
+  intro σ _
+  apply ContDiffOn.mul contDiffOn_const
+  apply contDiffOn_prod
+  intro i _
+  exact hG (σ i) i
+
+/-- The genuine density weight is smooth on the chart target and agrees
+there with the Hausdorff density. No global extension is asserted. -/
+theorem chartWeight_regular (g : ClosedSmoothRiemannianMetric n M) (p : M) :
+    ContDiffOn ℝ ∞
+      (fun z ↦ (rawHausdorffLebesgueScale n : ℝ) *
+        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z))
+      (extChartAt I p).target ∧
+    (∀ z : (extChartAt I p).target,
+      (rawHausdorffLebesgueScale n : ℝ) *
+        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z) =
+        (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
+  have hdet := contDiffOn_matrix_det (inverseChartPullbackGramMatrixField g p)
+    (extChartAt I p).target (contDiffOn_inverseChartPullbackGramMatrixField_entry g p)
+  have hpos (z : E) (hz : z ∈ (extChartAt I p).target) :
+      0 < (inverseChartPullbackGramMatrixField g p z).det := by
+    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
+    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos
+  constructor
+  · apply ContDiffOn.mul contDiffOn_const
+    apply (hdet.sqrt (fun z hz ↦ (hpos z hz).ne')).congr
+    intro z hz
+    simp only [VolumeDensity.chartVolumeDensity, VolumeDensity.chartGramDet,
+      abs_of_pos (hpos z hz)]
+  · intro z
+    rw [← inverseChartPullbackGramMatrix_eq_field g p z]
+    rfl
+
+/-- The genuine inverse-metric entries are smooth on the chart target. -/
+theorem chartInverseMetric_contDiffOn (g : ClosedSmoothRiemannianMetric n M) (p : M)
+    (i j : Fin n) :
+    ContDiffOn ℝ ∞ (fun z ↦ (inverseChartPullbackGramMatrixField g p z)⁻¹ i j)
+      (extChartAt I p).target := by
+  classical
+  have hG := contDiffOn_inverseChartPullbackGramMatrixField_entry g p
+  have hdet := contDiffOn_matrix_det (inverseChartPullbackGramMatrixField g p)
+    (extChartAt I p).target hG
+  have hne (z : E) (hz : z ∈ (extChartAt I p).target) :
+      (inverseChartPullbackGramMatrixField g p z).det ≠ 0 := by
+    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
+    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
+  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
+    Matrix.adjugate_apply]
+  apply (hdet.inv hne).mul
+  apply contDiffOn_matrix_det
+  intro k l
+  by_cases hk : k = j
+  · simpa only [Matrix.updateRow_apply, hk, ite_true] using
+      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ) l)
+        (extChartAt I p).target)
+  · simpa only [Matrix.updateRow_apply, hk, ite_false] using hG k l
+
+end Poincare.ClosedLaplacianStokesProducer
```
