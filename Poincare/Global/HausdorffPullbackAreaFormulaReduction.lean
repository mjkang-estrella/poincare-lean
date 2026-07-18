import Poincare.Global.HausdorffCoordinateDensityVariation
import Poincare.Global.CoordinateChartFrameDensityVariation

/-!
# Pullback reduction for the missing Riemannian area formula

`HausdorffChartDensityEquality` compares a coordinate-density measure with
the Hausdorff measure of the Riemannian path metric on the manifold.  The
map-theoretic part of that comparison is already in Mathlib: after pulling
the target metric back along an embedding, the parametrization is an
isometry, and isometries push Hausdorff measure to its restriction to their
range.

This file isolates the remaining statement on the coordinate domain.  It
also records the actual inverse-chart Gram matrix: its frame is obtained by
applying the derivative of the inverse chart to the standard orthonormal
basis of the Euclidean model.  This is deliberately distinct from the
pointwise `Module.finBasis` Gram density used elsewhere for basis-invariant
time-variation calculations.  Identifying those two densities is exposed as
a separate proposition; no such identification is assumed for an arbitrary
chart.

The missing analytic theorem is therefore precise: the Hausdorff measure for
the pulled-back variable Riemannian metric must equal the fixed raw-Hausdorff
normalization times `sqrt |det G|` relative to Euclidean Lebesgue measure.
Mathlib's finite-dimensional Jacobian theorem has an additive Haar target and
does not prove this variable path-metric statement.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Set Filter Metric
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
The exact source-side area formula left after pulling the Riemannian metric
back along a coordinate embedding.

The metric-space instance on `U` has the same topology as the original
subtype topology because `comapMetricSpace` uses `IsEmbedding`.  Thus the
existing Borel measurable space and the coordinate Lebesgue measure remain
the intended ones, while `μH[n]` is computed using the pulled-back metric.
-/
def PullbackMetricHausdorffDensityFormula
    (g : ClosedSmoothRiemannianMetric n M)
    (U : Set E) (ψ : U → M) (hψ : Topology.IsEmbedding ψ)
    (δ : U → ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U :=
    pullbackEMetric.toPseudoEMetricSpace
  (μH[(n : ℝ)] : Measure U) =
    rawHausdorffCoordinateDensityMeasure U δ

/--
Mathlib's isometry pushforward theorem transports the source-side area
formula to the local chart equality.  No differentiability or Jacobian
theorem is used in this step.
-/
theorem hausdorffChartDensityEquality_range_of_pullbackMetricFormula
    (g : ClosedSmoothRiemannianMetric n M)
    (U : Set E) (ψ : U → M) (hψ : Topology.IsEmbedding ψ)
    (δ : U → ℝ)
    (harea : PullbackMetricHausdorffDensityFormula g U ψ hψ δ) :
    HausdorffChartDensityEquality g U ψ (Set.range ψ) δ := by
  letI : MetricSpace M := g.toMetricSpace
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U :=
    pullbackEMetric.toPseudoEMetricSpace
  have hsource :
      (μH[(n : ℝ)] : Measure U) =
        rawHausdorffCoordinateDensityMeasure U δ := by
    simpa [PullbackMetricHausdorffDensityFormula] using harea
  have hψiso : Isometry ψ := by
    intro x y
    rfl
  rw [HausdorffChartDensityEquality, ← hsource]
  simpa [volumeMeasure] using
    hψiso.map_hausdorffMeasure (Or.inl (by positivity : (0 : ℝ) ≤ n))

/-- The same bridge for a named chart image rather than the literal range. -/
theorem hausdorffChartDensityEquality_of_pullbackMetricFormula
    (g : ClosedSmoothRiemannianMetric n M)
    (U : Set E) (ψ : U → M) (hψ : Topology.IsEmbedding ψ)
    (V : Set M) (δ : U → ℝ) (hV : V = Set.range ψ)
    (harea : PullbackMetricHausdorffDensityFormula g U ψ hψ δ) :
    HausdorffChartDensityEquality g U ψ V δ := by
  rw [hV]
  exact hausdorffChartDensityEquality_range_of_pullbackMetricFormula
    g U ψ hψ δ harea

/-- The partial equivalence of an extended chart is a genuine homeomorphism
between the subtypes of its target and source. -/
def inverseExtendedChartHomeomorph (x₀ : M) :
    (extChartAt I x₀).target ≃ₜ (extChartAt I x₀).source where
  toEquiv := (extChartAt I x₀).toEquiv.symm
  continuous_toFun :=
    (continuousOn_extChartAt_symm x₀).mapsToRestrict
      (fun _z hz ↦ (extChartAt I x₀).map_target hz)
  continuous_invFun :=
    (continuousOn_extChartAt x₀).mapsToRestrict
      (fun _x hx ↦ (extChartAt I x₀).map_source hx)

/-- The inverse extended chart, restricted to its genuine target. -/
def inverseExtendedChartParametrization (x₀ : M) :
    (extChartAt I x₀).target → M :=
  fun z ↦ inverseExtendedChartHomeomorph (n := n) (M := M) x₀ z

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
    [BorelSpace M] [IsManifold I ∞ M] in
/-- Restricting the inverse extended chart to its target is automatically a
topological embedding; this is not part of the missing area theorem. -/
theorem inverseExtendedChartParametrization_isEmbedding (x₀ : M) :
    Topology.IsEmbedding
      (inverseExtendedChartParametrization (n := n) (M := M) x₀) := by
  exact Topology.IsEmbedding.subtypeVal.comp
    (inverseExtendedChartHomeomorph (n := n) (M := M) x₀).isEmbedding

/--
The pullback Gram matrix of `g` in the standard Euclidean coordinate frame
of the inverse extended chart.

Using `EuclideanSpace.basisFun` here is essential: the density is relative to
the fixed Euclidean Lebesgue measure used by
`rawHausdorffCoordinateDensityMeasure`, not to an arbitrary chosen basis of a
tangent fiber.
-/
noncomputable def inverseChartPullbackGramMatrix
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) : Matrix (Fin n) (Fin n) ℝ :=
  ClosedSmoothRiemannianMetric.metricMatrixInBasisAt g
    (inverseExtendedChartParametrization (n := n) (M := M) x₀ z)
    (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
      (n := n) (M := M) x₀ z.2)

/-- The honest `sqrt |det G|` density of the inverse chart. -/
noncomputable def inverseChartPullbackVolumeDensity
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) : ℝ :=
  VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrix g x₀ z)

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
    [BorelSpace M] in
/-- The static pullback density agrees definitionally with the time-dependent
inverse-chart density at a constant metric path. -/
theorem inverseChartPullbackVolumeDensity_eq_inverseChartVolumeDensityAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    inverseChartPullbackVolumeDensity g x₀ z =
      ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt
        (fun _t : ℝ ↦ g) x₀ z.2 0 := by
  rfl

omit [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
    [BorelSpace M] in
/-- At one time of a metric path, the static pullback density is exactly the
time-dependent inverse-chart density from the chart-frame variation module. -/
theorem inverseChartPullbackVolumeDensity_eq_inverseChartVolumeDensityAt_path
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x₀ : M)
    (z : (extChartAt I x₀).target) :
    inverseChartPullbackVolumeDensity (gt t) x₀ z =
      ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt gt x₀ z.2 t := by
  rfl

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The explicit pullback-coordinate density has the intrinsic first
variation furnished by the inverse-chart frame calculation. -/
theorem hasDerivAt_inverseChartPullbackVolumeDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x₀ : M}
    (z : (extChartAt I x₀).target)
    (hgt : TimeDifferentiableAt gt t₀
      (inverseExtendedChartParametrization (n := n) (M := M) x₀ z)) :
    HasDerivAt (fun t ↦ inverseChartPullbackVolumeDensity (gt t) x₀ z)
      ((1 / 2 : ℝ) * inverseChartPullbackVolumeDensity (gt t₀) x₀ z *
        traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀)
          (inverseExtendedChartParametrization (n := n) (M := M) x₀ z)) t₀ := by
  have hfun :
      (fun t ↦ inverseChartPullbackVolumeDensity (gt t) x₀ z) =
        ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt
          gt x₀ z.2 := by
    funext t
    exact
      inverseChartPullbackVolumeDensity_eq_inverseChartVolumeDensityAt_path
        gt t x₀ z
  rw [hfun]
  rw [inverseChartPullbackVolumeDensity_eq_inverseChartVolumeDensityAt_path]
  exact
    ClosedSmoothRiemannianMetric.hasDerivAt_inverseChartVolumeDensityAt
      z.2 hgt

/--
The precise variable-metric Hausdorff area formula still absent from
Mathlib, specialized to one genuine inverse chart.
-/
def InverseChartPullbackHausdorffAreaFormula
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : Prop :=
  PullbackMetricHausdorffDensityFormula g (extChartAt I x₀).target
    (inverseExtendedChartParametrization (n := n) (M := M) x₀)
    (inverseExtendedChartParametrization_isEmbedding (n := n) (M := M) x₀)
    (inverseChartPullbackVolumeDensity g x₀)

/--
Once the missing source-side area formula is supplied, the actual inverse
chart density gives the required local Hausdorff equality automatically.
-/
theorem inverseChart_hausdorffChartDensityEquality_of_areaFormula
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (harea : InverseChartPullbackHausdorffAreaFormula g x₀) :
    HausdorffChartDensityEquality g (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀))
      (inverseChartPullbackVolumeDensity g x₀) := by
  exact hausdorffChartDensityEquality_range_of_pullbackMetricFormula
    g (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (inverseExtendedChartParametrization_isEmbedding (n := n) (M := M) x₀)
      (inverseChartPullbackVolumeDensity g x₀) harea

/-- The source-side area formula feeds the correct time-dependent
inverse-chart density directly, without passing through a selected tangent
fiber basis. -/
theorem inverseChart_hausdorffChartDensityEquality_chartFrame
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x₀ : M)
    (harea : InverseChartPullbackHausdorffAreaFormula (gt t) x₀) :
    HausdorffChartDensityEquality (gt t) (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀))
      (fun z ↦ ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt
        gt x₀ z.2 t) := by
  have hlocal := inverseChart_hausdorffChartDensityEquality_of_areaFormula
    (g := gt t) (x₀ := x₀) harea
  have hdensity :
      (fun z : (extChartAt I x₀).target ↦
          ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt
            gt x₀ z.2 t) =
        inverseChartPullbackVolumeDensity (gt t) x₀ := by
    funext z
    exact
      (inverseChartPullbackVolumeDensity_eq_inverseChartVolumeDensityAt_path
        gt t x₀ z).symm
  simpa only [hdensity] using hlocal

/--
The separate frame-identification obligation needed to replace the honest
inverse-chart density by the repository's pointwise canonical-fiber density.

This proposition is not automatic: its right side uses `Module.finBasis` in
each tangent fiber, whereas its left side uses derivatives of the inverse
chart applied to the standard Euclidean basis.
-/
def InverseChartCanonicalFrameDensityIdentification
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x₀ : M) :
    Prop :=
  ∀ z : (extChartAt I x₀).target,
    inverseChartPullbackVolumeDensity (gt t) x₀ z =
      ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt gt
        (inverseExtendedChartParametrization (n := n) (M := M) x₀ z) t

/--
The area formula and the independent frame identification together recover
the density shape expected by `UsesCoordinateGramDensity`.  Keeping the two
hypotheses separate prevents an arbitrary chart frame from being silently
identified with `Module.finBasis`.
-/
theorem inverseChart_hausdorffChartDensityEquality_coordinateGram
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x₀ : M)
    (harea : InverseChartPullbackHausdorffAreaFormula (gt t) x₀)
    (hframe : InverseChartCanonicalFrameDensityIdentification gt t x₀) :
    HausdorffChartDensityEquality (gt t) (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀))
      (fun z ↦ ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt gt
        (inverseExtendedChartParametrization (n := n) (M := M) x₀ z) t) := by
  have hlocal := inverseChart_hausdorffChartDensityEquality_of_areaFormula
    (g := gt t) (x₀ := x₀) harea
  have hdensity :
      (fun z : (extChartAt I x₀).target ↦
          ClosedSmoothRiemannianMetric.coordinateGramVolumeDensityAt gt
            (inverseExtendedChartParametrization (n := n) (M := M) x₀ z) t) =
        inverseChartPullbackVolumeDensity (gt t) x₀ := by
    funext z
    exact (hframe z).symm
  simpa only [hdensity] using hlocal

end Poincare
