import Poincare.Global.CartanScaleGeneric

/-!
# Hosted speed package

This module isolates the non-unit-speed fact available for the hosted
geodesic curves used in the Cartan cascade: on any closed interval strictly
inside the exported PL interval, the transported chart-metric speed of the
actual hosted base curve is constant and equal to its anchor speed value.

The statements deliberately expose the speed value, not a unit-speed
normalization.  Downstream consumers that need frequency-one Jacobi pinning
must either choose genuinely unit anchor data or use a speed-parameterized
oscillator package.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SpeedPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- The source anchor chart metric is nonnegative on diagonal entries. -/
theorem sourceAnchorChartMetric_self_nonneg
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (v : E) :
    0 ≤ CartanMap.sourceAnchorChartMetric g x₀ v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (CartanMap.sourceAnchorChartMetric_pos (g := g) (x₀ := x₀) hv)

/-- The target anchor chart metric is nonnegative on diagonal entries. -/
theorem targetAnchorChartMetric_self_nonneg (p₀ : RoundSphere3) (v : E) :
    0 ≤ CartanMap.targetAnchorChartMetric p₀ v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (CartanMap.targetAnchorChartMetric_pos (p₀ := p₀) hv)

/-- The hosted source speed squared is the source anchor speed value. -/
theorem hostedSourceSpeed_sq
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (δ : ℝ) (v : E) :
    CartanScaleGeneric.hostedSourceSpeed g x₀ δ v ^ 2 =
      CartanMap.sourceAnchorChartMetric g x₀
        (CartanHomogeneity.workingVelocity δ v)
        (CartanHomogeneity.workingVelocity δ v) := by
  rw [CartanScaleGeneric.hostedSourceSpeed]
  exact Real.sq_sqrt
    (sourceAnchorChartMetric_self_nonneg g x₀
      (CartanHomogeneity.workingVelocity δ v))

/-- The hosted target speed squared is the aligned target anchor speed value. -/
theorem hostedTargetSpeed_sq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    CartanScaleGeneric.hostedTargetSpeed L δ v ^ 2 =
      CartanMap.targetAnchorChartMetric p₀
        (L (CartanHomogeneity.workingVelocity δ v))
        (L (CartanHomogeneity.workingVelocity δ v)) := by
  rw [CartanScaleGeneric.hostedTargetSpeed]
  exact Real.sq_sqrt
    (targetAnchorChartMetric_self_nonneg p₀
      (L (CartanHomogeneity.workingVelocity δ v)))

/-- The aligned hosted target speed squared equals the hosted source speed squared. -/
theorem hostedTargetSpeed_sq_eq_hostedSourceSpeed_sq
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E) :
    CartanScaleGeneric.hostedTargetSpeed L δ v ^ 2 =
      CartanScaleGeneric.hostedSourceSpeed g x₀ δ v ^ 2 := by
  rw [hostedTargetSpeed_sq, hostedSourceSpeed_sq]
  exact CartanMap.TangentAlignment.map_app L
    (CartanHomogeneity.workingVelocity δ v)
    (CartanHomogeneity.workingVelocity δ v)

/--
On any closed interval strictly inside the exported PL interval, the genuine
transported chart-metric speed of the hosted source curve is its anchor speed
value.
-/
theorem chartMetric_speed_eq_anchor_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v₀ : E}
    (hα0 : α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) x₀ (α (extChartAt I x₀ x₀, v₀) t).1 = 1)
    {a b t : ℝ} (ha : -ε < a) (hb : b < ε) (ht : t ∈ Icc a b) :
    CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I x₀ x₀, v₀) t).1
        (α (extChartAt I x₀ x₀, v₀) t).2
        (α (extChartAt I x₀ x₀, v₀) t).2 =
      CartanMap.sourceAnchorChartMetric g x₀ v₀ v₀ := by
  have htIoo : t ∈ Ioo (-ε) ε :=
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have htIcc : t ∈ Icc (-ε) ε := Ioo_subset_Icc_self htIoo
  have hspeed :=
    plFlow_chartGeodesicMetric_speed_eq_initial_of_mem_Ioo
      (g := g) (x₀ := x₀) (ε := ε) (α := α) (v₀ := v₀)
      hε hα0 hαder htIoo
  have htMetric :
      chartGeodesicMetric g x₀ (α (extChartAt I x₀ x₀, v₀) t).1 =
        CovariantDerivative.chartMetric g.inner x₀
          (α (extChartAt I x₀ x₀, v₀) t).1 := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) (hαcut t htIcc))
  have hanchorCut : cutoff (n := 3) x₀ (extChartAt I x₀ x₀) = 1 :=
    (cutoff_eventuallyEq_one (n := 3) x₀).self_of_nhds
  have hanchorMetric :
      chartGeodesicMetric g x₀ (extChartAt I x₀ x₀) =
        CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x₀) := by
    simpa [chartGeodesicMetric] using
      (blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
        (g := g) (x₀ := x₀) hanchorCut)
  have hspeed' := hspeed
  rw [htMetric, hanchorMetric] at hspeed'
  simpa [CartanMap.sourceAnchorChartMetric] using hspeed'

/-- Target-metric version of `chartMetric_speed_eq_anchor_on_shrunk_Icc`. -/
theorem target_chartMetric_speed_eq_anchor_on_shrunk_Icc
    (p₀ : RoundSphere3)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v₀ : E}
    (hα0 : α (extChartAt I p₀ p₀, v₀) 0 = (extChartAt I p₀ p₀, v₀))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I p₀ p₀, v₀))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I p₀ p₀, v₀) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) p₀ (α (extChartAt I p₀ p₀, v₀) t).1 = 1)
    {a b t : ℝ} (ha : -ε < a) (hb : b < ε) (ht : t ∈ Icc a b) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I p₀ p₀, v₀) t).1
        (α (extChartAt I p₀ p₀, v₀) t).2
        (α (extChartAt I p₀ p₀, v₀) t).2 =
      CartanMap.targetAnchorChartMetric p₀ v₀ v₀ := by
  have h :=
    chartMetric_speed_eq_anchor_on_shrunk_Icc
      (g := roundSphereMetric3) (x₀ := p₀)
      (ε := ε) hε (α := α) (v₀ := v₀)
      hα0 hαder hαcut ha hb ht
  simpa [CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric] using h

/--
Actual source hosted-curve specialization for the cascade shape
`αs (extChartAt I x₀ x₀, T⁻¹ • v)`.
-/
theorem hosted_source_curve_speedValue_eq_anchor_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v : E}
    (hα0 :
      α (extChartAt I x₀ x₀, T⁻¹ • v) 0 =
        (extChartAt I x₀ x₀, T⁻¹ • v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, T⁻¹ • v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, T⁻¹ • v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) x₀ (α (extChartAt I x₀ x₀, T⁻¹ • v) t).1 = 1)
    {a b t : ℝ} (ha : -ε < a) (hb : b < ε) (ht : t ∈ Icc a b) :
    CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I x₀ x₀, T⁻¹ • v) t).1
        (α (extChartAt I x₀ x₀, T⁻¹ • v) t).2
        (α (extChartAt I x₀ x₀, T⁻¹ • v) t).2 =
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) :=
  chartMetric_speed_eq_anchor_on_shrunk_Icc
    (g := g) (x₀ := x₀) (ε := ε) hε
    (α := α) (v₀ := T⁻¹ • v) hα0 hαder hαcut ha hb ht

/--
Actual target hosted-curve specialization for the cascade shape
`αt (extChartAt I p₀ p₀, T⁻¹ • v)`.
-/
theorem hosted_target_curve_speedValue_eq_anchor_on_shrunk_Icc
    (p₀ : RoundSphere3)
    {T ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v : E}
    (hα0 :
      α (extChartAt I p₀ p₀, T⁻¹ • v) 0 =
        (extChartAt I p₀ p₀, T⁻¹ • v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I p₀ p₀, T⁻¹ • v))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I p₀ p₀, T⁻¹ • v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) p₀ (α (extChartAt I p₀ p₀, T⁻¹ • v) t).1 = 1)
    {a b t : ℝ} (ha : -ε < a) (hb : b < ε) (ht : t ∈ Icc a b) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I p₀ p₀, T⁻¹ • v) t).1
        (α (extChartAt I p₀ p₀, T⁻¹ • v) t).2
        (α (extChartAt I p₀ p₀, T⁻¹ • v) t).2 =
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • v) :=
  target_chartMetric_speed_eq_anchor_on_shrunk_Icc
    (p₀ := p₀) (ε := ε) hε
    (α := α) (v₀ := T⁻¹ • v) hα0 hαder hαcut ha hb ht

/--
Aligned target hosted-curve speed value, rewritten through the tangent
alignment to the source anchor metric.
-/
theorem hosted_aligned_target_curve_speedValue_eq_source_anchor_on_shrunk_Icc
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {T ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E} {v : E}
    (hα0 :
      α (extChartAt I p₀ p₀, T⁻¹ • L v) 0 =
        (extChartAt I p₀ p₀, T⁻¹ • L v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I p₀ p₀, T⁻¹ • L v))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I p₀ p₀, T⁻¹ • L v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) p₀ (α (extChartAt I p₀ p₀, T⁻¹ • L v) t).1 = 1)
    {a b t : ℝ} (ha : -ε < a) (hb : b < ε) (ht : t ∈ Icc a b) :
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (α (extChartAt I p₀ p₀, T⁻¹ • L v) t).1
        (α (extChartAt I p₀ p₀, T⁻¹ • L v) t).2
        (α (extChartAt I p₀ p₀, T⁻¹ • L v) t).2 =
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) := by
  have htarget :=
    hosted_target_curve_speedValue_eq_anchor_on_shrunk_Icc
      (p₀ := p₀) (T := T) (ε := ε) hε
      (α := α) (v := L v) hα0 hαder hαcut ha hb ht
  have halign :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • L v) (T⁻¹ • L v) =
        CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) := by
    simpa using CartanMap.TangentAlignment.map_app L (T⁻¹ • v) (T⁻¹ • v)
  exact htarget.trans halign

end SpeedPackage
end Poincare
