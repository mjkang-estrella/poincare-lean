import Poincare.Global.SpeedGeneric

/-!
# The local isometry instantiation boundary

This module records the non-vacuous pieces of the hosted-data instantiation
that are available after the speed-generic layer.  The final local-isometry
wrapper is intentionally not stated here: the remaining Picard-Lindelöf norm
package hypotheses needed by the endpoint-pairing feeds are not exported by
the current cascade data.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace TheLocalIsometry

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- The hosted working time is positive for nonzero endpoint vectors. -/
theorem workingTime_pos_of_ne_zero
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    0 < CartanHomogeneity.workingTime δ v := by
  dsimp [CartanHomogeneity.workingTime]
  exact div_pos (norm_pos_iff.mpr hv) (by linarith)

/-- The hosted working time is nonzero for nonzero endpoint vectors. -/
theorem workingTime_ne_zero_of_ne_zero
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    CartanHomogeneity.workingTime δ v ≠ 0 :=
  ne_of_gt (workingTime_pos_of_ne_zero hδ hv)

/-- The hosted working velocity is nonzero for nonzero endpoint vectors. -/
theorem workingVelocity_ne_zero_of_ne_zero
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    CartanHomogeneity.workingVelocity δ v ≠ 0 := by
  intro hzero
  have hhost :=
    CartanHomogeneity.workingTime_smul_workingVelocity δ hδ v
  rw [hzero] at hhost
  have hvzero : v = 0 := by
    simpa using hhost.symm
  exact hv hvzero

/--
The inverse hosted time recovers the working velocity.  This is the algebraic
identification between the final endpoint vector `v` and the hosted initial
velocity consumed by the speed package.
-/
theorem inv_workingTime_smul_eq_workingVelocity
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    (CartanHomogeneity.workingTime δ v)⁻¹ • v =
      CartanHomogeneity.workingVelocity δ v := by
  have hTne : CartanHomogeneity.workingTime δ v ≠ 0 :=
    workingTime_ne_zero_of_ne_zero hδ hv
  calc
    (CartanHomogeneity.workingTime δ v)⁻¹ • v =
        (CartanHomogeneity.workingTime δ v)⁻¹ •
          (CartanHomogeneity.workingTime δ v •
            CartanHomogeneity.workingVelocity δ v) := by
          rw [CartanHomogeneity.workingTime_smul_workingVelocity δ hδ v]
    _ = CartanHomogeneity.workingVelocity δ v := by
          simp [smul_smul, hTne]

/-- The source hosted speed is positive for nonzero endpoint vectors. -/
theorem hostedSourceSpeed_pos_of_ne_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    0 < CartanScaleGeneric.hostedSourceSpeed g x₀ δ v := by
  rw [CartanScaleGeneric.hostedSourceSpeed]
  exact Real.sqrt_pos_of_pos
    (CartanMap.sourceAnchorChartMetric_pos g x₀
      (workingVelocity_ne_zero_of_ne_zero hδ hv))

/-- The source hosted speed is nonzero for nonzero endpoint vectors. -/
theorem hostedSourceSpeed_ne_zero_of_ne_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    CartanScaleGeneric.hostedSourceSpeed g x₀ δ v ≠ 0 :=
  ne_of_gt (hostedSourceSpeed_pos_of_ne_zero g x₀ hδ hv)

/-- The target hosted speed is positive for nonzero endpoint vectors. -/
theorem hostedTargetSpeed_pos_of_ne_zero
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    0 < CartanScaleGeneric.hostedTargetSpeed L δ v := by
  rw [CartanScaleGeneric.hostedTargetSpeed]
  have hu : CartanHomogeneity.workingVelocity δ v ≠ 0 :=
    workingVelocity_ne_zero_of_ne_zero hδ hv
  have hLu : L (CartanHomogeneity.workingVelocity δ v) ≠ 0 := by
    intro hzero
    have hlin :
        L.toContinuousLinearEquiv (CartanHomogeneity.workingVelocity δ v) = 0 := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using hzero
    have hlin0 :
        L.toContinuousLinearEquiv (CartanHomogeneity.workingVelocity δ v) =
          L.toContinuousLinearEquiv 0 := by
      simpa using hlin
    exact hu (L.toContinuousLinearEquiv.injective hlin0)
  exact Real.sqrt_pos_of_pos
    (CartanMap.targetAnchorChartMetric_pos p₀ hLu)

/-- The target hosted speed is nonzero for nonzero endpoint vectors. -/
theorem hostedTargetSpeed_ne_zero_of_ne_zero
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {δ : ℝ} (hδ : 0 < δ) {v : E} (hv : v ≠ 0) :
    CartanScaleGeneric.hostedTargetSpeed L δ v ≠ 0 :=
  ne_of_gt (hostedTargetSpeed_pos_of_ne_zero L hδ hv)

/--
The actual hosted source base curve has the speed hypothesis required by the
speed-generic Jacobi package, once the usual cutoff-one PL data are available
on a strictly smaller interval.
-/
theorem source_speed_hypothesis_of_hosted_workingVelocity_on_shrunk_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (δ : ℝ) (v : E)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E}
    (hα0 :
      α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) 0 =
        (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) x₀
        (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).1 = 1)
    {a b : ℝ} (ha : -ε < a) (hb : b < ε) :
    ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric g.inner x₀
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).1
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).2
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).2 =
        CartanScaleGeneric.hostedSourceSpeed g x₀ δ v ^ 2 := by
  have hspeedValue : ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric g.inner x₀
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).1
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).2
          (α (extChartAt I x₀ x₀, CartanHomogeneity.workingVelocity δ v) t).2 =
        CartanMap.sourceAnchorChartMetric g x₀
          (CartanHomogeneity.workingVelocity δ v)
          (CartanHomogeneity.workingVelocity δ v) := by
    intro t ht
    exact
      SpeedPackage.chartMetric_speed_eq_anchor_on_shrunk_Icc
        (g := g) (x₀ := x₀) (ε := ε) hε
        (α := α) (v₀ := CartanHomogeneity.workingVelocity δ v)
        hα0 hαder hαcut ha hb ht
  exact
    SpeedGeneric.source_speed_hypothesis_of_hostedSourceSpeed_sq
      (g := g) (x₀ := x₀) δ v hspeedValue

/--
The actual aligned target hosted base curve has the speed hypothesis required
by the speed-generic target package.
-/
theorem target_speed_hypothesis_of_hosted_workingVelocity_on_shrunk_Icc
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) (δ : ℝ) (v : E)
    {ε : ℝ} (hε : 0 < ε) {α : E × E → ℝ → E × E}
    (hα0 :
      α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) 0 =
        (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)))
    (hαder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)))
        (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t))
        (Icc (-ε) ε) t)
    (hαcut : ∀ t ∈ Icc (-ε) ε,
      cutoff (n := 3) p₀
        (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).1 = 1)
    {a b : ℝ} (ha : -ε < a) (hb : b < ε) :
    ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).1
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).2
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).2 =
        CartanScaleGeneric.hostedTargetSpeed L δ v ^ 2 := by
  have hspeedValue : ∀ t ∈ Icc a b,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).1
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).2
          (α (extChartAt I p₀ p₀, L (CartanHomogeneity.workingVelocity δ v)) t).2 =
        CartanMap.targetAnchorChartMetric p₀
          (L (CartanHomogeneity.workingVelocity δ v))
          (L (CartanHomogeneity.workingVelocity δ v)) := by
    intro t ht
    exact
      SpeedPackage.target_chartMetric_speed_eq_anchor_on_shrunk_Icc
        (p₀ := p₀) (ε := ε) hε
        (α := α) (v₀ := L (CartanHomogeneity.workingVelocity δ v))
        hα0 hαder hαcut ha hb ht
  exact
    SpeedGeneric.target_speed_hypothesis_of_hostedTargetSpeed_sq
      (L := L) δ v hspeedValue

end TheLocalIsometry
end Poincare
