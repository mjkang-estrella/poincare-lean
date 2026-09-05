import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Poincare.Global.MetricEntryThirdJetFormalRicci

/-!
# Invertibility of positive formal profile metrics

A uniform positive lower bound on the genuine cutoff-blended metrics is a
closed condition in the scalar profile topology.  It therefore persists on
the full compact profile closure.  Finite-dimensional duality then turns the
resulting strict positivity into invertibility of every reconstructed formal
metric.

This discharges the formal-invertibility premise of the compact-profile Ricci
bound from a concrete lower metric comparison; smooth realization of profile
limits remains unnecessary.
-/

noncomputable section

open Bundle Function Set Topology
open scoped Manifold ContDiff Topology

universe u v

namespace Poincare

/-- A strictly positive real bilinear operator on a finite-dimensional inner
product space is a continuous linear equivalence with its continuous dual. -/
theorem continuousLinearMap_isInvertible_of_strictlyPositive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hpos : ∀ w : V, w ≠ 0 → 0 < B w w) :
    B.IsInvertible := by
  have hInjective : Function.Injective B := by
    intro u w huw
    have hzero : B (u - w) = 0 := by
      rw [map_sub, huw, sub_self]
    have hsub : u - w = 0 := by
      by_contra hne
      have hpositive := hpos (u - w) hne
      have heval : B (u - w) (u - w) = 0 := by
        rw [hzero]
        rfl
      linarith
    exact sub_eq_zero.mp hsub
  have hdim : Module.finrank ℝ V =
      Module.finrank ℝ (V →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ V).toLinearEquiv.finrank_eq
  have hSurjective : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      hInjective
  let eLinear : V ≃ₗ[ℝ] (V →L[ℝ] ℝ) :=
    LinearEquiv.ofBijective B.toLinearMap ⟨hInjective, hSurjective⟩
  let eContinuous : V ≃L[ℝ] (V →L[ℝ] ℝ) :=
    eLinear.toContinuousLinearEquiv
  exact ⟨eContinuous, by
    ext w
    rfl⟩

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "G" => ClosedSmoothRiemannianMetric n M
local notation "P" => MetricEntryThirdJetProfileTarget n M

/-- One fixed anchor and coordinate set have a uniform positive Euclidean
lower comparison along a metric family. -/
def UniformAnchorBlendedMetricLowerComparison
    {J : Type v} (gt : J → G) (x : M) (Q : Set E) (c : ℝ) : Prop :=
  0 < c ∧ ∀ t : J, ∀ z ∈ Q, ∀ w : E,
    c * ‖w‖ ^ 2 ≤ anchorBlendedMetricFamily gt x t z w w

/-- Every genuine cutoff-blended chart metric is strictly positive. -/
theorem anchorBlendedMetricFamily_pos
    {J : Type v} (gt : J → G) (x : M) (t : J) (z : E)
    {w : E} (hw : w ≠ 0) :
    0 < anchorBlendedMetricFamily gt x t z w w := by
  exact CovariantDerivative.blendedChartMetric_posDef
    (GeodesicTransport.cutoff (n := n) x)
    (GeodesicTransport.backgroundMetric (n := n))
    (GeodesicTransport.backgroundMetric_pos (n := n))
    (gt t).inner
    (fun y a ha => (gt t).inner_pos y (v := a) ha) x
    (GeodesicTransport.cutoff_nonneg (n := n) x z)
    (GeodesicTransport.cutoff_le_one (n := n) x z)
    (GeodesicTransport.cutoff_support_invertible (n := n) x z) hw

/-- A uniform fixed-chart lower comparison passes to every formal profile in
the family closure. -/
theorem formalProfileMetricAt_lower_of_mem_closure
    {J : Type v} (gt : J → G) (x : M) {Q : Set E} (c : ℝ)
    (hLower : UniformAnchorBlendedMetricLowerComparison gt x Q c)
    {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    {z : E} (hz : z ∈ Q) (w : E) :
    c * ‖w‖ ^ 2 ≤ formalProfileMetricAt p x z w w := by
  have hFormal : Continuous (fun q : P => formalProfileMetricAt q x z) :=
    (continuous_formalProfileMetricAt x).comp
      (continuous_id.prodMk continuous_const)
  have hValue : Continuous (fun q : P => formalProfileMetricAt q x z w w) :=
    (hFormal.clm_apply continuous_const).clm_apply continuous_const
  have hClosed : IsClosed
      {q : P | c * ‖w‖ ^ 2 ≤ formalProfileMetricAt q x z w w} :=
    isClosed_Ici.preimage hValue
  apply (closure_minimal ?_ hClosed) hp
  rintro q ⟨t, rfl⟩
  simpa using hLower.2 t z hz w

/-- The positive lower comparison makes every reconstructed formal metric on
the profile closure and coordinate set invertible. -/
theorem formalProfileMetricAt_isInvertible_of_mem_closure
    {J : Type v} (gt : J → G) (x : M) {Q : Set E} (c : ℝ)
    (hLower : UniformAnchorBlendedMetricLowerComparison gt x Q c)
    {p : P}
    (hp : p ∈ closure (Set.range
      (metricEntryThirdJetProfile (n := n) (M := M) ∘ gt)))
    {z : E} (hz : z ∈ Q) :
    (formalProfileMetricAt p x z).IsInvertible := by
  apply continuousLinearMap_isInvertible_of_strictlyPositive
  intro w hw
  have hnorm : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  exact lt_of_lt_of_le (mul_pos hLower.1 hnorm)
    (formalProfileMetricAt_lower_of_mem_closure
      gt x c hLower hp hz w)

end Poincare
