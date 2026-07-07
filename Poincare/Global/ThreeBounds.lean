import Poincare.Global.CoefficientShrink

/-!
# Selector-time coefficient, center, and shrink bounds

This module exports the non-vacuous bounded-`w` center estimates used by the
bounded norm-system tuple, together with small arithmetic adapters for the
coefficient-time shrink.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace ThreeBounds

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/-- The source quadratic center is uniformly bounded on each bounded `w`-ball. -/
theorem source_exists_qcenter_bound_on_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (R : ℝ≥0) :
    ∃ qmax : ℝ, 0 ≤ qmax ∧
      (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) ∧
      (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
        ‖(((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ qmax) := by
  let G : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
  let q : E3 → ℝ := fun w => G (T⁻¹ • w) (T⁻¹ • w)
  have hscale : Continuous fun w : E3 => T⁻¹ • w := by
    exact continuous_const_smul T⁻¹
  have hq_cont : Continuous q := by
    have hG : Continuous fun _w : E3 => G := continuous_const
    simpa [q] using (hG.clm_apply hscale).clm_apply hscale
  rcases (isCompact_closedBall (0 : E3) (R : ℝ)).exists_bound_of_continuousOn
      hq_cont.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_, ?_⟩
  · intro w hw
    have hnorm : ‖q w‖ ≤ max C 0 := (hC w hw).trans (le_max_left C 0)
    simpa [q, G, Real.norm_eq_abs] using hnorm
  · intro w hw
    have hq : |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ max C 0 := by
      have hnorm : ‖q w‖ ≤ max C 0 := (hC w hw).trans (le_max_left C 0)
      simpa [q, G, Real.norm_eq_abs] using hnorm
    rw [GronwallMembership.norm_triple_zero_zero]
    exact hq

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/-- The target quadratic center is uniformly bounded on each bounded `w`-ball. -/
theorem target_exists_qcenter_bound_on_closedBall
    (p₀ : RoundSphere3) (T : ℝ) (R : ℝ≥0) :
    ∃ qmax : ℝ, 0 ≤ qmax ∧
      (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) ∧
      (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
        ‖(((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ qmax) := by
  let G : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
  let q : E3 → ℝ := fun w => G (T⁻¹ • w) (T⁻¹ • w)
  have hscale : Continuous fun w : E3 => T⁻¹ • w := by
    exact continuous_const_smul T⁻¹
  have hq_cont : Continuous q := by
    have hG : Continuous fun _w : E3 => G := continuous_const
    simpa [q] using (hG.clm_apply hscale).clm_apply hscale
  rcases (isCompact_closedBall (0 : E3) (R : ℝ)).exists_bound_of_continuousOn
      hq_cont.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_, ?_⟩
  · intro w hw
    have hnorm : ‖q w‖ ≤ max C 0 := (hC w hw).trans (le_max_left C 0)
    simpa [q, G, Real.norm_eq_abs] using hnorm
  · intro w hw
    have hq : |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ max C 0 := by
      have hnorm : ‖q w‖ ≤ max C 0 := (hC w hw).trans (le_max_left C 0)
      simpa [q, G, Real.norm_eq_abs] using hnorm
    rw [GronwallMembership.norm_triple_zero_zero]
    exact hq

omit [T2Space M] in
/--
Ball-uniform compact coefficient bound extracted from the `UniformShrink`
construction for the linearized geodesic-flow operator.
-/
theorem exists_ball_uniform_linearized_coefficient_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (aBase : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : E3 × E3,
        q ∈ closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (aBase : ℝ) →
          ‖linearizedGeodesicFlowOperator (chartChristoffelField g x₀) q‖ ≤ C := by
  let Γ : E3 → E3 →L[ℝ] E3 →L[ℝ] E3 := chartChristoffelField g x₀
  let A : E3 × E3 → (E3 × E3) →L[ℝ] (E3 × E3) :=
    fun q => linearizedGeodesicFlowOperator Γ q
  have hA_cont : Continuous A := by
    simpa [A, Γ, linearizedGeodesicFlowOperator] using
      (geodesicFlowField_chartChristoffelField_contDiff
        (g := g) (x₀ := x₀)).continuous_fderiv (by norm_num)
  rcases
      (isCompact_closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (aBase : ℝ)).exists_bound_of_continuousOn
        hA_cont.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro q hq
  exact (hC q hq).trans (le_max_left C 0)

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/-- Target specialization of `exists_ball_uniform_linearized_coefficient_bound`. -/
theorem target_exists_ball_uniform_linearized_coefficient_bound
    (p₀ : RoundSphere3) (aBase : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : E3 × E3,
        q ∈ closedBall (extChartAt I3 p₀ p₀, (0 : E3)) (aBase : ℝ) →
          ‖linearizedGeodesicFlowOperator
            (chartChristoffelField roundSphereMetric3 p₀) q‖ ≤ C := by
  exact exists_ball_uniform_linearized_coefficient_bound
    (g := roundSphereMetric3) (x₀ := p₀) aBase

/-- The tautological coefficient bound used when the selector has fixed `Aop`. -/
theorem coefficient_bound_self (Aop : Triple →L[ℝ] Triple) :
    ‖Aop‖ ≤ ‖Aop‖ :=
  le_rfl

/-- Nonnegative coefficient bound supplied by an operator norm. -/
theorem coefficient_norm_nonneg (Aop : Triple →L[ℝ] Triple) :
    0 ≤ ‖Aop‖ :=
  norm_nonneg Aop

/-- A convenient scalar arithmetic form of the coefficient-time shrink. -/
theorem coefficient_time_shrink_of_le_div
    {C T : ℝ} (hC : 0 < C) (hT : T ≤ ((1 : ℝ) / 2) / C) :
    C * T ≤ (1 : ℝ) / 2 := by
  calc
    C * T ≤ C * (((1 : ℝ) / 2) / C) := by
      exact mul_le_mul_of_nonneg_left hT hC.le
    _ = (1 : ℝ) / 2 := by field_simp [ne_of_gt hC]

/--
Source selector continuation after exporting the compact center bound and using
the fixed coefficient norm as the coefficient bound.  The remaining short-time
input is exactly the selector-time shrink `‖Aop‖ * T ≤ 1/2`.
-/
theorem source_transverseTransverse_of_selector_three_bounds
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed Cgr : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple) {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hCgr : 0 ≤ Cgr) (hAopNormGronwall : ‖Aop‖ ≤ Cgr) :
    ∃ qmax : ℝ, 0 ≤ qmax ∧
      ∃ radius _rNorm _LNorm _KNorm _B : ℝ≥0,
        0 < (radius : ℝ) ∧
          ‖Aop‖ * T ≤ 1 ∧
          (qmax * Real.exp (Cgr * T) + qmax ≤ (radius : ℝ) →
            (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
              CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
                (MembershipBound.speedPinnedMembershipRadius speed
                  (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                    (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) →
            ∀ a a' : E3,
              CovariantDerivative.chartMetric g.inner x₀
                  ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
                  (Ψ (CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
                  (Ψ (CartanPullback.transversePart
                    (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
                JacobiNormSystem.speedPinnedScale speed T *
                  CartanMap.sourceAnchorChartMetric g x₀
                    (T⁻¹ • CartanPullback.transversePart
                      (CartanMap.sourceAnchorChartMetric g x₀) v a)
                    (T⁻¹ • CartanPullback.transversePart
                      (CartanMap.sourceAnchorChartMetric g x₀) v a')) := by
  rcases source_exists_qcenter_bound_on_closedBall
      (g := g) (x₀ := x₀) (T := T) (R := R) with
    ⟨qmax, hqmax_nonneg, hqBound, hcenterNorm⟩
  refine ⟨qmax, hqmax_nonneg, ?_⟩
  exact
    CoefficientShrink.source_transverseTransverse_of_selector_coefficient_shrink
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (Ccoeff := ‖Aop‖) (Q := qmax) (Cgr := Cgr) (qmax := qmax)
      (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v) hT hbase hlin
      hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      (coefficient_norm_nonneg Aop) hqmax_nonneg hcoeffTime
      (coefficient_bound_self Aop) hcenterNorm hAop hCgr hAopNormGronwall
      (fun w hw _horth => hqBound w hw)

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/--
Target selector continuation after exporting the compact center bound and using
the fixed coefficient norm as the coefficient bound.
-/
theorem target_transverseTransverse_of_selector_three_bounds
    (p₀ : RoundSphere3)
    {T ε speed Cgr : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple) {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hCgr : 0 ≤ Cgr) (hAopNormGronwall : ‖Aop‖ ≤ Cgr) :
    ∃ qmax : ℝ, 0 ≤ qmax ∧
      ∃ radius _rNorm _LNorm _KNorm _B : ℝ≥0,
        0 < (radius : ℝ) ∧
          ‖Aop‖ * T ≤ 1 ∧
          (qmax * Real.exp (Cgr * T) + qmax ≤ (radius : ℝ) →
            (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
              CartanMap.targetAnchorChartMetric p₀ v w = 0 →
                (MembershipBound.speedPinnedMembershipRadius speed
                  (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
                    (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) →
            ∀ a a' : E3,
              CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                  ((expAtChartOpenPartialHomeomorph
                    (g := roundSphereMetric3) p₀) v)
                  (Ψ (CartanPullback.transversePart
                    (CartanMap.targetAnchorChartMetric p₀) v a) T).1
                  (Ψ (CartanPullback.transversePart
                    (CartanMap.targetAnchorChartMetric p₀) v a') T).1 =
                JacobiNormSystem.speedPinnedScale speed T *
                  CartanMap.targetAnchorChartMetric p₀
                    (T⁻¹ • CartanPullback.transversePart
                      (CartanMap.targetAnchorChartMetric p₀) v a)
                    (T⁻¹ • CartanPullback.transversePart
                      (CartanMap.targetAnchorChartMetric p₀) v a')) := by
  rcases target_exists_qcenter_bound_on_closedBall
      (p₀ := p₀) (T := T) (R := R) with
    ⟨qmax, hqmax_nonneg, hqBound, hcenterNorm⟩
  refine ⟨qmax, hqmax_nonneg, ?_⟩
  exact
    CoefficientShrink.target_transverseTransverse_of_selector_coefficient_shrink
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed)
      (Ccoeff := ‖Aop‖) (Q := qmax) (Cgr := Cgr) (qmax := qmax)
      (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v) hT hbase hlin
      hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      (coefficient_norm_nonneg Aop) hqmax_nonneg hcoeffTime
      (coefficient_bound_self Aop) hcenterNorm hAop hCgr hAopNormGronwall
      (fun w hw _horth => hqBound w hw)

end ThreeBounds
end Poincare
