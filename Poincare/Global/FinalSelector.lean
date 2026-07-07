import Poincare.Global.ThreeBounds

/-!
# Final selector shrink boundary

This module closes the quantitative selector continuations that were still
external after `ThreeBounds`: once the scalar norm-system coefficient-time
shrink is available, the radius tuple can be chosen large enough to satisfy the
Gronwall and speed-pinned radius floors at the same time.

It deliberately does not assert the remaining curvature-only selector theorem:
the current public common-time selector still does not export a scalar
norm-system coefficient bound for the `Aop` used below.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace FinalSelector

universe u v

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/-- Fixed scalar floor dominating the explicit speed-pinned radius when `|q| ≤ qmax`. -/
def speedPinnedRadiusBound (speed qmax : ℝ) : ℝ :=
  max (max (|(speed ^ 2)⁻¹| * qmax) (|speed⁻¹| * qmax)) (2 * qmax)

/-- The explicit pinned membership radius is monotone in the quadratic bound. -/
theorem speedPinnedMembershipRadius_le_bound_of_abs_le
    {speed q qmax : ℝ} (hq : |q| ≤ qmax) :
    (MembershipBound.speedPinnedMembershipRadius speed q : ℝ) ≤
      speedPinnedRadiusBound speed qmax := by
  have hsq :
      |(speed ^ 2)⁻¹| * |q| ≤ |(speed ^ 2)⁻¹| * qmax :=
    mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hinv : |speed⁻¹| * |q| ≤ |speed⁻¹| * qmax :=
    mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have htwo : 2 * |q| ≤ 2 * qmax :=
    mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2)
  rw [MembershipBound.speedPinnedMembershipRadius]
  change
    max (max (|(speed ^ 2)⁻¹| * |q|) (|speed⁻¹| * |q|)) (2 * |q|) ≤
      speedPinnedRadiusBound speed qmax
  exact max_le_max (max_le_max hsq hinv) htwo

/--
Coefficient-time shrink from a robust `1 / (2 * (C + 1))` margin.

This is the arithmetic form used by a selector that adds one more positive term
to the common-time minimum.
-/
theorem coeff_mul_time_le_half_of_le_inv_two_mul_add_one
    {C T : ℝ} (hC : 0 ≤ C) (hT : T ≤ 1 / (2 * (C + 1))) :
    C * T ≤ (1 : ℝ) / 2 := by
  have hden_pos : 0 < 2 * (C + 1) := by nlinarith
  calc
    C * T ≤ C * (1 / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hT hC
    _ = C / (2 * (C + 1)) := by ring
    _ ≤ (1 : ℝ) / 2 := by
      rw [div_le_iff₀ hden_pos]
      nlinarith

/-- Operator-norm specialization of the extra selector margin. -/
theorem norm_mul_time_le_half_of_le_inv_two_mul_norm_add_one
    (Aop : Triple →L[ℝ] Triple) {T : ℝ}
    (hT : T ≤ 1 / (2 * (‖Aop‖ + 1))) :
    ‖Aop‖ * T ≤ (1 : ℝ) / 2 :=
  coeff_mul_time_le_half_of_le_inv_two_mul_add_one
    (C := ‖Aop‖) (T := T) (norm_nonneg Aop) hT

/--
Radius tuple with an additional scalar floor.

The proof is the same arithmetic as `CoefficientShrink`, except that the
selected radius also dominates `floor`.  This lets the caller discharge the
Gronwall and pinned-membership radius hypotheses immediately.
-/
theorem exists_radius_tuple_of_uniform_center_bound_and_floor
    {ι : Type v} {T C Q floor : ℝ}
    (hT_nonneg : 0 ≤ T) (hC_nonneg : 0 ≤ C) (hQ_nonneg : 0 ≤ Q)
    (hCT : C * T ≤ (1 : ℝ) / 2)
    (Aop : Triple →L[ℝ] Triple)
    (hAopNorm : ‖Aop‖ ≤ C)
    (center : ι → Triple)
    (hcenterNorm : ∀ i : ι, ‖center i‖ ≤ Q) :
    ∃ radius rNorm LNorm KNorm B : ℝ≥0,
      0 < (radius : ℝ) ∧
        ‖Aop‖ ≤ (KNorm : ℝ) ∧
        (∀ i : ι, ‖center i‖ + (radius : ℝ) ≤ (B : ℝ)) ∧
        ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ) ∧
        (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ) ∧
        ‖Aop‖ * T ≤ 1 ∧
        floor ≤ (radius : ℝ) := by
  let a : ℝ := max (max 1 (2 * (C * T * Q))) floor
  have hCT_nonneg : 0 ≤ C * T := mul_nonneg hC_nonneg hT_nonneg
  have hCTQ_nonneg : 0 ≤ C * T * Q := mul_nonneg hCT_nonneg hQ_nonneg
  have ha_ge_one : (1 : ℝ) ≤ a := by
    dsimp [a]
    exact (le_max_left (1 : ℝ) (2 * (C * T * Q))).trans (le_max_left _ _)
  have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha_ge_one
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha_ge_one
  have ha_ge_two : 2 * (C * T * Q) ≤ a := by
    dsimp [a]
    exact (le_max_right (1 : ℝ) (2 * (C * T * Q))).trans (le_max_left _ _)
  have ha_ge_floor : floor ≤ a := by
    dsimp [a]
    exact le_max_right _ _
  have hCTQ_le_half_a : C * T * Q ≤ a / 2 := by
    nlinarith
  have hCTa_le_half_a : C * T * a ≤ a / 2 := by
    nlinarith
  have hQa_nonneg : 0 ≤ Q + a := add_nonneg hQ_nonneg ha_nonneg
  let radius : ℝ≥0 := ⟨a, ha_nonneg⟩
  let rNorm : ℝ≥0 := 0
  let KNorm : ℝ≥0 := ⟨C, hC_nonneg⟩
  let B : ℝ≥0 := ⟨Q + a, hQa_nonneg⟩
  let LNorm : ℝ≥0 := ⟨C * (Q + a), mul_nonneg hC_nonneg hQa_nonneg⟩
  refine ⟨radius, rNorm, LNorm, KNorm, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha_pos
  · simpa [KNorm] using hAopNorm
  · intro i
    have hi := hcenterNorm i
    calc
      ‖center i‖ + (radius : ℝ) = ‖center i‖ + a := rfl
      _ ≤ Q + a := by linarith
      _ = (B : ℝ) := rfl
  · have hmul :
        ‖Aop‖ * (Q + a) ≤ C * (Q + a) :=
      mul_le_mul_of_nonneg_right hAopNorm hQa_nonneg
    simpa [B, LNorm] using hmul
  · have hroom : C * (Q + a) * T ≤ a := by
      nlinarith
    simpa [radius, rNorm, LNorm, sub_zero, mul_assoc, mul_comm, mul_left_comm]
      using hroom
  · have hnorm_time : ‖Aop‖ * T ≤ C * T :=
      mul_le_mul_of_nonneg_right hAopNorm hT_nonneg
    nlinarith
  · simpa [radius] using ha_ge_floor

/--
Source transverse block with the final selector radius floors discharged.

The only remaining scalar short-time input is the coefficient-time shrink
`‖Aop‖ * T ≤ 1 / 2`; the constructed radius is large enough for both the
Gronwall bound and the speed-pinned membership radius.
-/
theorem source_transverseTransverse_of_selector_final_bounds
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
              (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
  rcases ThreeBounds.source_exists_qcenter_bound_on_closedBall
      (g := g) (x₀ := x₀) (T := T) (R := R) with
    ⟨qmax, hqmax_nonneg, hqBound, hcenterNorm⟩
  let grFloor : ℝ := qmax * Real.exp (Cgr * T) + qmax
  let pinFloor : ℝ := speedPinnedRadiusBound speed qmax
  let floor : ℝ := max grFloor pinFloor
  let center :
      {w : E3 // w ∈ closedBall (0 : E3) (R : ℝ)} → Triple :=
    fun w =>
      ((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • (w : E3)) (T⁻¹ • (w : E3)))
  rcases
      exists_radius_tuple_of_uniform_center_bound_and_floor
        (T := T) (C := ‖Aop‖) (Q := qmax) (floor := floor)
        hT.le (norm_nonneg Aop) hqmax_nonneg hcoeffTime
        Aop (le_rfl : ‖Aop‖ ≤ ‖Aop‖) center
        (fun w => hcenterNorm w w.property) with
    ⟨radius, rNorm, LNorm, KNorm, B, _hradius_pos, hAopNormPL,
      hcenter, hbound, hmulT, _hnormT, hfloor_le_radius⟩
  have hgronwallRadius : grFloor ≤ (radius : ℝ) :=
    (le_max_left grFloor pinFloor).trans hfloor_le_radius
  have hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ) := by
    intro w hw horth
    have hpin :
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ pinFloor := by
      dsimp [pinFloor]
      exact speedPinnedMembershipRadius_le_bound_of_abs_le
        (speed := speed) (qmax := qmax) (hqBound w hw)
    exact hpin.trans ((le_max_right grFloor pinFloor).trans hfloor_le_radius)
  exact
    TransverseExport.source_transverseTransverse_of_selector_bounded_data
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (C := Cgr) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ)
      (v := v) hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop
      (R := R) (radius := radius) (rNorm := rNorm) (LNorm := LNorm)
      (KNorm := KNorm) (B := B) hRpos hAopNormPL
      (fun w hw => hcenter ⟨w, hw⟩) hbound hmulT hAop hCgr
      hAopNormGronwall (fun w hw _horth => hqBound w hw)
      hgronwallRadius hpinnedRadius

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/-- Target analogue of `source_transverseTransverse_of_selector_final_bounds`. -/
theorem target_transverseTransverse_of_selector_final_bounds
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
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a') := by
  rcases ThreeBounds.target_exists_qcenter_bound_on_closedBall
      (p₀ := p₀) (T := T) (R := R) with
    ⟨qmax, hqmax_nonneg, hqBound, hcenterNorm⟩
  let grFloor : ℝ := qmax * Real.exp (Cgr * T) + qmax
  let pinFloor : ℝ := speedPinnedRadiusBound speed qmax
  let floor : ℝ := max grFloor pinFloor
  let center :
      {w : E3 // w ∈ closedBall (0 : E3) (R : ℝ)} → Triple :=
    fun w =>
      ((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • (w : E3)) (T⁻¹ • (w : E3)))
  rcases
      exists_radius_tuple_of_uniform_center_bound_and_floor
        (T := T) (C := ‖Aop‖) (Q := qmax) (floor := floor)
        hT.le (norm_nonneg Aop) hqmax_nonneg hcoeffTime
        Aop (le_rfl : ‖Aop‖ ≤ ‖Aop‖) center
        (fun w => hcenterNorm w w.property) with
    ⟨radius, rNorm, LNorm, KNorm, B, _hradius_pos, hAopNormPL,
      hcenter, hbound, hmulT, _hnormT, hfloor_le_radius⟩
  have hgronwallRadius : grFloor ≤ (radius : ℝ) :=
    (le_max_left grFloor pinFloor).trans hfloor_le_radius
  have hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ) := by
    intro w hw horth
    have hpin :
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ pinFloor := by
      dsimp [pinFloor]
      exact speedPinnedMembershipRadius_le_bound_of_abs_le
        (speed := speed) (qmax := qmax) (hqBound w hw)
    exact hpin.trans ((le_max_right grFloor pinFloor).trans hfloor_le_radius)
  exact
    TransverseExport.target_transverseTransverse_of_selector_bounded_data
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed) (C := Cgr)
      (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop
      (R := R) (radius := radius) (rNorm := rNorm) (LNorm := LNorm)
      (KNorm := KNorm) (B := B) hRpos hAopNormPL
      (fun w hw => hcenter ⟨w, hw⟩) hbound hmulT hAop hCgr
      hAopNormGronwall (fun w hw _horth => hqBound w hw)
      hgronwallRadius hpinnedRadius

end FinalSelector
end Poincare
