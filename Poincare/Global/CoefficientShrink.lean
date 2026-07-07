import Poincare.Global.RadiusTuple

/-!
# Coefficient-time shrink for bounded norm-system packages

This module records the non-vacuous radius-tuple construction behind the
coefficient-time shrink.  Once the scalar norm-system coefficient is bounded by
a ball-uniform constant `C`, shrinking the selector time so that `C * T ≤ 1/2`
leaves enough room to choose the bounded Picard-Lindelöf tuple consumed by
`TransverseExport`.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CoefficientShrink

universe u v

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
Arithmetic radius tuple from a ball-uniform coefficient bound.

The chosen radius is `max 1 (2 * C * T * Q)`.  The inequalities use both
halves of the shrink `C * T ≤ 1/2`: one half absorbs the center bound `Q`, and
the other half absorbs the radius contribution in the vector-field bound.
-/
theorem exists_radius_tuple_of_uniform_center_bound
    {ι : Type v} {T C Q : ℝ}
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
        ‖Aop‖ * T ≤ 1 := by
  let a : ℝ := max 1 (2 * C * T * Q)
  have hCT_nonneg : 0 ≤ C * T := mul_nonneg hC_nonneg hT_nonneg
  have hCTQ_nonneg : 0 ≤ C * T * Q := mul_nonneg hCT_nonneg hQ_nonneg
  have ha_ge_one : (1 : ℝ) ≤ a := by
    dsimp [a]
    exact le_max_left _ _
  have ha_nonneg : 0 ≤ a := le_trans zero_le_one ha_ge_one
  have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha_ge_one
  have ha_ge_two : 2 * (C * T * Q) ≤ a := by
    dsimp [a]
    nlinarith [le_max_right (1 : ℝ) (2 * C * T * Q)]
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
  refine ⟨radius, rNorm, LNorm, KNorm, B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha_pos
  · simpa [KNorm] using hAopNorm
  · intro i
    have hi := hcenterNorm i
    calc
      ‖center i‖ + (radius : ℝ) = ‖center i‖ + a := rfl
      _ ≤ Q + a := by linarith
      _ = (B : ℝ) := rfl
  · have hmul :
        ‖Aop‖ * (Q + a) ≤ C * (Q + a) := by
      exact mul_le_mul_of_nonneg_right hAopNorm hQa_nonneg
    simpa [B, LNorm] using hmul
  · have hroom : C * (Q + a) * T ≤ a := by
      nlinarith
    simpa [radius, rNorm, LNorm, sub_zero, mul_assoc, mul_comm, mul_left_comm]
      using hroom
  · have hnorm_time : ‖Aop‖ * T ≤ C * T := by
      exact mul_le_mul_of_nonneg_right hAopNorm hT_nonneg
    nlinarith

omit [T2Space M] in
/--
Source-side specialization of `exists_radius_tuple_of_uniform_center_bound` for
the quadratic centers appearing in the selector norm-system package.
-/
theorem source_exists_radius_tuple_of_uniform_center_bound
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T C Q : ℝ} {R : ℝ≥0}
    (hT_nonneg : 0 ≤ T) (hC_nonneg : 0 ≤ C) (hQ_nonneg : 0 ≤ Q)
    (hCT : C * T ≤ (1 : ℝ) / 2)
    (Aop : Triple →L[ℝ] Triple)
    (hAopNorm : ‖Aop‖ ≤ C)
    (hcenterNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ Q) :
    ∃ radius rNorm LNorm KNorm B : ℝ≥0,
      0 < (radius : ℝ) ∧
        ‖Aop‖ ≤ (KNorm : ℝ) ∧
        (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
          ‖(((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ)) ∧
        ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ) ∧
        (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ) ∧
        ‖Aop‖ * T ≤ 1 := by
  let center : {w : E3 // w ∈ closedBall (0 : E3) (R : ℝ)} → Triple :=
    fun w =>
      ((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • (w : E3)) (T⁻¹ • (w : E3)))
  rcases
      exists_radius_tuple_of_uniform_center_bound
        hT_nonneg hC_nonneg hQ_nonneg hCT Aop hAopNorm center
        (fun w => hcenterNorm w w.property) with
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hKNorm, hcenter,
      hbound, hmulT, hnormT⟩
  refine
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hKNorm, ?_,
      hbound, hmulT, hnormT⟩
  intro w hw
  exact hcenter ⟨w, hw⟩

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/--
Target-side specialization of `exists_radius_tuple_of_uniform_center_bound`.
-/
theorem target_exists_radius_tuple_of_uniform_center_bound
    (p₀ : RoundSphere3)
    {T C Q : ℝ} {R : ℝ≥0}
    (hT_nonneg : 0 ≤ T) (hC_nonneg : 0 ≤ C) (hQ_nonneg : 0 ≤ Q)
    (hCT : C * T ≤ (1 : ℝ) / 2)
    (Aop : Triple →L[ℝ] Triple)
    (hAopNorm : ‖Aop‖ ≤ C)
    (hcenterNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ Q) :
    ∃ radius rNorm LNorm KNorm B : ℝ≥0,
      0 < (radius : ℝ) ∧
        ‖Aop‖ ≤ (KNorm : ℝ) ∧
        (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
          ‖(((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
              (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ)) ∧
        ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ) ∧
        (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ) ∧
        ‖Aop‖ * T ≤ 1 := by
  let center : {w : E3 // w ∈ closedBall (0 : E3) (R : ℝ)} → Triple :=
    fun w =>
      ((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • (w : E3)) (T⁻¹ • (w : E3)))
  rcases
      exists_radius_tuple_of_uniform_center_bound
        hT_nonneg hC_nonneg hQ_nonneg hCT Aop hAopNorm center
        (fun w => hcenterNorm w w.property) with
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hKNorm, hcenter,
      hbound, hmulT, hnormT⟩
  refine
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hKNorm, ?_,
      hbound, hmulT, hnormT⟩
  intro w hw
  exact hcenter ⟨w, hw⟩

/--
Source transverse block after the coefficient-time shrink constructs the
bounded norm-system tuple.  The remaining Gronwall and speed-pinned membership
bounds are stated for the constructed radius, then passed unchanged to
`TransverseExport`.
-/
theorem source_transverseTransverse_of_selector_coefficient_shrink
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed Ccoeff Q Cgr qmax : ℝ} {aPkg : ℝ≥0}
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
    (Aop : Triple →L[ℝ] Triple)
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hCcoeff_nonneg : 0 ≤ Ccoeff) (hQ_nonneg : 0 ≤ Q)
    (hcoeffTime : Ccoeff * T ≤ (1 : ℝ) / 2)
    (hAopNormCoeff : ‖Aop‖ ≤ Ccoeff)
    (hcenterNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ Q)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hCgr : 0 ≤ Cgr) (hAopNormGronwall : ‖Aop‖ ≤ Cgr)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) :
    ∃ radius rNorm LNorm KNorm B : ℝ≥0,
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
  rcases
      source_exists_radius_tuple_of_uniform_center_bound
        (g := g) (x₀ := x₀) (R := R) hT.le hCcoeff_nonneg hQ_nonneg
        hcoeffTime Aop hAopNormCoeff hcenterNorm with
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hAopNormPL,
      hcenter, hbound, hmulT, hnormT⟩
  refine ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hnormT, ?_⟩
  intro hgronwallRadius hpinnedRadius
  exact
    TransverseExport.source_transverseTransverse_of_selector_bounded_data
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (C := Cgr) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ)
      (v := v) hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop
      hRpos hAopNormPL hcenter hbound hmulT hAop hCgr hAopNormGronwall
      hqBound hgronwallRadius hpinnedRadius

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/--
Target analogue of
`source_transverseTransverse_of_selector_coefficient_shrink`.
-/
theorem target_transverseTransverse_of_selector_coefficient_shrink
    (p₀ : RoundSphere3)
    {T ε speed Ccoeff Q Cgr qmax : ℝ} {aPkg : ℝ≥0}
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
    (Aop : Triple →L[ℝ] Triple)
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hCcoeff_nonneg : 0 ≤ Ccoeff) (hQ_nonneg : 0 ≤ Q)
    (hcoeffTime : Ccoeff * T ≤ (1 : ℝ) / 2)
    (hAopNormCoeff : ‖Aop‖ ≤ Ccoeff)
    (hcenterNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ Q)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hCgr : 0 ≤ Cgr) (hAopNormGronwall : ‖Aop‖ ≤ Cgr)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) :
    ∃ radius rNorm LNorm KNorm B : ℝ≥0,
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
                    (CartanMap.targetAnchorChartMetric p₀) v a')) := by
  rcases
      target_exists_radius_tuple_of_uniform_center_bound
        (p₀ := p₀) (R := R) hT.le hCcoeff_nonneg hQ_nonneg
        hcoeffTime Aop hAopNormCoeff hcenterNorm with
    ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hAopNormPL,
      hcenter, hbound, hmulT, hnormT⟩
  refine ⟨radius, rNorm, LNorm, KNorm, B, hradius_pos, hnormT, ?_⟩
  intro hgronwallRadius hpinnedRadius
  exact
    TransverseExport.target_transverseTransverse_of_selector_bounded_data
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed) (C := Cgr)
      (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      hAopNormPL hcenter hbound hmulT hAop hCgr hAopNormGronwall
      hqBound hgronwallRadius hpinnedRadius

end CoefficientShrink
end Poincare
