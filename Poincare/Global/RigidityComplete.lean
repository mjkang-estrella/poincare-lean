import Poincare.Global.AopBound
import Poincare.Global.BlockDiagonal
import Poincare.Global.CombinedFeed
import Poincare.Global.SpeedReconcile

/-!
# Final rigidity assembly

This module adds the last scalar norm-system shrink to the selector stack and
assembles the verified block-diagonal Cartan local-isometry consumer.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RigidityComplete

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/-- The scalar speed-generic norm-system coefficient operator. -/
def speedNormSystemAop (speed : ℝ) : Triple →L[ℝ] Triple :=
  let fst3 : Triple →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let snd3 : Triple →L[ℝ] ℝ × ℝ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  let mid3 : Triple →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp snd3
  let last3 : Triple →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp snd3
  ((2 : ℝ) • mid3).prod
    ( (last3 - (speed ^ 2 : ℝ) • fst3).prod
      (((-2 : ℝ) * speed ^ 2) • mid3) )

@[simp]
theorem speedNormSystemAop_apply (speed : ℝ) (x : Triple) :
    speedNormSystemAop speed x =
      (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1) := by
  simp [speedNormSystemAop, mul_assoc]

omit [T2Space M] in
/-- The source anchor speed-square is bounded on each compact closed model ball. -/
theorem exists_source_anchor_speed_sq_bound_on_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (R : ℝ≥0) :
    ∃ S : ℝ, 0 ≤ S ∧
      ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
        CartanMap.sourceAnchorChartMetric g x₀ w w ≤ S := by
  let q : E3 → ℝ := fun w => CartanMap.sourceAnchorChartMetric g x₀ w w
  have hq_cont : Continuous q := by
    have hG : Continuous fun _w : E3 => CartanMap.sourceAnchorChartMetric g x₀ :=
      continuous_const
    simpa [q] using (hG.clm_apply continuous_id).clm_apply continuous_id
  rcases (isCompact_closedBall (0 : E3) (R : ℝ)).exists_bound_of_continuousOn
      hq_cont.continuousOn with
    ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro w hw
  have hnorm : ‖q w‖ ≤ max C 0 := (hC w hw).trans (le_max_left C 0)
  have hle_abs : q w ≤ |q w| := le_abs_self (q w)
  exact hle_abs.trans (by simpa [q, Real.norm_eq_abs] using hnorm)

theorem inv_smul_ne_zero {T : ℝ} (hT : T ≠ 0) {v : E3} (hv : v ≠ 0) :
    T⁻¹ • v ≠ 0 := by
  intro h
  apply hv
  calc
    v = T • (T⁻¹ • v) := by
      simp [smul_smul, hT]
    _ = 0 := by simp [h]

theorem speed_mul_time_mem_Ioo_of_sq_bound
    {speed S T : ℝ} (hspeed_pos : 0 < speed) (hspeed_sq : speed ^ 2 ≤ S)
    (hT_pos : 0 < T) (hTangle : T ≤ Real.pi / (2 * (Real.sqrt S + 1))) :
    speed * T ∈ Ioo (0 : ℝ) Real.pi := by
  constructor
  · exact mul_pos hspeed_pos hT_pos
  · have hspeed_le_sqrt : speed ≤ Real.sqrt S := by
      exact Real.le_sqrt_of_sq_le hspeed_sq
    have hsqrt_nonneg : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
    have hden_pos : 0 < 2 * (Real.sqrt S + 1) := by positivity
    calc
      speed * T ≤ Real.sqrt S * (Real.pi / (2 * (Real.sqrt S + 1))) := by
        exact mul_le_mul hspeed_le_sqrt hTangle hT_pos.le hsqrt_nonneg
      _ < Real.pi := by
        have hpi_pos : 0 < Real.pi := Real.pi_pos
        have hratio :
            Real.sqrt S / (2 * (Real.sqrt S + 1)) < (1 : ℝ) := by
          rw [div_lt_one hden_pos]
          nlinarith [hsqrt_nonneg]
        calc
          Real.sqrt S * (Real.pi / (2 * (Real.sqrt S + 1)))
              = Real.pi * (Real.sqrt S / (2 * (Real.sqrt S + 1))) := by ring
          _ < Real.pi * 1 := mul_lt_mul_of_pos_left hratio hpi_pos
          _ = Real.pi := by ring

/--
Speed-generic source transverse block with the final scalar `Aop` shrink
discharged from an exported speed-square bound and the added time floor.
-/
theorem source_transverseTransverse_of_selector_aop_bound
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed S : ℝ} {aPkg : ℝ≥0}
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
    (hspeed_sq : speed ^ 2 ≤ S)
    (hTscalar : T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1)))
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ)) :
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
  let Aop : Triple →L[ℝ] Triple := speedNormSystemAop speed
  have hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
        -2 * speed ^ 2 * x.2.1) := by
    intro x
    simp [Aop]
  have hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2 :=
    AopBound.speed_normSystem_mul_time_le_half_of_speed_sq_bound
      (speed := speed) (S := S) (T := T) hspeed_sq hT.le Aop hAop hTscalar
  have hAopNorm : ‖Aop‖ ≤ 4 * max (1 : ℝ) S :=
    AopBound.speed_normSystem_opNorm_le_of_speed_sq_bound
      (speed := speed) (S := S) hspeed_sq Aop hAop
  have hCgr_nonneg : 0 ≤ 4 * max (1 : ℝ) S := by
    have hmax_nonneg : 0 ≤ max (1 : ℝ) S :=
      le_trans zero_le_one (le_max_left _ _)
    nlinarith
  exact
    FinalSelector.source_transverseTransverse_of_selector_final_bounds
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (Cgr := 4 * max (1 : ℝ) S) (aPkg := aPkg) (α := α) (Ψ := Ψ)
      (v := v) hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop
      (R := R) hRpos hcoeffTime hAop hCgr_nonneg hAopNorm

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/-- Target analogue of `source_transverseTransverse_of_selector_aop_bound`. -/
theorem target_transverseTransverse_of_selector_aop_bound
    (p₀ : RoundSphere3)
    {T ε speed S : ℝ} {aPkg : ℝ≥0}
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
    (hspeed_sq : speed ^ 2 ≤ S)
    (hTscalar : T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1)))
    {R : ℝ≥0} (hRpos : 0 < (R : ℝ)) :
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
  let Aop : Triple →L[ℝ] Triple := speedNormSystemAop speed
  have hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
        -2 * speed ^ 2 * x.2.1) := by
    intro x
    simp [Aop]
  have hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2 :=
    AopBound.speed_normSystem_mul_time_le_half_of_speed_sq_bound
      (speed := speed) (S := S) (T := T) hspeed_sq hT.le Aop hAop hTscalar
  have hAopNorm : ‖Aop‖ ≤ 4 * max (1 : ℝ) S :=
    AopBound.speed_normSystem_opNorm_le_of_speed_sq_bound
      (speed := speed) (S := S) hspeed_sq Aop hAop
  have hCgr_nonneg : 0 ≤ 4 * max (1 : ℝ) S := by
    have hmax_nonneg : 0 ≤ max (1 : ℝ) S :=
      le_trans zero_le_one (le_max_left _ _)
    nlinarith
  exact
    FinalSelector.target_transverseTransverse_of_selector_final_bounds
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed)
      (Cgr := 4 * max (1 : ℝ) S) (aPkg := aPkg) (α := α) (Ψ := Ψ)
      (v := v) hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop
      (R := R) hRpos hcoeffTime hAop hCgr_nonneg hAopNorm

omit [T2Space M] in
/--
Variant of the block-diagonal adapter that returns one source/target endpoint
equivalence pair and the full pullback equality for every tangent pair.
-/
theorem exists_equiv_and_cartanMap_isLocalIsometry_pullback_of_angle_time_blocks
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {v : E3} {Ψs Ψt : E3 → ℝ → E3 × E3} {speed T : ℝ}
    {hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1}
    {hsmuls : ∀ (c : ℝ) (w : E3),
      (Ψs (c • w) T).1 = c • (Ψs w T).1}
    {haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1}
    {hsmult : ∀ (c : ℝ) (w : E3),
      (Ψt (c • w) T).1 = c • (Ψt w T).1}
    (hT : T ≠ 0) (hspeed : speed ≠ 0)
    (hAngle : speed * T ∈ Ioo (0 : ℝ) Real.pi)
    (hvsrc : v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hsourceDeriv :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v)
    (htargetDeriv :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀)
        (linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult) (L v))
    (hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a'))
    (hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) = 0)
    (hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a'))
    (hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a'))
    (hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) = 0)
    (hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a')) :
    ∃ A B : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls ∧
      (B : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult ∧
      HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) u u' := by
  let Gs : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric g.inner x₀
      ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
  let Gt : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
      ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) (L v))
  have hSourceBlock :
      ∀ a a' : E3,
        Gs (Ψs a T).1 (Ψs a' T).1 =
          CorrectedRadial.timeRadialScale T *
              CartanMap.sourceAnchorChartMetric g x₀
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.sourceAnchorChartMetric g x₀) v a)
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.sourceAnchorChartMetric g x₀) v a') +
            JacobiNormSystem.speedPinnedScale speed T *
              CartanMap.sourceAnchorChartMetric g x₀
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x₀) v a)
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
    intro a a'
    exact
      CorrectedRadial.source_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
        (g := g) (x0 := x₀) (Psi := Ψs) (v := v) (T := T) (speed := speed)
        hadds hSourceRadialRadial hSourceRadialTransverse
        hSourceTransverseTransverse a a'
  have hTargetBlock :
      ∀ a a' : E3,
        Gt (Ψt a T).1 (Ψt a' T).1 =
          CorrectedRadial.timeRadialScale T *
              CartanMap.targetAnchorChartMetric p₀
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.targetAnchorChartMetric p₀) (L v) a)
                (T⁻¹ • CartanPullback.radialPart
                  (CartanMap.targetAnchorChartMetric p₀) (L v) a') +
            JacobiNormSystem.speedPinnedScale speed T *
              CartanMap.targetAnchorChartMetric p₀
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p₀) (L v) a)
                (T⁻¹ • CartanPullback.transversePart
                  (CartanMap.targetAnchorChartMetric p₀) (L v) a') := by
    intro a a'
    exact
      CorrectedRadial.target_hosted_rescaled_endpoint_pairing_eq_of_time_radial_transverse_blocks
        (p0 := p₀) (Psi := Ψt) (v := L v) (T := T) (speed := speed)
        haddt hTargetRadialRadial hTargetRadialTransverse
        hTargetTransverseTransverse a a'
  have hRadialScale : 0 < CorrectedRadial.timeRadialScale T :=
    BlockDiagonal.timeRadialScale_pos_of_ne_zero hT
  have hTransverseScale : 0 < JacobiNormSystem.speedPinnedScale speed T :=
    BlockDiagonal.speedPinnedScale_pos_of_mul_mem_Ioo hspeed hAngle
  rcases
      BlockDiagonal.exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
        (g := g) (x0 := x₀) (Psi := Ψs) (v := v) (T := T)
        hadds hsmuls (G := Gs) hT hRadialScale hTransverseScale hSourceBlock with
    ⟨A, hA⟩
  rcases
      BlockDiagonal.exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
        (p0 := p₀) (Psi := Ψt) (v := L v) (T := T)
        haddt hsmult (G := Gt) hT hRadialScale hTransverseScale hTargetBlock with
    ⟨B, hB⟩
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · exact
      (CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_time_radial_decomposed_blocks
        (g := g) (x0 := x₀) (p0 := p₀) L
        (v := v) (A := A) (B := B) (PsiS := Ψs) (PsiT := Ψt)
        (speed := speed) (T := T)
        hA hB hvsrc (by simpa [hA] using hsourceDeriv)
        (by simpa [hB] using htargetDeriv) 0 0
        hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
        hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse).1
  · intro u u'
    exact
      (CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_time_radial_decomposed_blocks
        (g := g) (x0 := x₀) (p0 := p₀) L
        (v := v) (A := A) (B := B) (PsiS := Ψs) (PsiT := Ψt)
        (speed := speed) (T := T)
        hA hB hvsrc (by simpa [hA] using hsourceDeriv)
        (by simpa [hB] using htargetDeriv) u u'
        hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
        hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse).2

/--
One selector datum, with the final scalar `Aop` time floor threaded through,
assembles to the Cartan chart-metric pullback equality.
-/
theorem cartanMap_isLocalIsometry_of_selector_aop_bound
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀)
    {T εs εt speed S : ℝ} {as aTgt : ℝ≥0}
    {αs αt : E3 × E3 → ℝ → E3 × E3}
    {Ψs Ψt : E3 → ℝ → E3 × E3} {v : E3}
    (hT : 0 < T)
    (hTscalar : T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1)))
    (hAngle : speed * T ∈ Ioo (0 : ℝ) Real.pi)
    (hvsrc : v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source)
    (hbaseS : EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v)
    (hlinS : EnrichedCascade.LinearizedFamilyPackage g x₀ T εs αs v Ψs)
    (hadds : ∀ w w' : E3,
      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1)
    (hsmuls : ∀ (c : ℝ) (w : E3),
      (Ψs (c • w) T).1 = c • (Ψs w T).1)
    (hstrictS :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v)
    (hRayS :
      (Ψs v T).1 =
        T • (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2)
    (hbaseT :
      EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T εt aTgt αt (L v))
    (hlinT :
      EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T εt αt (L v) Ψt)
    (haddt : ∀ w w' : E3,
      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1)
    (hsmult : ∀ (c : ℝ) (w : E3),
      (Ψt (c • w) T).1 = c • (Ψt w T).1)
    (hstrictT :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀)
        (linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult) (L v))
    (hRayT :
      (Ψt (L v) T).1 =
        T • (αt (extChartAt I3 p₀ p₀, T⁻¹ • L v) T).2)
    (hspeed_ne : speed ≠ 0)
    (hsourceAnchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (htargetAnchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • L v) (T⁻¹ • L v) = speed ^ 2)
    (hspeed_sq : speed ^ 2 ≤ S) :
    ∃ A B : E3 ≃L[ℝ] E3,
      (A : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls ∧
      (B : E3 →L[ℝ] E3) = linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult ∧
      HasStrictFDerivAt
        (CartanDifferential.cartanChartMap g x₀ p₀ L)
        (CartanLocalIsometry.cartanChartDifferential L A B)
        ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
      ∀ u u' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            (CartanLocalIsometry.cartanChartDifferential L A B u)
            (CartanLocalIsometry.cartanChartDifferential L A B u') =
          CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) u u' := by
  have hTne : T ≠ 0 := ne_of_gt hT
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  let Vs : E3 := (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2
  let Vt : E3 := (αt (extChartAt I3 p₀ p₀, T⁻¹ • L v) T).2
  have hbaseS_fields := hbaseS
  dsimp [EnrichedCascade.BaseCurvePackage] at hbaseS_fields
  rcases hbaseS_fields with
    ⟨_hγ0S, _hγderS, _hγder0TS, _hγAtS, _hγmemS, _hγtargetS,
      _hγtarget0TS, _hγcutS, _hγχ0TS, hspeedBaseS, hendpointS⟩
  have hbaseT_fields := hbaseT
  dsimp [EnrichedCascade.BaseCurvePackage] at hbaseT_fields
  rcases hbaseT_fields with
    ⟨_hγ0T, _hγderT, _hγder0TT, _hγAtT, _hγmemT, _hγtargetT,
      _hγtarget0TT, _hγcutT, _hγχ0TT, hspeedBaseT, hendpointT⟩
  have hSourceEndpointSpeed :
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) Vs Vs =
        speed ^ 2 := by
    have hspeed := hspeedBaseS T hTmem
    simpa [Vs, hendpointS] using hspeed.trans hsourceAnchorSpeed
  have hTargetEndpointSpeed :
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L v)) Vt Vt =
        speed ^ 2 := by
    have hspeed := hspeedBaseT T hTmem
    simpa [Vt, hendpointT] using hspeed.trans htargetAnchorSpeed
  have hSourceTransverseOrthogonal :
      ∀ a : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1) Vs = 0 := by
    intro a
    have horth :=
      IsometryComplete.source_orthogonal_of_enriched_packages
        (g := g) (x₀ := x₀) (T := T) (ε := εs) (aPkg := as)
        (α := αs) (Ψ := Ψs) (v := v) hT hbaseS hlinS
        (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v a)
        (PLNormFeed.sourceAnchorChartMetric_transversePart_eq_zero
          (g := g) (x₀ := x₀) v a)
        T hTmem
    simpa [Vs, hendpointS] using horth
  have hTargetTransverseOrthogonal :
      ∀ a : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1) Vt = 0 := by
    intro a
    have horth :=
      IsometryComplete.target_orthogonal_of_enriched_packages
        (p₀ := p₀) (T := T) (ε := εt) (aPkg := aTgt)
        (α := αt) (Ψ := Ψt) (v := L v) hT hbaseT hlinT
        (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) (L v) a)
        (PLNormFeed.targetAnchorChartMetric_transversePart_eq_zero
          (p₀ := p₀) (L v) a)
        T hTmem
    simpa [Vt, hendpointT] using horth
  have hSourceRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
    intro a a'
    exact
      SpeedReconcile.source_radialPart_endpoint_pairing_eq_timeRadialScale
        (g := g) (x0 := x₀) (Psi := Ψs) (v := v) (V := Vs)
        (T := T) (speed := speed) hRayS hsmuls hSourceEndpointSpeed
        hsourceAnchorSpeed a a'
  have hTargetRadialRadial :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          CorrectedRadial.timeRadialScale T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.radialPart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a') := by
    intro a a'
    exact
      SpeedReconcile.target_radialPart_endpoint_pairing_eq_timeRadialScale
        (p0 := p₀) (Psi := Ψt) (v := L v) (V := Vt)
        (T := T) (speed := speed) hRayT hsmult hTargetEndpointSpeed
        htargetAnchorSpeed a a'
  have hSourceRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.radialPart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) = 0 := by
    intro a a'
    exact
      CombinedFeed.source_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
        (g := g) (x0 := x₀) (Psi := Ψs) (v := v) (Vs := Vs) (T := T)
        hRayS hsmuls hSourceTransverseOrthogonal a a'
  have hTargetRadialTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.radialPart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) = 0 := by
    intro a a'
    exact
      CombinedFeed.target_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal
        (p0 := p₀) (Psi := Ψt) (v := L v) (Vt := Vt) (T := T)
        hRayT hsmult hTargetTransverseOrthogonal a a'
  have hSourceTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric g.inner x₀
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
            ((Ψs (CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.sourceAnchorChartMetric g x₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.sourceAnchorChartMetric g x₀) v a') :=
    source_transverseTransverse_of_selector_aop_bound
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := εs) (speed := speed)
      (S := S) (aPkg := as) (α := αs) (Ψ := Ψs) (v := v) hT hbaseS
      hlinS hadds hsmuls hspeed_ne hsourceAnchorSpeed hspeed_sq hTscalar
      (R := (1 : ℝ≥0)) (by norm_num)
  have hTargetTransverseTransverse :
      ∀ a a' : E3,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            ((expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) p₀) (L v))
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
            ((Ψt (CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
          JacobiNormSystem.speedPinnedScale speed T *
            CartanMap.targetAnchorChartMetric p₀
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a)
              (T⁻¹ • CartanPullback.transversePart
                (CartanMap.targetAnchorChartMetric p₀) (L v) a') :=
    target_transverseTransverse_of_selector_aop_bound
      (p₀ := p₀) (T := T) (ε := εt) (speed := speed) (S := S)
      (aPkg := aTgt) (α := αt) (Ψ := Ψt) (v := L v) hT hbaseT hlinT
      haddt hsmult hspeed_ne htargetAnchorSpeed hspeed_sq hTscalar
      (R := (1 : ℝ≥0)) (by norm_num)
  exact
    exists_equiv_and_cartanMap_isLocalIsometry_pullback_of_angle_time_blocks
      (g := g) (x₀ := x₀) (p₀ := p₀) L
      (v := v) (Ψs := Ψs) (Ψt := Ψt) (speed := speed) (T := T)
      hTne hspeed_ne hAngle hvsrc hstrictS hstrictT
      hSourceRadialRadial hSourceRadialTransverse hSourceTransverseTransverse
      hTargetRadialRadial hTargetRadialTransverse hTargetTransverseTransverse

/--
Curvature-only final local-isometry assembly on a punctured shrunk normal ball.

The selected common time includes the final scalar norm-system floor
`T ≤ 1 / (2 * (4 * max 1 S + 1))`, where `S` bounds the source anchor
speed-square on the source hosted velocity ball.
-/
theorem cartanMap_isLocalIsometry
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ),
      ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
        ∃ A B : E3 ≃L[ℝ] E3,
          HasStrictFDerivAt
            (CartanDifferential.cartanChartMap g x₀ p₀ L)
            (CartanLocalIsometry.cartanChartDifferential L A B)
            ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
          ∀ u u' : E3,
            CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                ((expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀) (L v))
                (CartanLocalIsometry.cartanChartDifferential L A B u)
                (CartanLocalIsometry.cartanChartDifferential L A B u') =
              CovariantDerivative.chartMetric g.inner x₀
                ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) u u' := by
  rcases
      UniformFlowExport.exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (g := g) (x₀ := x₀) with
    ⟨εs, hεs_pos, δs, hδs_pos, as, αs, hα0S_full, hαderS_full,
      hαmemS_full, hαtargetS_full, hexpS_full, hsourceT⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (g := g) (x₀ := x₀) hεs_pos as with
    ⟨εlinS, hεlinS_pos, hεlinS_le, aPLS, rS, LipS, KS, hrS, hplS_uniform⟩
  rcases
      UniformFlowExport.exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨εt, hεt_pos, δt, hδt_pos, aTgt, αt, hα0T_full, hαderT_full,
      hαmemT_full, hαtargetT_full, hexpT_full, htargetT⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) hεt_pos
        aTgt with
    ⟨εlinT, hεlinT_pos, hεlinT_le, aPLT, rT, LipT, KT, hrT, hplT_uniform⟩
  rcases
      exists_source_anchor_speed_sq_bound_on_closedBall
        (g := g) (x₀ := x₀) (R := ⟨δs, hδs_pos.le⟩) with
    ⟨S, hS_nonneg, hSbound⟩
  let scalarFloor : ℝ := 1 / (2 * (4 * max (1 : ℝ) S + 1))
  let angleFloor : ℝ := Real.pi / (2 * (Real.sqrt S + 1))
  have hscalarFloor_pos : 0 < scalarFloor := by
    dsimp [scalarFloor]
    have hmax_nonneg : 0 ≤ max (1 : ℝ) S :=
      le_trans zero_le_one (le_max_left _ _)
    positivity
  have hangleFloor_pos : 0 < angleFloor := by
    dsimp [angleFloor]
    positivity
  let η : ℝ := min εs (min εt (min εlinS (min εlinT (min scalarFloor angleFloor))))
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hεs_pos
      (lt_min hεt_pos
        (lt_min hεlinS_pos
          (lt_min hεlinT_pos (lt_min hscalarFloor_pos hangleFloor_pos))))
  let T : ℝ := η / 2
  have hT_pos : 0 < T := by
    dsimp [T]
    exact half_pos hη_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hT_lt_η : T < η := by
    dsimp [T]
    linarith [hη_pos]
  have hT_le_η : T ≤ η := le_of_lt hT_lt_η
  have hη_le_εs : η ≤ εs := by
    dsimp [η]
    exact min_le_left _ _
  have hη_le_εt : η ≤ εt := by
    dsimp [η]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hη_le_εlinS : η ≤ εlinS := by
    dsimp [η]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hη_le_εlinT : η ≤ εlinT := by
    dsimp [η]
    exact (((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  have hη_le_scalarFloor : η ≤ scalarFloor := by
    dsimp [η]
    exact ((((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hη_le_angleFloor : η ≤ angleFloor := by
    dsimp [η]
    exact ((((min_le_right _ _).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hT_lt_εs : T < εs := lt_of_lt_of_le hT_lt_η hη_le_εs
  have hT_lt_εt : T < εt := lt_of_lt_of_le hT_lt_η hη_le_εt
  have hT_lt_εlinS : T < εlinS := lt_of_lt_of_le hT_lt_η hη_le_εlinS
  have hT_lt_εlinT : T < εlinT := lt_of_lt_of_le hT_lt_η hη_le_εlinT
  have hTscalar : T ≤ 1 / (2 * (4 * max (1 : ℝ) S + 1)) := by
    simpa [scalarFloor] using hT_le_η.trans hη_le_scalarFloor
  have hTangle : T ≤ Real.pi / (2 * (Real.sqrt S + 1)) := by
    simpa [angleFloor] using hT_le_η.trans hη_le_angleFloor
  rcases hsourceT T hT_pos hT_lt_εs with ⟨ρs, hρs_pos, hsource⟩
  rcases htargetT T hT_pos hT_lt_εt with ⟨ρt, hρt_pos, htarget⟩
  let C : ℝ := ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ + 1
  let ρ : ℝ := min ρs (ρt / C) / 2
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hρt_div_pos : 0 < ρt / C := div_pos hρt_pos hC_pos
  have hminρ_pos : 0 < min ρs (ρt / C) := lt_min hρs_pos hρt_div_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact half_pos hminρ_pos
  have hρ_le_ρs : ρ ≤ ρs := by
    dsimp [ρ]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_left ρs (ρt / C))
  have hρ_le_ρt_div : ρ ≤ ρt / C := by
    dsimp [ρ]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_right ρs (ρt / C))
  have hsubS : Icc (-εlinS) εlinS ⊆ Icc (-εs) εs := by
    intro s hs
    exact ⟨(neg_le_neg hεlinS_le).trans hs.1, hs.2.trans hεlinS_le⟩
  have hαderS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        HasDerivWithinAt (αs (extChartAt I3 x₀ x₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (αs (extChartAt I3 x₀ x₀, v₀) s))
          (Icc (-εlinS) εlinS) s := by
    intro v₀ hv₀ s hs
    exact (hαderS_full v₀ hv₀ s (hsubS hs)).mono hsubS
  have hαmemS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        αs (extChartAt I3 x₀ x₀, v₀) s ∈
          closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (as : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemS_full v₀ hv₀ s (hsubS hs)
  have hαtargetS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        (αs (extChartAt I3 x₀ x₀, v₀) s).1 ∈ (extChartAt I3 x₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetS_full v₀ hv₀ s (hsubS hs)
  have hexpS : ∀ v₀ : E3, ‖v₀‖ < δs →
      ∀ s ∈ Icc (0 : ℝ) εlinS,
        expAt g x₀ (s • v₀) =
          (extChartAt I3 x₀).symm
            (αs (extChartAt I3 x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpS_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinS_le⟩
  have hsubT : Icc (-εlinT) εlinT ⊆ Icc (-εt) εt := by
    intro s hs
    exact ⟨(neg_le_neg hεlinT_le).trans hs.1, hs.2.trans hεlinT_le⟩
  have hαderT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        HasDerivWithinAt (αt (extChartAt I3 p₀ p₀, v₀))
          (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
            (αt (extChartAt I3 p₀ p₀, v₀) s))
          (Icc (-εlinT) εlinT) s := by
    intro v₀ hv₀ s hs
    exact (hαderT_full v₀ hv₀ s (hsubT hs)).mono hsubT
  have hαmemT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        αt (extChartAt I3 p₀ p₀, v₀) s ∈
          closedBall (extChartAt I3 p₀ p₀, (0 : E3)) (aTgt : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemT_full v₀ hv₀ s (hsubT hs)
  have hαtargetT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        (αt (extChartAt I3 p₀ p₀, v₀) s).1 ∈ (extChartAt I3 p₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetT_full v₀ hv₀ s (hsubT hs)
  have hexpT : ∀ v₀ : E3, ‖v₀‖ < δt →
      ∀ s ∈ Icc (0 : ℝ) εlinT,
        expAt roundSphereMetric3 p₀ (s • v₀) =
          (extChartAt I3 p₀).symm
            (αt (extChartAt I3 p₀ p₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpT_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinT_le⟩
  refine ⟨ρ, hρ_pos, T, hT_pos, ?_⟩
  intro v hv hvne
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hρ_le_ρs
  have halign_norm : ‖L v‖ < ρt := by
    have hnorm_bound :
        ‖L v‖ ≤ ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (L.toContinuousLinearEquiv : E3 →L[ℝ] E3) v
    have hCnorm :
        ‖(L.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hρ_le_ρt_div
    have hCmul : C * ‖v‖ < ρt := by
      calc
        C * ‖v‖ < C * (ρt / C) := mul_lt_mul_of_pos_left hv_div hC_pos
        _ = ρt := by field_simp [ne_of_gt hC_pos]
    exact lt_of_le_of_lt (hnorm_bound.trans hCnorm) hCmul
  rcases hsource v hv_source_norm with ⟨hvsrc, hvscaledS, hbaseS⟩
  rcases htarget (L v) halign_norm with ⟨_hvtgt, hvscaledT, hbaseT⟩
  have hplS := hplS_uniform (T := T) (α := αs) (v := v) hbaseS
  have hplT := hplT_uniform (T := T) (α := αt) (v := L v) hbaseT
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (g := g) (x₀ := x₀) (δ := δs) (ε := εlinS) (T := T)
        (a := as) (α := αs) (v := v)
        hεlinS_pos hT_pos hT_lt_εlinS hvscaledS hα0S_full hαderS hαmemS
        hαtargetS hexpS hrS hplS with
    ⟨Ψs, hadds, hsmuls, hlinS, hstrictS, hRayS⟩
  rcases
      IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀)
        (δ := δt) (ε := εlinT) (T := T) (a := aTgt) (α := αt)
        (v := L v) hεlinT_pos hT_pos hT_lt_εlinT hvscaledT hα0T_full
        hαderT hαmemT hαtargetT hexpT hrT hplT with
    ⟨Ψt, haddt, hsmult, hlinT, hstrictT, hRayT⟩
  have hbaseSlin :
      EnrichedCascade.BaseCurvePackage g x₀ T εlinS as αs v :=
    IntervalAlign.baseCurvePackage_restrict_interval
      (g := g) (x₀ := x₀) (ε' := εlinS) hεlinS_le hbaseS
  have hbaseTlin :
      EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀
        T εlinT aTgt αt (L v) :=
    IntervalAlign.baseCurvePackage_restrict_interval
      (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀)
      (ε' := εlinT) hεlinT_le hbaseT
  let speed : ℝ :=
    Real.sqrt (CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v))
  have hscaled_ne : T⁻¹ • v ≠ 0 := inv_smul_ne_zero hT_ne hvne
  have hsourceMetric_pos :
      0 < CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) :=
    CartanMap.sourceAnchorChartMetric_pos g x₀ hscaled_ne
  have hspeed_pos : 0 < speed := by
    dsimp [speed]
    exact Real.sqrt_pos.mpr hsourceMetric_pos
  have hspeed_ne : speed ≠ 0 := ne_of_gt hspeed_pos
  have hsourceAnchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2 := by
    dsimp [speed]
    exact (Real.sq_sqrt hsourceMetric_pos.le).symm
  have htargetAnchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • L v) (T⁻¹ • L v) = speed ^ 2 :=
    CommonTime.target_anchorSpeed_of_source_anchorSpeed L hsourceAnchorSpeed
  have hscaled_mem : T⁻¹ • v ∈ closedBall (0 : E3) (δs : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using le_of_lt hvscaledS
  have hspeed_sq : speed ^ 2 ≤ S := by
    exact hsourceAnchorSpeed ▸ hSbound (T⁻¹ • v) hscaled_mem
  have hAngle : speed * T ∈ Ioo (0 : ℝ) Real.pi :=
    speed_mul_time_mem_Ioo_of_sq_bound hspeed_pos hspeed_sq hT_pos hTangle
  rcases
      cartanMap_isLocalIsometry_of_selector_aop_bound
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L
        (T := T) (εs := εlinS) (εt := εlinT) (speed := speed) (S := S)
        (as := as) (aTgt := aTgt) (αs := αs) (αt := αt)
        (Ψs := Ψs) (Ψt := Ψt) (v := v)
        hT_pos hTscalar hAngle hvsrc hbaseSlin hlinS hadds hsmuls hstrictS hRayS
        hbaseTlin hlinT haddt hsmult hstrictT hRayT hspeed_ne
        hsourceAnchorSpeed htargetAnchorSpeed hspeed_sq with
    ⟨A, B, _hA, _hB, hderiv, hpullback⟩
  exact ⟨A, B, hderiv, hpullback⟩

end RigidityComplete
end Poincare
