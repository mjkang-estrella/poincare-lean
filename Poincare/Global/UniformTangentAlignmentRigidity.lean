import Poincare.Global.RigidityComplete
import Poincare.Global.TangentAlignmentFiberCompactness

/-!
# Fixed-anchor rigidity uniform over tangent alignments

The final radius in `RigidityComplete.cartanMap_isLocalIsometry` is obtained by
shrinking a source flow radius against a target flow radius divided by the
operator norm of the chosen tangent alignment.  For fixed anchors, all of the
flow, linearization, speed, and time data used before that shrink are
independent of the alignment.

This module replays that final assembly with one external positive operator
bound and quantifies the tangent alignment only after the common radius and
time have been chosen.  Compactness of the fixed-anchor alignment fiber then
supplies the bound, producing one punctured normal ball on which the full
local-isometry payload is available for every tangent alignment.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformTangentAlignmentRigidity

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport
open RigidityComplete

/--
An external positive bound for the operator norms of the fixed-anchor tangent
alignments gives one common rigidity radius and one common selector time.  The
payload is exactly the local-isometry payload of
`RigidityComplete.cartanMap_isLocalIsometry`; only the quantifier order is
strengthened so that `rho` and `T` precede the tangent alignment.
-/
theorem exists_uniform_cartanMap_isLocalIsometry_of_operatorNorm_bound
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (C : ℝ) (hC_pos : 0 < C) :
    ∃ rho > (0 : ℝ), ∃ T > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x₀ p₀),
        ‖L.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ C →
        ∀ v : E, ‖v‖ < rho → v ≠ 0 →
          ∃ A B : E ≃L[ℝ] E,
            HasStrictFDerivAt
                (expAtChartOpenPartialHomeomorph (g := g) x₀)
                (A : E →L[ℝ] E) v ∧
              HasStrictFDerivAt
                (expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀)
                (B : E →L[ℝ] E) (L v) ∧
              HasStrictFDerivAt
                (CartanDifferential.cartanChartMap g x₀ p₀ L)
                (CartanLocalIsometry.cartanChartDifferential L A B)
                ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
              ∀ u u' : E,
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
  let rho : ℝ := min ρs (ρt / C) / 2
  have hρt_div_pos : 0 < ρt / C := div_pos hρt_pos hC_pos
  have hminρ_pos : 0 < min ρs (ρt / C) := lt_min hρs_pos hρt_div_pos
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact half_pos hminρ_pos
  have hrho_le_ρs : rho ≤ ρs := by
    dsimp [rho]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_left ρs (ρt / C))
  have hrho_le_ρt_div : rho ≤ ρt / C := by
    dsimp [rho]
    exact (by linarith [hminρ_pos.le] :
      min ρs (ρt / C) / 2 ≤ min ρs (ρt / C)).trans
        (min_le_right ρs (ρt / C))
  have hsubS : Icc (-εlinS) εlinS ⊆ Icc (-εs) εs := by
    intro s hs
    exact ⟨(neg_le_neg hεlinS_le).trans hs.1, hs.2.trans hεlinS_le⟩
  have hαderS : ∀ v₀ : E, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        HasDerivWithinAt (αs (extChartAt I x₀ x₀, v₀))
          (geodesicFlowField (chartChristoffelField g x₀)
            (αs (extChartAt I x₀ x₀, v₀) s))
          (Icc (-εlinS) εlinS) s := by
    intro v₀ hv₀ s hs
    exact (hαderS_full v₀ hv₀ s (hsubS hs)).mono hsubS
  have hαmemS : ∀ v₀ : E, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        αs (extChartAt I x₀ x₀, v₀) s ∈
          closedBall (extChartAt I x₀ x₀, (0 : E)) (as : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemS_full v₀ hv₀ s (hsubS hs)
  have hαtargetS : ∀ v₀ : E, ‖v₀‖ < δs →
      ∀ s ∈ Icc (-εlinS) εlinS,
        (αs (extChartAt I x₀ x₀, v₀) s).1 ∈ (extChartAt I x₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetS_full v₀ hv₀ s (hsubS hs)
  have hexpS : ∀ v₀ : E, ‖v₀‖ < δs →
      ∀ s ∈ Icc (0 : ℝ) εlinS,
        expAt g x₀ (s • v₀) =
          (extChartAt I x₀).symm
            (αs (extChartAt I x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpS_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinS_le⟩
  have hsubT : Icc (-εlinT) εlinT ⊆ Icc (-εt) εt := by
    intro s hs
    exact ⟨(neg_le_neg hεlinT_le).trans hs.1, hs.2.trans hεlinT_le⟩
  have hαderT : ∀ v₀ : E, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        HasDerivWithinAt (αt (extChartAt I p₀ p₀, v₀))
          (geodesicFlowField (chartChristoffelField roundSphereMetric3 p₀)
            (αt (extChartAt I p₀ p₀, v₀) s))
          (Icc (-εlinT) εlinT) s := by
    intro v₀ hv₀ s hs
    exact (hαderT_full v₀ hv₀ s (hsubT hs)).mono hsubT
  have hαmemT : ∀ v₀ : E, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        αt (extChartAt I p₀ p₀, v₀) s ∈
          closedBall (extChartAt I p₀ p₀, (0 : E)) (aTgt : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmemT_full v₀ hv₀ s (hsubT hs)
  have hαtargetT : ∀ v₀ : E, ‖v₀‖ < δt →
      ∀ s ∈ Icc (-εlinT) εlinT,
        (αt (extChartAt I p₀ p₀, v₀) s).1 ∈ (extChartAt I p₀).target := by
    intro v₀ hv₀ s hs
    exact hαtargetT_full v₀ hv₀ s (hsubT hs)
  have hexpT : ∀ v₀ : E, ‖v₀‖ < δt →
      ∀ s ∈ Icc (0 : ℝ) εlinT,
        expAt roundSphereMetric3 p₀ (s • v₀) =
          (extChartAt I p₀).symm
            (αt (extChartAt I p₀ p₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexpT_full v₀ hv₀ s ⟨hs.1, hs.2.trans hεlinT_le⟩
  refine ⟨rho, hrho_pos, T, hT_pos, ?_⟩
  intro L hL v hv hvne
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hrho_le_ρs
  have halign_norm : ‖L v‖ < ρt := by
    have hnorm_bound :
        ‖L v‖ ≤ ‖(L.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (L.toContinuousLinearEquiv : E →L[ℝ] E) v
    have hCnorm :
        ‖(L.toContinuousLinearEquiv : E →L[ℝ] E)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right hL (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hrho_le_ρt_div
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
  have hscaled_mem : T⁻¹ • v ∈ closedBall (0 : E) (δs : ℝ) := by
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
    ⟨A, B, hA, hB, hderiv, hpullback⟩
  have hsourceStrict :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := g) x₀)
        (A : E →L[ℝ] E) v := by
    rw [hA]
    exact hstrictS
  have htargetStrict :
      HasStrictFDerivAt
        (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀)
        (B : E →L[ℝ] E) (L v) := by
    rw [hB]
    exact hstrictT
  exact ⟨A, B, hsourceStrict, htargetStrict, hderiv, hpullback⟩

/--
For fixed anchors, compactness of the tangent-alignment operator fiber turns
the bounded-norm theorem above into a curvature-only radius and time shared by
all tangent alignments.
-/
theorem exists_uniform_cartanMap_isLocalIsometry
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) :
    ∃ rho > (0 : ℝ), ∃ T > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x₀ p₀),
        ∀ v : E, ‖v‖ < rho → v ≠ 0 →
          ∃ A B : E ≃L[ℝ] E,
            HasStrictFDerivAt
                (expAtChartOpenPartialHomeomorph (g := g) x₀)
                (A : E →L[ℝ] E) v ∧
              HasStrictFDerivAt
                (expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀)
                (B : E →L[ℝ] E) (L v) ∧
              HasStrictFDerivAt
                (CartanDifferential.cartanChartMap g x₀ p₀ L)
                (CartanLocalIsometry.cartanChartDifferential L A B)
                ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
              ∀ u u' : E,
                CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                    ((expAtChartOpenPartialHomeomorph
                      (g := roundSphereMetric3) p₀) (L v))
                    (CartanLocalIsometry.cartanChartDifferential L A B u)
                    (CartanLocalIsometry.cartanChartDifferential L A B u') =
                  CovariantDerivative.chartMetric g.inner x₀
                    ((expAtChartOpenPartialHomeomorph (g := g) x₀) v) u u' := by
  rcases
      CartanMap.exists_pos_uniform_tangentAlignment_operatorNorm_bound
        g x₀ p₀ with
    ⟨C, hC_pos, hC⟩
  rcases
      exists_uniform_cartanMap_isLocalIsometry_of_operatorNorm_bound
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) C hC_pos with
    ⟨rho, hrho_pos, T, hT_pos, hlocal⟩
  refine ⟨rho, hrho_pos, T, hT_pos, ?_⟩
  intro L
  exact hlocal L (hC L)

end UniformTangentAlignmentRigidity
end Poincare
