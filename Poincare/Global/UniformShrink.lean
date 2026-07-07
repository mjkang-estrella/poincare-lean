import Poincare.Global.SmallTCommon

/-!
# Ball-uniform linearized PL shrink

The shrink in `PLPackages` is determined by an operator-norm bound for the
linearized chart-geodesic coefficient.  This module records the corresponding
ball-uniform version: once the hosted base curves all remain in one closed
ball, the same linearized Picard-Lindelöf interval works for every endpoint
direction whose base curve is hosted in that ball.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformShrink

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/--
Uniform zero-centered linearized PL package on the hosted base-flow ball.

The chosen `εlin` depends only on the original hosted time margin, the
closed-ball radius, and the coefficient bound of
`linearizedGeodesicFlowOperator` on that ball.  It is therefore independent of
the endpoint direction `v`, the common time `T`, and the particular hosted base
curve, once that curve satisfies `BaseCurvePackage`.
-/
theorem exists_ball_uniform_zero_centered_linearized_pl_package
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (aBase : ℝ≥0) :
    ∃ εlin : ℝ, ∃ hεlin_pos : 0 < εlin, εlin ≤ ε₀ ∧
      ∃ aPL r Lip K : ℝ≥0, 0 < (r : ℝ) ∧
        ∀ {T : ℝ} {α : E3 × E3 → ℝ → E3 × E3} {v : E3},
          EnrichedCascade.BaseCurvePackage g x₀ T ε₀ aBase α v →
            IsPicardLindelof
              (fun s : ℝ => fun ψ : E3 × E3 =>
                linearizedGeodesicFlowOperator
                  (chartChristoffelField g x₀)
                  (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
              (tmin := -εlin) (tmax := εlin)
              ⟨(0 : ℝ), by constructor <;> linarith [hεlin_pos]⟩
              ((0 : E3), (0 : E3)) aPL r Lip K := by
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
  let K : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  let aPL : ℝ≥0 := 1
  let r : ℝ≥0 := (1 / 2 : ℝ≥0)
  let Lip : ℝ≥0 := K
  let εlin : ℝ := min ε₀ (1 / (4 * ((Lip : ℝ) + 1)))
  have hε_bound_pos : 0 < 1 / (4 * ((Lip : ℝ) + 1)) := by positivity
  have hεlin_pos : 0 < εlin := by
    dsimp [εlin]
    exact lt_min hε₀ hε_bound_pos
  have hεlin_le_ε₀ : εlin ≤ ε₀ := by
    dsimp [εlin]
    exact min_le_left _ _
  have hεlin_le_bound : εlin ≤ 1 / (4 * ((Lip : ℝ) + 1)) := by
    dsimp [εlin]
    exact min_le_right _ _
  refine ⟨εlin, hεlin_pos, hεlin_le_ε₀, aPL, r, Lip, K, ?_, ?_⟩
  · dsimp [r]
    norm_num
  · intro T α v hbase
    let γ : ℝ → E3 × E3 := fun s => α (extChartAt I3 x₀ x₀, T⁻¹ • v) s
    dsimp [EnrichedCascade.BaseCurvePackage] at hbase
    rcases hbase with
      ⟨_hγ0, hγder, _hγder0T, _hγAt, hγmem, _hγtarget,
        _hγtarget0T, _hγcut, _hγχ0T, _hspeed, _hendpoint⟩
    have hγ_cont : ContinuousOn γ (Icc (-ε₀) ε₀) :=
      HasDerivWithinAt.continuousOn hγder
    have hsub : Icc (-εlin) εlin ⊆ Icc (-ε₀) ε₀ := by
      intro s hs
      exact ⟨(neg_le_neg hεlin_le_ε₀).trans hs.1, hs.2.trans hεlin_le_ε₀⟩
    have hAγ : ContinuousOn (fun s : ℝ => A (γ s)) (Icc (-εlin) εlin) := by
      simpa [A, γ] using hA_cont.comp_continuousOn (hγ_cont.mono hsub)
    refine
      { lipschitzOnWith := ?_
        continuousOn := ?_
        norm_le := ?_
        mul_max_le := ?_ }
    · intro t ht
      have ht₀ : t ∈ Icc (-ε₀) ε₀ := hsub ht
      have hnorm : ‖A (γ t)‖ ≤ (K : ℝ) :=
        (hC (γ t) (hγmem t ht₀)).trans (le_max_left C 0)
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le hnorm).lipschitzOnWith
    · intro x _hx
      simpa [A, Γ, γ] using hAγ.clm_apply continuousOn_const
    · intro t ht x hx
      have ht₀ : t ∈ Icc (-ε₀) ε₀ := hsub ht
      have hnormA : ‖A (γ t)‖ ≤ (K : ℝ) :=
        (hC (γ t) (hγmem t ht₀)).trans (le_max_left C 0)
      have hxnorm' : ‖x - ((0 : E3), (0 : E3))‖ ≤ (1 : ℝ) := by
        simpa [aPL, Metric.mem_closedBall, dist_eq_norm] using hx
      have hxnorm : ‖x‖ ≤ (1 : ℝ) := by
        calc
          ‖x‖ ≤ ‖x - ((0 : E3), (0 : E3))‖ + ‖((0 : E3), (0 : E3))‖ :=
            norm_le_norm_sub_add x ((0 : E3), (0 : E3))
          _ ≤ 1 + 0 := by
            exact add_le_add hxnorm' (by simp)
          _ = (1 : ℝ) := by norm_num
      calc
        ‖A (γ t) x‖ ≤ ‖A (γ t)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm (A (γ t)) x
        _ ≤ (K : ℝ) * 1 := by
          gcongr
        _ = (Lip : ℝ) := by
          simp [Lip]
    · dsimp [aPL, r]
      rw [sub_zero, zero_sub, neg_neg, max_eq_left (le_of_eq rfl)]
      have hLip_nonneg : 0 ≤ (Lip : ℝ) := by positivity
      calc
        (Lip : ℝ) * εlin
            ≤ (Lip : ℝ) * (1 / (4 * ((Lip : ℝ) + 1))) := by
              exact mul_le_mul_of_nonneg_left hεlin_le_bound hLip_nonneg
        _ = (Lip : ℝ) / (4 * ((Lip : ℝ) + 1)) := by ring
        _ ≤ (1 : ℝ) / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
          nlinarith
        _ ≤ (1 : ℝ) - 1 / 2 := by norm_num

/--
Common source/target time with ball-uniform linearized PL shrinks.

The common time is selected after the two uniform linearized PL margins are
known, so `T < εlin_source` and `T < εlin_target` hold before the endpoint ball
is finalized.  The last two conjuncts instantiate the basic zero-centered PL
selectors on those aligned intervals.
-/
theorem exists_common_time_with_uniform_linearized_pl_and_basic_selectors
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ T > (0 : ℝ),
        ∃ εs : ℝ, ∃ _hεs_pos : 0 < εs,
          ∃ as : ℝ≥0, ∃ αs : E3 × E3 → ℝ → E3 × E3,
            ∃ εlin_source : ℝ, ∃ hεlin_source_pos : 0 < εlin_source,
              εlin_source ≤ εs ∧ T < εlin_source ∧
                ∃ aPLS rS LipS KS : ℝ≥0, 0 < (rS : ℝ) ∧
                  ∃ εt : ℝ, ∃ _hεt_pos : 0 < εt,
                    ∃ aTgt : ℝ≥0, ∃ αt : E3 × E3 → ℝ → E3 × E3,
                      ∃ εlin_target : ℝ, ∃ hεlin_target_pos : 0 < εlin_target,
                        εlin_target ≤ εt ∧ T < εlin_target ∧
                          ∃ aPLT rT LipT KT : ℝ≥0, 0 < (rT : ℝ) ∧
                            ∀ v : E3, ‖v‖ < ρ →
                              v ∈
                                  (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                                align v ∈
                                  (expAtChartOpenPartialHomeomorph
                                    (g := roundSphereMetric3) p₀).source ∧
                                EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v ∧
                                EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀
                                  T εt aTgt αt (align v) ∧
                                IsPicardLindelof
                                  (fun s : ℝ => fun ψ : E3 × E3 =>
                                    linearizedGeodesicFlowOperator
                                      (chartChristoffelField g x₀)
                                      (αs
                                        (extChartAt I3 x₀ x₀, T⁻¹ • v) s) ψ)
                                  (tmin := -εlin_source) (tmax := εlin_source)
                                  ⟨(0 : ℝ), by
                                    constructor <;> linarith [hεlin_source_pos]⟩
                                  ((0 : E3), (0 : E3)) aPLS rS LipS KS ∧
                                (∃ Ψs : E3 → ℝ → E3 × E3,
                                  (∀ w : E3, Ψs w 0 = ((0 : E3), T⁻¹ • w)) ∧
                                    (∀ w : E3, ∀ s ∈ Icc (-εlin_source) εlin_source,
                                      HasDerivWithinAt (Ψs w)
                                        (linearizedGeodesicFlowFieldAlong
                                          (chartChristoffelField g x₀)
                                          (fun τ : ℝ =>
                                            αs (extChartAt I3 x₀ x₀, T⁻¹ • v) τ)
                                          s (Ψs w s))
                                        (Icc (-εlin_source) εlin_source) s) ∧
                                    (∀ w w' : E3,
                                      (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1) ∧
                                    ∀ (c : ℝ) (w : E3),
                                      (Ψs (c • w) T).1 = c • (Ψs w T).1) ∧
                                IsPicardLindelof
                                  (fun s : ℝ => fun ψ : E3 × E3 =>
                                    linearizedGeodesicFlowOperator
                                      (chartChristoffelField roundSphereMetric3 p₀)
                                      (αt
                                        (extChartAt I3 p₀ p₀, T⁻¹ • align v) s) ψ)
                                  (tmin := -εlin_target) (tmax := εlin_target)
                                  ⟨(0 : ℝ), by
                                    constructor <;> linarith [hεlin_target_pos]⟩
                                  ((0 : E3), (0 : E3)) aPLT rT LipT KT ∧
                                (∃ Ψt : E3 → ℝ → E3 × E3,
                                  (∀ w : E3, Ψt w 0 = ((0 : E3), T⁻¹ • w)) ∧
                                    (∀ w : E3, ∀ s ∈ Icc (-εlin_target) εlin_target,
                                      HasDerivWithinAt (Ψt w)
                                        (linearizedGeodesicFlowFieldAlong
                                          (chartChristoffelField roundSphereMetric3 p₀)
                                          (fun τ : ℝ =>
                                            αt (extChartAt I3 p₀ p₀,
                                              T⁻¹ • align v) τ)
                                          s (Ψt w s))
                                        (Icc (-εlin_target) εlin_target) s) ∧
                                    (∀ w w' : E3,
                                      (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1) ∧
                                    ∀ (c : ℝ) (w : E3),
                                      (Ψt (c • w) T).1 = c • (Ψt w T).1) := by
  rcases
      CommonTime.exists_shrunk_cutoff_one_strictDeriv_package_for_smaller_time
        (g := g) (x₀ := x₀) with
    ⟨εs, hεs_pos, as, αs, hsourceT⟩
  rcases
      exists_ball_uniform_zero_centered_linearized_pl_package
        (g := g) (x₀ := x₀) hεs_pos as with
    ⟨εlinS, hεlinS_pos, hεlinS_le, aPLS, rS, LipS, KS, hrS, hplS_uniform⟩
  rcases
      CommonTime.exists_shrunk_cutoff_one_strictDeriv_package_for_smaller_time
        (g := roundSphereMetric3) (x₀ := p₀) with
    ⟨εt, hεt_pos, aTgt, αt, htargetT⟩
  rcases
      exists_ball_uniform_zero_centered_linearized_pl_package
        (g := roundSphereMetric3) (x₀ := p₀) hεt_pos aTgt with
    ⟨εlinT, hεlinT_pos, hεlinT_le, aPLT, rT, LipT, KT, hrT, hplT_uniform⟩
  let η : ℝ := min εs (min εt (min εlinS εlinT))
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hεs_pos (lt_min hεt_pos (lt_min hεlinS_pos hεlinT_pos))
  let T : ℝ := η / 2
  have hT_pos : 0 < T := by
    dsimp [T]
    exact half_pos hη_pos
  have hT_lt_η : T < η := by
    dsimp [T]
    linarith [hη_pos]
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
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hT_lt_εs : T < εs := lt_of_lt_of_le hT_lt_η hη_le_εs
  have hT_lt_εt : T < εt := lt_of_lt_of_le hT_lt_η hη_le_εt
  have hT_lt_εlinS : T < εlinS := lt_of_lt_of_le hT_lt_η hη_le_εlinS
  have hT_lt_εlinT : T < εlinT := lt_of_lt_of_le hT_lt_η hη_le_εlinT
  rcases hsourceT T hT_pos hT_lt_εs with ⟨ρs, hρs_pos, hsource⟩
  rcases htargetT T hT_pos hT_lt_εt with ⟨ρt, hρt_pos, htarget⟩
  let C : ℝ := ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ + 1
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
  refine
    ⟨ρ, hρ_pos, T, hT_pos, εs, hεs_pos, as, αs, εlinS, hεlinS_pos,
      hεlinS_le, hT_lt_εlinS, aPLS, rS, LipS, KS, hrS,
      εt, hεt_pos, aTgt, αt, εlinT, hεlinT_pos, hεlinT_le,
      hT_lt_εlinT, aPLT, rT, LipT, KT, hrT, ?_⟩
  intro v hv
  have hv_source_norm : ‖v‖ < ρs := hv.trans_le hρ_le_ρs
  have halign_norm : ‖align v‖ < ρt := by
    have hnorm_bound :
        ‖align v‖ ≤ ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ := by
      simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using
        ContinuousLinearMap.le_opNorm
          (align.toContinuousLinearEquiv : E3 →L[ℝ] E3) v
    have hCnorm :
        ‖(align.toContinuousLinearEquiv : E3 →L[ℝ] E3)‖ * ‖v‖ ≤ C * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp [C]; linarith) (norm_nonneg v)
    have hv_div : ‖v‖ < ρt / C := hv.trans_le hρ_le_ρt_div
    have hCmul : C * ‖v‖ < ρt := by
      calc
        C * ‖v‖ < C * (ρt / C) := mul_lt_mul_of_pos_left hv_div hC_pos
        _ = ρt := by field_simp [ne_of_gt hC_pos]
    exact lt_of_le_of_lt (hnorm_bound.trans hCnorm) hCmul
  rcases hsource v hv_source_norm with ⟨hvsrc, hbaseS, _hlinS_cond⟩
  rcases htarget (align v) halign_norm with ⟨hvtgt, hbaseT, _hlinT_cond⟩
  have hplS := hplS_uniform (T := T) (α := αs) (v := v) hbaseS
  have hplT := hplT_uniform (T := T) (α := αt) (v := align v) hbaseT
  have hTmemS : T ∈ Icc (-εlinS) εlinS :=
    ⟨by linarith [hεlinS_pos, hT_pos], le_of_lt hT_lt_εlinS⟩
  have hTmemT : T ∈ Icc (-εlinT) εlinT :=
    ⟨by linarith [hεlinT_pos, hT_pos], le_of_lt hT_lt_εlinT⟩
  rcases
      PLPackages.exists_selected_linearized_family_of_zero_centered_pl_package
        (g := g) (x₀ := x₀)
        (γ := fun τ : ℝ => αs (extChartAt I3 x₀ x₀, T⁻¹ • v) τ)
        (ε := εlinS) (T := T) hεlinS_pos hTmemS hrS hplS with
    ⟨Ψs, hΨs0, hΨsder, hΨsadd, hΨssmul⟩
  rcases
      PLPackages.exists_selected_linearized_family_of_zero_centered_pl_package
        (g := roundSphereMetric3) (x₀ := p₀)
        (γ := fun τ : ℝ => αt (extChartAt I3 p₀ p₀, T⁻¹ • align v) τ)
        (ε := εlinT) (T := T) hεlinT_pos hTmemT hrT hplT with
    ⟨Ψt, hΨt0, hΨtder, hΨtadd, hΨtsmul⟩
  exact
    ⟨hvsrc, hvtgt, hbaseS, hbaseT, hplS,
      ⟨Ψs, hΨs0, hΨsder, hΨsadd, hΨssmul⟩,
      hplT, ⟨Ψt, hΨt0, hΨtder, hΨtadd, hΨtsmul⟩⟩

end UniformShrink
end Poincare
