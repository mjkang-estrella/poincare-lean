import Poincare.Global.FixedChartUniformDifferentialPullback

/-!
# Variations along retained fixed-chart geodesics

The derivative identification includes the retained endpoint time and keeps
both the moving initial position and the inverse-time velocity normalization.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartUniformJacobiComparison
open CartanSuppliedDifferentialSuccessor FixedChartLocalSuccessorExistence
open FixedChartUniformDifferentialPullback


section LinearContinuation
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Solutions with matching values and derivatives glue at a time boundary. -/
theorem hasDerivAt_glue {f g : ℝ → X} {c : ℝ} {d : X}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (heq : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) d c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · simp
  have hr : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases h : t ≤ c
      · have : t = c := le_antisymm h ht
        subst t
        simpa using heq
      · simp only [if_neg h]
    · simpa using heq
  exact (hl.union hr).hasDerivAt (by rw [Iic_union_Ici]; exact univ_mem)

/-- A bounded continuous linear coefficient has a solution through any finite
positive time. Short fundamental solutions are continued with matching derivatives. -/
theorem exists_linearODE_on_Icc {A : ℝ → X →L[ℝ] X}
    (hA : Continuous A) (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ (K : ℝ))
    (x : X) (T : ℝ) :
    ∃ f : ℝ → X, f 0 = x ∧
      ∀ t ∈ Icc 0 T, HasDerivAt f (A t (f t)) t := by
  let δ : ℝ := 1 / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKδ : (K : ℝ) * δ ≤ 1 / 4 := by
    dsimp [δ]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    nlinarith [K.2]
  have hlocal : ∀ (c : ℝ) (y : X), ∃ f : ℝ → X, f c = y ∧
      ∀ t ∈ Ioo (c - δ) (c + δ), HasDerivAt f (A t (f t)) t := by
    intro c y
    obtain ⟨P, hP0, hP, _⟩ :=
      GeodesicFlowJointDerivative.exists_fundamentalSolution_on_prescribed_Icc hδ.le
        (hA.comp (continuous_const.add continuous_id)).continuousOn K
        (fun t _ => hK (c + t)) hKδ
    refine ⟨fun t => P (t - c) y, ?_, ?_⟩
    · simp [hP0]
    · intro t ht
      have htc : t - c ∈ Ioo (-δ) δ := by constructor <;> linarith [ht.1, ht.2]
      have hp := (hP (t - c) (Ioo_subset_Icc_self htc)).hasDerivAt
        (Icc_mem_nhds htc.1 htc.2)
      have hpy := hp.clm_apply (hasDerivAt_const (t - c) y)
      simpa using hpy.scomp t ((hasDerivAt_id t).sub_const c)
  let d := δ / 2
  have hd : 0 < d := half_pos hδ
  have hdδ : d < δ := by dsimp [d]; linarith
  have hstep : ∀ n : ℕ, ∃ f : ℝ → X, f 0 = x ∧
      ∀ t ∈ Icc 0 ((n : ℝ) * d), HasDerivAt f (A t (f t)) t := by
    intro n
    induction n with
    | zero =>
      obtain ⟨f, hf0, hf⟩ := hlocal 0 x
      refine ⟨f, hf0, ?_⟩
      intro t ht
      have : t = 0 := by simpa using ht
      subst t
      exact hf 0 ⟨by linarith, by linarith⟩
    | succ n ih =>
      obtain ⟨f, hf0, hf⟩ := ih
      let c : ℝ := (n : ℝ) * d
      have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg _) hd.le
      obtain ⟨k, hk0, hk⟩ := hlocal c (f c)
      let F : ℝ → X := fun t => if t ≤ c then f t else k t
      have hFc : F c = f c := by simp [F]
      have hkc : HasDerivAt k (A c (f c)) c := by
        simpa only [hk0] using hk c ⟨by linarith, by linarith⟩
      refine ⟨F, by simpa [F, hc] using hf0, ?_⟩
      intro t ht
      have htend : t ≤ c + d := by
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ht.2
      rcases lt_trichotomy t c with hlt | heq | hgt
      · have hft := hf t ⟨ht.1, hlt.le⟩
        have he : F =ᶠ[𝓝 t] f := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          exact if_pos hs.le
        simpa only [F, if_pos hlt.le] using hft.congr_of_eventuallyEq he
      · subst t
        simpa only [hFc] using hasDerivAt_glue (hf c ⟨hc, le_rfl⟩) hkc hk0.symm
      · have hkt := hk t ⟨by linarith, by linarith⟩
        have he : F =ᶠ[𝓝 t] k := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          exact if_neg (not_le.mpr hs)
        simpa only [F, if_neg (not_le.mpr hgt)] using hkt.congr_of_eventuallyEq he
  obtain ⟨n, hn⟩ := exists_nat_gt (T / d)
  obtain ⟨f, hf0, hf⟩ := hstep n
  refine ⟨f, hf0, fun t ht => hf t ⟨ht.1, ht.2.trans ?_⟩⟩
  exact ((div_lt_iff₀ hd).mp hn).le


/-- Continuous linear coefficients have solutions on an entire prescribed
symmetric interval, with no smallness condition on its length. -/
theorem exists_linearODE_on_symmetric_Icc {A : ℝ → X →L[ℝ] X}
    {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc (-T) T)) (x : X) :
    ∃ f : ℝ → X, f 0 = x ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt f (A t (f t)) (Icc (-T) T) t := by
  have hTT : -T ≤ T := by linarith
  let B : ℝ → X →L[ℝ] X := fun t => A (projIcc (-T) T hTT t)
  have hB : Continuous B :=
    (continuousOn_iff_continuous_restrict.mp hA).comp continuous_projIcc
  obtain ⟨k, hk⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max k 0, le_max_right _ _⟩
  have hK : ∀ t, ‖B t‖ ≤ (K : ℝ) := fun t =>
    (hk _ (projIcc (-T) T hTT t).property).trans (le_max_left _ _)
  obtain ⟨f, hf0, hf⟩ := exists_linearODE_on_Icc hB K hK x T
  obtain ⟨k, hk0, hk⟩ := exists_linearODE_on_Icc
    ((hB.comp continuous_neg).neg) K (fun t => by simpa using hK (-t)) x T
  let k' : ℝ → X := fun t => k (-t)
  have hk' : ∀ t ∈ Icc (-T) 0, HasDerivAt k' (B t (k' t)) t := by
    intro t ht
    have hnt : -t ∈ Icc 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [k'] using (hk (-t) hnt).scomp t (hasDerivAt_neg t)
  let F : ℝ → X := fun t => if t ≤ 0 then k' t else f t
  have hF0 : F 0 = x := by simp [F, k', hk0]
  have hder : ∀ t ∈ Icc (-T) T, HasDerivAt F (B t (F t)) t := by
    intro t ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · have he : F =ᶠ[𝓝 t] k' := by
        filter_upwards [Iio_mem_nhds hlt] with s hs
        exact if_pos hs.le
      simpa only [F, if_pos hlt.le] using
        (hk' t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq he
    · subst t
      have hleft : HasDerivAt k' (B 0 x) 0 := by
        simpa [k', hk0] using hk' 0 ⟨by linarith, le_rfl⟩
      have hright : HasDerivAt f (B 0 x) 0 := by
        simpa [hf0] using hf 0 ⟨le_rfl, hT⟩
      simpa only [hF0] using hasDerivAt_glue hleft hright (by simp [k', hk0, hf0])
    · have he : F =ᶠ[𝓝 t] f := by
        filter_upwards [Ioi_mem_nhds hgt] with s hs
        exact if_neg (not_le.mpr hs)
      simpa only [F, if_neg (not_le.mpr hgt)] using
        (hf t ⟨hgt.le, ht.2⟩).congr_of_eventuallyEq he
  refine ⟨F, hF0, ?_⟩
  intro t ht
  simpa only [B, projIcc_of_mem hTT ht] using (hder t ht).hasDerivWithinAt


/-- The full operator fundamental solution exists through the prescribed
endpoint, even when the short-interval Picard bound fails for that time. -/
theorem exists_fundamentalSolution_on_Icc {A : ℝ → X →L[ℝ] X}
    {T : ℝ} (hT : 0 ≤ T) (hA : ContinuousOn A (Icc (-T) T)) :
    ∃ Φ : ℝ → X →L[ℝ] X, Φ 0 = ContinuousLinearMap.id ℝ X ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt Φ ((A t).comp (Φ t)) (Icc (-T) T) t := by
  exact exists_linearODE_on_symmetric_Icc hT
    ((ContinuousLinearMap.compL ℝ X X X).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ X)

end LinearContinuation

/-- A fundamental solution for the retained flow identifies its full state
 derivative, including both endpoints of the closed time interval. -/
theorem flow_hasFDerivAt_of_fundamentalSolution {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
        (C.α q t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    HasFDerivAt (fun y => C.α y t) (Φ t) q := by
  have hF := GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two g x₀
  obtain ⟨G, hG, a, hGa⟩ :=
    GeodesicFlowJointDerivative.exists_smoothField_near_uniformFlow
      (U := Set.univ) isOpen_univ (fun _ _ => hF.contDiffAt)
      C.continuous_flow (fun _ _ _ _ => Set.mem_univ _)
  have hαG : ∀ y ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ),
      C.α y 0 = y ∧
      (∀ s ∈ Icc (-C.T) C.T, HasDerivWithinAt (C.α y)
        (G (C.α y s)) (Icc (-C.T) C.T) s) ∧
      ∀ s ∈ Icc (-C.T) C.T, C.α y s ∈ closedBall (extChartAt I x₀ x₀, 0) a := by
    intro y hy
    have hyc := ball_subset_closedBall hy
    refine ⟨(C.flow_law y hyc).1, ?_, fun s hs => (hGa y hyc s hs).1⟩
    intro s hs
    rw [(hGa y hyc s hs).2.eq_of_nhds]
    exact (C.flow_law y hyc).2 s hs
  apply GeodesicFlowJointDerivative.flow_hasFDerivAt_initialState
    (hG.of_le (by norm_num)) C.T_pos hq hαG hΦ0 ?_ ht
  intro s hs
  simpa only [(hGa q (ball_subset_closedBall hq) s hs).2.fderiv_eq] using hΦ s hs

/-- The actual coordinate exponential differentiates to the position component
of the full retained endpoint derivative, with the required inverse-time input. -/
theorem coordinateEndpoint_fderiv {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v a : E) (hv : v ∈ (C.endpoint x).source) :
    fderiv ℝ ((C.endpoint x).trans (chartAt E x₀)) v a =
      (fderiv ℝ (fun q => C.α q C.T)
        (extChartAt I x₀ x, C.T⁻¹ • v) (0, C.T⁻¹ • a)).1 := by
  have hq := C.P_source_subset hv.1.2
  have hfull := (C.endpoint_C1.contDiffAt (isOpen_ball.mem_nhds hq)).differentiableAt
    (by norm_num)
  have hs := hfull.hasFDerivAt.fst.comp v
    ((hasFDerivAt_const (extChartAt I x₀ x) v).prodMk C.timeRescaling.hasFDerivAt)
  have he : HasFDerivAt ((C.endpoint x).trans (chartAt E x₀))
      (((ContinuousLinearMap.fst ℝ E E).comp
        (fderiv ℝ (fun q => C.α q C.T) (extChartAt I x₀ x, C.T⁻¹ • v))).comp
        ((0 : E →L[ℝ] E).prod (C.timeRescaling : E →L[ℝ] E))) v := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [(C.endpoint x).open_source.mem_nhds hv] with w hw
    exact coordinateEndpoint_eq_normalizedEndpoint C x w hw
  rw [he.fderiv]
  rfl

/-- The full-time fundamental solution gives the actual exponential derivative.
This applies separately to the source patch and the round-sphere patch. -/
theorem coordinateEndpoint_fderiv_of_fundamentalSolution {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v a : E) (hv : v ∈ (C.endpoint x).source)
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
        (C.α (extChartAt I x₀ x, C.T⁻¹ • v) t)).comp (Φ t))
          (Icc (-C.T) C.T) t) :
    fderiv ℝ ((C.endpoint x).trans (chartAt E x₀)) v a =
      (Φ C.T (0, C.T⁻¹ • a)).1 := by
  have hq : (extChartAt I x₀ x, C.T⁻¹ • v) ∈
      ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := C.P_source_subset hv.1.2
  have hf := (flow_hasFDerivAt_of_fundamentalSolution C hq hΦ0 hΦ
    (show C.T ∈ Icc (-C.T) C.T from ⟨by linarith [C.T_pos], le_rfl⟩)).fderiv
  rw [coordinateEndpoint_fderiv C x v a hv, hf]

/-- Reconstruct the jointly continuous fundamental solution for the actual
retained patch on its entire time interval. Neither the flow nor its time changes. -/
theorem exists_patch_fundamentalSolution {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    ∃ Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E),
      (∀ q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ),
        Φ q 0 = ContinuousLinearMap.id ℝ (E × E)) ∧
      (∀ q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ), ∀ t ∈ Icc (-C.T) C.T,
        HasDerivWithinAt (Φ q)
          ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
            (C.α q t)).comp (Φ q t)) (Icc (-C.T) C.T) t) ∧
      (∀ q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ), ∀ t ∈ Icc (-C.T) C.T,
        HasFDerivAt (fun y => C.α y t) (Φ q t) q) ∧
      ContinuousOn (fun qt : (E × E) × ℝ => Φ qt.1 qt.2)
        (ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) ×ˢ Icc (-C.T) C.T) := by
  classical
  have hF := GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two g x₀
  have hex : ∀ q : E × E, ∃ Φ : ℝ → (E × E) →L[ℝ] (E × E),
      q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) →
      Φ 0 = ContinuousLinearMap.id ℝ (E × E) ∧
      ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
        ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
          (C.α q t)).comp (Φ t)) (Icc (-C.T) C.T) t := by
    intro q
    by_cases hq : q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ)
    · have hc : ContinuousOn
          (fun t => linearizedGeodesicFlowOperator
            (GeodesicTransport.chartChristoffelField g x₀) (C.α q t)) (Icc (-C.T) C.T) :=
        ((hF.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuous_fderiv one_ne_zero).comp_continuousOn
          (HasDerivWithinAt.continuousOn (C.flow_law q (ball_subset_closedBall hq)).2)
      obtain ⟨Φ, h0, hd⟩ := exists_fundamentalSolution_on_Icc C.T_pos.le hc
      exact ⟨Φ, fun _ => ⟨h0, hd⟩⟩
    · exact ⟨fun _ => ContinuousLinearMap.id ℝ (E × E), fun h => (hq h).elim⟩
  choose Φ hΦ using hex
  have h0 := fun q hq => (hΦ q hq).1
  have hd := fun q hq => (hΦ q hq).2
  have hcompact := ((isCompact_closedBall (extChartAt I x₀ x₀, (0 : E)) (C.r : ℝ)).prod
    isCompact_Icc).image_of_continuousOn C.continuous_flow
  obtain ⟨a, ha⟩ := hcompact.isBounded.subset_closedBall (extChartAt I x₀ x₀, 0)
  have hα : ∀ q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ),
      C.α q 0 = q ∧
      (∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt (C.α q)
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) (C.α q t))
        (Icc (-C.T) C.T) t) ∧
      ∀ t ∈ Icc (-C.T) C.T, C.α q t ∈ closedBall (extChartAt I x₀ x₀, 0) a := by
    intro q hq
    exact ⟨(C.flow_law q (ball_subset_closedBall hq)).1,
      (C.flow_law q (ball_subset_closedBall hq)).2,
      fun t ht => ha ⟨(q, t), ⟨ball_subset_closedBall hq, ht⟩, rfl⟩⟩
  exact ⟨Φ, h0, hd,
    fun q hq t ht => flow_hasFDerivAt_of_fundamentalSolution C hq (h0 q hq) (hd q hq) ht,
    GeodesicFlowJointDerivative.continuousOn_fundamentalSolution hF C.T_pos.le hα h0 hd⟩

/-- In time-one coordinates the position variation has initial value zero
and initial derivative exactly the input tangent vector. -/
theorem normalizedJacobiField_initialData {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (q : E × E) (a : E)
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
        (C.α q t)).comp (Φ t)) (Icc (-C.T) C.T) t) :
    (Φ 0 (0, C.T⁻¹ • a)).1 = 0 ∧
      HasDerivAt (fun t : ℝ => (Φ (C.T * t) (0, C.T⁻¹ • a)).1) a 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos⟩
  have hd := ((hΦ 0 (Ioo_subset_Icc_self hz)).hasDerivAt
    (Icc_mem_nhds hz.1 hz.2)).clm_apply (hasDerivAt_const 0 (0, C.T⁻¹ • a))
  have hlin : HasDerivAt (fun t => Φ t (0, C.T⁻¹ • a))
      (linearizedGeodesicFlowFieldAlong (GeodesicTransport.chartChristoffelField g x₀)
        (C.α q) 0 (Φ 0 (0, C.T⁻¹ • a))) 0 := by simpa using hd
  have hpos := GeodesicTransport.chart_linearized_fst_hasDerivAt g x₀ hlin
  have hpos' : HasDerivAt (fun t => (Φ t (0, C.T⁻¹ • a)).1)
      (Φ 0 (0, C.T⁻¹ • a)).2 (C.T * 0) := by simpa only [mul_zero] using hpos
  have hscaled := hpos'.scomp 0 (hasDerivAt_const_mul C.T)
  constructor
  · simp [hΦ0]
  · simpa [hΦ0, smul_smul, C.T_pos.ne'] using hscaled

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The remaining geometric identity compares full-time Jacobi pairings along
one source and one sphere geodesic with moving initial positions. Both velocities
belong to the actual retained endpoint domains. There is no point-dependent radius
in this assertion; uniform domain radii are already proved. -/
def MovingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ x ∈ C.anchors, ∀ p ∈ D.anchors,
  ∀ (L : CartanMap.TangentAlignment g x p) (v : E),
    let l := linear (patch C D) ⟨x, p, L⟩
    let qs : E × E := (extChartAt I x₀ x, C.T⁻¹ • v)
    let qt : E × E := (extChartAt I p₀ p, D.T⁻¹ • l v)
    v ∈ (C.endpoint x).source → l v ∈ (D.endpoint p).source →
    ∀ (Φs Φt : ℝ → (E × E) →L[ℝ] (E × E)),
      Φs 0 = ContinuousLinearMap.id ℝ (E × E) →
      (∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φs
        ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
          (C.α qs t)).comp (Φs t)) (Icc (-C.T) C.T) t) →
      Φt 0 = ContinuousLinearMap.id ℝ (E × E) →
      (∀ t ∈ Icc (-D.T) D.T, HasDerivWithinAt Φt
        ((linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀)
          (D.α qt t)).comp (Φt t)) (Icc (-D.T) D.T) t) →
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ (D.α qt D.T).1
          (Φt D.T (0, D.T⁻¹ • l a)).1 (Φt D.T (0, D.T⁻¹ • l a')).1 =
        CovariantDerivative.chartMetric g.inner x₀ (C.α qs C.T).1
          (Φs C.T (0, C.T⁻¹ • a)).1 (Φs C.T (0, C.T⁻¹ • a')).1

/-- Full-time Jacobi comparison on the actual endpoint domains implies the
frozen nonzero metric target. Compact domain and alignment bounds choose one
radius before all moving anchors, alignments, successor points, and vectors. -/
theorem target_of_movingInitialPositionJacobiComparison
    (hJacobi : MovingInitialPositionJacobiComparison g) :
    UniformNonzeroMetricPullback g := by
  intro x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨Φs, hs0, hsode, _, _⟩ := exists_patch_fundamentalSolution C
  obtain ⟨Φt, ht0, htode, _, _⟩ := exists_patch_fundamentalSolution D
  obtain ⟨b, hb, hbound⟩ := exists_uniform_linear_bound C D K H hK hKC hH hHD
  obtain ⟨ρs, hρs, hs⟩ := exists_uniform_endpoint_radius C K hK hKC
  obtain ⟨ρt, hρt, ht⟩ := exists_uniform_endpoint_radius D H hH hHD
  obtain ⟨η, hη, hnormal⟩ := exists_uniform_normal_radius C K hK hKC
    (lt_min hρs (div_pos hρt hb))
  refine ⟨η, hη, ?_⟩
  intro x hx p hp L z hz _hne
  dsimp only
  intro a a'
  let v := C.normal x z
  let l := linear (patch C D) ⟨x, p, L⟩
  obtain ⟨_, _, hv⟩ := hnormal x hx z hz
  have hsv : ‖v‖ < ρs := hv.trans_le (min_le_left _ _)
  have htv : ‖l v‖ < ρt := by
    calc
      _ ≤ ‖(l : E →L[ℝ] E)‖ * ‖v‖ := (l : E →L[ℝ] E).le_opNorm _
      _ ≤ b * ‖v‖ := mul_le_mul_of_nonneg_right (hbound x hx p hp L) (norm_nonneg _)
      _ < ρt := by
        simpa only [mul_comm b] using
          (lt_div_iff₀ hb).mp (hv.trans_le (min_le_right _ _))
  have hvs := (hs x hx v hsv).1
  have hvt := (ht p hp (l v) htv).1
  let qs : E × E := (extChartAt I x₀ x, C.T⁻¹ • v)
  let qt : E × E := (extChartAt I p₀ p, D.T⁻¹ • l v)
  have hqs : qs ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := C.P_source_subset hvs.1.2
  have hqt : qt ∈ ball (extChartAt I p₀ p₀, 0) (D.r : ℝ) := D.P_source_subset hvt.1.2
  have hj := hJacobi x₀ p₀ U V C D hcurv hU hV x (hKC hx) p (hHD hp) L v
    hvs hvt (Φs qs) (Φt qt) (hs0 qs hqs) (hsode qs hqs)
      (ht0 qt hqt) (htode qt hqt) a a'
  have hse : sourceExp (patch C D) x v = (C.α qs C.T).1 :=
    coordinateEndpoint_eq_normalizedEndpoint C x v hvs
  have hte : targetExp (patch C D) p (l v) = (D.α qt D.T).1 :=
    coordinateEndpoint_eq_normalizedEndpoint D p (l v) hvt
  have hsd : ∀ a : E, fderiv ℝ (sourceExp (patch C D) x) v a =
      (Φs qs C.T (0, C.T⁻¹ • a)).1 := fun a =>
    coordinateEndpoint_fderiv_of_fundamentalSolution C x v a hvs (hs0 qs hqs) (hsode qs hqs)
  have htd : ∀ a : E, fderiv ℝ (targetExp (patch C D) p) (l v) (l a) =
      (Φt qt D.T (0, D.T⁻¹ • l a)).1 := fun a =>
    coordinateEndpoint_fderiv_of_fundamentalSolution D p (l v) (l a) hvt
      (ht0 qt hqt) (htode qt hqt)
  change CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
    (targetExp (patch C D) p (l v))
    (fderiv ℝ (targetExp (patch C D) p) (l v) (l a))
    (fderiv ℝ (targetExp (patch C D) p) (l v) (l a')) =
    CovariantDerivative.chartMetric g.inner x₀ (sourceExp (patch C D) x v)
      (fderiv ℝ (sourceExp (patch C D) x) v a)
      (fderiv ℝ (sourceExp (patch C D) x) v a')
  rw [hse, hte, hsd a, hsd a', htd a, htd a']
  exact hj

/-- The original uniform differential interface follows from the same single
geometric remainder. -/
theorem uniformDifferentialPullback_of_movingInitialPositionJacobiComparison
    (hJacobi : MovingInitialPositionJacobiComparison g)
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    UniformDifferentialPullback (patch C D) K H :=
  uniformDifferentialPullback_of_uniformNonzeroMetricPullback
    (target_of_movingInitialPositionJacobiComparison hJacobi)
    x₀ p₀ U V C D hcurv hU hV K H hK hKC hH hHD

/-- The frozen task-8 radius conclusion, conditional only on the displayed
moving-position Jacobi identity. -/
theorem exists_radius_of_movingInitialPositionJacobiComparison
    (hJacobi : MovingInitialPositionJacobiComparison g) :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    ∃ η > (0 : ℝ), OnCompact (patch C D) K H η :=
  target_of_uniformNonzeroMetricPullback
    (target_of_movingInitialPositionJacobiComparison hJacobi)

end FixedChartUniformJacobiComparison
end Poincare
