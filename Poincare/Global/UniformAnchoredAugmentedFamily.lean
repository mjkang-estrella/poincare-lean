import Poincare.Global.AnchoredEndpointIdentity
import Poincare.Global.GronwallMembership
import Poincare.Global.LinearEndpointGronwall
import Poincare.Global.UniformShrink

/-!
# Uniform anchored augmented families

The uniform chart-geodesic flow and the aligned first-variation selector fit
together without another ODE choice: their product is an augmented trajectory.
This file makes that family uniform on one small normal-coordinate ball and
records its exact endpoint as the application of the derivative of the
exponential chart.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace UniformAnchoredAugmentedFamily

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/--
There is one anchored augmented trajectory family on a uniform normal ball.

For `z = (q,w)`, its initial state is
`((chart(x₀), T⁻¹q), (0,T⁻¹w))`; it solves the augmented chart-geodesic ODE;
and its first-variation position at time `T` is exactly
`fderiv expAtChart q w`.
-/
theorem exists_uniform_anchored_augmented_family_for_all_small_times
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ε > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ Kcoeff : ℝ≥0,
      ∀ T : ℝ, 0 < T → T < ε →
      ∃ ρ > (0 : ℝ), ∃ β : (E × E) → ℝ → A,
        ∀ q ∈ ball (0 : E) ρ, ∀ w : E,
          β (q, w) 0 =
              ((extChartAt I x₀ x₀, T⁻¹ • q), ((0 : E), T⁻¹ • w)) ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (β (q, w))
                (augmentedGeodesicFlowField
                  (chartChristoffelField g x₀) (β (q, w) t))
                (Icc (0 : ℝ) T) t) ∧
            (β (q, w) T).2.1 =
              fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q w ∧
            HasFDerivAt
              (expAtChartOpenPartialHomeomorph (g := g) x₀)
              (fderiv ℝ
                (expAtChartOpenPartialHomeomorph (g := g) x₀) q) q ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              β (q, w) t ∈ closedBall (0 : A)
                (C₀ + (|T⁻¹| * ‖w‖) * Real.exp ((Kcoeff : ℝ) * T)) := by
  classical
  rcases
      UniformFlowExport.exists_shrunk_cutoff_one_base_package_with_uniform_flow_for_smaller_time
        (g := g) (x₀ := x₀) with
    ⟨ε₀, hε₀, δ, _hδ, a, α, hα0, hαder₀, hαmem₀,
      hαtarget₀, hexp₀, hsmall⟩
  rcases
      UniformShrink.exists_ball_uniform_zero_centered_linearized_pl_package
        (g := g) (x₀ := x₀) hε₀ a with
    ⟨ε, hε, hεle, aPL, r, Lip, K, hr, hpl_uniform⟩
  rcases
      exists_chartChristoffel_linearizedCoefficient_bounds_closedBall
        (g := g) (x₀ := x₀)
        (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) with
    ⟨Kcoeff, _Lcoeff, hcoeffOp, _hcoeffLip⟩
  let C₀ : ℝ := ‖(extChartAt I x₀ x₀, (0 : E))‖ + (a : ℝ)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  refine ⟨ε, hε, C₀, hC₀, Kcoeff, ?_⟩
  intro T hT hT_lt_ε
  have hT_lt_ε₀ : T < ε₀ := hT_lt_ε.trans_le hεle
  rcases hsmall T hT hT_lt_ε₀ with ⟨ρ, hρ, hsource⟩
  have hsub : Icc (-ε) ε ⊆ Icc (-ε₀) ε₀ := by
    intro s hs
    exact ⟨(neg_le_neg hεle).trans hs.1, hs.2.trans hεle⟩
  have hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) s))
        (Icc (-ε) ε) s := by
    intro v₀ hv₀ s hs
    exact (hαder₀ v₀ hv₀ s (hsub hs)).mono hsub
  have hαmem : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      α (extChartAt I x₀ x₀, v₀) s ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) := by
    intro v₀ hv₀ s hs
    exact hαmem₀ v₀ hv₀ s (hsub hs)
  have hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (-ε) ε,
      (α (extChartAt I x₀ x₀, v₀) s).1 ∈ (extChartAt I x₀).target := by
    intro v₀ hv₀ s hs
    exact hαtarget₀ v₀ hv₀ s (hsub hs)
  have hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ s ∈ Icc (0 : ℝ) ε,
      expAt g x₀ (s • v₀) =
        (extChartAt I x₀).symm
          (α (extChartAt I x₀ x₀, v₀) s).1 := by
    intro v₀ hv₀ s hs
    exact hexp₀ v₀ hv₀ s ⟨hs.1, hs.2.trans hεle⟩
  have hselected : ∀ q : E, q ∈ ball (0 : E) ρ →
      ∃ Ψ : E → ℝ → E × E,
        ∃ hadd : ∀ w w' : E,
          (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1,
          ∃ hsmul : ∀ (c : ℝ) (w : E),
            (Ψ (c • w) T).1 = c • (Ψ w T).1,
            EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q Ψ ∧
              HasStrictFDerivAt
                (expAtChartOpenPartialHomeomorph (g := g) x₀)
                (linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul) q := by
    intro q hq
    have hqnorm : ‖q‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq
    rcases hsource q hqnorm with ⟨_hqsource, hqscaled, hbase⟩
    have hpl := hpl_uniform (T := T) (α := α) (v := q) hbase
    rcases
        IntervalAlign.exists_linearized_family_on_aligned_interval_of_uniform_flow
          (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (T := T)
          (a := a) (α := α) (v := q) hε hT hT_lt_ε hqscaled
          hα0 hαder hαmem hαtarget hexp hr hpl with
      ⟨Ψ, hadd, hsmul, hlin, hstrict, _hray⟩
    exact ⟨Ψ, hadd, hsmul, hlin, hstrict⟩
  let chosen : ∀ q : E, q ∈ ball (0 : E) ρ →
      E → ℝ → E × E := fun q hq => Classical.choose (hselected q hq)
  let Ψ : E → E → ℝ → E × E := fun q =>
    if hq : ‖q‖ < ρ then
      chosen q (by simpa [Metric.mem_ball, dist_eq_norm] using hq)
    else fun _ _ => (0 : E × E)
  have hΨ : ∀ q (hq : q ∈ ball (0 : E) ρ),
      ∃ hadd : ∀ w w' : E,
        (Ψ q (w + w') T).1 = (Ψ q w T).1 + (Ψ q w' T).1,
        ∃ hsmul : ∀ (c : ℝ) (w : E),
          (Ψ q (c • w) T).1 = c • (Ψ q w T).1,
          EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q (Ψ q) ∧
            HasStrictFDerivAt
              (expAtChartOpenPartialHomeomorph (g := g) x₀)
              (linearizedEndpointCLM (Ψ := Ψ q) T hadd hsmul) q := by
    intro q hq
    have hchosen := Classical.choose_spec (hselected q hq)
    have hqnorm : ‖q‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hq
    have hEq : Ψ q = chosen q hq := by
      simp only [Ψ, dif_pos hqnorm]
    rw [hEq]
    exact hchosen
  let β : (E × E) → ℝ → A := fun z t =>
    (α (extChartAt I x₀ x₀, T⁻¹ • z.1) t, Ψ z.1 z.2 t)
  refine ⟨ρ, hρ, β, ?_⟩
  intro q hq w
  rcases hΨ q hq with ⟨hadd, hsmul, hlin, hstrict⟩
  have hqnorm : ‖q‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq
  rcases hsource q hqnorm with ⟨_hqsource, hqscaled, _hbase⟩
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hlin with
    ⟨hΨ0, _hΨderFull, hΨder, _hΨAt, _hflow, _hspeed⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [β]
    rw [hα0 _ hqscaled, hΨ0 w]
  · intro t ht
    have htfull : t ∈ Icc (-ε) ε :=
      ⟨by linarith [hε, ht.1], ht.2.trans hT_lt_ε.le⟩
    have hbaseDer := (hαder _ hqscaled t htfull).mono (by
      intro s (hs : s ∈ Icc (0 : ℝ) T)
      exact ⟨by linarith [hε, hs.1], hs.2.trans hT_lt_ε.le⟩)
    have hlinDer := hΨder w t ht
    have hprod := hbaseDer.prodMk hlinDer
    simpa [β, augmentedGeodesicFlowField,
      linearizedGeodesicFlowFieldAlong] using hprod
  · simpa [β] using
      (AnchoredEndpointIdentity.linearized_position_endpoint_eq_fderiv_expAtChart_apply
        (g := g) (x0 := x₀) hadd hsmul hstrict)
  · exact
      hstrict.hasFDerivAt.congr_fderiv
        hstrict.hasFDerivAt.fderiv.symm
  · intro t ht
    have htfull : t ∈ Icc (-ε) ε :=
      ⟨by linarith [hε, ht.1], ht.2.trans hT_lt_ε.le⟩
    have hbaseMem := hαmem _ hqscaled t htfull
    have hbaseNorm :
        ‖α (extChartAt I x₀ x₀, T⁻¹ • q) t‖ ≤
          ‖(extChartAt I x₀ x₀, (0 : E))‖ + (a : ℝ) := by
      have hdist :
          ‖α (extChartAt I x₀ x₀, T⁻¹ • q) t -
              (extChartAt I x₀ x₀, (0 : E))‖ ≤ (a : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hbaseMem
      calc
        ‖α (extChartAt I x₀ x₀, T⁻¹ • q) t‖ ≤
            ‖α (extChartAt I x₀ x₀, T⁻¹ • q) t -
                (extChartAt I x₀ x₀, (0 : E))‖ +
              ‖(extChartAt I x₀ x₀, (0 : E))‖ :=
          norm_le_norm_sub_add _ _
        _ ≤ (a : ℝ) + ‖(extChartAt I x₀ x₀, (0 : E))‖ := by
          gcongr
        _ = ‖(extChartAt I x₀ x₀, (0 : E))‖ + (a : ℝ) := by
          ring
    let Aop : ℝ → (E × E) →L[ℝ] (E × E) := fun s =>
      fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
        (α (extChartAt I x₀ x₀, T⁻¹ • q) s)
    have hΨcont : ContinuousOn (Ψ q w) (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn (fun s hs => hΨder w s hs)
    have hΨderIci : ∀ s ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (Ψ q w) (Aop s (Ψ q w s)) (Ici s) s := by
      intro s hs
      have hraw := hΨder w s (Ico_subset_Icc_self hs)
      have hnhds : Icc (0 : ℝ) T ∈ 𝓝[Ici s] s :=
        Icc_mem_nhdsGE_of_mem ⟨hs.1, hs.2⟩
      simpa [Aop, linearizedGeodesicFlowFieldAlong] using
        hraw.mono_of_mem_nhdsWithin hnhds
    have hAop : ∀ s ∈ Ico (0 : ℝ) T, ‖Aop s‖ ≤ (Kcoeff : ℝ) := by
      intro s hs
      apply hcoeffOp
      exact hαmem _ hqscaled s
        ⟨by linarith [hε, hs.1], (le_of_lt hs.2).trans hT_lt_ε.le⟩
    have hΨbound :=
      GronwallMembership.linearODE_norm_le_exp_T_of_opNorm_le
        (C := (Kcoeff : ℝ))
        Kcoeff.2 hΨcont hΨderIci hAop ht
    have hΨ0norm : ‖Ψ q w 0‖ = |T⁻¹| * ‖w‖ := by
      rw [hΨ0 w, Prod.norm_def]
      simp only [norm_zero, norm_smul, Real.norm_eq_abs]
      rw [max_eq_right]
      positivity
    have hΨnorm :
        ‖Ψ q w t‖ ≤
          (|T⁻¹| * ‖w‖) * Real.exp ((Kcoeff : ℝ) * T) := by
      simpa [hΨ0norm] using hΨbound
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [β, Prod.norm_def]
    apply max_le
    · exact hbaseNorm.trans (by
        dsimp [C₀]
        exact le_add_of_nonneg_right (mul_nonneg
          (mul_nonneg (abs_nonneg _) (norm_nonneg w))
          (Real.exp_pos _).le))
    · exact hΨnorm.trans (by
        dsimp [C₀]
        exact le_add_of_nonneg_left
          (add_nonneg
            (norm_nonneg (extChartAt I x₀ x₀, (0 : E)))
            (NNReal.coe_nonneg a)))

/-- A single-time consequence of the uniform all-small-times family. -/
theorem exists_uniform_anchored_augmented_family
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ),
      ∃ β : (E × E) → ℝ → A,
        ∀ q ∈ ball (0 : E) ρ, ∀ w : E,
          β (q, w) 0 =
              ((extChartAt I x₀ x₀, T⁻¹ • q), ((0 : E), T⁻¹ • w)) ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (β (q, w))
                (augmentedGeodesicFlowField
                  (chartChristoffelField g x₀) (β (q, w) t))
                (Icc (0 : ℝ) T) t) ∧
            (β (q, w) T).2.1 =
              fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q w ∧
            HasFDerivAt
              (expAtChartOpenPartialHomeomorph (g := g) x₀)
              (fderiv ℝ
                (expAtChartOpenPartialHomeomorph (g := g) x₀) q) q ∧
            ∃ R : ℝ, 0 ≤ R ∧
              ∀ t ∈ Icc (0 : ℝ) T,
                β (q, w) t ∈ closedBall (0 : A) R := by
  rcases
      exists_uniform_anchored_augmented_family_for_all_small_times g x₀ with
    ⟨ε, hε, C₀, hC₀, Kcoeff, hfamily⟩
  let T : ℝ := ε / 2
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hTε : T < ε := by
    dsimp [T]
    linarith
  rcases hfamily T hT hTε with ⟨ρ, hρ, β, hβ⟩
  refine ⟨ρ, hρ, T, hT, β, ?_⟩
  intro q hq w
  rcases hβ q hq w with ⟨hβ0, hβder, hβend, hExpDer, hβmem⟩
  refine ⟨hβ0, hβder, hβend, hExpDer, ?_⟩
  let R : ℝ :=
    C₀ + (|T⁻¹| * ‖w‖) * Real.exp ((Kcoeff : ℝ) * T)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  exact ⟨R, hR, hβmem⟩

end UniformAnchoredAugmentedFamily
end Poincare
