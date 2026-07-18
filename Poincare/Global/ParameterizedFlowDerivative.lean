import Poincare.Global.TransitionLands
import Poincare.Global.AugmentedPackage

/-!
# Restricted-parameter flow derivatives

The flow endpoint residual argument is useful even when the available family
of trajectories is parameterized by a proper linear subspace of the state
space.  This is the situation for anchored exponential charts: the anchor is
fixed and only the initial velocity varies.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {P X : Type*}
variable [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
Two trajectories in a parameterized flow remain uniformly close when their
initial states differ through a fixed continuous linear map.  This is the
pairwise estimate needed to compare the endpoint CLMs of their linearized
equations.
-/
theorem parameterizedFlow_sub_norm_le_of_initial_clm
    {F : X → X} {β : P → ℝ → X} {q₁ q₂ : P}
    (J : P →L[ℝ] X) {T a : ℝ} {K : ℝ≥0} {p : X} {t : ℝ}
    (hLip : LipschitzOnWith K F (closedBall p (a + 1)))
    (hinit : β q₂ 0 = β q₁ 0 + J (q₂ - q₁))
    (hder₁ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β q₁) (F (β q₁ τ)) (Icc (0 : ℝ) T) τ)
    (hder₂ : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β q₂) (F (β q₂ τ)) (Icc (0 : ℝ) T) τ)
    (hmem₁ : ∀ τ ∈ Icc (0 : ℝ) T, β q₁ τ ∈ closedBall p a)
    (hmem₂ : ∀ τ ∈ Icc (0 : ℝ) T, β q₂ τ ∈ closedBall p a)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖β q₂ t - β q₁ t‖ ≤
      (‖J‖ * Real.exp ((K : ℝ) * T)) * ‖q₂ - q₁‖ := by
  have hcont₁ : ContinuousOn (β q₁) (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn
      (f' := fun τ => F (β q₁ τ)) (fun τ hτ => hder₁ τ hτ)
  have hcont₂ : ContinuousOn (β q₂) (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn
      (f' := fun τ => F (β q₂ τ)) (fun τ hτ => hder₂ τ hτ)
  have hdist :
      dist (β q₂ t) (β q₁ t) ≤
        dist (β q₂ 0) (β q₁ 0) *
          Real.exp ((K : ℝ) * (t - 0)) := by
    exact
      dist_le_of_trajectories_ODE_of_mem
        (v := fun _ : ℝ => F)
        (s := fun _ : ℝ => closedBall p (a + 1))
        (K := K) (a := 0) (b := T)
        (by intro _ _; simpa using hLip)
        hcont₂
        (by
          intro τ hτ
          exact (hder₂ τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩))
        (by
          intro τ hτ
          exact closedBall_subset_closedBall (by linarith)
            (hmem₂ τ (Ico_subset_Icc_self hτ)))
        hcont₁
        (by
          intro τ hτ
          exact (hder₁ τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩))
        (by
          intro τ hτ
          exact closedBall_subset_closedBall (by linarith)
            (hmem₁ τ (Ico_subset_Icc_self hτ)))
        le_rfl t ht
  have hexp :
      Real.exp ((K : ℝ) * (t - 0)) ≤ Real.exp ((K : ℝ) * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by simpa using ht.2) K.2
  have hinitial : dist (β q₂ 0) (β q₁ 0) ≤ ‖J‖ * ‖q₂ - q₁‖ := by
    rw [hinit, dist_eq_norm]
    simpa using ContinuousLinearMap.le_opNorm J (q₂ - q₁)
  calc
    ‖β q₂ t - β q₁ t‖ = dist (β q₂ t) (β q₁ t) := by rw [dist_eq_norm]
    _ ≤ dist (β q₂ 0) (β q₁ 0) *
        Real.exp ((K : ℝ) * (t - 0)) := hdist
    _ ≤ (‖J‖ * ‖q₂ - q₁‖) * Real.exp ((K : ℝ) * T) :=
      mul_le_mul hinitial hexp (Real.exp_pos _).le
        (mul_nonneg (norm_nonneg J) (norm_nonneg (q₂ - q₁)))
    _ = (‖J‖ * Real.exp ((K : ℝ) * T)) * ‖q₂ - q₁‖ := by ring

/--
Frechet differentiability of a flow endpoint along an arbitrary normed
parameter space.  The continuous linear map `J` is the exact first-order
change of the initial state.  No extension of the parameterized flow to all
initial states is required.
-/
theorem parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
    {F : X → X} {β : P → ℝ → X} {q : P}
    {J : P →L[ℝ] X} {Ψ : P → ℝ → X} {D : P →L[ℝ] X}
    {T a : ℝ} {K : ℝ≥0} {p : X} {t : ℝ}
    (hT : 0 < T)
    (hLip : LipschitzOnWith K F (closedBall p (a + 1)))
    (hTaylor :
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
        ∀ x ∈ closedBall p (a + 1),
          ‖x - base‖ ≤ ρ →
            ‖F x - F base - fderiv ℝ F base (x - base)‖ ≤
              ε * ‖x - base‖)
    (hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β q) (F (β q τ)) (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T, β q τ ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : P),
      β (q + h) 0 = β q 0 + J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (q + h)) (F (β (q + h) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, β (q + h) τ ∈ closedBall p a)
    (hΨD : ∀ᶠ h in 𝓝 (0 : P),
      Ψ h 0 = J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ψ h)
            (fderiv ℝ F (β q τ) (Ψ h τ)) (Icc (0 : ℝ) T) τ) ∧
        Ψ h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun y : P => β y t) D q := by
  let R : P → ℝ → X := fun h τ =>
    β (q + h) τ - β q τ - Ψ h τ
  let Rder : P → ℝ → X := fun h τ =>
    F (β (q + h) τ) - F (β q τ) -
      fderiv ℝ F (β q τ) (Ψ h τ)
  let C : ℝ := Real.exp ((K : ℝ) * T) * ‖J‖
  have hT_nonneg : 0 ≤ T := hT.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hIco_subset : Ico (0 : ℝ) T ⊆ Icc (0 : ℝ) T :=
    Ico_subset_Icc_self
  have hclose : ∀ᶠ h in 𝓝 (0 : P),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖β (q + h) τ - β q τ‖ ≤ C * ‖h‖ := by
    filter_upwards [hpert] with h hh
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hpert_cont : ContinuousOn (β (q + h)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (q + h) r)) (by
          intro r hr
          simpa using hh.2.1 r hr)
    have hbase_cont : ContinuousOn (β q) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β q r)) (by
          intro r hr
          simpa using hbase_der r hr)
    have hdist :
        dist (β (q + h) τ) (β q τ) ≤
          dist (β (q + h) 0) (β q 0) *
            Real.exp ((K : ℝ) * (τ - 0)) := by
      exact
        dist_le_of_trajectories_ODE_of_mem
          (v := fun _ : ℝ => F)
          (s := fun _ : ℝ => closedBall p (a + 1))
          (K := K) (a := 0) (b := T)
          (by
            intro _ _
            simpa using hLip)
          hpert_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hh.2.1 r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hh.2.2 r (hIco_subset hr)))
          hbase_cont
          (by
            intro r hr
            have hrIcc : r ∈ Icc (0 : ℝ) T := hIco_subset hr
            exact (hbase_der r hrIcc).mono_of_mem_nhdsWithin
              (Icc_mem_nhdsGE_of_mem ⟨hr.1, hr.2⟩))
          (by
            intro r hr
            exact closedBall_subset_closedBall (by linarith)
              (hbase_mem r (hIco_subset hr)))
          le_rfl τ hτIcc
    have hexp_le :
        Real.exp ((K : ℝ) * (τ - 0)) ≤ Real.exp ((K : ℝ) * T) := by
      apply Real.exp_le_exp.mpr
      have hK_nonneg : 0 ≤ (K : ℝ) := K.2
      nlinarith [hτIcc.2]
    have hinitial : dist (β (q + h) 0) (β q 0) ≤ ‖J‖ * ‖h‖ := by
      rw [hh.1, dist_eq_norm]
      simpa using ContinuousLinearMap.le_opNorm J h
    calc
      ‖β (q + h) τ - β q τ‖ = dist (β (q + h) τ) (β q τ) := by
        rw [dist_eq_norm]
      _ ≤ dist (β (q + h) 0) (β q 0) *
          Real.exp ((K : ℝ) * (τ - 0)) := hdist
      _ ≤ (‖J‖ * ‖h‖) * Real.exp ((K : ℝ) * T) :=
        mul_le_mul hinitial hexp_le (Real.exp_pos _).le
          (mul_nonneg (norm_nonneg J) (norm_nonneg h))
      _ = C * ‖h‖ := by
        simp [C]
        ring
  have hRcont : ∀ᶠ h in 𝓝 (0 : P),
      ContinuousOn (R h) (Icc (0 : ℝ) T) := by
    filter_upwards [hpert, hΨD] with h hh hlin
    have hpert_cont : ContinuousOn (β (q + h)) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β (q + h) r)) (by
          intro r hr
          simpa using hh.2.1 r hr)
    have hbase_cont : ContinuousOn (β q) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => F (β q r)) (by
          intro r hr
          simpa using hbase_der r hr)
    have hΨ_cont : ContinuousOn (Ψ h) (Icc (0 : ℝ) T) := by
      exact HasDerivWithinAt.continuousOn
        (f' := fun r => fderiv ℝ F (β q r) (Ψ h r)) (by
          intro r hr
          exact hlin.2.1 r hr)
    simpa [R] using (hpert_cont.sub hbase_cont).sub hΨ_cont
  have hRderiv : ∀ᶠ h in 𝓝 (0 : P),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (R h) (Rder h τ) (Ici τ) τ := by
    filter_upwards [hpert, hΨD] with h hh hlin
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    have hnhds : Icc (0 : ℝ) T ∈ 𝓝[Ici τ] τ :=
      Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩
    have hpert_der :
        HasDerivWithinAt (β (q + h))
          (F (β (q + h) τ)) (Ici τ) τ := by
      simpa using (hh.2.1 τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hbase_der' :
        HasDerivWithinAt (β q) (F (β q τ)) (Ici τ) τ := by
      simpa using (hbase_der τ hτIcc).mono_of_mem_nhdsWithin hnhds
    have hΨ_der' :
        HasDerivWithinAt (Ψ h)
          (fderiv ℝ F (β q τ) (Ψ h τ)) (Ici τ) τ := by
      simpa using (hlin.2.1 τ hτIcc).mono_of_mem_nhdsWithin hnhds
    simpa [R, Rder] using (hpert_der.sub hbase_der').sub hΨ_der'
  have hR0 : ∀ᶠ h in 𝓝 (0 : P), R h 0 = 0 := by
    filter_upwards [hpert, hΨD] with h hh hlin
    simp [R, hh.1, hlin.1]
  have hbound : ∀ μ > (0 : ℝ), ∀ᶠ h in 𝓝 (0 : P),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖Rder h τ‖ ≤ (K : ℝ) * ‖R h τ‖ + μ * ‖h‖ := by
    intro μ hμ
    let θ : ℝ := μ / (C + 1)
    have hden_pos : 0 < C + 1 := by positivity
    have hθ_pos : 0 < θ := by
      dsimp [θ]
      positivity
    have hθC_le : θ * C ≤ μ := by
      dsimp [θ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
      nlinarith [hμ.le, hC_nonneg]
    rcases hTaylor θ hθ_pos with ⟨ρ, hρ_pos, hrem⟩
    have hsmall : ∀ᶠ h in 𝓝 (0 : P), C * ‖h‖ ≤ ρ :=
      eventually_const_mul_norm_le_nhds_zero_normed
        (P := P) hC_nonneg hρ_pos
    filter_upwards [hpert, hclose, hsmall] with h hh hhclose hsmall_h
    intro τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) T := hIco_subset hτ
    let base : X := β q τ
    let x : X := β (q + h) τ
    let A : X →L[ℝ] X := fderiv ℝ F base
    have hbase_mem_small : base ∈ closedBall p a := by
      simpa [base] using hbase_mem τ hτIcc
    have hx_mem_small : x ∈ closedBall p a := by
      simpa [x] using hh.2.2 τ hτIcc
    have hbase_mem_wide : base ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hbase_mem_small
    have hx_mem_wide : x ∈ closedBall p (a + 1) :=
      closedBall_subset_closedBall (by linarith) hx_mem_small
    have hdiff : ‖x - base‖ ≤ C * ‖h‖ := by
      simpa [x, base] using hhclose τ hτ
    have hcloseρ : ‖x - base‖ ≤ ρ := hdiff.trans hsmall_h
    have hremθ :
        ‖F x - F base - A (x - base)‖ ≤ θ * ‖x - base‖ := by
      simpa [A] using hrem base hbase_mem_wide x hx_mem_wide hcloseρ
    have hremμ :
        ‖F x - F base - A (x - base)‖ ≤ μ * ‖h‖ := by
      calc
        ‖F x - F base - A (x - base)‖ ≤ θ * ‖x - base‖ := hremθ
        _ ≤ θ * (C * ‖h‖) :=
          mul_le_mul_of_nonneg_left hdiff hθ_pos.le
        _ = (θ * C) * ‖h‖ := by ring
        _ ≤ μ * ‖h‖ :=
          mul_le_mul_of_nonneg_right hθC_le (norm_nonneg h)
    have hbase_nhds : closedBall p (a + 1) ∈ 𝓝 base :=
      closedBall_radius_add_one_mem_nhds hbase_mem_small
    have hAnorm : ‖A‖ ≤ (K : ℝ) := by
      have hfd : ‖fderiv ℝ F base‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hbase_nhds hLip
      simpa [A] using hfd
    have hlinear :
        ‖A (x - base - Ψ h τ)‖ ≤
          (K : ℝ) * ‖x - base - Ψ h τ‖ := by
      calc
        ‖A (x - base - Ψ h τ)‖ ≤ ‖A‖ * ‖x - base - Ψ h τ‖ :=
          ContinuousLinearMap.le_opNorm A (x - base - Ψ h τ)
        _ ≤ (K : ℝ) * ‖x - base - Ψ h τ‖ :=
          mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _)
    have hrewrite :
        Rder h τ =
          (F x - F base - A (x - base)) + A (x - base - Ψ h τ) := by
      simp only [Rder, A, x, base, map_sub]
      abel
    have hraw :
        ‖Rder h τ‖ ≤
          (K : ℝ) * ‖x - base - Ψ h τ‖ + μ * ‖h‖ := by
      calc
        ‖Rder h τ‖ =
            ‖(F x - F base - A (x - base)) +
                A (x - base - Ψ h τ)‖ := by rw [hrewrite]
        _ ≤ ‖F x - F base - A (x - base)‖ +
              ‖A (x - base - Ψ h τ)‖ := norm_add_le _ _
        _ ≤ μ * ‖h‖ + (K : ℝ) * ‖x - base - Ψ h τ‖ :=
          add_le_add hremμ hlinear
        _ = (K : ℝ) * ‖x - base - Ψ h τ‖ + μ * ‖h‖ := by ring
    simpa [R, Rder, x, base] using hraw
  have hunif :
      ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝 (0 : P),
        ∀ τ ∈ Icc (0 : ℝ) T, ‖R h τ‖ ≤ ε * ‖h‖ :=
    residual_uniform_isLittleO_on_Icc_of_gronwall_bound_param
      (R := R) (R' := Rder) hT_nonneg K.2 hRcont hRderiv hR0 hbound
  have hres :
      (fun h : P => R h t) =o[𝓝 (0 : P)] (fun h : P => h) :=
    residual_isLittleO_at_fixedTime_of_uniform_param (R := R) hunif ht
  have hres' :
      (fun h : P => β (q + h) t - β q t - D h)
        =o[𝓝 (0 : P)] (fun h : P => h) := by
    rw [isLittleO_iff] at hres ⊢
    intro c hc
    filter_upwards [hres hc, hΨD] with h hsmall hlin
    simpa [R, hlin.2.2] using hsmall
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only using hres'

namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
On a compact augmented-state ball, the second-variation coefficient has a
uniform operator-norm bound and is Lipschitz.  These are the two compact
constants needed for pairwise Gronwall comparison of restricted endpoint
derivatives.
-/
theorem exists_chartChristoffel_secondVariationCoefficient_bounds_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (p : A) (a : ℝ) :
    ∃ K L : ℝ≥0,
      (∀ z ∈ closedBall p a,
        ‖fderiv ℝ
          (augmentedGeodesicFlowField (chartChristoffelField g x₀)) z‖ ≤
          (K : ℝ)) ∧
      LipschitzOnWith L
        (fun z : A =>
          fderiv ℝ
            (augmentedGeodesicFlowField (chartChristoffelField g x₀)) z)
        (closedBall p a) := by
  let F : A → A := augmentedGeodesicFlowField (chartChristoffelField g x₀)
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
        (g := g) (x₀ := x₀) (p := (0 : A)) (a := 0) with
    ⟨hF2, _hLip⟩
  have hF1 : ContDiff ℝ 1 F := by
    simpa [F] using hF2.of_le (by norm_num)
  rcases
      hF1.contDiffOn.exists_lipschitzOnWith
        (by norm_num) (convex_closedBall p (a + 1))
        (isCompact_closedBall p (a + 1)) with
    ⟨K, hFLip⟩
  have hcoeff : ContDiff ℝ 1 (fun z : A => fderiv ℝ F z) := by
    simpa [F] using hF2.fderiv_right (m := 1) (by norm_num)
  rcases
      hcoeff.contDiffOn.exists_lipschitzOnWith
        (by norm_num) (convex_closedBall p a) (isCompact_closedBall p a) with
    ⟨L, hcoeffLip⟩
  refine ⟨K, L, ?_, by simpa [F] using hcoeffLip⟩
  intro z hz
  have hnhds : closedBall p (a + 1) ∈ 𝓝 z :=
    closedBall_radius_add_one_mem_nhds hz
  simpa [F] using
    (norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hnhds hFLip)

omit [T2Space M] in
/--
Restricted-parameter endpoint derivative for the augmented chart-geodesic
flow.  The second-variation family needs to exist only eventually for small
parameter increments, and its initial state is the prescribed linear change
`J h` of the anchored augmented initialization.
-/
theorem chartChristoffel_parameterizedAugmentedEndpoint_hasFDerivAt_of_secondVariation_eventually
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : P → ℝ → A} {q : P} {J : P →L[ℝ] A}
    {Ξ : P → ℝ → A} {D : P →L[ℝ] A}
    {T a : ℝ} {p : A} {t : ℝ}
    (hT : 0 < T)
    (hbase_der : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β q)
        (augmentedGeodesicFlowField (chartChristoffelField g x₀) (β q τ))
        (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T, β q τ ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : P),
      β (q + h) 0 = β q 0 + J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (q + h))
            (augmentedGeodesicFlowField
              (chartChristoffelField g x₀) (β (q + h) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, β (q + h) τ ∈ closedBall p a)
    (hΞD : ∀ᶠ h in 𝓝 (0 : P),
      Ξ h 0 = J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ h)
            (secondVariationFlowFieldAlong
              (chartChristoffelField g x₀) (β q) τ (Ξ h τ))
            (Icc (0 : ℝ) T) τ) ∧
        Ξ h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (fun y : P => β y t) D q := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : A → A := augmentedGeodesicFlowField Γ
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall
        (g := g) (x₀ := x₀) p a with
    ⟨_hF, K, hLip⟩
  have hTaylor :
      ∀ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ base ∈ closedBall p (a + 1),
        ∀ x ∈ closedBall p (a + 1),
          ‖x - base‖ ≤ ρ →
            ‖F x - F base - fderiv ℝ F base (x - base)‖ ≤
              ε * ‖x - base‖ := by
    simpa [F, Γ, secondVariationFlowOperator] using
      chartChristoffel_augmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
        (g := g) (x₀ := x₀)
        (Kset := closedBall p (a + 1))
        (isCompact_closedBall p (a + 1))
        (convex_closedBall p (a + 1))
  have hbase_der' : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β q) (F (β q τ)) (Icc (0 : ℝ) T) τ := by
    intro τ hτ
    simpa [F, Γ] using hbase_der τ hτ
  have hpert' : ∀ᶠ h in 𝓝 (0 : P),
      β (q + h) 0 = β q 0 + J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (q + h)) (F (β (q + h) τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T, β (q + h) τ ∈ closedBall p a := by
    simpa [F, Γ] using hpert
  have hΞD' : ∀ᶠ h in 𝓝 (0 : P),
      Ξ h 0 = J h ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ h)
            (fderiv ℝ F (β q τ) (Ξ h τ))
            (Icc (0 : ℝ) T) τ) ∧
        Ξ h t = D h := by
    filter_upwards [hΞD] with h hh
    exact ⟨hh.1, by
      intro τ hτ
      simpa [F, Γ, secondVariationFlowFieldAlong,
        secondVariationFlowOperator] using hh.2.1 τ hτ,
      hh.2.2⟩
  exact
    parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually
      (F := F) (β := β) (q := q) (J := J) (Ψ := Ξ) (D := D)
      (T := T) (a := a) (K := K) (p := p) (t := t)
      hT hLip hTaylor hbase_der' hbase_mem hpert' hΞD' ht

end GeodesicTransport

end Poincare
