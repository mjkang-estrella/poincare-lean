import Poincare.Global.OmegaGronwall
import Poincare.Global.EnrichedCascade
import Poincare.Global.FlowSmoothness

/-!
# Projected linear-ODE endpoint Gronwall estimate

This file generalizes the endpoint-operator estimate in `OmegaGronwall` to
the shape used by first variations of a geodesic flow: the parameter space,
ODE state space, and endpoint space may differ, and fixed continuous linear
maps inject the initial parameter and project the terminal state.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

/--
Two linear ODE families with the same injected initial value have projected
endpoint operators that are Lipschitz in a uniform perturbation of their
coefficients.

This is the exact analytic shape needed for first variations: `J` inserts an
endpoint direction as the initial linearized state and `P` extracts the
position component at the terminal time.
-/
theorem projected_linearODE_endpoint_clm_lipschitz_of_coefficients
    {H X Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A₁ A₂ : ℝ → X →L[ℝ] X}
    {Ω₁ Ω₂ : H → ℝ → X} {D₁ D₂ : H →L[ℝ] Y}
    (J : H →L[ℝ] X) (P : X →L[ℝ] Y)
    {K L δnorm T t : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hL : 0 ≤ L) (hδ : 0 ≤ δnorm)
    (hA₁op : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₁ τ‖ ≤ K)
    (hA₂op : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₂ τ‖ ≤ K)
    (hAdiff : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₂ τ - A₁ τ‖ ≤ L * δnorm)
    (hΩ₁0 : ∀ h : H, Ω₁ h 0 = J h)
    (hΩ₂0 : ∀ h : H, Ω₂ h 0 = J h)
    (hΩ₁der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h) (A₁ τ (Ω₁ h τ)) (Icc (0 : ℝ) T) τ)
    (hΩ₂der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h) (A₂ τ (Ω₂ h τ)) (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : H, D₁ h = P (Ω₁ h t))
    (hD₂ : ∀ h : H, D₂ h = P (Ω₂ h t))
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖D₂ - D₁‖ ≤
      (‖P‖ * ‖J‖ * L * Real.exp (K * T) * gronwallBound 0 K 1 T) *
        δnorm := by
  let Cgr : ℝ := gronwallBound 0 K 1 T
  have hCgr_nonneg : 0 ≤ Cgr := by
    have hmono : Monotone (gronwallBound 0 K 1) :=
      gronwallBound_mono (by norm_num) (by norm_num) hK
    have h0T := hmono hT
    simpa [Cgr, gronwallBound_x0] using h0T
  have hM_nonneg :
      0 ≤
        (‖P‖ * ‖J‖ * L * Real.exp (K * T) * Cgr) * δnorm := by
    positivity
  apply ContinuousLinearMap.opNorm_le_bound (D₂ - D₁) hM_nonneg
  intro h
  have hΩ₁cont : ContinuousOn (Ω₁ h) (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn
      (f' := fun τ => A₁ τ (Ω₁ h τ))
      (by intro τ hτ; exact hΩ₁der h τ hτ)
  have hΩ₂cont : ContinuousOn (Ω₂ h) (Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn
      (f' := fun τ => A₂ τ (Ω₂ h τ))
      (by intro τ hτ; exact hΩ₂der h τ hτ)
  have hΩ₁derIci : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h) (A₁ τ (Ω₁ h τ)) (Ici τ) τ := by
    intro τ hτ
    exact (hΩ₁der h τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩)
  have hΩ₂derIci : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h) (A₂ τ (Ω₂ h τ)) (Ici τ) τ := by
    intro τ hτ
    exact (hΩ₂der h τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩)
  have hΩ₁norm : ∀ τ ∈ Icc (0 : ℝ) T,
      ‖Ω₁ h τ‖ ≤ ‖J‖ * ‖h‖ * Real.exp (K * T) := by
    intro τ hτ
    have hbound : ∀ s ∈ Ico (0 : ℝ) T,
        ‖A₁ s (Ω₁ h s)‖ ≤ K * ‖Ω₁ h s‖ + 0 := by
      intro s hs
      calc
        ‖A₁ s (Ω₁ h s)‖ ≤ ‖A₁ s‖ * ‖Ω₁ h s‖ :=
          ContinuousLinearMap.le_opNorm (A₁ s) (Ω₁ h s)
        _ ≤ K * ‖Ω₁ h s‖ :=
          mul_le_mul_of_nonneg_right (hA₁op s hs) (norm_nonneg _)
        _ = K * ‖Ω₁ h s‖ + 0 := by ring
    have hgr :
        ‖Ω₁ h τ‖ ≤ gronwallBound ‖J h‖ K 0 (τ - 0) :=
      norm_le_gronwallBound_of_norm_deriv_right_le
        (f := Ω₁ h) (f' := fun s => A₁ s (Ω₁ h s))
        (δ := ‖J h‖) (K := K) (ε := 0)
        (a := 0) (b := T) hΩ₁cont hΩ₁derIci
        (by rw [hΩ₁0 h]) hbound τ hτ
    have hpoint : ‖Ω₁ h τ‖ ≤ ‖J h‖ * Real.exp (K * τ) := by
      simpa [sub_zero, gronwallBound_ε0] using hgr
    have hJ : ‖J h‖ ≤ ‖J‖ * ‖h‖ := ContinuousLinearMap.le_opNorm J h
    have hexp : Real.exp (K * τ) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hK)
    calc
      ‖Ω₁ h τ‖ ≤ ‖J h‖ * Real.exp (K * τ) := hpoint
      _ ≤ (‖J‖ * ‖h‖) * Real.exp (K * T) :=
        mul_le_mul hJ hexp (Real.exp_pos _).le
          (mul_nonneg (norm_nonneg J) (norm_nonneg h))
      _ = ‖J‖ * ‖h‖ * Real.exp (K * T) := rfl
  have hRcont :
      ContinuousOn (fun τ : ℝ => Ω₂ h τ - Ω₁ h τ) (Icc (0 : ℝ) T) :=
    hΩ₂cont.sub hΩ₁cont
  have hRderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => Ω₂ h s - Ω₁ h s)
        (A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)) (Ici τ) τ := by
    intro τ hτ
    exact (hΩ₂derIci τ hτ).sub (hΩ₁derIci τ hτ)
  let η : ℝ :=
    (L * δnorm) * (‖J‖ * ‖h‖ * Real.exp (K * T))
  have hη_nonneg : 0 ≤ η := by
    dsimp [η]
    positivity
  have hRbound : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)‖ ≤
        K * ‖Ω₂ h τ - Ω₁ h τ‖ + η := by
    intro τ hτ
    have hsplit :
        A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ) =
          A₂ τ (Ω₂ h τ - Ω₁ h τ) +
            (A₂ τ - A₁ τ) (Ω₁ h τ) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    have hlinear :
        ‖A₂ τ (Ω₂ h τ - Ω₁ h τ)‖ ≤
          K * ‖Ω₂ h τ - Ω₁ h τ‖ := by
      calc
        ‖A₂ τ (Ω₂ h τ - Ω₁ h τ)‖ ≤
            ‖A₂ τ‖ * ‖Ω₂ h τ - Ω₁ h τ‖ :=
          ContinuousLinearMap.le_opNorm (A₂ τ) (Ω₂ h τ - Ω₁ h τ)
        _ ≤ K * ‖Ω₂ h τ - Ω₁ h τ‖ :=
          mul_le_mul_of_nonneg_right (hA₂op τ hτ) (norm_nonneg _)
    have hforce : ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ ≤ η := by
      have hΩ := hΩ₁norm τ (Ico_subset_Icc_self hτ)
      calc
        ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ ≤
            ‖A₂ τ - A₁ τ‖ * ‖Ω₁ h τ‖ :=
          ContinuousLinearMap.le_opNorm (A₂ τ - A₁ τ) (Ω₁ h τ)
        _ ≤ (L * δnorm) *
            (‖J‖ * ‖h‖ * Real.exp (K * T)) :=
          mul_le_mul (hAdiff τ hτ) hΩ (norm_nonneg _)
            (mul_nonneg hL hδ)
        _ = η := rfl
    calc
      ‖A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)‖ =
          ‖A₂ τ (Ω₂ h τ - Ω₁ h τ) +
            (A₂ τ - A₁ τ) (Ω₁ h τ)‖ := by rw [hsplit]
      _ ≤ ‖A₂ τ (Ω₂ h τ - Ω₁ h τ)‖ +
          ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ := norm_add_le _ _
      _ ≤ K * ‖Ω₂ h τ - Ω₁ h τ‖ + η :=
        add_le_add hlinear hforce
  have hR0 : (fun τ : ℝ => Ω₂ h τ - Ω₁ h τ) 0 = 0 := by
    change Ω₂ h 0 - Ω₁ h 0 = 0
    rw [hΩ₂0 h, hΩ₁0 h]
    simp
  have hgr :
      ‖Ω₂ h t - Ω₁ h t‖ ≤ gronwallBound 0 K η t :=
    gronwall_residual_norm_le
      (R := fun τ : ℝ => Ω₂ h τ - Ω₁ h τ)
      (R' := fun τ : ℝ => A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ))
      (K := K) (η := η) (T := T) hRcont hRderiv hR0 hRbound ht
  have hmono : Monotone (gronwallBound 0 K 1) :=
    gronwallBound_mono (by norm_num) (by norm_num) hK
  have hgrT : ‖Ω₂ h t - Ω₁ h t‖ ≤ η * Cgr := by
    calc
      ‖Ω₂ h t - Ω₁ h t‖ ≤ gronwallBound 0 K η t := hgr
      _ = η * gronwallBound 0 K 1 t := by
        rw [gronwallBound_zero_left_mul]
      _ ≤ η * Cgr := mul_le_mul_of_nonneg_left (hmono ht.2) hη_nonneg
  have hP :
      ‖P (Ω₂ h t - Ω₁ h t)‖ ≤ ‖P‖ * ‖Ω₂ h t - Ω₁ h t‖ :=
    ContinuousLinearMap.le_opNorm P (Ω₂ h t - Ω₁ h t)
  calc
    ‖(D₂ - D₁) h‖ = ‖P (Ω₂ h t - Ω₁ h t)‖ := by
      simp only [ContinuousLinearMap.sub_apply, hD₂ h, hD₁ h, map_sub]
    _ ≤ ‖P‖ * ‖Ω₂ h t - Ω₁ h t‖ := hP
    _ ≤ ‖P‖ * (η * Cgr) :=
      mul_le_mul_of_nonneg_left hgrT (norm_nonneg P)
    _ = ((‖P‖ * ‖J‖ * L * Real.exp (K * T) * Cgr) * δnorm) * ‖h‖ := by
      dsimp [η]
      ring

/--
Base-curve form of
`projected_linearODE_endpoint_clm_lipschitz_of_coefficients`.

If the derivative of the nonlinear vector field is Lipschitz on a common
tube, then a uniform bound on the distance between two base curves gives the
required coefficient perturbation automatically.
-/
theorem projected_linearODE_endpoint_clm_lipschitz_of_base_curves
    {H X Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X → X} {γ₁ γ₂ : ℝ → X}
    {Ω₁ Ω₂ : H → ℝ → X} {D₁ D₂ : H →L[ℝ] Y}
    (J : H →L[ℝ] X) (P : X →L[ℝ] Y)
    {S : Set X} {K : ℝ} {L B : ℝ≥0} {δnorm T t : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 ≤ δnorm)
    (hcoeff : LipschitzOnWith L (fun x : X => fderiv ℝ F x) S)
    (hγ₁mem : ∀ τ ∈ Ico (0 : ℝ) T, γ₁ τ ∈ S)
    (hγ₂mem : ∀ τ ∈ Ico (0 : ℝ) T, γ₂ τ ∈ S)
    (hγdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖γ₂ τ - γ₁ τ‖ ≤ (B : ℝ) * δnorm)
    (hA₁op : ∀ τ ∈ Ico (0 : ℝ) T, ‖fderiv ℝ F (γ₁ τ)‖ ≤ K)
    (hA₂op : ∀ τ ∈ Ico (0 : ℝ) T, ‖fderiv ℝ F (γ₂ τ)‖ ≤ K)
    (hΩ₁0 : ∀ h : H, Ω₁ h 0 = J h)
    (hΩ₂0 : ∀ h : H, Ω₂ h 0 = J h)
    (hΩ₁der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h)
        (fderiv ℝ F (γ₁ τ) (Ω₁ h τ)) (Icc (0 : ℝ) T) τ)
    (hΩ₂der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h)
        (fderiv ℝ F (γ₂ τ) (Ω₂ h τ)) (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : H, D₁ h = P (Ω₁ h t))
    (hD₂ : ∀ h : H, D₂ h = P (Ω₂ h t))
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖D₂ - D₁‖ ≤
      (‖P‖ * ‖J‖ * ((L : ℝ) * (B : ℝ)) * Real.exp (K * T) *
          gronwallBound 0 K 1 T) * δnorm := by
  have hAdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ F (γ₂ τ) - fderiv ℝ F (γ₁ τ)‖ ≤
        ((L : ℝ) * (B : ℝ)) * δnorm := by
    intro τ hτ
    have hLip :=
      hcoeff.dist_le_mul (γ₂ τ) (hγ₂mem τ hτ) (γ₁ τ) (hγ₁mem τ hτ)
    have hLip' :
        ‖fderiv ℝ F (γ₂ τ) - fderiv ℝ F (γ₁ τ)‖ ≤
          (L : ℝ) * ‖γ₂ τ - γ₁ τ‖ := by
      simpa only [dist_eq_norm] using hLip
    calc
      ‖fderiv ℝ F (γ₂ τ) - fderiv ℝ F (γ₁ τ)‖ ≤
          (L : ℝ) * ‖γ₂ τ - γ₁ τ‖ := hLip'
      _ ≤ (L : ℝ) * ((B : ℝ) * δnorm) :=
        mul_le_mul_of_nonneg_left (hγdiff τ hτ) L.2
      _ = ((L : ℝ) * (B : ℝ)) * δnorm := by ring
  exact
    projected_linearODE_endpoint_clm_lipschitz_of_coefficients
      (A₁ := fun τ => fderiv ℝ F (γ₁ τ))
      (A₂ := fun τ => fderiv ℝ F (γ₂ τ))
      (Ω₁ := Ω₁) (Ω₂ := Ω₂) (D₁ := D₁) (D₂ := D₂)
      J P hT hK (mul_nonneg L.2 B.2) hδ hA₁op hA₂op hAdiff
      hΩ₁0 hΩ₂0 hΩ₁der hΩ₂der hD₁ hD₂ ht

namespace GeodesicTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The first-order chart geodesic vector field has the `C²` regularity
needed to make its linearized coefficient locally Lipschitz. -/
theorem geodesicFlowField_chartChristoffelField_contDiff_two
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ContDiff ℝ 2 (geodesicFlowField (chartChristoffelField g x₀)) := by
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
        (g := g) (x₀ := x₀)
        (p := (0 : (E × E) × (E × E))) (a := 0) with
    ⟨haug, _hLip⟩
  have hembed :
      ContDiff ℝ 2 (fun z : E × E => (z, (0 : E × E))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp :
      ContDiff ℝ 2
        (fun z : E × E =>
          augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (z, (0 : E × E))) :=
    haug.comp hembed
  have hfst :
      ContDiff ℝ 2
        (fun z : E × E =>
          (augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (z, (0 : E × E))).1) :=
    hcomp.fst
  simpa [augmentedGeodesicFlowField] using hfst

/--
On a compact chart-state ball, the linearized geodesic coefficient has both a
uniform operator-norm bound and a Lipschitz constant.
-/
theorem exists_chartChristoffel_linearizedCoefficient_bounds_closedBall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (p : E × E) (a : ℝ) :
    ∃ K L : ℝ≥0,
      (∀ z ∈ closedBall p a,
        ‖fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀)) z‖ ≤
          (K : ℝ)) ∧
      LipschitzOnWith L
        (fun z : E × E =>
          fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀)) z)
        (closedBall p a) := by
  let F : E × E → E × E :=
    geodesicFlowField (chartChristoffelField g x₀)
  have hF2 : ContDiff ℝ 2 F := by
    simpa [F] using
      geodesicFlowField_chartChristoffelField_contDiff_two (g := g) (x₀ := x₀)
  have hF1 : ContDiff ℝ 1 F := hF2.of_le (by norm_num)
  rcases
      hF1.contDiffOn.exists_lipschitzOnWith
        (by norm_num) (convex_closedBall p (a + 1))
        (isCompact_closedBall p (a + 1)) with
    ⟨K, hFLip⟩
  have hcoeff : ContDiff ℝ 1 (fun z : E × E => fderiv ℝ F z) :=
    hF2.fderiv_right (m := 1) (by norm_num)
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

/--
Direct first-variation endpoint estimate for two hosted exponential-chart
linearized families.

Unlike the third-variation route, this theorem compares the two linearized
ODEs themselves.  The base-curve distance and the Lipschitz dependence of the
linearized coefficient produce an operator-norm Gronwall estimate for the two
`linearizedEndpointCLM`s.
-/
theorem linearizedEndpointCLM_sub_norm_le_of_base_curve_gronwall
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {α : E × E → ℝ → E × E} {q₁ q₂ : E}
    {Ψ₁ Ψ₂ : E → ℝ → E × E} {T ε δnorm : ℝ}
    {S : Set (E × E)} {K : ℝ} {L B : ℝ≥0}
    (hT : 0 < T) (hδ : 0 ≤ δnorm)
    (hlin₁ : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q₁ Ψ₁)
    (hlin₂ : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q₂ Ψ₂)
    (hadd₁ : ∀ w w' : E,
      (Ψ₁ (w + w') T).1 = (Ψ₁ w T).1 + (Ψ₁ w' T).1)
    (hsmul₁ : ∀ (c : ℝ) (w : E),
      (Ψ₁ (c • w) T).1 = c • (Ψ₁ w T).1)
    (hadd₂ : ∀ w w' : E,
      (Ψ₂ (w + w') T).1 = (Ψ₂ w T).1 + (Ψ₂ w' T).1)
    (hsmul₂ : ∀ (c : ℝ) (w : E),
      (Ψ₂ (c • w) T).1 = c • (Ψ₂ w T).1)
    (hcoeff : LipschitzOnWith L
      (fun z : E × E =>
        fderiv ℝ
          (geodesicFlowField (chartChristoffelField g x₀)) z) S)
    (hγ₁mem : ∀ τ ∈ Ico (0 : ℝ) T,
      α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ ∈ S)
    (hγ₂mem : ∀ τ ∈ Ico (0 : ℝ) T,
      α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ ∈ S)
    (hγdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ -
          α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ‖ ≤
        (B : ℝ) * δnorm)
    (hA₁op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
          (α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ)‖ ≤ K)
    (hA₂op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
          (α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ)‖ ≤ K) :
    ‖linearizedEndpointCLM (Ψ := Ψ₂) T hadd₂ hsmul₂ -
        linearizedEndpointCLM (Ψ := Ψ₁) T hadd₁ hsmul₁‖ ≤
      (‖(ContinuousLinearMap.fst ℝ E E)‖ *
          ‖(0 : E →L[ℝ] E).prod
              (T⁻¹ • ContinuousLinearMap.id ℝ E)‖ *
          ((L : ℝ) * (B : ℝ)) * Real.exp (K * T) *
          gronwallBound 0 K 1 T) * δnorm := by
  let J : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E)
  let P : (E × E) →L[ℝ] E := ContinuousLinearMap.fst ℝ E E
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin₁ hlin₂
  rcases hlin₁ with
    ⟨hΨ₁0, _hΨ₁der_full, hΨ₁der, _hΨ₁At, _hΨ₁flow, _hΨ₁speed⟩
  rcases hlin₂ with
    ⟨hΨ₂0, _hΨ₂der_full, hΨ₂der, _hΨ₂At, _hΨ₂flow, _hΨ₂speed⟩
  have hJ_apply : ∀ w : E, J w = ((0 : E), T⁻¹ • w) := by
    intro w
    simp [J]
  have hΩ₁0 : ∀ w : E, Ψ₁ w 0 = J w := by
    intro w
    rw [hΨ₁0 w, hJ_apply]
  have hΩ₂0 : ∀ w : E, Ψ₂ w 0 = J w := by
    intro w
    rw [hΨ₂0 w, hJ_apply]
  have hD₁ : ∀ w : E,
      linearizedEndpointCLM (Ψ := Ψ₁) T hadd₁ hsmul₁ w =
        P (Ψ₁ w T) := by
    intro w
    rfl
  have hD₂ : ∀ w : E,
      linearizedEndpointCLM (Ψ := Ψ₂) T hadd₂ hsmul₂ w =
        P (Ψ₂ w T) := by
    intro w
    rfl
  have hK : 0 ≤ K :=
    (norm_nonneg
      (fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
        (α (extChartAt I x₀ x₀, T⁻¹ • q₁) 0))).trans
      (hA₁op 0 ⟨le_rfl, hT⟩)
  have hbound :=
    projected_linearODE_endpoint_clm_lipschitz_of_base_curves
      (F := geodesicFlowField (chartChristoffelField g x₀))
      (γ₁ := fun τ => α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ)
      (γ₂ := fun τ => α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ)
      (Ω₁ := Ψ₁) (Ω₂ := Ψ₂)
      (D₁ := linearizedEndpointCLM (Ψ := Ψ₁) T hadd₁ hsmul₁)
      (D₂ := linearizedEndpointCLM (Ψ := Ψ₂) T hadd₂ hsmul₂)
      J P hT.le hK hδ hcoeff hγ₁mem hγ₂mem hγdiff
      hA₁op hA₂op hΩ₁0 hΩ₂0
      (by
        intro w τ hτ
        exact hΨ₁der w τ hτ)
      (by
        intro w τ hτ
        exact hΨ₂der w τ hτ)
      hD₁ hD₂ ⟨hT.le, le_rfl⟩
  simpa [J, P] using hbound

/--
A uniform chart flow on one compact tube supplies a single constant controlling
all pairs of hosted first-variation endpoint CLMs.

The constant is chosen before the two normal vectors and before their hosted
linearized families.  Consequently this theorem has the quantifier order
required by the derivative-field coherence theorem in `SelectorAssembly`.
-/
theorem exists_uniform_linearizedEndpointCLM_gronwall_constant_of_chartFlow
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ ε : ℝ} {a : ℝ≥0} {α : E × E → ℝ → E × E} {T : ℝ}
    (hε : 0 < ε) (hT : 0 < T) (hTε : T ≤ ε)
    (hα0 : ∀ v : E, ‖v‖ < δ →
      α (extChartAt I x₀ x₀, v) 0 = (extChartAt I x₀ x₀, v))
    (hαder : ∀ v : E, ‖v‖ < δ → ∀ τ ∈ Icc (-ε) ε,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v))
        (geodesicFlowField (chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v) τ))
        (Icc (-ε) ε) τ)
    (hαmem : ∀ v : E, ‖v‖ < δ → ∀ τ ∈ Icc (-ε) ε,
      α (extChartAt I x₀ x₀, v) τ ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ)) :
    ∃ C : ℝ≥0,
      ∀ {q₁ q₂ : E} {Ψ₁ Ψ₂ : E → ℝ → E × E},
        ‖T⁻¹ • q₁‖ < δ →
        ‖T⁻¹ • q₂‖ < δ →
        EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q₁ Ψ₁ →
        EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α q₂ Ψ₂ →
        ∀ (hadd₁ : ∀ w w' : E,
            (Ψ₁ (w + w') T).1 = (Ψ₁ w T).1 + (Ψ₁ w' T).1)
          (hsmul₁ : ∀ (c : ℝ) (w : E),
            (Ψ₁ (c • w) T).1 = c • (Ψ₁ w T).1)
          (hadd₂ : ∀ w w' : E,
            (Ψ₂ (w + w') T).1 = (Ψ₂ w T).1 + (Ψ₂ w' T).1)
          (hsmul₂ : ∀ (c : ℝ) (w : E),
            (Ψ₂ (c • w) T).1 = c • (Ψ₂ w T).1),
          ‖linearizedEndpointCLM (Ψ := Ψ₂) T hadd₂ hsmul₂ -
              linearizedEndpointCLM (Ψ := Ψ₁) T hadd₁ hsmul₁‖ ≤
            (C : ℝ) * dist q₂ q₁ := by
  let p : E × E := (extChartAt I x₀ x₀, (0 : E))
  rcases
      geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        (g := g) (x₀ := x₀) p (a : ℝ) with
    ⟨Kbase, hbaseLip⟩
  rcases
      exists_chartChristoffel_linearizedCoefficient_bounds_closedBall
        (g := g) (x₀ := x₀) p (a : ℝ) with
    ⟨Kcoeff, Lcoeff, hcoeffOp, hcoeffLip⟩
  let B : ℝ≥0 :=
    ⟨Real.exp ((Kbase : ℝ) * ε) * T⁻¹, by positivity⟩
  let J : E →L[ℝ] E × E :=
    (0 : E →L[ℝ] E).prod (T⁻¹ • ContinuousLinearMap.id ℝ E)
  let C : ℝ≥0 :=
    ⟨‖(ContinuousLinearMap.fst ℝ E E)‖ * ‖J‖ *
        ((Lcoeff : ℝ) * (B : ℝ)) *
        Real.exp ((Kcoeff : ℝ) * T) *
        gronwallBound 0 (Kcoeff : ℝ) 1 T,
      by
        have hmono : Monotone (gronwallBound 0 (Kcoeff : ℝ) 1) :=
          gronwallBound_mono (by norm_num) (by norm_num) Kcoeff.2
        have hgr_nonneg :
            0 ≤ gronwallBound 0 (Kcoeff : ℝ) 1 T := by
          have h0T := hmono hT.le
          simpa [gronwallBound_x0] using h0T
        positivity⟩
  refine ⟨C, ?_⟩
  intro q₁ q₂ Ψ₁ Ψ₂ hq₁ hq₂ hlin₁ hlin₂
    hadd₁ hsmul₁ hadd₂ hsmul₂
  have hscaled₁ : T⁻¹ • q₁ ∈ ball (0 : E) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq₁
  have hscaled₂ : T⁻¹ • q₂ ∈ ball (0 : E) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq₂
  have htimeLip : ∀ τ ∈ Icc (0 : ℝ) ε,
      LipschitzOnWith
        ⟨Real.exp ((Kbase : ℝ) * ε), (Real.exp_pos _).le⟩
        (fun v : E => α (extChartAt I x₀ x₀, v) τ)
        (ball (0 : E) δ) := by
    intro τ hτ
    exact
      chart_flow_initialVelocity_lipschitzOn_of_ODE
        (g := g) (x₀ := x₀) (δ := δ) (ε := ε) (a := (a : ℝ))
        (K := Kbase) (α := α) hε hbaseLip hα0 hαder hαmem hτ
  have hγdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ -
          α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ‖ ≤
        (B : ℝ) * dist q₂ q₁ := by
    intro τ hτ
    have hτε : τ ∈ Icc (0 : ℝ) ε :=
      ⟨hτ.1, (le_of_lt hτ.2).trans hTε⟩
    have hraw :=
      (htimeLip τ hτε).dist_le_mul
        (T⁻¹ • q₂) hscaled₂ (T⁻¹ • q₁) hscaled₁
    have hTinv_pos : 0 < T⁻¹ := inv_pos.mpr hT
    have hscaled_dist :
        dist (T⁻¹ • q₂) (T⁻¹ • q₁) = T⁻¹ * dist q₂ q₁ := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : T⁻¹ • q₂ - T⁻¹ • q₁ = T⁻¹ • (q₂ - q₁) := by
        rw [smul_sub]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hTinv_pos]
    calc
      ‖α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ -
          α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ‖ =
          dist (α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ)
            (α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ) := by
              rw [dist_eq_norm]
      _ ≤ Real.exp ((Kbase : ℝ) * ε) *
          dist (T⁻¹ • q₂) (T⁻¹ • q₁) := hraw
      _ = (B : ℝ) * dist q₂ q₁ := by
        rw [hscaled_dist]
        change
          Real.exp ((Kbase : ℝ) * ε) * (T⁻¹ * dist q₂ q₁) =
            (Real.exp ((Kbase : ℝ) * ε) * T⁻¹) * dist q₂ q₁
        ring
  have hfull : ∀ τ ∈ Ico (0 : ℝ) T, τ ∈ Icc (-ε) ε := by
    intro τ hτ
    exact ⟨by linarith [hε, hτ.1], (le_of_lt hτ.2).trans hTε⟩
  have hA₁op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
          (α (extChartAt I x₀ x₀, T⁻¹ • q₁) τ)‖ ≤ (Kcoeff : ℝ) := by
    intro τ hτ
    exact hcoeffOp _ (hαmem _ hq₁ τ (hfull τ hτ))
  have hA₂op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ (geodesicFlowField (chartChristoffelField g x₀))
          (α (extChartAt I x₀ x₀, T⁻¹ • q₂) τ)‖ ≤ (Kcoeff : ℝ) := by
    intro τ hτ
    exact hcoeffOp _ (hαmem _ hq₂ τ (hfull τ hτ))
  have hbound :=
    linearizedEndpointCLM_sub_norm_le_of_base_curve_gronwall
      (g := g) (x₀ := x₀) (α := α) (q₁ := q₁) (q₂ := q₂)
      (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂) (T := T) (ε := ε)
      (δnorm := dist q₂ q₁) (S := closedBall p (a : ℝ))
      (K := (Kcoeff : ℝ)) (L := Lcoeff) (B := B)
      hT dist_nonneg hlin₁ hlin₂ hadd₁ hsmul₁ hadd₂ hsmul₂
      (by simpa [p] using hcoeffLip)
      (by
        intro τ hτ
        simpa [p] using hαmem _ hq₁ τ (hfull τ hτ))
      (by
        intro τ hτ
        simpa [p] using hαmem _ hq₂ τ (hfull τ hτ))
      hγdiff hA₁op hA₂op
  simpa [C, J] using hbound

end GeodesicTransport

end Poincare
