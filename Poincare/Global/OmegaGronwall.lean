import Poincare.Global.ThirdFamily
import Poincare.Global.DoublyResidual

/-!
# Omega instantiation and third-variation endpoint Gronwall bound

This module contains only the two level-three analytic facts requested by the
M5-glob-58 harness task:

1. instantiate the hosted third-variation family at the paired
   augmented/second-variation base curve;
2. prove a Gronwall endpoint Lipschitz bound for two third-variation endpoint
   CLMs whose bases are uniformly close.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
private theorem chartChristoffel_doublyAugmentedField_contDiff_two
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    let doubleF : A × A → A × A := fun y =>
      let F : A → A :=
        augmentedGeodesicFlowField (chartChristoffelField g x₀)
      (F y.1, (fderiv ℝ F y.1) y.2)
    ContDiff ℝ 2 doubleF := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  have hΓ : ContDiff ℝ 4 Γ := by
    rw [contDiff_iff_contDiffAt]
    intro q
    have hfive_le_top : (5 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      rw [show (5 : ℕ∞ω) = ((5 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hfive_add_one_le_top : (5 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
      rw [show (5 : ℕ∞ω) + 1 = ((6 : ℕ∞) : ℕ∞ω) from rfl,
        show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
      exact WithTop.coe_le_coe.mpr le_top
    have hg5 :
        ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 5
          (fun y : M =>
            (⟨y, g.inner y⟩ :
              TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
                (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
      simpa using g.contMDiff_inner.of_le hfive_le_top
    have hblend :
        ContDiff ℝ (4 + 1)
          (CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀) := by
      simpa using
        (CovariantDerivative.contDiff_blendedChartMetric
          (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
          hfive_add_one_le_top (cutoff_contDiff (n := n) x₀)
          (cutoff_tsupport (n := n) x₀) hg5)
    apply contDiffAt_clm_of_apply
    intro u
    apply contDiffAt_clm_of_apply
    intro v
    simpa [Γ, chartChristoffelField] using
      (CovariantDerivative.contDiffAt_christoffelAt
        (G := CovariantDerivative.blendedChartMetric (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (k := 4) (x := q)
        hblend
        (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
          (backgroundMetric (n := n)) g.inner x₀)
        (CovariantDerivative.chartBilin_nondegenerate
          (cutoff (n := n) x₀) (backgroundMetric (n := n))
          (backgroundMetric_pos (n := n)) g.inner
          (fun y u hu => g.inner_pos y (v := u) hu) x₀
          (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
          (cutoff_support_invertible (n := n) x₀))
        (fun z v w => rfl) v u)
  have hF : ContDiff ℝ 4 (geodesicFlowField Γ) := by
    have hp : ContDiff ℝ 4 (fun q : E × E => q.1) := contDiff_fst
    have hv : ContDiff ℝ 4 (fun q : E × E => q.2) := contDiff_snd
    have hΓp : ContDiff ℝ 4 (fun q : E × E => Γ q.1) := hΓ.comp hp
    have hΓpv : ContDiff ℝ 4 (fun q : E × E => Γ q.1 q.2) :=
      hΓp.clm_apply hv
    have hΓpvv : ContDiff ℝ 4 (fun q : E × E => Γ q.1 q.2 q.2) :=
      hΓpv.clm_apply hv
    simpa [geodesicFlowField, Γ] using hv.prodMk hΓpvv.neg
  let F₀ : E × E → E × E := geodesicFlowField Γ
  have haug : ContDiff ℝ 3 (augmentedGeodesicFlowField Γ) := by
    have hbase : ContDiff ℝ 3 (fun y : A => F₀ y.1) :=
      (hF.of_le (by norm_num)).comp contDiff_fst
    have hlin :
        ContDiff ℝ 3
          (fun y : A => (fderiv ℝ F₀ y.1 : (E × E) →L[ℝ] (E × E)) y.2) := by
      simpa [F₀] using
        (hF.contDiff_fderiv_apply (m := 3) (by norm_num))
    simpa [augmentedGeodesicFlowField, linearizedGeodesicFlowOperator, F₀, Γ] using
      hbase.prodMk hlin
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y => (F y.1, (fderiv ℝ F y.1) y.2)
  have hbase : ContDiff ℝ 2 (fun y : A × A => F y.1) :=
    (haug.of_le (by norm_num)).comp contDiff_fst
  have hlin :
      ContDiff ℝ 2
        (fun y : A × A => (fderiv ℝ F y.1 : A →L[ℝ] A) y.2) := by
    simpa [F, Γ] using
      (haug.contDiff_fderiv_apply (m := 2) (by norm_num))
  simpa [doubleF, F, Γ] using hbase.prodMk hlin

omit [T2Space M] in
private theorem exists_lipschitzOnWith_chartChristoffel_thirdVariation_coefficient_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (p : A × A) (a : ℝ) :
    let doubleF : A × A → A × A := fun y =>
      let F : A → A :=
        augmentedGeodesicFlowField (chartChristoffelField g x₀)
      (F y.1, (fderiv ℝ F y.1) y.2)
    ContDiff ℝ 2 doubleF ∧
      ∃ K : ℝ≥0,
        LipschitzOnWith K (fun y : A × A => fderiv ℝ doubleF y)
          (closedBall p (a + 1)) := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y => (F y.1, (fderiv ℝ F y.1) y.2)
  have hdouble : ContDiff ℝ 2 doubleF := by
    simpa [doubleF, F, Γ] using
      chartChristoffel_doublyAugmentedField_contDiff_two (g := g) (x₀ := x₀)
  constructor
  · exact hdouble
  have hcoeff : ContDiff ℝ 1 (fun y : A × A => fderiv ℝ doubleF y) :=
    hdouble.fderiv_right (m := 1) (by norm_num)
  exact
    hcoeff.contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall p (a + 1))
      (isCompact_closedBall p (a + 1))

private theorem linearODE_endpoint_clm_lipschitz_of_coefficients
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A₁ A₂ : ℝ → X →L[ℝ] X}
    {Ω₁ Ω₂ : X → ℝ → X} {D₁ D₂ : X →L[ℝ] X}
    {K L δnorm T t : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hL : 0 ≤ L) (hδ : 0 ≤ δnorm)
    (hA₁op : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₁ τ‖ ≤ K)
    (hA₂op : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₂ τ‖ ≤ K)
    (hAdiff : ∀ τ ∈ Ico (0 : ℝ) T, ‖A₂ τ - A₁ τ‖ ≤ L * δnorm)
    (hΩ₁0 : ∀ h : X, Ω₁ h 0 = h)
    (hΩ₂0 : ∀ h : X, Ω₂ h 0 = h)
    (hΩ₁der : ∀ h : X, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h) (A₁ τ (Ω₁ h τ)) (Icc (0 : ℝ) T) τ)
    (hΩ₂der : ∀ h : X, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h) (A₂ τ (Ω₂ h τ)) (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : X, Ω₁ h t = D₁ h)
    (hD₂ : ∀ h : X, Ω₂ h t = D₂ h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖D₂ - D₁‖ ≤
      (L * Real.exp (K * T) * gronwallBound 0 K 1 T) * δnorm := by
  let Cgr : ℝ := gronwallBound 0 K 1 T
  have hCgr_nonneg : 0 ≤ Cgr := by
    have hmono : Monotone (gronwallBound 0 K 1) :=
      gronwallBound_mono (by norm_num) (by norm_num) hK
    have h0T := hmono hT
    simpa [Cgr, gronwallBound_x0] using h0T
  have hM_nonneg :
      0 ≤ (L * Real.exp (K * T) * Cgr) * δnorm := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hL (Real.exp_pos _).le) hCgr_nonneg) hδ
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
      ‖Ω₁ h τ‖ ≤ ‖h‖ * Real.exp (K * T) := by
    intro τ hτ
    have hbound : ∀ s ∈ Ico (0 : ℝ) T,
        ‖A₁ s (Ω₁ h s)‖ ≤ K * ‖Ω₁ h s‖ + 0 := by
      intro s hs
      calc
        ‖A₁ s (Ω₁ h s)‖ ≤ ‖A₁ s‖ * ‖Ω₁ h s‖ :=
          ContinuousLinearMap.le_opNorm (A₁ s) (Ω₁ h s)
        _ ≤ K * ‖Ω₁ h s‖ := by
          exact mul_le_mul_of_nonneg_right (hA₁op s hs) (norm_nonneg _)
        _ = K * ‖Ω₁ h s‖ + 0 := by ring
    have hgr :
        ‖Ω₁ h τ‖ ≤ gronwallBound ‖h‖ K 0 (τ - 0) :=
      norm_le_gronwallBound_of_norm_deriv_right_le
        (f := Ω₁ h) (f' := fun s => A₁ s (Ω₁ h s))
        (δ := ‖h‖) (K := K) (ε := 0)
        (a := 0) (b := T) hΩ₁cont hΩ₁derIci (by rw [hΩ₁0 h]) hbound τ hτ
    have hpoint : ‖Ω₁ h τ‖ ≤ ‖h‖ * Real.exp (K * τ) := by
      simpa [sub_zero, gronwallBound_ε0] using hgr
    have hexp : Real.exp (K * τ) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 hK)
    exact hpoint.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg h))
  have hRcont :
      ContinuousOn (fun τ : ℝ => Ω₂ h τ - Ω₁ h τ) (Icc (0 : ℝ) T) :=
    hΩ₂cont.sub hΩ₁cont
  have hRderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => Ω₂ h s - Ω₁ h s)
        (A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)) (Ici τ) τ := by
    intro τ hτ
    exact (hΩ₂derIci τ hτ).sub (hΩ₁derIci τ hτ)
  let η : ℝ := (L * δnorm) * (‖h‖ * Real.exp (K * T))
  have hη_nonneg : 0 ≤ η := by
    exact mul_nonneg (mul_nonneg hL hδ)
      (mul_nonneg (norm_nonneg h) (Real.exp_pos _).le)
  have hRbound : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)‖ ≤
        K * ‖Ω₂ h τ - Ω₁ h τ‖ + η := by
    intro τ hτ
    have hsplit :
        A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ) =
          A₂ τ (Ω₂ h τ - Ω₁ h τ) + (A₂ τ - A₁ τ) (Ω₁ h τ) := by
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
    have hforce :
        ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ ≤ η := by
      have hΩ := hΩ₁norm τ (Ico_subset_Icc_self hτ)
      calc
        ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ ≤
            ‖A₂ τ - A₁ τ‖ * ‖Ω₁ h τ‖ :=
          ContinuousLinearMap.le_opNorm (A₂ τ - A₁ τ) (Ω₁ h τ)
        _ ≤ (L * δnorm) * (‖h‖ * Real.exp (K * T)) :=
          mul_le_mul (hAdiff τ hτ) hΩ (norm_nonneg _)
            (mul_nonneg hL hδ)
        _ = η := rfl
    calc
      ‖A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ)‖ =
          ‖A₂ τ (Ω₂ h τ - Ω₁ h τ) + (A₂ τ - A₁ τ) (Ω₁ h τ)‖ := by
            rw [hsplit]
      _ ≤ ‖A₂ τ (Ω₂ h τ - Ω₁ h τ)‖ +
          ‖(A₂ τ - A₁ τ) (Ω₁ h τ)‖ :=
            norm_add_le _ _
      _ ≤ K * ‖Ω₂ h τ - Ω₁ h τ‖ + η :=
            add_le_add hlinear hforce
  have hR0 : (fun τ : ℝ => Ω₂ h τ - Ω₁ h τ) 0 = 0 := by
    simp [hΩ₂0 h, hΩ₁0 h]
  have hgr :
      ‖Ω₂ h t - Ω₁ h t‖ ≤ gronwallBound 0 K η t :=
    gronwall_residual_norm_le
      (R := fun τ : ℝ => Ω₂ h τ - Ω₁ h τ)
      (R' := fun τ : ℝ => A₂ τ (Ω₂ h τ) - A₁ τ (Ω₁ h τ))
      (K := K) (η := η) (T := T) hRcont hRderiv hR0 hRbound ht
  have hmono : Monotone (gronwallBound 0 K 1) :=
    gronwallBound_mono (by norm_num) (by norm_num) hK
  have hgrT :
      ‖Ω₂ h t - Ω₁ h t‖ ≤ η * Cgr := by
    calc
      ‖Ω₂ h t - Ω₁ h t‖ ≤ gronwallBound 0 K η t := hgr
      _ = η * gronwallBound 0 K 1 t := by
        rw [gronwallBound_zero_left_mul]
      _ ≤ η * Cgr := by
        exact mul_le_mul_of_nonneg_left (hmono ht.2) hη_nonneg
  calc
    ‖(D₂ - D₁) h‖ = ‖D₂ h - D₁ h‖ := by rfl
    _ = ‖Ω₂ h t - Ω₁ h t‖ := by rw [hD₂ h, hD₁ h]
    _ ≤ η * Cgr := hgrT
    _ = ((L * Real.exp (K * T) * Cgr) * δnorm) * ‖h‖ := by
      ring

omit [T2Space M] in
/--
The concrete hosted third-variation family obtained by applying
`ThirdFamily.exists_hosted_thirdVariation_solution_family_on_pl_closedBall`
to the paired augmented/second-variation base curve
`τ ↦ (β y.1 τ, Ξ y.1 y.2 τ)`.
-/
theorem exists_hosted_thirdVariation_solution_family_on_paired_base
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (fun τ : ℝ => (β y.1 τ, Ξ y.1 y.2 τ))) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ a r : ℝ≥0, 0 < r ∧
      ∃ Ω : A × A → ℝ → A × A,
        ∀ h : A × A, h ∈ closedBall (0 : A × A) r →
          Ω h 0 = h ∧
            (∀ t ∈ Icc (-ε) ε,
              HasDerivWithinAt (Ω h)
                (fderiv ℝ
                  (fun y' : A × A =>
                    let F : A → A :=
                      augmentedGeodesicFlowField (chartChristoffelField g x₀)
                    (F y'.1, (fderiv ℝ F y'.1) y'.2))
                  (β y.1 t, Ξ y.1 y.2 t) (Ω h t))
                (Icc (-ε) ε) t) ∧
            ∀ t ∈ Icc (-ε) ε, Ω h t ∈ closedBall (0 : A × A) a := by
  simpa using
    exists_hosted_thirdVariation_solution_family_on_pl_closedBall
      (g := g) (x₀ := x₀)
      (ζ := fun τ : ℝ => (β y.1 τ, Ξ y.1 y.2 τ)) hpaired

omit [T2Space M] in
/--
Grönwall endpoint bound for two third-variation endpoint CLMs based at nearby
doubly-augmented curves.  The coefficient Lipschitz constant is obtained from
one higher chart-Christoffel regularity of the doubly-augmented field.
-/
theorem chartChristoffel_thirdVariation_endpoint_gronwall_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ₁ ζ₂ : ℝ → A × A}
    {Ω₁ Ω₂ : A × A → ℝ → A × A}
    {D₁ D₂ : (A × A) →L[ℝ] (A × A)}
    {T a δnorm : ℝ} {p : A × A} {t : ℝ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δnorm)
    (hζ₁mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₁ τ ∈ closedBall p (a + 1))
    (hζ₂mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₂ τ ∈ closedBall p (a + 1))
    (hζdist : ∀ τ ∈ Ico (0 : ℝ) T, ‖ζ₂ τ - ζ₁ τ‖ ≤ δnorm)
    (hΩ₁0 : ∀ h : A × A, Ω₁ h 0 = h)
    (hΩ₂0 : ∀ h : A × A, Ω₂ h 0 = h)
    (hΩ₁der : ∀ h : A × A, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ₁ τ) (Ω₁ h τ))
        (Icc (0 : ℝ) T) τ)
    (hΩ₂der : ∀ h : A × A, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ₂ τ) (Ω₂ h τ))
        (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : A × A, Ω₁ h t = D₁ h)
    (hD₂ : ∀ h : A × A, Ω₂ h t = D₂ h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖D₂ - D₁‖ ≤ C * δnorm := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y => (F y.1, (fderiv ℝ F y.1) y.2)
  rcases
      exists_lipschitzOnWith_chartChristoffel_thirdVariation_coefficient_closedBall
        (g := g) (x₀ := x₀) (p := p) (a := a) with
    ⟨hdouble, L, hLipCoeff⟩
  rcases
      (isCompact_closedBall p (a + 1)).exists_bound_of_continuousOn
        ((hdouble.continuous_fderiv (by norm_num)).continuousOn) with
    ⟨K₀, hK₀⟩
  let K : ℝ := max K₀ 0
  have hK_nonneg : 0 ≤ K := le_max_right K₀ 0
  have hA₁op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ doubleF (ζ₁ τ)‖ ≤ K := by
    intro τ hτ
    exact (hK₀ (ζ₁ τ) (hζ₁mem τ hτ)).trans (le_max_left K₀ 0)
  have hA₂op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ doubleF (ζ₂ τ)‖ ≤ K := by
    intro τ hτ
    exact (hK₀ (ζ₂ τ) (hζ₂mem τ hτ)).trans (le_max_left K₀ 0)
  have hAdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ doubleF (ζ₂ τ) - fderiv ℝ doubleF (ζ₁ τ)‖ ≤
        (L : ℝ) * δnorm := by
    intro τ hτ
    calc
      ‖fderiv ℝ doubleF (ζ₂ τ) - fderiv ℝ doubleF (ζ₁ τ)‖ =
          dist (fderiv ℝ doubleF (ζ₂ τ)) (fderiv ℝ doubleF (ζ₁ τ)) := by
            rw [dist_eq_norm]
      _ ≤ (L : ℝ) * dist (ζ₂ τ) (ζ₁ τ) :=
          hLipCoeff.dist_le_mul (ζ₂ τ) (hζ₂mem τ hτ) (ζ₁ τ) (hζ₁mem τ hτ)
      _ = (L : ℝ) * ‖ζ₂ τ - ζ₁ τ‖ := by
          rw [dist_eq_norm]
      _ ≤ (L : ℝ) * δnorm :=
          mul_le_mul_of_nonneg_left (hζdist τ hτ) L.2
  let C : ℝ := (L : ℝ) * Real.exp (K * T) * gronwallBound 0 K 1 T
  have hC_nonneg : 0 ≤ C := by
    have hCgr_nonneg : 0 ≤ gronwallBound 0 K 1 T := by
      have hmono : Monotone (gronwallBound 0 K 1) :=
        gronwallBound_mono (by norm_num) (by norm_num) hK_nonneg
      have h0T := hmono hT
      simpa [gronwallBound_x0] using h0T
    exact mul_nonneg (mul_nonneg L.2 (Real.exp_pos _).le) hCgr_nonneg
  use C
  constructor
  · exact hC_nonneg
  have hmain :
      ‖D₂ - D₁‖ ≤ C * δnorm := by
    simpa [C, doubleF, F, Γ] using
      linearODE_endpoint_clm_lipschitz_of_coefficients
        (A₁ := fun τ : ℝ => fderiv ℝ doubleF (ζ₁ τ))
        (A₂ := fun τ : ℝ => fderiv ℝ doubleF (ζ₂ τ))
        (Ω₁ := Ω₁) (Ω₂ := Ω₂) (D₁ := D₁) (D₂ := D₂)
        (K := K) (L := (L : ℝ)) (δnorm := δnorm) (T := T) (t := t)
        hT hK_nonneg L.2 hδ hA₁op hA₂op hAdiff hΩ₁0 hΩ₂0
        (by
          intro h τ hτ
          simpa [doubleF, F, Γ] using hΩ₁der h τ hτ)
        (by
          intro h τ hτ
          simpa [doubleF, F, Γ] using hΩ₂der h τ hτ)
        hD₁ hD₂ ht
  exact hmain

end GeodesicTransport
end Poincare
