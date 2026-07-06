import Poincare.Global.GeodesicDerivative

/-!
# Gronwall residual comparison for the geodesic-flow derivative

This module records the final comparison step in a spelling that Lean can type.
The schematic report statement

`(fun s => fun t => R s t) =o[𝓝 0] (fun s => fun _t => s)`

would require a normed structure on the full function space `ℝ → E`, which is
not available here.  We therefore use the equivalent uniform-on-`Icc` estimate:
for every `ε > 0`, eventually in `s`, the residual is bounded by
`ε * ‖s‖` at every time in the interval.
-/

noncomputable section

open Asymptotics Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The nonhomogeneous Gronwall comparison for a residual curve. -/
theorem gronwall_residual_norm_le
    {R R' : ℝ → X} {K η T t : ℝ}
    (hRcont : ContinuousOn R (Icc (0 : ℝ) T))
    (hRderiv : ∀ τ ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt R (R' τ) (Ici τ) τ)
    (hR0 : R 0 = 0)
    (hbound : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖R' τ‖ ≤ K * ‖R τ‖ + η)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖R t‖ ≤ gronwallBound 0 K η t := by
  have h :=
    norm_le_gronwallBound_of_norm_deriv_right_le
      (f := R) (f' := R') (δ := 0) (K := K) (ε := η)
      (a := 0) (b := T) hRcont hRderiv (by simp [hR0]) hbound t ht
  simpa using h

/-- With zero initial residual, the Gronwall bound is linear in the driving term. -/
theorem gronwallBound_zero_left_mul (K η x : ℝ) :
    gronwallBound 0 K η x = η * gronwallBound 0 K 1 x := by
  by_cases hK : K = 0
  · subst K
    simp [gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hK, gronwallBound_of_K_ne_0 hK]
    ring

/--
Algebraic source of the residual derivative bound.

For `R = q - γ - s • ψ`, the derivative residual
`F q - F γ - s • A ψ` splits as the Taylor remainder
`F q - F γ - A (q - γ)` plus the linear term `A R`.
-/
theorem residual_derivative_norm_bound_of_taylor_remainder
    {F : X → X} {A : X →L[ℝ] X} {q γ ψ R' : X} {K η s : ℝ}
    (hR' : R' = F q - F γ - s • A ψ)
    (hlinear : ‖A (q - γ - s • ψ)‖ ≤ K * ‖q - γ - s • ψ‖)
    (hrem : ‖F q - F γ - A (q - γ)‖ ≤ η * ‖s‖) :
    ‖R'‖ ≤ K * ‖q - γ - s • ψ‖ + η * ‖s‖ := by
  have hrewrite :
      R' =
        (F q - F γ - A (q - γ)) + A (q - γ - s • ψ) := by
    rw [hR']
    simp only [map_sub, map_smul]
    abel
  calc
    ‖R'‖ =
        ‖(F q - F γ - A (q - γ)) + A (q - γ - s • ψ)‖ := by
          rw [hrewrite]
    _ ≤ ‖F q - F γ - A (q - γ)‖ +
        ‖A (q - γ - s • ψ)‖ :=
          norm_add_le _ _
    _ ≤ η * ‖s‖ + K * ‖q - γ - s • ψ‖ :=
          add_le_add hrem hlinear
    _ = K * ‖q - γ - s • ψ‖ + η * ‖s‖ := by
          ring

/--
Uniform residual little-o on a closed time interval from the differential
Gronwall inequality with an arbitrarily small `‖s‖` driving coefficient.
-/
theorem residual_uniform_isLittleO_on_Icc_of_gronwall_bound
    {R R' : ℝ → ℝ → X} {K T : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hRcont : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContinuousOn (R s) (Icc (0 : ℝ) T))
    (hRderiv : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt (R s) (R' s τ) (Ici τ) τ)
    (hR0 : ∀ᶠ s in 𝓝 (0 : ℝ), R s 0 = 0)
    (hbound : ∀ η > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖R' s τ‖ ≤ K * ‖R s τ‖ + η * ‖s‖) :
    ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) T, ‖R s t‖ ≤ ε * ‖s‖ := by
  intro ε hε
  let C : ℝ := gronwallBound 0 K 1 T
  have hC_nonneg : 0 ≤ C := by
    have hmono :
        Monotone (gronwallBound 0 K 1) :=
      gronwallBound_mono (by norm_num) (by norm_num) hK
    have h0T := hmono hT
    simpa [C, gronwallBound_x0] using h0T
  let η : ℝ := ε / (C + 1)
  have hden_pos : 0 < C + 1 := by positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hηC_le : η * C ≤ ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith [hε.le, hC_nonneg]
  filter_upwards [hRcont, hRderiv, hR0, hbound η hη_pos] with
    s hscont hsderiv hs0 hsbound
  intro t ht
  have hgr :
      ‖R s t‖ ≤ gronwallBound 0 K (η * ‖s‖) t :=
    gronwall_residual_norm_le
      (R := R s) (R' := R' s) (K := K) (η := η * ‖s‖)
      hscont hsderiv hs0 hsbound ht
  calc
    ‖R s t‖ ≤ gronwallBound 0 K (η * ‖s‖) t := hgr
    _ = (η * ‖s‖) * gronwallBound 0 K 1 t := by
      rw [gronwallBound_zero_left_mul]
    _ ≤ (η * ‖s‖) * C := by
      have hmono :
          Monotone (gronwallBound 0 K 1) :=
        gronwallBound_mono (by norm_num) (by norm_num) hK
      exact mul_le_mul_of_nonneg_left (hmono ht.2)
        (mul_nonneg hη_pos.le (norm_nonneg s))
    _ ≤ ε * ‖s‖ := by
      calc
        (η * ‖s‖) * C = (η * C) * ‖s‖ := by ring
        _ ≤ ε * ‖s‖ := mul_le_mul_of_nonneg_right hηC_le (norm_nonneg s)

omit [NormedSpace ℝ X] in
/-- Fixed-time little-o extracted from the uniform-on-interval spelling. -/
theorem residual_isLittleO_at_fixedTime_of_uniform
    {R : ℝ → ℝ → X} {T t : ℝ}
    (hunif : ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Icc (0 : ℝ) T, ‖R s τ‖ ≤ ε * ‖s‖)
    (ht : t ∈ Icc (0 : ℝ) T) :
    (fun s : ℝ => R s t) =o[𝓝 (0 : ℝ)] (fun s : ℝ => s) := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [hunif c hc] with s hs
  exact hs t ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Residual for the initial-velocity variation of a first-order chart flow. -/
def initialVelocityResidual
    (α : E × E → ℝ → E × E) (z₀ v w : E) (Ψ : ℝ → E × E)
    (s t : ℝ) : E × E :=
  α (z₀, v + s • w) t - α (z₀, v) t - s • Ψ t

/--
Uniform little-o comparison for the geodesic-flow initial-velocity residual,
in the interval-uniform spelling described in the module docstring.
-/
theorem initialVelocityResidual_uniform_isLittleO_on_Icc_of_gronwall_bound
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {R' : ℝ → ℝ → E × E} {K T : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hRcont : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContinuousOn
        (fun t : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
        (Icc (0 : ℝ) T))
    (hRderiv : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun t : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
          (R' s τ) (Ici τ) τ)
    (hR0 : ∀ᶠ s in 𝓝 (0 : ℝ),
      initialVelocityResidual α z₀ v w Ψ s 0 = 0)
    (hbound : ∀ η > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖R' s τ‖ ≤
          K * ‖initialVelocityResidual α z₀ v w Ψ s τ‖ + η * ‖s‖) :
    ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖initialVelocityResidual α z₀ v w Ψ s t‖ ≤ ε * ‖s‖ := by
  exact
    residual_uniform_isLittleO_on_Icc_of_gronwall_bound
      (R := fun s t => initialVelocityResidual α z₀ v w Ψ s t)
      (R' := R') hT hK hRcont hRderiv hR0 hbound

/-- Fixed-time little-o for the initial-velocity residual. -/
theorem initialVelocityResidual_isLittleO_at_fixedTime_of_uniform
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {T t : ℝ}
    (hunif : ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Icc (0 : ℝ) T,
        ‖initialVelocityResidual α z₀ v w Ψ s τ‖ ≤ ε * ‖s‖)
    (ht : t ∈ Icc (0 : ℝ) T) :
    (fun s : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
      =o[𝓝 (0 : ℝ)] (fun s : ℝ => s) :=
  residual_isLittleO_at_fixedTime_of_uniform (R := initialVelocityResidual α z₀ v w Ψ)
    hunif ht

/--
The fixed-time derivative of the chart flow in the initial-velocity direction,
once the residual has the uniform Gronwall little-o estimate.
-/
theorem initialVelocity_hasDerivAt_of_residual_uniform_isLittleO
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {T t : ℝ}
    (hunif : ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Icc (0 : ℝ) T,
        ‖initialVelocityResidual α z₀ v w Ψ s τ‖ ≤ ε * ‖s‖)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => α (z₀, v + s • w) t) (Ψ t) 0 := by
  have hres :
      (fun s : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
        =o[𝓝 (0 : ℝ)] (fun s : ℝ => s) :=
    initialVelocityResidual_isLittleO_at_fixedTime_of_uniform
      (α := α) (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ)
      hunif ht
  rw [hasDerivAt_iff_isLittleO]
  simpa [initialVelocityResidual]
    using hres

/--
Combined derivative theorem: if the initial-velocity residual satisfies the
nonhomogeneous Gronwall hypotheses with arbitrarily small `‖s‖` driving term,
then the fixed-time derivative is the linearized solution value.
-/
theorem initialVelocity_hasDerivAt_of_gronwall_residual_bound
    {α : E × E → ℝ → E × E} {z₀ v w : E} {Ψ : ℝ → E × E}
    {R' : ℝ → ℝ → E × E} {K T t : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hRcont : ∀ᶠ s in 𝓝 (0 : ℝ),
      ContinuousOn
        (fun t : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
        (Icc (0 : ℝ) T))
    (hRderiv : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        HasDerivWithinAt
          (fun t : ℝ => initialVelocityResidual α z₀ v w Ψ s t)
          (R' s τ) (Ici τ) τ)
    (hR0 : ∀ᶠ s in 𝓝 (0 : ℝ),
      initialVelocityResidual α z₀ v w Ψ s 0 = 0)
    (hbound : ∀ η > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ τ ∈ Ico (0 : ℝ) T,
        ‖R' s τ‖ ≤
          K * ‖initialVelocityResidual α z₀ v w Ψ s τ‖ + η * ‖s‖)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => α (z₀, v + s • w) t) (Ψ t) 0 := by
  have hunif :
      ∀ ε > (0 : ℝ), ∀ᶠ s in 𝓝 (0 : ℝ),
        ∀ τ ∈ Icc (0 : ℝ) T,
          ‖initialVelocityResidual α z₀ v w Ψ s τ‖ ≤ ε * ‖s‖ :=
    initialVelocityResidual_uniform_isLittleO_on_Icc_of_gronwall_bound
      (α := α) (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ)
      (R' := R') hT hK hRcont hRderiv hR0 hbound
  exact initialVelocity_hasDerivAt_of_residual_uniform_isLittleO
    (α := α) (z₀ := z₀) (v := v) (w := w) (Ψ := Ψ)
    hunif ht

end Poincare
