import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof

/-!
# Chart-level geodesic ODEs

This file records the first-order autonomous ODE associated to the coordinate
geodesic equation `x'' + Γ_x(x', x') = 0`.
-/

noncomputable section

open Filter Set
open scoped Topology NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first-order vector field for the chart geodesic system. -/
def geodesicFlowField (Γ : E → E →L[ℝ] E →L[ℝ] E) :
    E × E → E × E :=
  fun p ↦ (p.2, -Γ p.1 p.2 p.2)

@[simp]
theorem geodesicFlowField_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (p : E × E) :
    geodesicFlowField Γ p = (p.2, -Γ p.1 p.2 p.2) :=
  rfl

/-- Local `C¹` regularity of the Christoffel field gives local `C¹` regularity of the flow. -/
theorem contDiffAt_geodesicFlowField
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 Γ p₀.1) :
    ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀ := by
  have hp : ContDiffAt ℝ 1 (fun p : E × E ↦ p.1) p₀ := contDiffAt_fst
  have hv : ContDiffAt ℝ 1 (fun p : E × E ↦ p.2) p₀ := contDiffAt_snd
  have hΓp : ContDiffAt ℝ 1 (fun p : E × E ↦ Γ p.1) p₀ :=
    hΓ.comp p₀ hp
  have hΓpv : ContDiffAt ℝ 1 (fun p : E × E ↦ Γ p.1 p.2) p₀ :=
    hΓp.clm_apply hv
  have hΓpvv : ContDiffAt ℝ 1 (fun p : E × E ↦ Γ p.1 p.2 p.2) p₀ :=
    hΓpv.clm_apply hv
  simpa [geodesicFlowField] using hv.prodMk hΓpvv.neg

/-- Global `C¹` regularity of the Christoffel field gives global `C¹` regularity of the flow. -/
theorem contDiff_geodesicFlowField
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : ContDiff ℝ 1 Γ) :
    ContDiff ℝ 1 (geodesicFlowField Γ) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  exact contDiffAt_geodesicFlowField (Γ := Γ) (p₀ := p₀) hΓ.contDiffAt

/--
Picard-Lindelöf local existence for the chart geodesic system, stated at the
regularity level consumed directly by Mathlib's ODE API.
-/
theorem exists_geodesicFlowField_solution_of_contDiffAt
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t := by
  rcases hΓ.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0 with
    ⟨γ, hγ0, ε, hε, hγ⟩
  refine ⟨ε, hε, γ, hγ0, ?_⟩
  simpa only [sub_eq_add_neg, zero_sub, zero_add] using hγ

/-- Picard-Lindelöf local existence from a `C¹` Christoffel field. -/
theorem exists_geodesicFlowField_solution
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E}
    (hΓ : ContDiffAt ℝ 1 Γ p₀.1) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t :=
  exists_geodesicFlowField_solution_of_contDiffAt
    (contDiffAt_geodesicFlowField (Γ := Γ) (p₀ := p₀) hΓ)

/-- Picard-Lindelöf local existence from a globally `C¹` Christoffel field. -/
theorem exists_geodesicFlowField_solution_of_contDiff
    [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ 1 Γ) (p₀ : E × E) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E × E,
      γ 0 = p₀ ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t :=
  exists_geodesicFlowField_solution (Γ := Γ) (p₀ := p₀) hΓ.contDiffAt

/--
Local uniqueness for the chart geodesic system from a neighborhood Lipschitz
hypothesis, exactly in the form used by Mathlib's Grönwall uniqueness theorem.
-/
theorem geodesicFlowField_eventuallyEq_of_lipschitz
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ η : ℝ → E × E}
    {K : ℝ≥0} {s : ℝ → Set (E × E)}
    (hLip : ∀ᶠ t in 𝓝 (0 : ℝ),
      LipschitzOnWith K (fun p ↦ geodesicFlowField Γ p) (s t))
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ (geodesicFlowField Γ (γ t)) t ∧ γ t ∈ s t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η (geodesicFlowField Γ (η t)) t ∧ η t ∈ s t)
    (h0 : γ 0 = η 0) :
    γ =ᶠ[𝓝 (0 : ℝ)] η :=
  ODE_solution_unique_of_eventually (v := fun _ ↦ geodesicFlowField Γ)
    hLip hγ hη h0

/-- Local uniqueness near `0` for the chart geodesic system from local `C¹` regularity. -/
theorem geodesicFlowField_eventuallyEq_of_contDiffAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {p₀ : E × E} {γ η : ℝ → E × E}
    (hΓ : ContDiffAt ℝ 1 (geodesicFlowField Γ) p₀)
    (hγ0 : γ 0 = p₀) (hη0 : η 0 = p₀)
    (hγ : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt γ (geodesicFlowField Γ (γ t)) t)
    (hη : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt η (geodesicFlowField Γ (η t)) t) :
    γ =ᶠ[𝓝 (0 : ℝ)] η := by
  rcases hΓ.exists_lipschitzOnWith with ⟨K, s, hs, hLip⟩
  have hγder0 : HasDerivAt γ (geodesicFlowField Γ (γ 0)) 0 :=
    hγ.self_of_nhds
  have hηder0 : HasDerivAt η (geodesicFlowField Γ (η 0)) 0 :=
    hη.self_of_nhds
  have hγmem : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ s :=
    hγder0.continuousAt.preimage_mem_nhds (by simpa [hγ0] using hs)
  have hηmem : ∀ᶠ t in 𝓝 (0 : ℝ), η t ∈ s :=
    hηder0.continuousAt.preimage_mem_nhds (by simpa [hη0] using hs)
  apply geodesicFlowField_eventuallyEq_of_lipschitz
    (Γ := Γ) (K := K) (s := fun _ : ℝ ↦ s)
  · exact .of_forall fun _ ↦ hLip
  · exact hγ.and hγmem
  · exact hη.and hηmem
  · rw [hγ0, hη0]

/--
Geodesic reading, first component: a first-order solution has position
derivative equal to velocity.
-/
theorem geodesic_position_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    HasDerivAt (fun τ ↦ (γ τ).1) (γ t).2 t := by
  simpa [geodesicFlowField] using hγ.hasFDerivAt.fst.hasDerivAt

/--
Geodesic reading, second component: a first-order solution has acceleration
`-Γ_x(v,v)`.
-/
theorem geodesic_velocity_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    HasDerivAt (fun τ ↦ (γ τ).2) (-(Γ (γ t).1) (γ t).2 (γ t).2) t := by
  simpa [geodesicFlowField] using hγ.hasFDerivAt.snd.hasDerivAt

/-- Geodesic reading bundled over an interval. -/
theorem geodesic_components_hasDerivAt
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E × E}
    {I : Set ℝ}
    (hγ : ∀ t ∈ I, HasDerivAt γ (geodesicFlowField Γ (γ t)) t) :
    (∀ t ∈ I, HasDerivAt (fun τ ↦ (γ τ).1) (γ t).2 t) ∧
      ∀ t ∈ I,
        HasDerivAt (fun τ ↦ (γ τ).2)
          (-(Γ (γ t).1) (γ t).2 (γ t).2) t := by
  exact ⟨fun t ht ↦ geodesic_position_hasDerivAt (hγ t ht),
    fun t ht ↦ geodesic_velocity_hasDerivAt (hγ t ht)⟩

end Poincare
