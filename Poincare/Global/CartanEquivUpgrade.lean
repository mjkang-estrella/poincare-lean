import Poincare.Global.CartanActionEquations

/-!
# Cartan equivalence upgrade

This module isolates the linear-algebra upgrade needed after the hosted action
equations: a continuous linear endpoint map whose radial/transverse action has
nonzero diagonal factors is a continuous linear equivalence.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanEquivUpgrade

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Upgrade a hosted endpoint CLM to a continuous linear equivalence from its
diagonal radial/transverse action.

The radial and transverse parts span by
`CartanPullback.radialPart_add_transversePart`.  If both diagonal factors are
nonzero, the displayed action has zero kernel; finite dimensionality then
turns injectivity of the endomorphism into a linear equivalence, and finite
dimensional continuity packages it as `E ≃L[ℝ] E`.
-/
theorem exists_continuousLinearEquiv_of_sourceScaledNormalVector_action
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {D : E →L[ℝ] E} {v : E} {ρ σ : ℝ}
    (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (hD :
      ∀ u : E,
        D u = CartanLocalIsometry.sourceScaledNormalVector g x₀ ρ σ v u) :
    ∃ A : E ≃L[ℝ] E, (A : E →L[ℝ] E) = D := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := CartanMap.sourceAnchorChartMetric g x₀
  have hker : ∀ u : E, D u = 0 → u = 0 := by
    intro u hDu
    by_cases hv : v = 0
    · subst v
      have hσu : σ • u = 0 := by
        simpa [hD u, CartanLocalIsometry.sourceScaledNormalVector,
          CartanPullback.radialPart, CartanPullback.radialCoeff,
          CartanPullback.transversePart] using hDu
      rcases smul_eq_zero.mp hσu with hσ_zero | hu_zero
      · exact (hσ hσ_zero).elim
      · exact hu_zero
    · let r : E := CartanPullback.radialPart B v u
      let t : E := CartanPullback.transversePart B v u
      have hscaled : ρ • r + σ • t = 0 := by
        simpa [B, r, t, hD u, CartanLocalIsometry.sourceScaledNormalVector] using hDu
      have hvv : B v v ≠ 0 :=
        CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv
      have ht_v : B t v = 0 := by
        simpa [B, t] using
          CartanPullback.transversePart_pair_self_right
            (B := B) (v := v) (u := u) hvv
      have hr_pair_zero : B r v = 0 := by
        have hpair : B (ρ • r + σ • t) v = 0 := by
          simpa using congrArg (fun z : E => B z v) hscaled
        have hmul : ρ * B r v = 0 := by
          simpa [ht_v] using hpair
        exact (mul_eq_zero.mp hmul).resolve_left hρ
      have hcoeff_zero : CartanPullback.radialCoeff B v u = 0 := by
        have hmul : CartanPullback.radialCoeff B v u * B v v = 0 := by
          simpa [r, CartanPullback.radialPart] using hr_pair_zero
        exact (mul_eq_zero.mp hmul).resolve_right hvv
      have hr_zero : r = 0 := by
        simp [r, CartanPullback.radialPart, hcoeff_zero]
      have ht_zero : t = 0 := by
        have hσt : σ • t = 0 := by
          simpa [hr_zero] using hscaled
        rcases smul_eq_zero.mp hσt with hσ_zero | ht_zero
        · exact (hσ hσ_zero).elim
        · exact ht_zero
      have hdecomp : r + t = u := by
        simp [B, r, t]
      rw [← hdecomp, hr_zero, ht_zero]
      simp
  have hDinj : Function.Injective D := by
    intro u u' huu'
    apply sub_eq_zero.mp
    apply hker (u - u')
    simp [map_sub, huu']
  let Aₗ : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo D.toLinearMap hDinj
  refine ⟨Aₗ.toContinuousLinearEquiv, ?_⟩
  ext u
  simp [Aₗ]

end CartanEquivUpgrade
end Poincare
