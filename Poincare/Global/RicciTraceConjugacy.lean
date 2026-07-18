import Poincare.CurvatureTensoriality
import Mathlib.LinearAlgebra.Trace

/-!
# Ricci trace under curvature conjugacy

The tensorial part of Ricci naturality is trace invariance under a tangent
linear equivalence.  This file isolates that exact algebraic step: once two
curvature endomorphisms intertwine through the differential of a coordinate
change, their Ricci contractions agree.  No geometric pullback law is assumed
or hidden here; the remaining geometric task is precisely to prove the stated
curvature intertwining.
-/

noncomputable section

namespace Poincare

section Trace

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- Trace is invariant when two endomorphisms intertwine through a linear
equivalence. -/
theorem LinearMap.trace_eq_of_equiv_intertwining
    (e : V ≃ₗ[R] W) (A : V →ₗ[R] V) (B : W →ₗ[R] W)
    (h : ∀ v : V, B (e v) = e (A v)) :
    LinearMap.trace R W B = LinearMap.trace R V A := by
  have hconj : B = e.conj A := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [h]
    simp [LinearEquiv.conj_apply]
  rw [hconj]
  exact LinearMap.trace_conj' A e

/-- Curvature-level form of trace naturality.  The family arguments represent
the two fixed curvature slots; the traced slot is the endomorphism argument. -/
theorem ricciTrace_natural_of_curvature_intertwining
    (e : V ≃ₗ[R] W)
    (curvV : V → V → (V →ₗ[R] V))
    (curvW : W → W → (W →ₗ[R] W))
    (hcurv : ∀ (u w v : V), curvW (e u) (e w) (e v) =
      e (curvV u w v))
    (u w : V) :
    LinearMap.trace R W (curvW (e u) (e w)) =
      LinearMap.trace R V (curvV u w) := by
  exact LinearMap.trace_eq_of_equiv_intertwining e
    (curvV u w) (curvW (e u) (e w)) (hcurv u w)

end Trace

end Poincare
