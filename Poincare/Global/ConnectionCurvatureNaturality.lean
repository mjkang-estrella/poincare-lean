import Poincare.Global.RicciTraceConjugacy

/-!
# Curvature naturality from connection and bracket naturality

The geometric curvature-pullback problem has a short algebraic core.  Once a
pushforward intertwines covariant differentiation and Lie brackets, the
commutator definition of curvature is automatically intertwined as well.
This module records that step without assuming any curvature identity.
-/

namespace Poincare

section

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- Algebraic curvature of a connection-like binary operation and a bracket. -/
def connectionCurvature
    (nabla bracket : V → V → V) (X Y Z : V) : V :=
  nabla X (nabla Y Z) - nabla Y (nabla X Z) - nabla (bracket X Y) Z

/-- Intertwining the connection and bracket intertwines their curvature. -/
theorem connectionCurvature_natural_of_intertwining
    (e : V ≃ₗ[R] W)
    (nablaV bracketV : V → V → V)
    (nablaW bracketW : W → W → W)
    (hnabla : ∀ X Y : V, e (nablaV X Y) = nablaW (e X) (e Y))
    (hbracket : ∀ X Y : V, e (bracketV X Y) = bracketW (e X) (e Y))
    (X Y Z : V) :
    e (connectionCurvature nablaV bracketV X Y Z) =
      connectionCurvature nablaW bracketW (e X) (e Y) (e Z) := by
  simp only [connectionCurvature, map_sub]
  rw [hnabla X (nablaV Y Z), hnabla Y Z,
    hnabla Y (nablaV X Z), hnabla X Z,
    hnabla (bracketV X Y) Z, hbracket X Y]

/-- Endomorphism-family form used by Ricci-trace naturality. -/
theorem connectionCurvature_endomorphism_intertwining
    (e : V ≃ₗ[R] W)
    (nablaV bracketV : V → V → V)
    (nablaW bracketW : W → W → W)
    (hnabla : ∀ X Y : V, e (nablaV X Y) = nablaW (e X) (e Y))
    (hbracket : ∀ X Y : V, e (bracketV X Y) = bracketW (e X) (e Y))
    (X Y Z : V) :
    connectionCurvature nablaW bracketW (e X) (e Y) (e Z) =
      e (connectionCurvature nablaV bracketV X Y Z) :=
  (connectionCurvature_natural_of_intertwining
    e nablaV bracketV nablaW bracketW hnabla hbracket X Y Z).symm

/-- Connection and bracket naturality imply naturality of the traced curvature
endomorphism, once the geometric curvature maps are identified with the
commutator formula. -/
theorem ricciTrace_natural_of_connection_intertwining
    (e : V ≃ₗ[R] W)
    (nablaV bracketV : V → V → V)
    (nablaW bracketW : W → W → W)
    (curvV : V → V → (V →ₗ[R] V))
    (curvW : W → W → (W →ₗ[R] W))
    (hnabla : ∀ X Y : V, e (nablaV X Y) = nablaW (e X) (e Y))
    (hbracket : ∀ X Y : V, e (bracketV X Y) = bracketW (e X) (e Y))
    (hcurvV : ∀ X Y Z : V,
      curvV X Y Z = connectionCurvature nablaV bracketV X Y Z)
    (hcurvW : ∀ X Y Z : W,
      curvW X Y Z = connectionCurvature nablaW bracketW X Y Z)
    (X Y : V) :
    LinearMap.trace R W (curvW (e X) (e Y)) =
      LinearMap.trace R V (curvV X Y) := by
  apply ricciTrace_natural_of_curvature_intertwining e curvV curvW
  intro X Y Z
  rw [hcurvW, hcurvV]
  exact connectionCurvature_endomorphism_intertwining
    e nablaV bracketV nablaW bracketW hnabla hbracket X Y Z

end

end Poincare
