import Poincare.Global.PullbackDifferentiate
import Poincare.ModelChristoffel

/-!
# Levi-Civita naturality under a metric-pullback map

This module isolates the map-generic Levi-Civita uniqueness algebra needed for
the Cartan chart map.  Once a local map `F` has an invertible differential field
`D` and the differentiated pullback identity, the Christoffel corrector of the
target metric is the signed transport of the source Christoffel corrector.
-/

noncomputable section

open scoped Topology

namespace Poincare
namespace GeodesicTransport

/--
Map-generic signed Christoffel transport from a differentiated metric pullback.

The orientation matches `chartChristoffelField`: the displayed
`christoffelAt ... v u` is the correction with section-value slot `u` and
direction slot `v`.  The correction term is therefore
`D²F(u,v) = (fderiv D z u) v`.
-/
theorem christoffelAt_map_eq_signed_transport_of_differentiated_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G₀ G₁ : E → E →L[ℝ] E →L[ℝ] ℝ) (F : E → E)
    (D : E → E →L[ℝ] E) {z : E}
    (hDinv : (D z).IsInvertible)
    (hD2symm : ∀ a b : E, (fderiv ℝ D z a) b = (fderiv ℝ D z b) a)
    (hdiff : ∀ e a b : E,
      ((fderiv ℝ G₁ (F z) (D z e)) (D z a) (D z b)) +
        G₁ (F z) ((fderiv ℝ D z e) a) (D z b) +
        G₁ (F z) (D z a) ((fderiv ℝ D z e) b) =
      ((fderiv ℝ G₀ z e) a b))
    (hpull : ∀ a b : E, G₁ (F z) (D z a) (D z b) = G₀ z a b)
    (hG₁symm : ∀ a b : E, G₁ (F z) a b = G₁ (F z) b a)
    (b₀ b₁ : LinearMap.BilinForm ℝ E)
    (hb₀ : b₀.Nondegenerate) (hb₁ : b₁.Nondegenerate)
    (hb₀G : ∀ a b : E, b₀ a b = G₀ z a b)
    (hb₁G : ∀ a b : E, b₁ a b = G₁ (F z) a b)
    (u v : E) :
    CovariantDerivative.christoffelAt G₁ (F z) b₁ hb₁ (D z v) (D z u) =
      D z (CovariantDerivative.christoffelAt G₀ z b₀ hb₀ v u) -
        (fderiv ℝ D z u) v := by
  let Dz : E →L[ℝ] E := D z
  let B : E →L[ℝ] E →L[ℝ] E := fderiv ℝ D z
  let Γ₀ : E := CovariantDerivative.christoffelAt G₀ z b₀ hb₀ v u
  let lhs : E := CovariantDerivative.christoffelAt G₁ (F z) b₁ hb₁ (Dz v) (Dz u)
  let rhs : E := Dz Γ₀ - B u v
  have hBsymm : ∀ a b : E, B a b = B b a := by
    intro a b
    simpa [B] using hD2symm a b
  have hpair : ∀ w : E, G₁ (F z) lhs (Dz w) = G₁ (F z) rhs (Dz w) := by
    intro w
    have htarget :
        G₁ (F z) lhs (Dz w) =
          (1 / 2 : ℝ) *
            (((fderiv ℝ G₁ (F z) (Dz v)) (Dz u) (Dz w)) +
              ((fderiv ℝ G₁ (F z) (Dz u)) (Dz v) (Dz w)) -
                ((fderiv ℝ G₁ (F z) (Dz w)) (Dz v) (Dz u))) := by
      have h :=
        CovariantDerivative.b_christoffelAt G₁ (F z) b₁ hb₁ (Dz v) (Dz u) (Dz w)
      simpa [lhs, hb₁G] using h
    have hleft :
        G₁ (F z) rhs (Dz w) =
          G₀ z Γ₀ w - G₁ (F z) (B u v) (Dz w) := by
      calc
        G₁ (F z) rhs (Dz w) =
            G₁ (F z) (Dz Γ₀) (Dz w) - G₁ (F z) (B u v) (Dz w) := by
          simp [rhs]
        _ = G₀ z Γ₀ w - G₁ (F z) (B u v) (Dz w) := by
          rw [hpull Γ₀ w]
    have hsource :
        G₀ z Γ₀ w =
          (1 / 2 : ℝ) *
            (((fderiv ℝ G₀ z v) u w) +
              ((fderiv ℝ G₀ z u) v w) -
                ((fderiv ℝ G₀ z w) v u)) := by
      have h := CovariantDerivative.b_christoffelAt G₀ z b₀ hb₀ v u w
      simpa [Γ₀, hb₀G] using h
    have hvuw :
        ((fderiv ℝ G₁ (F z) (Dz v)) (Dz u) (Dz w)) +
            G₁ (F z) (B v u) (Dz w) + G₁ (F z) (Dz u) (B v w) =
          ((fderiv ℝ G₀ z v) u w) := by
      simpa [Dz, B] using hdiff v u w
    have huvw :
        ((fderiv ℝ G₁ (F z) (Dz u)) (Dz v) (Dz w)) +
            G₁ (F z) (B u v) (Dz w) + G₁ (F z) (Dz v) (B u w) =
          ((fderiv ℝ G₀ z u) v w) := by
      simpa [Dz, B] using hdiff u v w
    have hwvu :
        ((fderiv ℝ G₁ (F z) (Dz w)) (Dz v) (Dz u)) +
            G₁ (F z) (B w v) (Dz u) + G₁ (F z) (Dz v) (B w u) =
          ((fderiv ℝ G₀ z w) v u) := by
      simpa [Dz, B] using hdiff w v u
    have hBvu : G₁ (F z) (B v u) (Dz w) = G₁ (F z) (B u v) (Dz w) := by
      rw [hBsymm v u]
    have hcorr₁ : G₁ (F z) (Dz u) (B v w) = G₁ (F z) (B w v) (Dz u) := by
      calc
        G₁ (F z) (Dz u) (B v w) = G₁ (F z) (B v w) (Dz u) := by
          rw [hG₁symm]
        _ = G₁ (F z) (B w v) (Dz u) := by
          rw [hBsymm v w]
    have hcorr₂ : G₁ (F z) (Dz v) (B u w) = G₁ (F z) (Dz v) (B w u) := by
      rw [hBsymm u w]
    have htransport :
        G₁ (F z) rhs (Dz w) =
          (1 / 2 : ℝ) *
            (((fderiv ℝ G₁ (F z) (Dz v)) (Dz u) (Dz w)) +
              ((fderiv ℝ G₁ (F z) (Dz u)) (Dz v) (Dz w)) -
                ((fderiv ℝ G₁ (F z) (Dz w)) (Dz v) (Dz u))) := by
      rw [hleft, hsource]
      linarith [hvuw, huvw, hwvu, hBvu, hcorr₁, hcorr₂]
    exact htarget.trans htransport.symm
  apply sub_eq_zero.mp
  apply hb₁.1
  intro ξ
  obtain ⟨e, he⟩ := hDinv
  have hξ : Dz (e.symm ξ) = ξ := by
    change (D z) (e.symm ξ) = ξ
    rw [← he]
    exact e.apply_symm_apply ξ
  have hξpair := hpair (e.symm ξ)
  rw [hξ] at hξpair
  calc
    b₁ (lhs - rhs) ξ = G₁ (F z) lhs ξ - G₁ (F z) rhs ξ := by
      simp [hb₁G]
    _ = 0 := by
      rw [hξpair]
      ring

end GeodesicTransport
end Poincare
