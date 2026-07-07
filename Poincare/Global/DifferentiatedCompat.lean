import Poincare.Global.TransitionLaw
import Poincare.Global.TransportedCompatibility

/-!
# Differentiated compatibility for the transported Christoffel field

This module isolates the algebraic heart of the differentiated pullback
argument.  Given the differentiated metric pullback identity, the source
Koszul pairing identity transports to the target Koszul pairing identity for
the signed field `Dσ Γ⁰ - D²σ`.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
If the cutoff-one metric pullback law has been differentiated at `z`, then
the signed transported source Christoffel field satisfies the target
metric-compatibility pairing identity on transported vectors.

The hypothesis `hdiff` is exactly the differentiated pullback law:
the derivative of
`G¹(σ z) (Dσ a) (Dσ b)` in direction `e` is expanded by the chain rule into
the target metric derivative plus the two `D²σ` slot-correction terms, and is
equal to the source metric derivative.
-/
theorem chartGeodesicMetric_transportedChristoffel_pairing_eq_of_differentiated_pullback
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hy : (extChartAt I x₀).symm z ∈ (extChartAt I y₀).source)
    (hχx : cutoff (n := n) x₀ z = 1)
    (hχy : cutoff (n := n) y₀ (chartTransition x₀ y₀ z) = 1)
    (hσ : ContDiffAt ℝ 2 (chartTransition (n := n) x₀ y₀) z)
    (hdiff : ∀ e a b : E,
      ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z)
          (chartTransitionDeriv x₀ y₀ z e))
        (chartTransitionDeriv x₀ y₀ z a)
        (chartTransitionDeriv x₀ y₀ z b)) +
        chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
          ((fderiv ℝ (chartTransitionDeriv x₀ y₀) z e) a)
          (chartTransitionDeriv x₀ y₀ z b) +
        chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
          (chartTransitionDeriv x₀ y₀ z a)
          ((fderiv ℝ (chartTransitionDeriv x₀ y₀) z e) b) =
      ((fderiv ℝ (chartGeodesicMetric g x₀) z e) a b))
    (u v w : E) :
    chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
        (chartTransitionDeriv x₀ y₀ z ((chartChristoffelField g x₀ z) u v) -
          (fderiv ℝ (chartTransitionDeriv x₀ y₀) z u) v)
        (chartTransitionDeriv x₀ y₀ z w) =
      (1 / 2 : ℝ) *
        (((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z)
            (chartTransitionDeriv x₀ y₀ z v))
          (chartTransitionDeriv x₀ y₀ z u)
          (chartTransitionDeriv x₀ y₀ z w)) +
          ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z)
            (chartTransitionDeriv x₀ y₀ z u))
          (chartTransitionDeriv x₀ y₀ z v)
          (chartTransitionDeriv x₀ y₀ z w)) -
            ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z)
              (chartTransitionDeriv x₀ y₀ z w))
            (chartTransitionDeriv x₀ y₀ z v)
            (chartTransitionDeriv x₀ y₀ z u))) := by
  set G₁ : E →L[ℝ] E →L[ℝ] ℝ :=
    chartGeodesicMetric g y₀ (chartTransition x₀ y₀ z)
  set D : E →L[ℝ] E := chartTransitionDeriv x₀ y₀ z
  set B : E →L[ℝ] E →L[ℝ] E := fderiv ℝ (chartTransitionDeriv x₀ y₀) z
  set Γ : E := (chartChristoffelField g x₀ z) u v
  have hBsymm : ∀ a b : E, B a b = B b a := by
    intro a b
    dsimp [B]
    simpa [chartTransitionDeriv] using
      (hσ.isSymmSndFDerivAt (by simp)).eq a b
  have hpull : G₁ (D Γ) (D w) = chartGeodesicMetric g x₀ z Γ w := by
    subst G₁
    subst D
    subst Γ
    simpa using
      (chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one
        (g := g) (x₀ := x₀) (y₀ := y₀) (z := z)
        hz hy hχx hχy ((chartChristoffelField g x₀ z) u v) w)
  have hleft :
      G₁ (D Γ - B u v) (D w) =
        chartGeodesicMetric g x₀ z Γ w - G₁ (B u v) (D w) := by
    calc
      G₁ (D Γ - B u v) (D w) =
          G₁ (D Γ) (D w) - G₁ (B u v) (D w) := by
        simp
      _ = chartGeodesicMetric g x₀ z Γ w - G₁ (B u v) (D w) := by
        rw [hpull]
  have hsource :
      chartGeodesicMetric g x₀ z Γ w =
        (1 / 2 : ℝ) *
          (((fderiv ℝ (chartGeodesicMetric g x₀) z v) u w) +
            ((fderiv ℝ (chartGeodesicMetric g x₀) z u) v w) -
              ((fderiv ℝ (chartGeodesicMetric g x₀) z w) v u)) := by
    subst Γ
    exact chartChristoffelField_pairing_eq_blendedChartMetric
      (g := g) (x₀ := x₀) (z := z) u v w
  have hvuw :
      ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z) (D v))
          (D u) (D w)) + G₁ (B v u) (D w) + G₁ (D u) (B v w) =
        ((fderiv ℝ (chartGeodesicMetric g x₀) z v) u w) := by
    simpa [G₁, D, B] using hdiff v u w
  have huvw :
      ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z) (D u))
          (D v) (D w)) + G₁ (B u v) (D w) + G₁ (D v) (B u w) =
        ((fderiv ℝ (chartGeodesicMetric g x₀) z u) v w) := by
    simpa [G₁, D, B] using hdiff u v w
  have hwvu :
      ((fderiv ℝ (chartGeodesicMetric g y₀) (chartTransition x₀ y₀ z) (D w))
          (D v) (D u)) + G₁ (B w v) (D u) + G₁ (D v) (B w u) =
        ((fderiv ℝ (chartGeodesicMetric g x₀) z w) v u) := by
    simpa [G₁, D, B] using hdiff w v u
  have hBvu : G₁ (B v u) (D w) = G₁ (B u v) (D w) := by
    rw [hBsymm v u]
  have hcorr₁ : G₁ (D u) (B v w) = G₁ (B w v) (D u) := by
    calc
      G₁ (D u) (B v w) = G₁ (B v w) (D u) := by
        subst G₁
        exact chartGeodesicMetric_symm
          (g := g) (x₀ := y₀) (z := chartTransition x₀ y₀ z)
          (D u) (B v w)
      _ = G₁ (B w v) (D u) := by
        rw [hBsymm v w]
  have hcorr₂ : G₁ (D v) (B u w) = G₁ (D v) (B w u) := by
    rw [hBsymm u w]
  rw [hleft, hsource]
  linarith [hvuw, huvw, hwvu, hBvu, hcorr₁, hcorr₂]

end GeodesicTransport
end Poincare
