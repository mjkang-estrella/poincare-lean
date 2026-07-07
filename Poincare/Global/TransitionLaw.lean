import Poincare.Global.GeodesicReanchorClose
import Poincare.Global.GeodesicSpeed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Chart-transition Christoffel law

This module records one strict partial of the minus-sign transition law:
the transported source Christoffel expression with the ordinary second
derivative subtracted is symmetric in its two velocity slots.  This is the
torsion-free half of the Levi-Civita uniqueness route.
-/

noncomputable section

open Bundle Filter Set
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
The minus-correction part of the chart-transition Christoffel expression is
symmetric in the two source velocity slots.

The expression is the torsion-free transported-field candidate:
`Dσ(Γ⁰(u,v)) - D²σ(u,v)`.  Its symmetry combines the source Christoffel
symmetry with the symmetry of the second Fréchet derivative of the chart
transition.
-/
theorem chartTransitionDeriv_chartChristoffelField_minus_sndFDeriv_symm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : E}
    (hσ : ContDiffAt ℝ 2 (chartTransition (n := n) x₀ y₀) z)
    (u v : E) :
    chartTransitionDeriv (n := n) x₀ y₀ z
        ((chartChristoffelField g x₀ z) u v)
      - fderiv ℝ (chartTransitionDeriv (n := n) x₀ y₀) z u v =
    chartTransitionDeriv (n := n) x₀ y₀ z
        ((chartChristoffelField g x₀ z) v u)
      - fderiv ℝ (chartTransitionDeriv (n := n) x₀ y₀) z v u := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hG2 : ContDiff ℝ 2 (chartGeodesicMetric g x₀) := by
    simpa [chartGeodesicMetric] using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := n) x₀) (backgroundMetric (n := n)) g.inner x₀
        htwo_add_one_le_top (cutoff_contDiff (n := n) x₀)
        (cutoff_tsupport (n := n) x₀) hg2)
  have hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) z :=
    (hG2.differentiable (by norm_num)) z
  have hΓ :
      (chartChristoffelField g x₀ z) u v =
        (chartChristoffelField g x₀ z) v u := by
    change
      CovariantDerivative.christoffelAt
          (chartGeodesicMetric g x₀) z
          (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ z)
          (CovariantDerivative.chartBilin_nondegenerate
            (cutoff (n := n) x₀) (backgroundMetric (n := n))
            (backgroundMetric_pos (n := n)) g.inner
            (fun y u hu => g.inner_pos y (v := u) hu) x₀
            (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
            (cutoff_support_invertible (n := n) x₀) z)
          v u =
        CovariantDerivative.christoffelAt
          (chartGeodesicMetric g x₀) z
          (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
            (backgroundMetric (n := n)) g.inner x₀ z)
          (CovariantDerivative.chartBilin_nondegenerate
            (cutoff (n := n) x₀) (backgroundMetric (n := n))
            (backgroundMetric_pos (n := n)) g.inner
            (fun y u hu => g.inner_pos y (v := u) hu) x₀
            (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
            (cutoff_support_invertible (n := n) x₀) z)
          u v
    exact CovariantDerivative.christoffelAt_symm
      (chartGeodesicMetric g x₀)
      (CovariantDerivative.chartBilin (cutoff (n := n) x₀)
        (backgroundMetric (n := n)) g.inner x₀ z)
      (CovariantDerivative.chartBilin_nondegenerate
        (cutoff (n := n) x₀) (backgroundMetric (n := n))
        (backgroundMetric_pos (n := n)) g.inner
        (fun y u hu => g.inner_pos y (v := u) hu) x₀
        (cutoff_nonneg (n := n) x₀) (cutoff_le_one (n := n) x₀)
        (cutoff_support_invertible (n := n) x₀) z)
      hGd
      (fun y p q => chartGeodesicMetric_symm (g := g) (x₀ := x₀) y p q)
      v u
  have hD2 :
      fderiv ℝ (chartTransitionDeriv (n := n) x₀ y₀) z u v =
        fderiv ℝ (chartTransitionDeriv (n := n) x₀ y₀) z v u := by
    simpa [chartTransitionDeriv] using
      (hσ.isSymmSndFDerivAt (by simp)).eq u v
  rw [hΓ, hD2]

end GeodesicTransport
end Poincare
