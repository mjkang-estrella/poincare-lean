import Poincare.Global.ConcreteResidual
import Poincare.Global.GermAndField

/-!
# Derivative uniqueness for the selected Cartan differential field

The selected Cartan `DF` field from `DifferentialField` is a strict derivative
of the Cartan chart map.  Hence, at each punctured normal endpoint, it is the
ordinary `fderiv` of that map.  This module records the resulting bridge from
canonical `fderiv` residuals to the concrete `DF` residual shape consumed by
`ConcreteResidual`.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DerivativeUnique

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
On the punctured normal ball, the selected Cartan differential field is the
canonical Fréchet derivative of the Cartan chart map.  Consequently, any
direction-uniform residual estimate written for `fderiv F` immediately gives
the Frechet differentiability of the selected chart-indexed `DF` field.
-/
theorem exists_cartanChartField_hasFDerivAt_of_fderiv_directional_residual_on_punctured_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ Afield Bfield : E3 → E3 ≃L[ℝ] E3,
      ∃ DF : E3 → E3 →L[ℝ] E3,
        (∀ v : E3,
          DF v =
            CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)) ∧
        ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
          let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          v ∈ eM.source →
            DF v = fderiv ℝ F (eM v) ∧
            ∀ CLM : E3 →L[ℝ] E3 →L[ℝ] E3,
              (∀ c > (0 : ℝ), ∀ᶠ δ in 𝓝 (0 : E3), ∀ u : E3,
                ‖(fderiv ℝ F (eM v + δ) - fderiv ℝ F (eM v) - CLM δ) u‖ ≤
                  (c * ‖δ‖) * ‖u‖) →
              HasFDerivAt (fun q : E3 => DF (eM.symm q)) CLM (eM v) := by
  rcases
      GermAndField.exists_cartanChartMap_fderiv_eventual_pullback_germ_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, Afield, Bfield, DF, hDF_def, hfield⟩
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · exact hDF_def
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  intro hvsrc
  rcases hfield v hv hvne hvsrc with ⟨hderiv_germ, _hpull_germ⟩
  have hbase_deriv :
      HasFDerivAt F (DF (eM.symm (eM v))) (eM v) :=
    hderiv_germ.self_of_nhds
  have hbase_fderiv :
      DF (eM.symm (eM v)) = fderiv ℝ F (eM v) :=
    hbase_deriv.fderiv.symm
  have hDF_fderiv : DF v = fderiv ℝ F (eM v) := by
    simpa [eM.left_inv hvsrc] using hbase_fderiv
  constructor
  · exact hDF_fderiv
  intro CLM hres
  apply
    GeodesicTransport.chartField_hasFDerivAt_of_directional_residual_norm_le
      (eM_symm := eM.symm) (DF := DF) (q := eM v) (CLM := CLM)
  intro c hc
  have hres_c := hres c hc
  have hshift :
      Tendsto (fun δ : E3 => eM v + δ) (𝓝 (0 : E3)) (𝓝 (eM v)) := by
    simpa using
      (tendsto_const_nhds.add tendsto_id :
        Tendsto (fun δ : E3 => eM v + δ) (𝓝 (0 : E3)) (𝓝 (eM v + 0)))
  have hnear_deriv :
      ∀ᶠ δ in 𝓝 (0 : E3),
        HasFDerivAt F (DF (eM.symm (eM v + δ))) (eM v + δ) :=
    hshift.eventually hderiv_germ
  filter_upwards [hres_c, hnear_deriv] with δ hδ hδ_deriv
  intro u
  have hδ_fderiv :
      DF (eM.symm (eM v + δ)) = fderiv ℝ F (eM v + δ) :=
    hδ_deriv.fderiv.symm
  calc
    ‖(DF (eM.symm (eM v + δ)) - DF (eM.symm (eM v)) - CLM δ) u‖
        =
      ‖(fderiv ℝ F (eM v + δ) - fderiv ℝ F (eM v) - CLM δ) u‖ := by
        rw [hδ_fderiv, hbase_fderiv]
    _ ≤ (c * ‖δ‖) * ‖u‖ := hδ u

end DerivativeUnique
end Poincare
