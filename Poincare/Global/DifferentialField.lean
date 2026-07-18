import Poincare.Global.RigidityComplete

/-!
# Pointwise differential field for the Cartan chart map

This module assembles the equivalence-valued differentials supplied pointwise by
`RigidityComplete.cartanMap_isLocalIsometry` into a single field on the model
space.  The verified payload is still pointwise on the punctured shrunk ball:
each selected value is invertible, is the strict derivative of the Cartan chart
map at the corresponding normal endpoint, and satisfies the metric-pullback
identity there.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialField

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The completed Cartan local-isometry theorem supplies pointwise endpoint
equivalences on a punctured shrunk normal ball.  Choosing those equivalences for
each model vector gives a differential field
`DF v = cartanChartDifferential L (Afield v) (Bfield v)` whose defining
strict-derivative and metric-pullback properties hold at every nonzero point in
that ball.
-/
theorem exists_cartanChartDifferential_field_on_punctured_ball
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
          HasStrictFDerivAt
              (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
              (Afield v : E3 →L[ℝ] E3) v ∧
            HasStrictFDerivAt
              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀)
              (Bfield v : E3 →L[ℝ] E3) (L v) ∧
            (DF v).IsInvertible ∧
            HasStrictFDerivAt
              (CartanDifferential.cartanChartMap g x₀ p₀ L)
              (DF v)
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
            ∀ u u' : E3,
              CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                  ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := roundSphereMetric3) p₀) (L v))
                  (DF v u) (DF v u') =
                CovariantDerivative.chartMetric g.inner x₀
                  ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
                  u u' := by
  rcases
      RigidityComplete.cartanMap_isLocalIsometry
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, _T, _hT_pos, hlocal⟩
  let Afield : E3 → E3 ≃L[ℝ] E3 := fun v =>
    if h : ‖v‖ < ρ ∧ v ≠ 0 then
      Classical.choose (hlocal v h.1 h.2)
    else
      ContinuousLinearEquiv.refl ℝ E3
  let Bfield : E3 → E3 ≃L[ℝ] E3 := fun v =>
    if h : ‖v‖ < ρ ∧ v ≠ 0 then
      Classical.choose (Classical.choose_spec (hlocal v h.1 h.2))
    else
      ContinuousLinearEquiv.refl ℝ E3
  let DF : E3 → E3 →L[ℝ] E3 := fun v =>
    CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · intro v
    rfl
  · intro v hv hvne
    have hdomain : ‖v‖ < ρ ∧ v ≠ 0 := ⟨hv, hvne⟩
    have hspec :
        HasStrictFDerivAt
          (CartanDifferential.cartanChartMap g x₀ p₀ L)
          (CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v))
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v) ∧
        ∀ u u' : E3,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) p₀) (L v))
              (CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v) u)
              (CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v) u') =
            CovariantDerivative.chartMetric g.inner x₀
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
              u u' := by
      simpa [Afield, Bfield, hdomain] using
        (Classical.choose_spec (Classical.choose_spec (hlocal v hv hvne))).2.2
    have hsourceStrict :
        HasStrictFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
          (Afield v : E3 →L[ℝ] E3) v := by
      simpa [Afield, hdomain] using
        (Classical.choose_spec (Classical.choose_spec (hlocal v hv hvne))).1
    have htargetStrict :
        HasStrictFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀)
          (Bfield v : E3 →L[ℝ] E3) (L v) := by
      simpa [Afield, Bfield, hdomain] using
        (Classical.choose_spec (Classical.choose_spec (hlocal v hv hvne))).2.1
    refine ⟨hsourceStrict, htargetStrict, ?_⟩
    constructor
    · let Dequiv : E3 ≃L[ℝ] E3 :=
        ((Afield v).symm.trans L.toContinuousLinearEquiv).trans (Bfield v)
      exact ⟨Dequiv, by
        ext u
        simp [DF, Dequiv, CartanLocalIsometry.cartanChartDifferential]⟩
    constructor
    · simpa [DF] using hspec.1
    · intro u u'
      simpa [DF] using hspec.2 u u'

end DifferentialField
end Poincare
