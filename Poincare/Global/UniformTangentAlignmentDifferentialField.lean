import Poincare.Global.UniformTangentAlignmentRigidity

/-!
# A differential field on one fixed-anchor ball for every alignment

The fixed-anchor rigidity radius from
`UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`
precedes the tangent alignment.  This module performs the same pointwise
choice as `DifferentialField`, but retains that quantifier order: one positive
punctured-ball radius works for all tangent alignments at the fixed anchors.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Poincare
namespace UniformTangentAlignmentDifferentialField

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
One fixed-anchor punctured normal ball carries a Cartan differential field for
every tangent alignment.  The fields may depend on the alignment; the radius
does not.
-/
theorem exists_uniform_cartanChartDifferential_field_on_punctured_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x₀ p₀,
        ∃ Afield Bfield : E → E ≃L[ℝ] E,
        ∃ DF : E → E →L[ℝ] E,
          (∀ v : E,
            DF v =
              CartanLocalIsometry.cartanChartDifferential
                L (Afield v) (Bfield v)) ∧
          ∀ v : E, ‖v‖ < rho → v ≠ 0 →
            HasStrictFDerivAt
                (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
                (Afield v : E →L[ℝ] E) v ∧
              HasStrictFDerivAt
                (GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀)
                (Bfield v : E →L[ℝ] E) (L v) ∧
              (DF v).IsInvertible ∧
              HasStrictFDerivAt
                (CartanDifferential.cartanChartMap g x₀ p₀ L)
                (DF v)
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₀) v) ∧
              ∀ u u' : E,
                CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                    ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                      (g := roundSphereMetric3) p₀) (L v))
                    (DF v u) (DF v u') =
                  CovariantDerivative.chartMetric g.inner x₀
                    ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                      (g := g) x₀) v) u u' := by
  rcases
      UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) with
    ⟨rho, hrho_pos, _T, _hT_pos, hlocal⟩
  refine ⟨rho, hrho_pos, ?_⟩
  intro L
  let Afield : E → E ≃L[ℝ] E := fun v =>
    if h : ‖v‖ < rho ∧ v ≠ 0 then
      Classical.choose (hlocal L v h.1 h.2)
    else
      ContinuousLinearEquiv.refl ℝ E
  let Bfield : E → E ≃L[ℝ] E := fun v =>
    if h : ‖v‖ < rho ∧ v ≠ 0 then
      Classical.choose (Classical.choose_spec (hlocal L v h.1 h.2))
    else
      ContinuousLinearEquiv.refl ℝ E
  let DF : E → E →L[ℝ] E := fun v =>
    CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)
  refine ⟨Afield, Bfield, DF, ?_, ?_⟩
  · intro v
    rfl
  · intro v hv hvne
    have hdomain : ‖v‖ < rho ∧ v ≠ 0 := ⟨hv, hvne⟩
    have hspec :
        HasStrictFDerivAt
            (CartanDifferential.cartanChartMap g x₀ p₀ L)
            (CartanLocalIsometry.cartanChartDifferential
              L (Afield v) (Bfield v))
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₀) v) ∧
          ∀ u u' : E,
            CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) p₀) (L v))
                (CartanLocalIsometry.cartanChartDifferential
                  L (Afield v) (Bfield v) u)
                (CartanLocalIsometry.cartanChartDifferential
                  L (Afield v) (Bfield v) u') =
              CovariantDerivative.chartMetric g.inner x₀
                ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₀) v) u u' := by
      simpa [Afield, Bfield, hdomain] using
        (Classical.choose_spec
          (Classical.choose_spec (hlocal L v hv hvne))).2.2
    have hsourceStrict :
        HasStrictFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀)
          (Afield v : E →L[ℝ] E) v := by
      simpa [Afield, hdomain] using
        (Classical.choose_spec
          (Classical.choose_spec (hlocal L v hv hvne))).1
    have htargetStrict :
        HasStrictFDerivAt
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀)
          (Bfield v : E →L[ℝ] E) (L v) := by
      simpa [Afield, Bfield, hdomain] using
        (Classical.choose_spec
          (Classical.choose_spec (hlocal L v hv hvne))).2.1
    refine ⟨hsourceStrict, htargetStrict, ?_⟩
    constructor
    · let Dequiv : E ≃L[ℝ] E :=
        ((Afield v).symm.trans L.toContinuousLinearEquiv).trans (Bfield v)
      exact ⟨Dequiv, by
        ext u
        simp [DF, Dequiv, CartanLocalIsometry.cartanChartDifferential]⟩
    constructor
    · simpa [DF] using hspec.1
    · intro u u'
      simpa [DF] using hspec.2 u u'

end UniformTangentAlignmentDifferentialField
end Poincare
