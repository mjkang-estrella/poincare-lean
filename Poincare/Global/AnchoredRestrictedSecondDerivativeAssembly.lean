import Poincare.Global.AnchoredEndpointIdentity
import Poincare.Global.BasisEndpointAssembly
import Poincare.Global.ParameterizedFlowDerivative

/-!
# Restricted anchored second-derivative assembly

For an anchored exponential chart the base point in the chart state remains
fixed; only the initial velocity varies.  This module assembles derivatives of
those restricted augmented endpoint families directly, avoiding an artificial
extension to arbitrary chart-position initial data.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace AnchoredRestrictedSecondDerivativeAssembly

open GeodesicTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Finite-basis derivatives of the anchored augmented endpoint imply a Frechet
derivative of the canonical operator field `q ↦ fderiv expAtChart q`.

Here `β q w` is allowed to be selected only for anchored initial data.  This
is the endpoint shape produced by the restricted-parameter Gronwall theorem.
-/
theorem exists_hasFDerivAt_expAtChart_fderiv_of_parameterized_augmented_finBasis
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (β : E → E → ℝ → A) (q : E)
    (hfield : ∀ q' w : E,
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q' w =
        AnchoredEndpointIdentity.augmentedFirstVariationPosition (β q' w T))
    (hendpoint : ∀ i : Fin (Module.finrank ℝ E),
      ∃ D : E →L[ℝ] A,
        HasFDerivAt
          (fun q' : E => β q' ((Module.finBasis ℝ E) i) T) D q) :
    ∃ D : E →L[ℝ] E →L[ℝ] E,
      HasFDerivAt
        (fun q' : E =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
        D q := by
  apply EndpointCurry.exists_hasFDerivAt_clm_of_apply_finBasis
  intro i
  rcases hendpoint i with ⟨D, hD⟩
  refine
    ⟨AnchoredEndpointIdentity.augmentedFirstVariationPosition.comp D, ?_⟩
  have hprojected :=
    AnchoredEndpointIdentity.augmentedFirstVariationPosition.hasFDerivAt.comp q hD
  simpa only [hfield] using hprojected

/--
Scaled-basis form of the restricted assembly.  Taking the scale to be the
positive endpoint time keeps the augmented initial variation uniformly
bounded, while linearity recovers the canonical operator field.
-/
theorem exists_hasFDerivAt_expAtChart_fderiv_of_scaled_parameterized_augmented_finBasis
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (hT : T ≠ 0) (β : E → E → ℝ → A) (q : E)
    (hfield : ∀ q' w : E,
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q' w =
        AnchoredEndpointIdentity.augmentedFirstVariationPosition (β q' w T))
    (hendpoint : ∀ i : Fin (Module.finrank ℝ E),
      ∃ D : E →L[ℝ] A,
        HasFDerivAt
          (fun q' : E => β q' (T • (Module.finBasis ℝ E) i) T) D q) :
    ∃ D : E →L[ℝ] E →L[ℝ] E,
      HasFDerivAt
        (fun q' : E =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
        D q := by
  apply EndpointCurry.exists_hasFDerivAt_clm_of_smul_finBasis T hT
  intro i
  rcases hendpoint i with ⟨D, hD⟩
  refine
    ⟨AnchoredEndpointIdentity.augmentedFirstVariationPosition.comp D, ?_⟩
  have hprojected :=
    AnchoredEndpointIdentity.augmentedFirstVariationPosition.hasFDerivAt.comp q hD
  simpa only [hfield] using hprojected

/--
Continuous basiswise endpoint-derivative fields give `C¹` regularity of the
canonical exponential-chart derivative field.  This is the exact regularity
input used by the existing `ExpChartC2` handoff.
-/
theorem expAtChart_fderiv_contDiffAt_one_of_parameterized_augmented_finBasis
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (β : E → E → ℝ → A)
    {U : Set E} {q : E} (hU : IsOpen U) (hq : q ∈ U)
    (hfield : ∀ q' w : E,
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q' w =
        AnchoredEndpointIdentity.augmentedFirstVariationPosition (β q' w T))
    (D : Fin (Module.finrank ℝ E) → E → E →L[ℝ] E)
    (hDcont : ∀ i, ContinuousOn (D i) U)
    (hDderiv : ∀ i q', q' ∈ U →
      HasFDerivAt
        (fun y : E =>
          AnchoredEndpointIdentity.augmentedFirstVariationPosition
            (β y ((Module.finBasis ℝ E) i) T))
        (D i q') q') :
    ContDiffAt ℝ 1
      (fun q' : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q') q := by
  apply EndpointCurry.contDiffAt_one_clm_of_finBasis_derivative_fields
    hU hq D hDcont
  intro i q' hq'
  simpa only [hfield] using hDderiv i q' hq'

end AnchoredRestrictedSecondDerivativeAssembly
end Poincare
