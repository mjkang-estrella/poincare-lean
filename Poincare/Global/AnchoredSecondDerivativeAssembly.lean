import Poincare.Global.AnchoredEndpointIdentity
import Poincare.Global.BasisEndpointAssembly

/-!
# Anchored second-derivative assembly

This module combines the exact anchored endpoint identification with the
finite-basis interpolation theorem.  Full derivatives of the augmented
endpoint at the finitely many basis first-variation inputs are enough to
differentiate the operator-valued exponential-chart derivative field.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace AnchoredSecondDerivativeAssembly

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open GeodesicTransport

/-- Insert a pair `(q,w)` as the anchored geodesic/first-variation initial
state. -/
def anchoredAugmentedInitialization (x₀ : M) (T : ℝ) : E × E → A :=
  fun z =>
    ((extChartAt I x₀ x₀, T⁻¹ • z.1), ((0 : E), T⁻¹ • z.2))

/-- Linear part of `anchoredAugmentedInitialization`. -/
def anchoredAugmentedInitializationCLM (T : ℝ) : (E × E) →L[ℝ] A :=
  ((0 : (E × E) →L[ℝ] E).prod
      (T⁻¹ • ContinuousLinearMap.fst ℝ E E)).prod
    ((0 : (E × E) →L[ℝ] E).prod
      (T⁻¹ • ContinuousLinearMap.snd ℝ E E))

@[simp]
theorem anchoredAugmentedInitializationCLM_apply (T : ℝ) (z : E × E) :
    anchoredAugmentedInitializationCLM T z =
      (((0 : E), T⁻¹ • z.1), ((0 : E), T⁻¹ • z.2)) := by
  rfl

/-- The anchored initialization is affine with the displayed constant
Frechet derivative. -/
theorem anchoredAugmentedInitialization_hasFDerivAt
    (x₀ : M) (T : ℝ) (z : E × E) :
    HasFDerivAt (anchoredAugmentedInitialization x₀ T)
      (anchoredAugmentedInitializationCLM T) z := by
  let c : A :=
    ((extChartAt I x₀ x₀, (0 : E)), ((0 : E), (0 : E)))
  have h :=
    (hasFDerivAt_const (x := z) (c := c)).add
      (anchoredAugmentedInitializationCLM T).hasFDerivAt
  convert h using 1
  · funext y
    ext <;>
      simp [anchoredAugmentedInitialization,
        anchoredAugmentedInitializationCLM, c]
  · simp

/--
Basiswise full augmented-endpoint derivatives produce a Frechet derivative of
the canonical operator field `q ↦ fderiv expAtChart q`.

The endpoint identification is stated extensionally as `hfield`; it is
exactly what `AnchoredEndpointIdentity` proves after the selected augmented
flow is tied to the hosted linearized family.
-/
theorem exists_hasFDerivAt_expAtChart_fderiv_of_augmentedEndpoint_finBasis
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (β : A → ℝ → A) (q : E)
    (hfield : ∀ q' w : E,
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q' w =
        AnchoredEndpointIdentity.augmentedFirstVariationPosition
          (β (anchoredAugmentedInitialization x₀ T (q', w)) T))
    (hendpoint : ∀ i : Fin (Module.finrank ℝ E),
      ∃ D : A →L[ℝ] A,
        HasFDerivAt (fun z : A => β z T) D
          (anchoredAugmentedInitialization x₀ T
            (q, (Module.finBasis ℝ E) i))) :
    ∃ D : E →L[ℝ] E →L[ℝ] E,
      HasFDerivAt
        (fun q' : E =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
        D q := by
  exact
    EndpointCurry.exists_hasFDerivAt_clm_of_endpoint_finBasis
      (post := AnchoredEndpointIdentity.augmentedFirstVariationPosition)
      (pre := anchoredAugmentedInitializationCLM T)
      (endpoint := fun z : A => β z T)
      (initMap := anchoredAugmentedInitialization x₀ T)
      (f := fun q' : E =>
        fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
      (x := q)
      (anchoredAugmentedInitialization_hasFDerivAt x₀ T)
      hfield hendpoint

end AnchoredSecondDerivativeAssembly
end Poincare
