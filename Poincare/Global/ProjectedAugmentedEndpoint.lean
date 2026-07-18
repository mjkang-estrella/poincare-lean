import Poincare.Global.SelectorAssembly
import Poincare.Global.EndpointCurry
import Poincare.Global.AnchoredSecondDerivativeAssembly

/-!
# Projecting a doubly-augmented endpoint derivative

`SelectorAssembly.exists_centered_hosted_endpoint_hasFDerivAt` produces a
derivative of the paired endpoint `(β, Ξ)`.  The first component, restricted
to perturbations of the augmented initial state, is the derivative required
by `AnchoredSecondDerivativeAssembly`.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace ProjectedAugmentedEndpoint

open GeodesicTransport

/-- A derivative of the paired `(β, Ξ)` endpoint gives a derivative of the
augmented endpoint `β` after fixing the second initial state. -/
theorem exists_hasFDerivAt_first_endpoint_of_paired
    {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A}
    {y : A × A} {T : ℝ}
    (hpaired : ∃ D : (A × A) →L[ℝ] (A × A),
      HasFDerivAt
        (fun y' : A × A => (β y'.1 T, Ξ y'.1 y'.2 T)) D y) :
    ∃ Dβ : A →L[ℝ] A,
      HasFDerivAt (fun z : A => β z T) Dβ y.1 := by
  rcases hpaired with ⟨D, hD⟩
  let Dβ : A →L[ℝ] A :=
    ((ContinuousLinearMap.fst ℝ A A).comp D).comp
      (ContinuousLinearMap.inl ℝ A A)
  refine ⟨Dβ, ?_⟩
  simpa [Dβ] using
    (EndpointCurry.HasFDerivAt.project_fixed_second
      (ContinuousLinearMap.fst ℝ A A) hD)

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A₃" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Basiswise paired `(β, Ξ)` endpoint derivatives provide exactly the
basiswise `β` derivatives consumed by the anchored second-derivative assembly.
The auxiliary second initial state may be chosen independently at each basis
vector. -/
theorem exists_hasFDerivAt_expAtChart_fderiv_of_pairedEndpoint_finBasis
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (T : ℝ) (β : A₃ → ℝ → A₃) (Ξ : A₃ → A₃ → ℝ → A₃) (q : E)
    (hfield : ∀ q' w : E,
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q' w =
        AnchoredEndpointIdentity.augmentedFirstVariationPosition
          (β (AnchoredSecondDerivativeAssembly.anchoredAugmentedInitialization
            x₀ T (q', w)) T))
    (hpairedEndpoint : ∀ i : Fin (Module.finrank ℝ E),
      ∃ ξ₀ : A₃, ∃ D : (A₃ × A₃) →L[ℝ] (A₃ × A₃),
        HasFDerivAt
          (fun y' : A₃ × A₃ =>
            (β y'.1 T, Ξ y'.1 y'.2 T)) D
          (AnchoredSecondDerivativeAssembly.anchoredAugmentedInitialization
            x₀ T (q, (Module.finBasis ℝ E) i), ξ₀)) :
    ∃ D : E →L[ℝ] E →L[ℝ] E,
      HasFDerivAt
        (fun q' : E =>
          fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x₀) q')
        D q := by
  apply
    AnchoredSecondDerivativeAssembly.exists_hasFDerivAt_expAtChart_fderiv_of_augmentedEndpoint_finBasis
      g x₀ T β q hfield
  intro i
  rcases hpairedEndpoint i with ⟨ξ₀, D, hD⟩
  exact
    exists_hasFDerivAt_first_endpoint_of_paired
      ⟨D, hD⟩

end ProjectedAugmentedEndpoint
end Poincare
