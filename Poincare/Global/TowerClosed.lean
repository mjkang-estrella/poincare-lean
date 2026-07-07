import Poincare.Global.DoublyResidual

/-!
# Tower closing boundary

This module records the first non-hypothetical consequence of the landed
doubly-augmented residual theorem for the final tower: the paired endpoint
Frechet derivative immediately supplies the derivative of the
second-variation endpoint field by projection.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
The doubly-augmented residual theorem differentiates the paired endpoint
`y' ↦ (β y'.1 t, Ξ y'.1 y'.2 t)`.  Projecting its second component gives the
Frechet derivative of the second-variation endpoint field itself, with the
projected third-variation endpoint CLM as derivative.
-/
theorem chartChristoffel_secondVariation_endpoint_hasFDerivAt_of_thirdVariation_data
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A}
    {y : A × A} {Ω : A × A → ℝ → A × A}
    {D : (A × A) →L[ℝ] (A × A)}
    {T a : ℝ} {p : A × A} {t : ℝ}
    (hT : 0 < T)
    (hbaseβ0 : β y.1 0 = y.1)
    (hbaseβder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β y.1)
        (augmentedGeodesicFlowField (chartChristoffelField g x₀) (β y.1 τ))
        (Icc (0 : ℝ) T) τ)
    (hbaseΞ0 : Ξ y.1 y.2 0 = y.2)
    (hbaseΞder : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ξ y.1 y.2)
        (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
          (β y.1) τ (Ξ y.1 y.2 τ))
        (Icc (0 : ℝ) T) τ)
    (hbase_mem : ∀ τ ∈ Icc (0 : ℝ) T,
      (β y.1 τ, Ξ y.1 y.2 τ) ∈ closedBall p a)
    (hpert : ∀ᶠ h in 𝓝 (0 : A × A),
      β (y + h).1 0 = (y + h).1 ∧
        Ξ (y + h).1 (y + h).2 0 = (y + h).2 ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β (y + h).1)
            (augmentedGeodesicFlowField (chartChristoffelField g x₀)
              (β (y + h).1 τ))
            (Icc (0 : ℝ) T) τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ (y + h).1 (y + h).2)
            (secondVariationFlowFieldAlong (chartChristoffelField g x₀)
              (β (y + h).1) τ (Ξ (y + h).1 (y + h).2 τ))
            (Icc (0 : ℝ) T) τ) ∧
        ∀ τ ∈ Icc (0 : ℝ) T,
          (β (y + h).1 τ, Ξ (y + h).1 (y + h).2 τ) ∈ closedBall p a)
    (hΩ0 : ∀ h : A × A, Ω h 0 = h)
    (hΩder : ∀ h : A × A, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω h)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (β y.1 τ, Ξ y.1 y.2 τ) (Ω h τ))
        (Icc (0 : ℝ) T) τ)
    (hD : ∀ h : A × A, Ω h t = D h)
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt
      (fun y' : A × A => Ξ y'.1 y'.2 t)
      ((ContinuousLinearMap.snd ℝ A A).comp D) y := by
  have hpaired :
      HasFDerivAt
        (fun y' : A × A => (β y'.1 t, Ξ y'.1 y'.2 t)) D y :=
    chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_data
      (g := g) (x₀ := x₀) (β := β) (Ξ := Ξ) (y := y) (Ω := Ω)
      (D := D) (T := T) (a := a) (p := p) (t := t)
      hT hbaseβ0 hbaseβder hbaseΞ0 hbaseΞder hbase_mem hpert
      hΩ0 hΩder hD ht
  simpa using hpaired.snd

end GeodesicTransport
end Poincare
