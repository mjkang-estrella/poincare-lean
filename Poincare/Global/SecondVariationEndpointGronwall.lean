import Poincare.Global.LinearEndpointGronwall
import Poincare.Global.SecondVariationRescale

/-!
# Second-variation endpoint Gronwall comparison

This is the order-two specialization of the generic projected linear-ODE
endpoint estimate.  It compares the derivative endpoint operators produced
along two augmented chart-geodesic trajectories.
-/

noncomputable section

open Metric Set
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

/--
Projected second-variation endpoint operators are Lipschitz when their
augmented base curves are uniformly close and the derivative of the augmented
field is Lipschitz on their common state set.

The initialization `J` permits restricted parameters (for example, varying
only the anchored base velocity), and `P` permits projecting the full
second-variation endpoint to the component used by the exponential chart.
-/
theorem projected_secondVariation_endpoint_clm_lipschitz_of_augmented_base_curves
    {H Y : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ₁ ζ₂ : ℝ → A}
    {Ξ₁ Ξ₂ : H → ℝ → A} {D₁ D₂ : H →L[ℝ] Y}
    (J : H →L[ℝ] A) (P : A →L[ℝ] Y)
    {T t δnorm K : ℝ} {L B : ℝ≥0} {S : Set A}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 ≤ δnorm)
    (hcoeff : LipschitzOnWith L
      (fun z : A =>
        fderiv ℝ
          (augmentedGeodesicFlowField (chartChristoffelField g x₀)) z) S)
    (hζ₁mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₁ τ ∈ S)
    (hζ₂mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₂ τ ∈ S)
    (hζdiff : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖ζ₂ τ - ζ₁ τ‖ ≤ (B : ℝ) * δnorm)
    (hA₁op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ
        (augmentedGeodesicFlowField (chartChristoffelField g x₀))
        (ζ₁ τ)‖ ≤ K)
    (hA₂op : ∀ τ ∈ Ico (0 : ℝ) T,
      ‖fderiv ℝ
        (augmentedGeodesicFlowField (chartChristoffelField g x₀))
        (ζ₂ τ)‖ ≤ K)
    (hΞ₁0 : ∀ h : H, Ξ₁ h 0 = J h)
    (hΞ₂0 : ∀ h : H, Ξ₂ h 0 = J h)
    (hΞ₁der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ξ₁ h)
        (secondVariationFlowFieldAlong
          (chartChristoffelField g x₀) ζ₁ τ (Ξ₁ h τ))
        (Icc (0 : ℝ) T) τ)
    (hΞ₂der : ∀ h : H, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ξ₂ h)
        (secondVariationFlowFieldAlong
          (chartChristoffelField g x₀) ζ₂ τ (Ξ₂ h τ))
        (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : H, D₁ h = P (Ξ₁ h t))
    (hD₂ : ∀ h : H, D₂ h = P (Ξ₂ h t))
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖D₂ - D₁‖ ≤
      (‖P‖ * ‖J‖ * ((L : ℝ) * (B : ℝ)) * Real.exp (K * T) *
          gronwallBound 0 K 1 T) * δnorm := by
  let F : A → A :=
    augmentedGeodesicFlowField (chartChristoffelField g x₀)
  apply
    projected_linearODE_endpoint_clm_lipschitz_of_base_curves
      (F := F) (γ₁ := ζ₁) (γ₂ := ζ₂)
      (Ω₁ := Ξ₁) (Ω₂ := Ξ₂) (D₁ := D₁) (D₂ := D₂)
      J P hT hK hδ
      (by simpa [F] using hcoeff)
      hζ₁mem hζ₂mem hζdiff
      (by simpa [F] using hA₁op)
      (by simpa [F] using hA₂op)
      hΞ₁0 hΞ₂0
  · intro h τ hτ
    simpa [F, secondVariationFlowFieldAlong,
      secondVariationFlowOperator] using hΞ₁der h τ hτ
  · intro h τ hτ
    simpa [F, secondVariationFlowFieldAlong,
      secondVariationFlowOperator] using hΞ₂der h τ hτ
  · exact hD₁
  · exact hD₂
  · exact ht

end GeodesicTransport
end Poincare
