import Poincare.Global.CartanActionEquations

/-!
# Hosted endpoint uniqueness for the Cartan action equation

This module isolates the endpoint-identification step needed by the hosted
Cartan action equation.  The comparison is between the cascade-produced
linearized state and the time-rescaled harmonic state, viewed with its hosted
time derivative as the second component.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanEndpointUnique

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Endpoint identification by hosted linearized ODE uniqueness.

If the cascade state `Ψ w` and the hosted time-rescaling of the harmonic state
`Φ w` solve the same linearized chart-geodesic equation on the same interval,
stay in the same Picard-Lindelöf ball, and have the matching hosted initial
state, then their position endpoints agree at the hosted time `T`.
-/
theorem hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {Ψ Φ : E → ℝ → E × E}
    {w : E} {ε T speed : ℝ} (hε : 0 < ε)
    (hspeed : speed ≠ 0) (hT_ne : T ≠ 0)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E), T⁻¹ • w) a r L K)
    (hΨ0 : Ψ w 0 = ((0 : E), T⁻¹ • w))
    (hΨder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w)
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t (Ψ w t))
        (Icc (-ε) ε) t)
    (hΨmem : ∀ t ∈ Icc (-ε) ε,
      Ψ w t ∈ closedBall ((0 : E), T⁻¹ • w) a)
    (hΦ0 : Φ w 0 = ((0 : E), (speed * T)⁻¹ • w))
    (hΦder : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt
        (fun τ : ℝ =>
          ((Φ w (speed * τ)).1, speed • (Φ w (speed * τ)).2))
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀) γ t
          ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2))
        (Icc (-ε) ε) t)
    (hΦmem : ∀ t ∈ Icc (-ε) ε,
      ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2) ∈
        closedBall ((0 : E), T⁻¹ • w) a)
    (hT : T ∈ Icc (-ε) ε) :
    (Ψ w T).1 = (Φ w (speed * T)).1 := by
  let A : ℝ → (E × E) →L[ℝ] (E × E) :=
    fun t =>
      linearizedGeodesicFlowOperator
        (GeodesicTransport.chartChristoffelField g x₀) (γ t)
  let Φhost : ℝ → E × E :=
    fun t => ((Φ w (speed * t)).1, speed • (Φ w (speed * t)).2)
  have hcoef : speed * (T⁻¹ * speed⁻¹) = T⁻¹ := by
    field_simp [hspeed, hT_ne]
  have hΦhost0 : Φhost 0 = ((0 : E), T⁻¹ • w) := by
    simp [Φhost, hΦ0, smul_smul, hcoef]
  have hΨderA : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt (Ψ w) (A t (Ψ w t)) (Icc (-ε) ε) t := by
    intro t ht
    simpa [A, linearizedGeodesicFlowFieldAlong] using hΨder t ht
  have hΦderA : ∀ t ∈ Icc (-ε) ε,
      HasDerivWithinAt Φhost (A t (Φhost t)) (Icc (-ε) ε) t := by
    intro t ht
    simpa [A, Φhost, linearizedGeodesicFlowFieldAlong] using hΦder t ht
  have hΦmemA : ∀ t ∈ Icc (-ε) ε,
      Φhost t ∈ closedBall ((0 : E), T⁻¹ • w) a := by
    intro t ht
    simpa [Φhost] using hΦmem t ht
  have hinitial :
      Ψ w (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) =
        Φhost (⟨(0 : ℝ), by constructor <;> linarith⟩ : Icc (-ε) ε) := by
    change Ψ w 0 = Φhost 0
    rw [hΨ0, hΦhost0]
  have hEq : EqOn (Ψ w) Φhost (Icc (-ε) ε) :=
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := ⟨(0 : ℝ), by constructor <;> linarith⟩)
      (x₀ := ((0 : E), T⁻¹ • w)) (a := a) (r := r) (L := L) (K := K)
      hpl hΨderA hΨmem hΦderA hΦmemA hinitial
  have hfst := congrArg Prod.fst (hEq hT)
  simpa [Φhost] using hfst

end CartanEndpointUnique
end Poincare
