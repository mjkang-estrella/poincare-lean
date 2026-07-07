import Poincare.Global.SecondDischarge

/-!
# Second-variation endpoint Frechet work surface

This module isolates the candidate continuous-linear endpoint map for the
second-variation equation.  It is the order-two analogue of the
`linearizedEndpointCLM` construction: once a second-variation solution family is
available for every perturbation and the standard Picard-Lindelof tube
hypotheses are supplied, uniqueness of the linear system gives endpoint
additivity and homogeneity, and finite dimensionality upgrades the endpoint map
to a CLM.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
The fixed-time endpoint of a second-variation solution family is a continuous
linear map in the perturbation.

This is the CLM candidate needed before a directional-to-Frechet upgrade of the
`D` field can be attempted.  The theorem does not assert the missing
neighborhood-level differentiability of that field; it only packages the
linear endpoint supplied by the second-variation linear ODE.
-/
theorem secondVariation_endpoint_clm_of_linearODE_uniqueOn_Icc
    [FiniteDimensional ℝ ((E × E) × (E × E))]
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {ζ : ℝ → (E × E) × (E × E)}
    {Ξ : ((E × E) × (E × E)) → ℝ → (E × E) × (E × E)}
    {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax) {a r L K : ℝ≥0}
    (hpl : ∀ η : (E × E) × (E × E),
      IsPicardLindelof
        (fun t ξ => secondVariationFlowFieldAlong Γ ζ t ξ)
        (tmin := tmin) (tmax := tmax)
        ⟨(0 : ℝ), hzero⟩ η a r L K)
    (hΞ0 : ∀ η : (E × E) × (E × E), Ξ η 0 = η)
    (hΞder : ∀ η : (E × E) × (E × E), ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ξ η)
        (secondVariationFlowFieldAlong Γ ζ t (Ξ η t))
        (Icc tmin tmax) t)
    (hΞmem : ∀ η : (E × E) × (E × E), ∀ t ∈ Icc tmin tmax,
      Ξ η t ∈ closedBall η a)
    (hadd_mem : ∀ η η' : (E × E) × (E × E), ∀ t ∈ Icc tmin tmax,
      Ξ η t + Ξ η' t ∈ closedBall (η + η') a)
    (hsmul_mem : ∀ (c : ℝ) (η : (E × E) × (E × E)), ∀ t ∈ Icc tmin tmax,
      c • Ξ η t ∈ closedBall (c • η) a) :
    ∃ D : ((E × E) × (E × E)) →L[ℝ] ((E × E) × (E × E)),
      ∀ η : (E × E) × (E × E), D η = Ξ η T := by
  let X := (E × E) × (E × E)
  let A : ℝ → X →L[ℝ] X := fun t => secondVariationFlowOperator Γ (ζ t)
  have hderA : ∀ η : X, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ξ η) (A t (Ξ η t)) (Icc tmin tmax) t := by
    intro η t ht
    simpa [A, X, secondVariationFlowFieldAlong] using hΞder η t ht
  have hadd : ∀ η η' : X, Ξ (η + η') T = Ξ η T + Ξ η' T := by
    intro η η'
    have hder_sum : ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun τ : ℝ => Ξ η τ + Ξ η' τ)
          (A t ((fun τ : ℝ => Ξ η τ + Ξ η' τ) t))
          (Icc tmin tmax) t := by
      intro t ht
      have hder := (hderA η t ht).add (hderA η' t ht)
      simpa [A] using hder
    have hinitial :
        Ξ (η + η') (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
          (fun τ : ℝ => Ξ η τ + Ξ η' τ)
            (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
      change Ξ (η + η') 0 = Ξ η 0 + Ξ η' 0
      rw [hΞ0 (η + η'), hΞ0 η, hΞ0 η']
    have hEq :
        EqOn (Ξ (η + η')) (fun τ : ℝ => Ξ η τ + Ξ η' τ)
          (Icc tmin tmax) :=
      linearODE_solution_uniqueOn_Icc
        (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩) (x₀ := η + η')
        (a := a) (r := r) (L := L) (K := K)
        (hpl (η + η')) (hderA (η + η')) (hΞmem (η + η'))
        hder_sum (hadd_mem η η') hinitial
    exact hEq hT
  have hsmul : ∀ (c : ℝ) (η : X), Ξ (c • η) T = c • Ξ η T := by
    intro c η
    have hder_smul : ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun τ : ℝ => c • Ξ η τ)
          (A t ((fun τ : ℝ => c • Ξ η τ) t))
          (Icc tmin tmax) t := by
      intro t ht
      have hder := (hderA η t ht).const_smul c
      simpa [A] using hder
    have hinitial :
        Ξ (c • η) (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
          (fun τ : ℝ => c • Ξ η τ)
            (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
      change Ξ (c • η) 0 = c • Ξ η 0
      rw [hΞ0 (c • η), hΞ0 η]
    have hEq :
        EqOn (Ξ (c • η)) (fun τ : ℝ => c • Ξ η τ)
          (Icc tmin tmax) :=
      linearODE_solution_uniqueOn_Icc
        (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩) (x₀ := c • η)
        (a := a) (r := r) (L := L) (K := K)
        (hpl (c • η)) (hderA (c • η)) (hΞmem (c • η))
        hder_smul (hsmul_mem c η) hinitial
    exact hEq hT
  let endpointLinearMap : X →ₗ[ℝ] X :=
    { toFun := fun η => Ξ η T
      map_add' := hadd
      map_smul' := hsmul }
  exact ⟨LinearMap.toContinuousLinearMap endpointLinearMap, fun _ => rfl⟩

end GeodesicTransport
end Poincare
