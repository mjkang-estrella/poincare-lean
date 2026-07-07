import Poincare.Global.TransitionLands

/-!
# Hosted third-variation endpoint CLM

This module packages the fixed-time endpoint map for the hosted
third-variation linear equation.  The construction follows the existing
second-variation pattern: additivity and homogeneity are consequences of
linear ODE uniqueness, and finite dimensionality upgrades the endpoint linear
map to a continuous linear map.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "B" => (E × E) × (E × E)

omit [T2Space M] in
/--
The fixed-time endpoint of a hosted third-variation solution family is a
continuous linear map in the perturbation variable.

This is the level-three analogue of
`secondVariation_endpoint_clm_of_linearODE_uniqueOn_Icc`.  The final
eventual clause is the exact endpoint-CLM package consumed by
`chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually`.
-/
theorem chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc
    [FiniteDimensional ℝ (B × B)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → B × B} {Ω : B × B → ℝ → B × B}
    {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax) {a r L K : ℝ≥0}
    (hpl : ∀ η : B × B,
      IsPicardLindelof
        (fun t ξ =>
          fderiv ℝ
            (fun y' : B × B =>
              let F : B → B :=
                augmentedGeodesicFlowField (chartChristoffelField g x₀)
              (F y'.1, (fderiv ℝ F y'.1) y'.2))
            (ζ t) ξ)
        (tmin := tmin) (tmax := tmax)
        ⟨(0 : ℝ), hzero⟩ η a r L K)
    (hΩ0 : ∀ η : B × B, Ω η 0 = η)
    (hΩder : ∀ η : B × B, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ω η)
        (fderiv ℝ
          (fun y' : B × B =>
            let F : B → B :=
              augmentedGeodesicFlowField (chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ t) (Ω η t))
        (Icc tmin tmax) t)
    (hΩmem : ∀ η : B × B, ∀ t ∈ Icc tmin tmax,
      Ω η t ∈ closedBall η a)
    (hadd_mem : ∀ η η' : B × B, ∀ t ∈ Icc tmin tmax,
      Ω η t + Ω η' t ∈ closedBall (η + η') a)
    (hsmul_mem : ∀ (c : ℝ) (η : B × B), ∀ t ∈ Icc tmin tmax,
      c • Ω η t ∈ closedBall (c • η) a) :
    ∃ D : (B × B) →L[ℝ] (B × B),
      (∀ η : B × B, D η = Ω η T) ∧
        ∀ᶠ h in 𝓝 (0 : B × B),
          Ω h 0 = h ∧
            (∀ t ∈ Icc tmin tmax,
              HasDerivWithinAt (Ω h)
                (fderiv ℝ
                  (fun y' : B × B =>
                    let F : B → B :=
                      augmentedGeodesicFlowField (chartChristoffelField g x₀)
                    (F y'.1, (fderiv ℝ F y'.1) y'.2))
                  (ζ t) (Ω h t))
                (Icc tmin tmax) t) ∧
            Ω h T = D h := by
  let X := B × B
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : B → B := augmentedGeodesicFlowField Γ
  let doubleF : X → X := fun y' => (F y'.1, (fderiv ℝ F y'.1) y'.2)
  let Aop : ℝ → X →L[ℝ] X := fun t => fderiv ℝ doubleF (ζ t)
  have hderA : ∀ η : X, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ω η) (Aop t (Ω η t)) (Icc tmin tmax) t := by
    intro η t ht
    simpa [Aop, doubleF, F, Γ, X] using hΩder η t ht
  have hadd : ∀ η η' : X, Ω (η + η') T = Ω η T + Ω η' T := by
    intro η η'
    have hder_sum : ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun τ : ℝ => Ω η τ + Ω η' τ)
          (Aop t ((fun τ : ℝ => Ω η τ + Ω η' τ) t))
          (Icc tmin tmax) t := by
      intro t ht
      have hder := (hderA η t ht).add (hderA η' t ht)
      simpa [Aop] using hder
    have hinitial :
        Ω (η + η') (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
          (fun τ : ℝ => Ω η τ + Ω η' τ)
            (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
      change Ω (η + η') 0 = Ω η 0 + Ω η' 0
      rw [hΩ0 (η + η'), hΩ0 η, hΩ0 η']
    have hEq :
        EqOn (Ω (η + η')) (fun τ : ℝ => Ω η τ + Ω η' τ)
          (Icc tmin tmax) :=
      linearODE_solution_uniqueOn_Icc
        (A := Aop) (t₀ := ⟨(0 : ℝ), hzero⟩) (x₀ := η + η')
        (a := a) (r := r) (L := L) (K := K)
        (hpl (η + η')) (hderA (η + η')) (hΩmem (η + η'))
        hder_sum (hadd_mem η η') hinitial
    exact hEq hT
  have hsmul : ∀ (c : ℝ) (η : X), Ω (c • η) T = c • Ω η T := by
    intro c η
    have hder_smul : ∀ t ∈ Icc tmin tmax,
        HasDerivWithinAt (fun τ : ℝ => c • Ω η τ)
          (Aop t ((fun τ : ℝ => c • Ω η τ) t))
          (Icc tmin tmax) t := by
      intro t ht
      have hder := (hderA η t ht).const_smul c
      simpa [Aop] using hder
    have hinitial :
        Ω (c • η) (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
          (fun τ : ℝ => c • Ω η τ)
            (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
      change Ω (c • η) 0 = c • Ω η 0
      rw [hΩ0 (c • η), hΩ0 η]
    have hEq :
        EqOn (Ω (c • η)) (fun τ : ℝ => c • Ω η τ)
          (Icc tmin tmax) :=
      linearODE_solution_uniqueOn_Icc
        (A := Aop) (t₀ := ⟨(0 : ℝ), hzero⟩) (x₀ := c • η)
        (a := a) (r := r) (L := L) (K := K)
        (hpl (c • η)) (hderA (c • η)) (hΩmem (c • η))
        hder_smul (hsmul_mem c η) hinitial
    exact hEq hT
  let endpointLinearMap : X →ₗ[ℝ] X :=
    { toFun := fun η => Ω η T
      map_add' := hadd
      map_smul' := hsmul }
  let D : X →L[ℝ] X := LinearMap.toContinuousLinearMap endpointLinearMap
  refine ⟨D, ?_, ?_⟩
  · intro η
    rfl
  · exact Filter.Eventually.of_forall fun h =>
      ⟨hΩ0 h, hΩder h, (show Ω h T = D h from rfl)⟩

end GeodesicTransport
end Poincare
