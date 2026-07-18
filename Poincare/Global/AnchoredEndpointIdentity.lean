import Poincare.Global.UniformFlowExport
import Poincare.Global.SecondDischarge

/-!
# Anchored augmented-endpoint identification

This module isolates the endpoint identity needed to connect the hosted
augmented/second-variation tower to the derivative of the exponential chart.

There are two independent ingredients:

* uniqueness identifies the second component of an augmented solution with
  the hosted linearized solution having the same initial data;
* the strict derivative exported by `EnrichedCascade` identifies the hosted
  linearized endpoint CLM with the Frechet derivative of the exponential
  chart.

The uniqueness lemma is phrased for a zero-centred Picard--Lindelof tube.  As
in `LinearizedAdditivity`, both solutions may first be rescaled into that tube.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace AnchoredEndpointIdentity

open GeodesicTransport

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/--
Two solutions of the same linearized geodesic equation agree if one common
positive rescaling puts both curves in the zero-centred Picard--Lindelof
tube.  This is the uniqueness adapter needed for the second component of an
augmented flow, whose natural initial datum need not itself lie in the
zero-centred tube used by the hosted cascade.
-/
theorem linearizedGeodesicFlow_solution_eq_of_rescaled_uniqueOn_Icc
    {Gamma : X → X →L[ℝ] X →L[ℝ] X}
    {gamma psi phi : ℝ → X × X}
    {tmin tmax : ℝ} {t0 : Icc tmin tmax}
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun z : X × X =>
        linearizedGeodesicFlowOperator Gamma (gamma t) z)
      t0 ((0 : X), (0 : X)) a r L K)
    {S : ℝ} (hS : 0 < S)
    (hpsi0 : psi t0 = phi t0)
    (hpsi : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt psi
        (linearizedGeodesicFlowFieldAlong Gamma gamma t (psi t))
        (Icc tmin tmax) t)
    (hphi : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt phi
        (linearizedGeodesicFlowFieldAlong Gamma gamma t (phi t))
        (Icc tmin tmax) t)
    (hpsi_mem : ∀ t ∈ Icc tmin tmax,
      S⁻¹ • psi t ∈ closedBall ((0 : X), (0 : X)) a)
    (hphi_mem : ∀ t ∈ Icc tmin tmax,
      S⁻¹ • phi t ∈ closedBall ((0 : X), (0 : X)) a) :
    EqOn psi phi (Icc tmin tmax) := by
  let A : ℝ → (X × X) →L[ℝ] (X × X) :=
    fun t => linearizedGeodesicFlowOperator Gamma (gamma t)
  have hpsi_scaled : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (fun tau : ℝ => S⁻¹ • psi tau)
        (A t ((fun tau : ℝ => S⁻¹ • psi tau) t))
        (Icc tmin tmax) t := by
    intro t ht
    have hder := (hpsi t ht).const_smul S⁻¹
    simpa [A, linearizedGeodesicFlowFieldAlong_smul] using hder
  have hphi_scaled : ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (fun tau : ℝ => S⁻¹ • phi tau)
        (A t ((fun tau : ℝ => S⁻¹ • phi tau) t))
        (Icc tmin tmax) t := by
    intro t ht
    have hder := (hphi t ht).const_smul S⁻¹
    simpa [A, linearizedGeodesicFlowFieldAlong_smul] using hder
  have hinitial : S⁻¹ • psi t0 = S⁻¹ • phi t0 := by
    rw [hpsi0]
  have hscaled :
      EqOn (fun t : ℝ => S⁻¹ • psi t)
        (fun t : ℝ => S⁻¹ • phi t) (Icc tmin tmax) :=
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := t0) (x₀ := ((0 : X), (0 : X)))
      (a := a) (r := r) (L := L) (K := K)
      hpl hpsi_scaled hpsi_mem hphi_scaled hphi_mem hinitial
  intro t ht
  have heq := hscaled ht
  have hunscaled := congrArg (fun z : X × X => S • z) heq
  simpa [smul_smul, ne_of_gt hS] using hunscaled

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "A" => (E × E) × (E × E)

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- Select the first-variation position from an augmented state
`((position, velocity), (variation, variationVelocity))`. -/
def augmentedFirstVariationPosition : A →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E E).comp
    (ContinuousLinearMap.snd ℝ (E × E) (E × E))

@[simp]
theorem augmentedFirstVariationPosition_apply (z : A) :
    augmentedFirstVariationPosition z = z.2.1 :=
  rfl

/--
Select the first-variation position from the base augmented endpoint inside a
doubly-augmented state.  This is the post-composition required when a
third-variation endpoint CLM has codomain `A x A`.
-/
def doublyAugmentedBaseFirstVariationPosition : (A × A) →L[ℝ] E :=
  augmentedFirstVariationPosition.comp
    (ContinuousLinearMap.fst ℝ A A)

@[simp]
theorem doublyAugmentedBaseFirstVariationPosition_apply (y : A × A) :
    doublyAugmentedBaseFirstVariationPosition y = y.1.2.1 :=
  rfl

omit [T2Space M] in
/--
Evaluation form of the strict derivative exported by the enriched cascade.
It turns the hosted position endpoint `(Psi w T).1` into the application of
the canonical Frechet derivative of the exponential chart.
-/
theorem linearized_position_endpoint_eq_fderiv_expAtChart_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {Psi : E → ℝ → E × E} {T : ℝ} {q w : E}
    (hadd : ∀ u v : E,
      (Psi (u + v) T).1 = (Psi u T).1 + (Psi v T).1)
    (hsmul : ∀ (c : ℝ) (u : E),
      (Psi (c • u) T).1 = c • (Psi u T).1)
    (hstrict : HasStrictFDerivAt
      (expAtChartOpenPartialHomeomorph (g := g) x0)
      (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul) q) :
    (Psi w T).1 =
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x0) q w := by
  have hfderiv := hstrict.hasFDerivAt.fderiv
  calc
    (Psi w T).1 = linearizedEndpointCLM (Ψ := Psi) T hadd hsmul w := rfl
    _ = fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x0) q w := by
      rw [hfderiv]

omit [T2Space M] in
/--
The exact product association at the anchored augmented endpoint.

For the augmented state `A = (E x E) x (E x E)`, the first factor is the
geodesic state and the second factor is the first-variation state.  Hence the
position derivative is `(beta z T).2.1`, not either first component of the
doubly-augmented endpoint used one level later.
-/
theorem augmented_anchored_second_position_eq_fderiv_expAtChart_apply_of_endpoint_eq
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {beta : A → ℝ → A} {Psi : E → ℝ → E × E}
    {T : ℝ} {q w : E}
    (hadd : ∀ u v : E,
      (Psi (u + v) T).1 = (Psi u T).1 + (Psi v T).1)
    (hsmul : ∀ (c : ℝ) (u : E),
      (Psi (c • u) T).1 = c • (Psi u T).1)
    (hstrict : HasStrictFDerivAt
      (expAtChartOpenPartialHomeomorph (g := g) x0)
      (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul) q)
    (hendpoint :
      (beta
        ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) T).2 =
        Psi w T) :
    (beta
      ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) T).2.1 =
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x0) q w := by
  rw [hendpoint]
  exact
    linearized_position_endpoint_eq_fderiv_expAtChart_apply
      (g := g) (x0 := x0) hadd hsmul hstrict

omit [T2Space M] in
/--
Anchored endpoint identification obtained from augmented-ODE uniqueness.

The hypotheses after `hbeta_der` are precisely the data not currently bundled
by `UniformFlowExport`: alignment of the augmented base component with the
exported hosted base and one common rescaling that puts the two linearized
curves in the zero-centred PL tube.
-/
theorem augmented_anchored_second_position_eq_fderiv_expAtChart_apply_of_rescaled_uniqueOn_Icc
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    {alpha : E × E → ℝ → E × E}
    {beta : A → ℝ → A} {Psi : E → ℝ → E × E}
    {epsilon T : ℝ} {q w : E}
    (hepsilon : 0 < epsilon) (hT : T ∈ Icc (-epsilon) epsilon)
    (hadd : ∀ u v : E,
      (Psi (u + v) T).1 = (Psi u T).1 + (Psi v T).1)
    (hsmul : ∀ (c : ℝ) (u : E),
      (Psi (c • u) T).1 = c • (Psi u T).1)
    (hlinearized :
      EnrichedCascade.LinearizedFamilyPackage g x0 T epsilon alpha q Psi)
    (hstrict : HasStrictFDerivAt
      (expAtChartOpenPartialHomeomorph (g := g) x0)
      (linearizedEndpointCLM (Ψ := Psi) T hadd hsmul) q)
    (hbeta0 :
      beta ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) 0 =
        ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)))
    (hbeta_der : ∀ t ∈ Icc (-epsilon) epsilon,
      HasDerivWithinAt
        (beta ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)))
        (augmentedGeodesicFlowField
          (GeodesicTransport.chartChristoffelField g x0)
          (beta
            ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) t))
        (Icc (-epsilon) epsilon) t)
    (hbase : ∀ t ∈ Icc (-epsilon) epsilon,
      (beta
        ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) t).1 =
        alpha (extChartAt I x0 x0, T⁻¹ • q) t)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun z : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x0)
          (alpha (extChartAt I x0 x0, T⁻¹ • q) t) z)
      (tmin := -epsilon) (tmax := epsilon)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E), (0 : E)) a r L K)
    {S : ℝ} (hS : 0 < S)
    (hbeta_mem : ∀ t ∈ Icc (-epsilon) epsilon,
      S⁻¹ •
          (beta
            ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) t).2 ∈
        closedBall ((0 : E), (0 : E)) a)
    (hPsi_mem : ∀ t ∈ Icc (-epsilon) epsilon,
      S⁻¹ • Psi w t ∈ closedBall ((0 : E), (0 : E)) a) :
    (beta
      ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w)) T).2.1 =
      fderiv ℝ (expAtChartOpenPartialHomeomorph (g := g) x0) q w := by
  let z : A :=
    ((extChartAt I x0 x0, T⁻¹ • q), ((0 : E), T⁻¹ • w))
  let gamma : ℝ → E × E :=
    alpha (extChartAt I x0 x0, T⁻¹ • q)
  let phi : ℝ → E × E := fun t => (beta z t).2
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlinearized
  rcases hlinearized with
    ⟨hPsi0, hPsi_der, _hPsi_der0T, _hPsiAt, _hflow, _hspeed⟩
  have hphi0 : phi 0 = Psi w 0 := by
    have hsnd := congrArg Prod.snd hbeta0
    simpa [phi, z, hPsi0 w] using hsnd
  have hphi_der : ∀ t ∈ Icc (-epsilon) epsilon,
      HasDerivWithinAt phi
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x0)
          gamma t (phi t))
        (Icc (-epsilon) epsilon) t := by
    intro t ht
    have hsnd := (hbeta_der t ht).hasFDerivWithinAt.snd.hasDerivWithinAt
    have hsnd' :
        HasDerivWithinAt
          (fun tau : ℝ => (beta z tau).2)
          (linearizedGeodesicFlowFieldAlong
            (chartChristoffelField g x0) (fun tau : ℝ => (beta z tau).1)
            t ((beta z t).2))
          (Icc (-epsilon) epsilon) t := by
      simpa [z, augmentedGeodesicFlowField,
        linearizedGeodesicFlowFieldAlong] using hsnd
    have hzbase : (beta z t).1 = gamma t := by
      simpa [z, gamma] using hbase t ht
    change HasDerivWithinAt (fun tau : ℝ => (beta z tau).2)
      (linearizedGeodesicFlowOperator (chartChristoffelField g x0)
        (beta z t).1 (beta z t).2) (Icc (-epsilon) epsilon) t at hsnd'
    rw [hzbase] at hsnd'
    simpa [phi, gamma, z, linearizedGeodesicFlowFieldAlong] using hsnd'
  have heq : EqOn phi (Psi w) (Icc (-epsilon) epsilon) :=
    linearizedGeodesicFlow_solution_eq_of_rescaled_uniqueOn_Icc
      (Gamma := GeodesicTransport.chartChristoffelField g x0)
      (gamma := gamma) (psi := phi) (phi := Psi w)
      (t0 := ⟨(0 : ℝ), by constructor <;> linarith⟩)
      (a := a) (r := r) (L := L) (K := K)
      hpl hS hphi0 hphi_der
      (by simpa [gamma] using hPsi_der w)
      (by simpa [phi, z] using hbeta_mem)
      hPsi_mem
  apply
    augmented_anchored_second_position_eq_fderiv_expAtChart_apply_of_endpoint_eq
      (g := g) (x0 := x0) (beta := beta) (Psi := Psi)
      hadd hsmul hstrict
  exact heq hT

end AnchoredEndpointIdentity
end Poincare
