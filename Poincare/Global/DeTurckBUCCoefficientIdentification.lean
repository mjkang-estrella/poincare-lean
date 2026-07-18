import Poincare.Global.DeTurckBUCChartCovariance
import Poincare.Global.HeatSemigroupBUCGeneratorEvolution

/-!
# Coefficient identification for the `BUC` Ricci--DeTurck solver

The abstract fixed-point output has initial rate

`A u₀ + N(u₀ + c)`.

This file isolates the exact local coefficient facts needed to identify that
rate with the geometric coordinate tensor `-2 Ric + L_W g`.  The split is the
standard parabolic one:

* `A u₀` is the flat componentwise Laplacian of the perturbation;
* `N(u₀ + c)` is the geometric coordinate right-hand side minus the flat
  Laplacian of the full coefficient, plus the flat Laplacian of the fixed
  background.

For `C²` perturbation and background coefficients, linearity of the
Laplacian then proves the desired equality.  Thus neither chart covariance
nor the full PDE conclusion is assumed.  The only remaining analytic inputs
are displayed scalar coefficient identities.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace Laplacian
  BoundedContinuousFunction Manifold ContDiff BigOperators

namespace Poincare

section CoordinateCoefficientCalculus

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Evaluation of a finite-dimensional coordinate two-tensor on two fixed
vectors, as a continuous linear functional on the tensor target itself. -/
def coordinateTwoTensorEvaluationLinearMap (v w : E) :
    CoordinateTwoTensor E →ₗ[ℝ] ℝ where
  toFun B := ⟪B v, w⟫_ℝ
  map_add' B C := by
    rw [ContinuousLinearMap.add_apply, inner_add_left]
  map_smul' c B := by
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    rfl

/-- The target-level two-tensor evaluation functional is continuous. -/
def coordinateTwoTensorEvaluationCLM (v w : E) :
    CoordinateTwoTensor E →L[ℝ] ℝ :=
  LinearMap.mkContinuous (coordinateTwoTensorEvaluationLinearMap v w)
    (‖v‖ * ‖w‖) (fun B ↦ by
      change |⟪B v, w⟫_ℝ| ≤ (‖v‖ * ‖w‖) * ‖B‖
      calc
        |⟪B v, w⟫_ℝ| ≤ ‖B‖ * ‖v‖ * ‖w‖ :=
          abs_coordinateTwoTensor_apply_le B v w
        _ = (‖v‖ * ‖w‖) * ‖B‖ := by ring)

@[simp]
theorem coordinateTwoTensorEvaluationCLM_apply
    (v w : E) (B : CoordinateTwoTensor E) :
    coordinateTwoTensorEvaluationCLM v w B = ⟪B v, w⟫_ℝ :=
  rfl

/-- Endpoint fundamental theorem of calculus.  A continuous Banach-valued
path with a continuous derivative field on the closed half-line and the
claimed derivative at every positive time has that derivative from the right
at zero. -/
theorem hasDerivWithinAt_zero_of_continuous_derivative_on_Ioi
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f f' : ℝ → G) (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ t : ℝ, 0 < t → HasDerivAt f (f' t) t) :
    HasDerivWithinAt f (f' 0) (Set.Ici 0) 0 := by
  have hidentity : ∀ {t : ℝ}, 0 ≤ t →
      (∫ s : ℝ in (0 : ℝ)..t, f' s) = f t - f 0 := by
    intro t ht
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
      hf.continuousOn
      (fun s hs ↦ hderiv s hs.1)
      (hf'.intervalIntegrable 0 t)
  have hint : HasDerivAt
      (fun t : ℝ ↦ ∫ s : ℝ in (0 : ℝ)..t, f' s) (f' 0) 0 := by
    simpa using (hf'.integral_hasStrictDerivAt (0 : ℝ) 0).hasDerivAt
  have hsum : HasDerivWithinAt
      (fun t : ℝ ↦ f 0 + ∫ s : ℝ in (0 : ℝ)..t, f' s)
      (f' 0) (Set.Ici 0) 0 :=
    hint.hasDerivWithinAt.const_add (f 0)
  apply hsum.congr
  · intro t ht
    rw [hidentity ht]
    abel
  · simp

/-- Flat componentwise Laplacian of a Riesz-operator coordinate coefficient,
evaluated on fixed tangent vectors. -/
def coordinateMetricLaplacianValue
    (g : CoordinateBUCTensor E) (x v w : E) : ℝ :=
  (Δ fun y : E ↦ coordinateMetricValue g y v w) x

/-- The scalar heat orbit obtained by evaluating a tensor-valued `BUC` heat
orbit at fixed spatial and tangent data. -/
def coordinateMetricHeatOrbit
    (u : CoordinateBUCTensor E) (x v w : E) : ℝ → ℝ :=
  fun t ↦ coordinateMetricValue
    (vectorHeatSemigroupBUCExtended
      (E := E) (F := CoordinateTwoTensor E) t u) x v w

@[simp]
theorem coordinateMetricHeatOrbit_zero
    (u : CoordinateBUCTensor E) (x v w : E) :
    coordinateMetricHeatOrbit u x v w 0 = coordinateMetricValue u x v w := by
  simp [coordinateMetricHeatOrbit, vectorHeatSemigroupBUCExtended]

/-- At positive time, scalar evaluation of the tensor-valued `BUC` heat
semigroup is the scalar heat convolution of the evaluated initial
coefficient. -/
theorem coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
    (u : CoordinateBUCTensor E) {t : ℝ} (ht : 0 < t) (x v w : E) :
    coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) x v w =
      heatSolution (E := E) t
        (fun y : E ↦ coordinateMetricValue u y v w) x := by
  have hbound : ∀ y : E,
      ‖(u : E → CoordinateTwoTensor E) y‖ ≤ ‖u‖ := by
    intro y
    exact BoundedContinuousFunction.norm_coe_le_norm
      (u : E →ᵇ CoordinateTwoTensor E) y
  have hconv := vectorHeatSolution_apply_continuousLinearMap
    (E := E) ht u.1.continuous.aestronglyMeasurable hbound
    (coordinateTwoTensorEvaluationCLM v w) x
  rw [vectorHeatSemigroupBUCExtended, dif_pos ht,
    vectorHeatSemigroupBUCLM_apply]
  simpa [vectorHeatSemigroupBUC, coordinateMetricValue,
    vectorHeatSolutionBCF_apply] using hconv

/-- Every positive-time scalar coordinate of a tensor-valued `BUC` heat
orbit has derivative equal to the scalar flat Laplacian of the current heat
coefficient. -/
theorem coordinateMetricValue_heatOrbit_hasDerivAt_laplacian
    (u : CoordinateBUCTensor E) {t : ℝ} (ht : 0 < t) (x v w : E) :
    HasDerivAt
      (coordinateMetricHeatOrbit u x v w)
      (coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) x v w) t := by
  let f : E → ℝ := fun y ↦ coordinateMetricValue u y v w
  let L : CoordinateTwoTensor E →L[ℝ] ℝ :=
    coordinateTwoTensorEvaluationCLM v w
  have hf : AEStronglyMeasurable f volume := by
    exact (L.continuous.comp u.1.continuous).aestronglyMeasurable
  have htargetBound : ∀ y : E,
      ‖(u : E → CoordinateTwoTensor E) y‖ ≤ ‖u‖ := by
    intro y
    exact BoundedContinuousFunction.norm_coe_le_norm
      (u : E →ᵇ CoordinateTwoTensor E) y
  have hbound : ∀ y : E, ‖f y‖ ≤ ‖u‖ * ‖v‖ * ‖w‖ := by
    intro y
    change |coordinateMetricValue u y v w| ≤ ‖u‖ * ‖v‖ * ‖w‖
    exact abs_coordinateMetricValue_le (E := E) u y v w
  have hheatDiff : DifferentiableAt ℝ
      (fun τ : ℝ ↦ heatSolution (E := E) τ f x) t := by
    have hvec := vectorHeatSolution_time_differentiableAt
      (E := E) (F := CoordinateTwoTensor E) ht
      u.1.continuous.aestronglyMeasurable htargetBound x
    have hL : DifferentiableAt ℝ
        (fun τ : ℝ ↦ L
          (vectorHeatSolution (E := E) τ
            (u : E → CoordinateTwoTensor E) x)) t :=
      L.differentiableAt.comp t hvec
    have heq :
        (fun τ : ℝ ↦ heatSolution (E := E) τ f x) =ᶠ[nhds t]
          (fun τ : ℝ ↦ L
            (vectorHeatSolution (E := E) τ
              (u : E → CoordinateTwoTensor E) x)) := by
      filter_upwards [eventually_gt_nhds ht] with τ hτ
      exact (vectorHeatSolution_apply_continuousLinearMap
        (E := E) hτ u.1.continuous.aestronglyMeasurable
        htargetBound L x).symm
    exact hL.congr_of_eventuallyEq heq
  have hpde := heatSolution_solves_heatEquation_of_bounded_measurable
    (E := E) ht hf hbound x
  have hheat : HasDerivAt
      (fun τ : ℝ ↦ heatSolution (E := E) τ f x)
      ((Δ fun y : E ↦ heatSolution (E := E) t f y) x) t := by
    rw [← hpde]
    exact hheatDiff.hasDerivAt
  have horbit :
      coordinateMetricHeatOrbit u x v w =ᶠ[nhds t]
        (fun τ : ℝ ↦ heatSolution (E := E) τ f x) := by
    filter_upwards [eventually_gt_nhds ht] with τ hτ
    exact coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
      u hτ x v w
  have hspace :
      (fun y : E ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) y v w) =
        fun y : E ↦ heatSolution (E := E) t f y := by
    funext y
    exact coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
      u ht y v w
  change HasDerivAt _
    ((Δ fun y : E ↦ coordinateMetricValue
      (vectorHeatSemigroupBUCExtended
        (E := E) (F := CoordinateTwoTensor E) t u) y v w) x) t
  rw [hspace]
  exact hheat.congr_of_eventuallyEq horbit

/-- If a `BUC` coefficient `lapu` represents the scalar Laplacian at the
initial point and positive-time heat convolution commutes with that scalar
Laplacian, then the initial scalar heat orbit has the classical right
derivative.  No generator-domain hypothesis is used here. -/
theorem coordinateMetricValue_heatTrace_of_laplacian_commutes
    (u lapu : CoordinateBUCTensor E) (z v w : E)
    (hlapu : coordinateMetricValue lapu z v w =
      coordinateMetricLaplacianValue u z v w)
    (hcommute : ∀ t : ℝ, 0 < t →
      coordinateMetricLaplacianValue
          (vectorHeatSemigroupBUCExtended
            (E := E) (F := CoordinateTwoTensor E) t u) z v w =
        coordinateMetricValue
          (vectorHeatSemigroupBUCExtended
            (E := E) (F := CoordinateTwoTensor E) t lapu) z v w) :
    HasDerivWithinAt
      (coordinateMetricHeatOrbit u z v w)
      (coordinateMetricLaplacianValue u z v w) (Set.Ici 0) 0 := by
  let orbitU : ℝ → ℝ := coordinateMetricHeatOrbit u z v w
  let orbitLap : ℝ → ℝ := coordinateMetricHeatOrbit lapu z v w
  let L := coordinateMetricEvaluationCLM z v w
  have horbitU : Continuous orbitU := by
    exact L.continuous.comp
      (continuous_vectorHeatSemigroupBUCExtended_apply
        (E := E) (F := CoordinateTwoTensor E) u)
  have horbitLap : Continuous orbitLap := by
    exact L.continuous.comp
      (continuous_vectorHeatSemigroupBUCExtended_apply
        (E := E) (F := CoordinateTwoTensor E) lapu)
  have hpositive : ∀ t : ℝ, 0 < t →
      HasDerivAt orbitU (orbitLap t) t := by
    intro t ht
    have h := coordinateMetricValue_heatOrbit_hasDerivAt_laplacian
      u ht z v w
    rw [hcommute t ht] at h
    exact h
  have hzero := hasDerivWithinAt_zero_of_continuous_derivative_on_Ioi
    orbitU orbitLap horbitU horbitLap hpositive
  simpa [orbitU, orbitLap, hlapu] using hzero

/-- Riesz conversion commutes with addition of coordinate coefficients. -/
theorem coordinateBilinearFormAt_add
    (g h : CoordinateBUCTensor E) (x : E) :
    coordinateBilinearFormAt (g + h) x =
      coordinateBilinearFormAt g x + coordinateBilinearFormAt h x := by
  ext v w
  simp only [coordinateBilinearFormAt_apply,
    ContinuousLinearMap.add_apply, coordinateMetricValue_add]

/-- Riesz conversion commutes with subtraction of coordinate coefficients. -/
theorem coordinateBilinearFormAt_sub
    (g h : CoordinateBUCTensor E) (x : E) :
    coordinateBilinearFormAt (g - h) x =
      coordinateBilinearFormAt g x - coordinateBilinearFormAt h x := by
  ext v w
  simp only [coordinateBilinearFormAt_apply, coordinateMetricValue,
    Submodule.coe_sub, BoundedContinuousFunction.sub_apply,
    ContinuousLinearMap.sub_apply]
  rw [inner_sub_left]

/-- Scalar evaluation commutes with a finite sum of `BUC` coordinate
two-tensor coefficients. -/
theorem coordinateMetricValue_finset_sum
    {ι : Type*} (s : Finset ι) (q : ι → CoordinateBUCTensor E)
    (x v w : E) :
    coordinateMetricValue (∑ i ∈ s, q i) x v w =
      ∑ i ∈ s, coordinateMetricValue (q i) x v w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coordinateMetricValue]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, coordinateMetricValue_add, ih]

/-- Fully expanded scalar coordinate value of the finite DeTurck-shaped
remainder package. -/
def deTurckShapedRemainderCoordinateValue
    {ι κ : Type*}
    (D : DeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (q : CoordinateBUCTensor E) (x v w : E) : ℝ :=
  coordinateMetricValue (D.linear q) x v w +
    (∑ i ∈ D.quadraticTerms,
      coordinateMetricValue
        (quadraticOfCLM (D.quadratic i) q) x v w) +
    (∑ j ∈ D.compositionTerms,
      coordinateMetricValue (D.outer j (D.inner j q)) x v w) +
    ∑ j ∈ D.bilinearTerms,
      coordinateMetricValue
        (D.bilinear j (D.left j q) (D.right j q)) x v w

/-- Scalar evaluation of a DeTurck-shaped remainder is exactly the sum of
the scalar evaluations of its linear, quadratic, composed, and bilinear
coefficient terms.  This removes the assembled `nonlinearity` abbreviation
from the geometric coefficient-identification boundary. -/
theorem coordinateMetricValue_deTurckShaped_nonlinearity_expanded
    {ι κ : Type*}
    (D : DeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (q : CoordinateBUCTensor E) (x v w : E) :
    coordinateMetricValue (D.nonlinearity q) x v w =
      coordinateMetricValue (D.linear q) x v w +
        (∑ i ∈ D.quadraticTerms,
          coordinateMetricValue
            (quadraticOfCLM (D.quadratic i) q) x v w) +
        (∑ j ∈ D.compositionTerms,
          coordinateMetricValue (D.outer j (D.inner j q)) x v w) +
        ∑ j ∈ D.bilinearTerms,
          coordinateMetricValue
            (D.bilinear j (D.left j q) (D.right j q)) x v w := by
  simp only [DeTurckShapedBUCRemainderData.nonlinearity,
    coordinateMetricValue_add, coordinateMetricValue_finset_sum]

/-- Compact name for the preceding termwise expansion. -/
theorem coordinateMetricValue_deTurckShaped_nonlinearity_eq_coordinateValue
    {ι κ : Type*}
    (D : DeTurckShapedBUCRemainderData
      (E := E) (F := CoordinateTwoTensor E) ι κ)
    (q : CoordinateBUCTensor E) (x v w : E) :
    coordinateMetricValue (D.nonlinearity q) x v w =
      deTurckShapedRemainderCoordinateValue D q x v w := by
  exact coordinateMetricValue_deTurckShaped_nonlinearity_expanded
    D q x v w

/-- Operator-valued `C²` regularity gives `C²` regularity of every scalar
coordinate coefficient. -/
theorem coordinateMetricValue_contDiffAt_two
    (g : CoordinateBUCTensor E) {x : E}
    (hg : ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt g y) x)
    (v w : E) :
    ContDiffAt ℝ 2 (fun y ↦ coordinateMetricValue g y v w) x := by
  have hv : ContDiffAt ℝ 2 (fun _y : E ↦ v) x := contDiffAt_const
  have hw : ContDiffAt ℝ 2 (fun _y : E ↦ w) x := contDiffAt_const
  simpa only [coordinateBilinearFormAt_apply] using
    (hg.clm_apply hv).clm_apply hw

/-- The flat Laplacian of a sum of `C²` coordinate coefficients is the sum
of their scalar flat Laplacians. -/
theorem coordinateMetricLaplacianValue_add
    (g h : CoordinateBUCTensor E) {x : E}
    (hg : ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt g y) x)
    (hh : ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt h y) x)
    (v w : E) :
    coordinateMetricLaplacianValue (g + h) x v w =
      coordinateMetricLaplacianValue g x v w +
        coordinateMetricLaplacianValue h x v w := by
  let fg : E → ℝ := fun y ↦ coordinateMetricValue g y v w
  let fh : E → ℝ := fun y ↦ coordinateMetricValue h y v w
  have hfg : ContDiffAt ℝ 2 fg x :=
    coordinateMetricValue_contDiffAt_two g hg v w
  have hfh : ContDiffAt ℝ 2 fh x :=
    coordinateMetricValue_contDiffAt_two h hh v w
  have hadd := hfg.laplacian_add hfh
  change (Δ fun y : E ↦ coordinateMetricValue (g + h) y v w) x = _
  have hfun : (fun y : E ↦ coordinateMetricValue (g + h) y v w) =
      fg + fh := by
    funext y
    exact coordinateMetricValue_add g h y v w
  rw [hfun]
  exact hadd

/-- A strong `BUC` heat-generator value agrees at one scalar coordinate with
the classical flat Laplacian as soon as that scalar heat orbit has the
expected one-sided derivative at zero.  This is strictly weaker than
constructing a second global `BUC` generator-graph representative for the
Laplacian. -/
theorem coordinateMetricValue_generator_eq_laplacian_of_heatTrace
    (u Au : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E)
    (hheatTrace : HasDerivWithinAt
      (coordinateMetricHeatOrbit u z v w)
      (coordinateMetricLaplacianValue u z v w) (Set.Ici 0) 0) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  have hevaluated := Poincare.HasDerivWithinAt.coordinateMetricValue hu z v w
  change HasDerivWithinAt (coordinateMetricHeatOrbit u z v w)
    (coordinateMetricValue Au z v w) (Set.Ici 0) 0 at hevaluated
  have hderiv := (uniqueDiffOn_Ici (0 : ℝ)).eq Set.self_mem_Ici
    hevaluated hheatTrace
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hderiv

/-- Concrete positive-time commutation criterion for identifying the strong
heat generator with the scalar flat Laplacian at one coordinate. -/
theorem coordinateMetricValue_generator_eq_laplacian_of_laplacian_commutes
    (u Au lapu : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E)
    (hlapu : coordinateMetricValue lapu z v w =
      coordinateMetricLaplacianValue u z v w)
    (hcommute : ∀ t : ℝ, 0 < t →
      coordinateMetricLaplacianValue
          (vectorHeatSemigroupBUCExtended
            (E := E) (F := CoordinateTwoTensor E) t u) z v w =
        coordinateMetricValue
          (vectorHeatSemigroupBUCExtended
            (E := E) (F := CoordinateTwoTensor E) t lapu) z v w) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  apply coordinateMetricValue_generator_eq_laplacian_of_heatTrace
    u Au hu z v w
  exact coordinateMetricValue_heatTrace_of_laplacian_commutes
    u lapu z v w hlapu hcommute

end CoordinateCoefficientCalculus

section SmoothChartCoefficients

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Smoothness of a closed smooth metric supplies `C²` regularity of its
bilinear-form-valued coefficient in every genuine preferred chart. -/
theorem deTurckChartMetric_contDiffAt_two_of_mem_target
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) :
    ContDiffAt ℝ 2 (CovariantDerivative.chartMetric g.inner anchor) z := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I
        ((closedSmoothModelWithCorners n).prod
          𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y : M ↦
          (⟨y, g.inner y⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦
                TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  apply Poincare.contDiffAt_clm_of_apply
  intro v
  apply Poincare.contDiffAt_clm_of_apply
  intro w
  have hscalar :=
    CovariantDerivative.contMDiffOn_chartMetric_pairing
      g.inner anchor htwo_add_one_le_top hg2 v w z hz
  exact contMDiffAt_iff_contDiffAt.mp
    (hscalar.contMDiffAt ((isOpen_extChartAt_target anchor).mem_nhds hz))

/-- A `BUC` coefficient germ equal to an honest smooth chart metric is itself
`C²` at the represented point.  This is the precise spatial-regularity bridge
missing from the bare `BUC` type. -/
theorem coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
    (q : CoordinateBUCTensor E)
    (g : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hgerm :
      (fun y ↦ coordinateBilinearFormAt q y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric g.inner anchor) :
    ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt q y) z := by
  exact (deTurckChartMetric_contDiffAt_two_of_mem_target g anchor hz).congr_of_eventuallyEq hgerm

/-- If the full coefficient germ and background germ are honest smooth chart
metrics, then their `BUC` perturbation difference is `C²`.  This derives the
regularity used by the flat-Laplacian split from geometric coefficient germs
rather than postulating regularity of the perturbation. -/
theorem coordinateBilinearFormAt_perturbation_contDiffAt_two_of_metric_germs
    (u c : CoordinateBUCTensor E)
    (g bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt (u + c) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric g.inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt c y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor) :
    ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u y) z := by
  have hfullC2 :=
    coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
      (u + c) g anchor hz hfullGerm
  have hbackgroundC2 :=
    coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
      c bg anchor hz hbackgroundGerm
  have hsub : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt (u + c) y -
        coordinateBilinearFormAt c y) z :=
    hfullC2.sub hbackgroundC2
  have hfun : (fun y ↦ coordinateBilinearFormAt u y) =
      (fun y ↦ coordinateBilinearFormAt (u + c) y -
        coordinateBilinearFormAt c y) := by
    funext y
    rw [← coordinateBilinearFormAt_sub,
      show (u + c) - c = u from add_sub_cancel_right u c]
  rw [hfun]
  exact hsub

end SmoothChartCoefficients

section RicciDeTurckCoefficientSplit

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {iota kappa : Type*}

/-- The concrete Ricci--DeTurck coefficient after removing the flat heat
principal part.  At a genuine cutoff-one chart point it consists of the
intrinsic curvature trace, ordinary coordinate metric advection, the two
ordinary derivative slots of the DeTurck field, and the fixed-background
Laplacian correction. -/
noncomputable def deTurckChartPrincipalRemovedCoefficientValue
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (t : ℝ) (z : E) (hz : z ∈ (extChartAt I anchor).target)
    (full background : CoordinateBUCTensor E) (v w : E) : ℝ :=
  -2 * LinearMap.trace ℝ E
      (chartRicciCurvatureEndAt (gt t) anchor z hz v w) +
    deTurckChartMetricAdvectionAt gt bg anchor t z v w +
    CovariantDerivative.chartMetric (gt t).inner anchor z
      (deTurckChartFieldDerivativeAt gt bg anchor t z v) w +
    CovariantDerivative.chartMetric (gt t).inner anchor z v
      (deTurckChartFieldDerivativeAt gt bg anchor t z w) -
    coordinateMetricLaplacianValue full z v w +
    coordinateMetricLaplacianValue background z v w

/-- At every genuine cutoff-one chart point, the geometric evolution with
its flat principal part removed is exactly the explicit curvature/advection/
field-derivative coefficient above. -/
theorem deTurckChartMetricEvolution_sub_laplacian_eq_principalRemovedCoefficientValue
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor y : M) (t : ℝ)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield : DeTurckVectorFieldRegularAt gt bg t)
    (full background : CoordinateBUCTensor E) (v w : E) :
    deTurckChartMetricEvolutionBilin gt bg anchor t
          (extChartAt I anchor y) v w -
        coordinateMetricLaplacianValue full
          (extChartAt I anchor y) v w +
        coordinateMetricLaplacianValue background
          (extChartAt I anchor y) v w =
      deTurckChartPrincipalRemovedCoefficientValue gt bg anchor t
        (extChartAt I anchor y) ((extChartAt I anchor).map_source hy)
        full background v w := by
  simp only [deTurckChartMetricEvolutionBilin,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [deTurckChartRicciBilin_eq_trace_chartRicciCurvatureEndAt
      gt anchor t (extChartAt I anchor y)
      ((extChartAt I anchor).map_source hy) v w,
    deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
      gt bg anchor t hy hcutoff hfield v w]
  unfold deTurckChartPrincipalRemovedCoefficientValue
  ring

/-- Exact coefficient calculation at the principal/remainder boundary.

The heat-generator hypothesis identifies `A u₀` with the flat Laplacian
of the perturbation.  The remainder hypothesis identifies the assembled
nonlinearity with the geometric right-hand side after removing the flat
Laplacian of the full metric and restoring the fixed background Laplacian.
`C²` regularity is used only to prove
`Δ(u₀ + c) = Δu₀ + Δc`. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hgenerator : ∀ v w : E,
      coordinateMetricValue Au₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  ext v w
  simp only [coordinateBilinearFormAt_apply, coordinateMetricValue_add]
  rw [hgenerator v w, hremainder v w,
    coordinateMetricLaplacianValue_add u₀ D.background
      hu₀C2 hbackgroundC2 v w]
  ring

/-- Fully explicit geometric-coefficient form of the local calculation.  The
finite algebraic remainder is matched only against the proved
curvature/advection/field-derivative formula; the conversion of that formula
to `-2 Ric + L_W g - Δg + Δbackground` is discharged by the preceding
geometric theorem. -/
theorem coordinateBilinearFormAt_generator_add_explicit_principalRemoved_eq_deTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor y : M)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield : DeTurckVectorFieldRegularAt gt bg 0)
    (hu₀C2 : ContDiffAt ℝ 2
      (fun z ↦ coordinateBilinearFormAt u₀ z)
      (extChartAt I anchor y))
    (hbackgroundC2 : ContDiffAt ℝ 2
      (fun z ↦ coordinateBilinearFormAt D.background z)
      (extChartAt I anchor y))
    (hgenerator : ∀ v w : E,
      coordinateMetricValue Au₀ (extChartAt I anchor y) v w =
        coordinateMetricLaplacianValue u₀
          (extChartAt I anchor y) v w)
    (hexplicit : ∀ v w : E,
      deTurckShapedRemainderCoordinateValue D.base
          (u₀ + D.background) (extChartAt I anchor y) v w =
        deTurckChartPrincipalRemovedCoefficientValue gt bg anchor 0
          (extChartAt I anchor y) ((extChartAt I anchor).map_source hy)
          (u₀ + D.background) D.background v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background))
        (extChartAt I anchor y) =
      deTurckChartMetricEvolutionBilin gt bg anchor 0
        (extChartAt I anchor y) := by
  apply coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    D u₀ Au₀ gt bg anchor (extChartAt I anchor y)
      hu₀C2 hbackgroundC2 hgenerator
  intro v w
  rw [coordinateMetricValue_deTurckShaped_nonlinearity_eq_coordinateValue,
    hexplicit v w]
  exact
    (deTurckChartMetricEvolution_sub_laplacian_eq_principalRemovedCoefficientValue
      gt bg anchor y 0 hy hcutoff hfield
      (u₀ + D.background) D.background v w).symm

/-- Minimal local analytic form of the coefficient calculation.  Instead of
requiring a second global generator-graph witness for a `BUC` Laplacian, it
assumes only the classical one-sided heat trace for each scalar coefficient
at the single spatial point under consideration. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_heatTrace
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hheatTrace : ∀ v w : E, HasDerivWithinAt
      (coordinateMetricHeatOrbit u₀ z v w)
      (coordinateMetricLaplacianValue u₀ z v w) (Set.Ici 0) 0)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    D u₀ Au₀ gt bg anchor z hu₀C2 hbackgroundC2
  · intro v w
    exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
      u₀ Au₀ hu₀ z v w (hheatTrace v w)
  · exact hremainder

/-- Positive-time heat/Laplacian commutation form of the principal-part
identification.  The candidate `lapu₀` only has to be a `BUC` representative
of the componentwise Laplacian and commute with positive-time heat
convolution; it need not separately be placed in the strong generator graph. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_laplacian_commutes
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hlapu₀ : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hcommute : ∀ t : ℝ, 0 < t → ∀ v w : E,
      coordinateMetricLaplacianValue
          (vectorHeatSemigroupBUCExtended t u₀) z v w =
        coordinateMetricValue
          (vectorHeatSemigroupBUCExtended t lapu₀) z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_heatTrace
      D u₀ Au₀ hu₀ gt bg anchor z hu₀C2 hbackgroundC2
  · intro v w
    exact coordinateMetricValue_heatTrace_of_laplacian_commutes
      u₀ lapu₀ z v w (hlapu₀ v w) (fun t ht ↦ hcommute t ht v w)
  · exact hremainder

/-- Exact coefficient calculation with the assembled lower-order hypothesis
expanded term by term.  The right-hand side is the actual chart formula
`-2 Ric + L_W g`, with only the flat Laplacian split subtracted.  Thus this
statement no longer hides either the polynomial coordinate terms or the
geometric evolution behind an abbreviation. -/
theorem coordinateBilinearFormAt_generator_add_expanded_remainder_eq_deTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hgenerator : ∀ v w : E,
      coordinateMetricValue Au₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hexpandedRemainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.linear (u₀ + D.background)) z v w +
          (∑ i ∈ D.base.quadraticTerms,
            coordinateMetricValue
              (quadraticOfCLM (D.base.quadratic i)
                (u₀ + D.background)) z v w) +
          (∑ j ∈ D.base.compositionTerms,
            coordinateMetricValue
              (D.base.outer j
                (D.base.inner j (u₀ + D.background))) z v w) +
          (∑ j ∈ D.base.bilinearTerms,
            coordinateMetricValue
              (D.base.bilinear j
                (D.base.left j (u₀ + D.background))
                (D.base.right j (u₀ + D.background))) z v w) =
        -2 * deTurckChartRicciBilin gt anchor 0 z v w +
          deTurckChartLieBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue
            (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    D u₀ Au₀ gt bg anchor z hu₀C2 hbackgroundC2 hgenerator
  intro v w
  rw [coordinateMetricValue_deTurckShaped_nonlinearity_expanded]
  simpa only [deTurckChartMetricEvolutionBilin,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] using hexpandedRemainder v w

/-- The fully exposed local boundary: the only principal-part input is the
scalar heat trace at zero, and every lower-order coordinate term is displayed
separately against `-2 Ric + L_W g`. -/
theorem coordinateBilinearFormAt_generator_add_expanded_remainder_eq_deTurckChartRHS_of_heatTrace
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hheatTrace : ∀ v w : E, HasDerivWithinAt
      (coordinateMetricHeatOrbit u₀ z v w)
      (coordinateMetricLaplacianValue u₀ z v w) (Set.Ici 0) 0)
    (hexpandedRemainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.linear (u₀ + D.background)) z v w +
          (∑ i ∈ D.base.quadraticTerms,
            coordinateMetricValue
              (quadraticOfCLM (D.base.quadratic i)
                (u₀ + D.background)) z v w) +
          (∑ j ∈ D.base.compositionTerms,
            coordinateMetricValue
              (D.base.outer j
                (D.base.inner j (u₀ + D.background))) z v w) +
          (∑ j ∈ D.base.bilinearTerms,
            coordinateMetricValue
              (D.base.bilinear j
                (D.base.left j (u₀ + D.background))
                (D.base.right j (u₀ + D.background))) z v w) =
        -2 * deTurckChartRicciBilin gt anchor 0 z v w +
          deTurckChartLieBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue
            (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply
    coordinateBilinearFormAt_generator_add_expanded_remainder_eq_deTurckChartRHS
      D u₀ Au₀ gt bg anchor z hu₀C2 hbackgroundC2
  · intro v w
    exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
      u₀ Au₀ hu₀ z v w (hheatTrace v w)
  · exact hexpandedRemainder

/-- At a genuine cutoff-one chart point, the lower-order identification can
be stated using the ordinary coordinate advection and derivative slots of
the concrete DeTurck field.  The intrinsic Lie derivative has been eliminated
from the hypotheses by the proved coordinate Lie-split theorem. -/
theorem coordinateBilinearFormAt_generator_add_expanded_chart_terms_eq_deTurckChartRHS
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor y : M)
    (hy : y ∈ (extChartAt I anchor).source)
    (hcutoff : ∀ᶠ z' in 𝓝 (extChartAt I anchor y),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfield : DeTurckVectorFieldRegularAt gt bg 0)
    (hu₀C2 : ContDiffAt ℝ 2
      (fun z ↦ coordinateBilinearFormAt u₀ z)
      (extChartAt I anchor y))
    (hbackgroundC2 : ContDiffAt ℝ 2
      (fun z ↦ coordinateBilinearFormAt D.background z)
      (extChartAt I anchor y))
    (hgenerator : ∀ v w : E,
      coordinateMetricValue Au₀ (extChartAt I anchor y) v w =
        coordinateMetricLaplacianValue u₀
          (extChartAt I anchor y) v w)
    (hexpandedRemainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.linear (u₀ + D.background))
          (extChartAt I anchor y) v w +
          (∑ i ∈ D.base.quadraticTerms,
            coordinateMetricValue
              (quadraticOfCLM (D.base.quadratic i)
                (u₀ + D.background))
              (extChartAt I anchor y) v w) +
          (∑ j ∈ D.base.compositionTerms,
            coordinateMetricValue
              (D.base.outer j
                (D.base.inner j (u₀ + D.background)))
              (extChartAt I anchor y) v w) +
          (∑ j ∈ D.base.bilinearTerms,
            coordinateMetricValue
              (D.base.bilinear j
                (D.base.left j (u₀ + D.background))
                (D.base.right j (u₀ + D.background)))
              (extChartAt I anchor y) v w) =
        -2 * deTurckChartRicciBilin gt anchor 0
            (extChartAt I anchor y) v w +
          deTurckChartMetricAdvectionAt gt bg anchor 0
            (extChartAt I anchor y) v w +
          CovariantDerivative.chartMetric (gt 0).inner anchor
            (extChartAt I anchor y)
            (deTurckChartFieldDerivativeAt gt bg anchor 0
              (extChartAt I anchor y) v) w +
          CovariantDerivative.chartMetric (gt 0).inner anchor
            (extChartAt I anchor y) v
            (deTurckChartFieldDerivativeAt gt bg anchor 0
              (extChartAt I anchor y) w) -
          coordinateMetricLaplacianValue (u₀ + D.background)
            (extChartAt I anchor y) v w +
          coordinateMetricLaplacianValue D.background
            (extChartAt I anchor y) v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background))
        (extChartAt I anchor y) =
      deTurckChartMetricEvolutionBilin gt bg anchor 0
        (extChartAt I anchor y) := by
  apply
    coordinateBilinearFormAt_generator_add_expanded_remainder_eq_deTurckChartRHS
      D u₀ Au₀ gt bg anchor (extChartAt I anchor y)
      hu₀C2 hbackgroundC2 hgenerator
  intro v w
  rw [deTurckChartLieBilin_apply_chart_eq_advection_add_DW_slots
    gt bg anchor 0 hy hcutoff hfield v w]
  convert hexpandedRemainder v w using 1 <;> ring

/-- The explicit generator-graph version of the coefficient calculation.
If a `BUC` coefficient `lapu₀` is both the strong heat generator of `u₀`
and its componentwise flat Laplacian, uniqueness of the generator supplies
the `A u₀ = Δu₀` hypothesis above. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_graph
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (hlapu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ lapu₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hlaplacianCoefficient : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    D u₀ Au₀ gt bg anchor z hu₀C2 hbackgroundC2
  · intro v w
    rw [IsInBUCHeatGeneratorDomain.unique hu₀ hlapu₀]
    exact hlaplacianCoefficient v w
  · exact hremainder

/-- Geometric-germ form of the coefficient identification.  Equality of the
full and background `BUC` coefficient germs with the corresponding honest
smooth chart metrics discharges both `C²` premises.  The only remaining
inputs are the displayed heat-generator and lower-order coefficient
identities. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt (u₀ + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hgenerator : ∀ v w : E,
      coordinateMetricValue Au₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  have hu₀C2 :=
    coordinateBilinearFormAt_perturbation_contDiffAt_two_of_metric_germs
      u₀ D.background (gt 0) bg anchor hz hfullGerm hbackgroundGerm
  have hbackgroundC2 :=
    coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
      D.background bg anchor hz hbackgroundGerm
  exact coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS
    D u₀ Au₀ gt bg anchor z hu₀C2 hbackgroundC2
      hgenerator hremainder

/-- Metric-germ version with the weakest local principal-part input.  Honest
metric germs provide all `C²` regularity, while the strong generator is
identified with the Laplacian only through scalar one-sided heat traces at
the represented point. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_heatTrace_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt (u₀ + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hheatTrace : ∀ v w : E, HasDerivWithinAt
      (coordinateMetricHeatOrbit u₀ z v w)
      (coordinateMetricLaplacianValue u₀ z v w) (Set.Ici 0) 0)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_metric_germs
      D u₀ Au₀ gt bg anchor hz hfullGerm hbackgroundGerm
  · intro v w
    exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
      u₀ Au₀ hu₀ z v w (hheatTrace v w)
  · exact hremainder

/-- Metric-germ version of the positive-time commutation criterion.  A `BUC`
coefficient representing the componentwise Laplacian at the chosen point,
together with commutation of that value through every positive-time heat
orbit, supplies the scalar heat traces needed for coefficient identification.
It need not itself lie in a second strong-generator graph. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_laplacian_commutes_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt (u₀ + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hlaplacianCoefficient : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hcommute : ∀ t : ℝ, 0 < t → ∀ v w : E,
      coordinateMetricLaplacianValue
          (vectorHeatSemigroupBUCExtended t u₀) z v w =
        coordinateMetricValue
          (vectorHeatSemigroupBUCExtended t lapu₀) z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_heatTrace_and_metric_germs
      D u₀ Au₀ hu₀ gt bg anchor hz hfullGerm hbackgroundGerm
  · intro v w
    exact coordinateMetricValue_heatTrace_of_laplacian_commutes
      u₀ lapu₀ z v w (hlaplacianCoefficient v w)
        (fun t ht ↦ hcommute t ht v w)
  · exact hremainder

/-- Generator-graph and geometric-germ form of the coefficient
identification.  This is the most concrete current boundary: a candidate
componentwise Laplacian must be shown to lie in the strong heat-generator
graph, and the assembled lower-order terms must satisfy the displayed local
coordinate formula. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_graph_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (hlapu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ lapu₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt (u₀ + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hlaplacianCoefficient : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue u₀ z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity (u₀ + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor 0 z v w -
          coordinateMetricLaplacianValue (u₀ + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    coordinateBilinearFormAt
        (Au₀ + D.base.nonlinearity (u₀ + D.background)) z =
      deTurckChartMetricEvolutionBilin gt bg anchor 0 z := by
  apply coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_metric_germs
    D u₀ Au₀ gt bg anchor hz hfullGerm hbackgroundGerm
  · intro v w
    rw [IsInBUCHeatGeneratorDomain.unique hu₀ hlapu₀]
    exact hlaplacianCoefficient v w
  · exact hremainder

/-- End-to-end local consequence of the concrete coefficient boundary.
The generator graph, the two honest metric-coefficient germs, and the
displayed lower-order formula produce the reconstructed fixed-point path's
initial scalar Ricci--DeTurck rate in every overlapping preferred chart. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_generator_graph_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) (u₀ : CoordinateBUCTensor E) Au₀)
    (hlapu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) (u₀ : CoordinateBUCTensor E) lapu₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor₁)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor₁)
    (hlaplacianCoefficient : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue (u₀ : CoordinateBUCTensor E) z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ 0 z v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∀ v w : E,
      HasDerivWithinAt
        (fun t : ℝ ↦ coordinateMetricValue
          (A.reconstructedMetricCoefficient K u₀
            (Set.projIcc 0 (A.uniformLifespan K : ℝ)
              (A.uniformLifespan K).property t)) z v w)
        (deTurckChartMetricEvolutionBilin gt bg anchor₂ 0
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w))
        (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  apply reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_bilinearForm_eq
    (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
    (gt := gt) (bg := bg) (anchor₁ := anchor₁) (anchor₂ := anchor₂)
    (z := z) (hz := hz) (hy := hy)
  exact
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_graph_and_metric_germs
      D (u₀ : CoordinateBUCTensor E) Au₀ lapu₀ hu₀ hlapu₀
      gt bg anchor₁ hz hfullGerm hbackgroundGerm
      hlaplacianCoefficient hremainder

/-- End-to-end reconstructed-metric evolution using only the local scalar
heat traces at the initial chart point.  This removes the auxiliary global
`lapu₀` generator-graph witness from the chart-covariant conclusion. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_heatTrace_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor₁)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor₁)
    (hheatTrace : ∀ v w : E, HasDerivWithinAt
      (coordinateMetricHeatOrbit
        (u₀ : CoordinateBUCTensor E) z v w)
      (coordinateMetricLaplacianValue
        (u₀ : CoordinateBUCTensor E) z v w) (Set.Ici 0) 0)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ 0 z v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∀ v w : E,
      HasDerivWithinAt
        (fun t : ℝ ↦ coordinateMetricValue
          (A.reconstructedMetricCoefficient K u₀
            (Set.projIcc 0 (A.uniformLifespan K : ℝ)
              (A.uniformLifespan K).property t)) z v w)
        (deTurckChartMetricEvolutionBilin gt bg anchor₂ 0
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w))
        (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  apply reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_bilinearForm_eq
    (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
    (gt := gt) (bg := bg) (anchor₁ := anchor₁) (anchor₂ := anchor₂)
    (z := z) (hz := hz) (hy := hy)
  exact
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_heatTrace_and_metric_germs
      D (u₀ : CoordinateBUCTensor E) Au₀ hu₀ gt bg anchor₁
      hz hfullGerm hbackgroundGerm hheatTrace hremainder

/-- End-to-end reconstructed-metric evolution from the source-only
positive-time heat/Laplacian commutation criterion.  Compared with the
generator-graph boundary, the Laplacian representative is required only to
be a `BUC` coefficient with the correct value at the chart point; no second
strong-generator witness is assumed. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_laplacian_commutes_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) (u₀ : CoordinateBUCTensor E) Au₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor₁ anchor₂ : M) {z : E}
    (hz : z ∈ (extChartAt I anchor₁).target)
    (hy : (extChartAt I anchor₁).symm z ∈
      (extChartAt I anchor₂).source)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((u₀ : CoordinateBUCTensor E) + D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt 0).inner anchor₁)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor₁)
    (hlaplacianCoefficient : ∀ v w : E,
      coordinateMetricValue lapu₀ z v w =
        coordinateMetricLaplacianValue
          (u₀ : CoordinateBUCTensor E) z v w)
    (hcommute : ∀ t : ℝ, 0 < t → ∀ v w : E,
      coordinateMetricLaplacianValue
          (vectorHeatSemigroupBUCExtended t
            (u₀ : CoordinateBUCTensor E)) z v w =
        coordinateMetricValue
          (vectorHeatSemigroupBUCExtended t lapu₀) z v w)
    (hremainder : ∀ v w : E,
      coordinateMetricValue
          (D.base.nonlinearity
            ((u₀ : CoordinateBUCTensor E) + D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor₁ 0 z v w -
          coordinateMetricLaplacianValue
            ((u₀ : CoordinateBUCTensor E) + D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    let A :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D
    ∀ v w : E,
      HasDerivWithinAt
        (fun t : ℝ ↦ coordinateMetricValue
          (A.reconstructedMetricCoefficient K u₀
            (Set.projIcc 0 (A.uniformLifespan K : ℝ)
              (A.uniformLifespan K).property t)) z v w)
        (deTurckChartMetricEvolutionBilin gt bg anchor₂ 0
          (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v)
          (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z w))
        (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  apply
    reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_heatTrace_and_metric_germs
      (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
      (gt := gt) (bg := bg) (anchor₁ := anchor₁) (anchor₂ := anchor₂)
      (z := z) (hz := hz) (hy := hy) (hfullGerm := hfullGerm)
      (hbackgroundGerm := hbackgroundGerm)
  · intro v w
    exact coordinateMetricValue_heatTrace_of_laplacian_commutes
      (u₀ : CoordinateBUCTensor E) lapu₀ z v w
      (hlaplacianCoefficient v w) (fun t ht ↦ hcommute t ht v w)
  · exact hremainder

end RicciDeTurckCoefficientSplit

end Poincare
