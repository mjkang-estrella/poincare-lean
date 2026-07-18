import Poincare.Global.DeTurckBUCCoefficientIdentification
import Poincare.Global.HeatGeneratorLocality

/-!
# Pointwise locality of the tensor-valued DeTurck heat generator

Scalar evaluation turns a bounded uniformly continuous coordinate two-tensor
into a scalar `BUC` datum and commutes with its heat orbit.  The scalar
Gaussian locality theorem therefore identifies every coordinate of a strong
tensor-valued heat generator with the classical flat Laplacian from only a
local `C²` germ at the tested point.

This removes the global bounded-derivative/classical-core premise from the
pointwise DeTurck coefficient identification step.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology NNReal InnerProductSpace Laplacian ContDiff
  BoundedContinuousFunction

namespace Poincare

section TensorHeatGeneratorLocality

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "ScalarBUC" =>
  BoundedUniformContinuousFunction (E := E) (F := ℝ)

/-- Scalar evaluation of a tensor-valued `BUC` coefficient at two fixed
tangent vectors. -/
def coordinateMetricScalarBUC (u : CoordinateBUCTensor E) (v w : E) :
    ScalarBUC :=
  ⟨(coordinateTwoTensorEvaluationCLM v w).compLeftContinuousBounded E u.1,
    (coordinateTwoTensorEvaluationCLM v w).uniformContinuous.comp u.2⟩

@[simp]
theorem coordinateMetricScalarBUC_apply
    (u : CoordinateBUCTensor E) (v w y : E) :
    ((coordinateMetricScalarBUC u v w : ScalarBUC) : E →ᵇ ℝ) y =
      coordinateMetricValue u y v w := by
  rfl

/-- Scalar projection commutes with the extended tensor heat orbit, including
the identity branch at nonpositive times. -/
theorem coordinateMetricHeatOrbit_eq_scalarBUCHeatOrbit
    (u : CoordinateBUCTensor E) (z v w : E) :
    coordinateMetricHeatOrbit u z v w =
      scalarBUCHeatOrbit (coordinateMetricScalarBUC u v w) z := by
  funext t
  change coordinateMetricValue
      (vectorHeatSemigroupBUCExtended
        (E := E) (F := CoordinateTwoTensor E) t u) z v w = _
  by_cases ht : 0 < t
  · rw [coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
      u ht z v w,
      scalarBUCHeatOrbit_eq_heatSolution
        (coordinateMetricScalarBUC u v w) z ht]
    congr 1
  · simp [scalarBUCHeatOrbit,
      vectorHeatSemigroupBUCExtended, ht]

/-- Local `C²` regularity of one scalar tensor coordinate supplies its
classical one-sided heat trace at zero. -/
theorem coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two_scalar
    (u : CoordinateBUCTensor E) (z v w : E)
    (hu : ContDiffAt ℝ 2 (fun y : E ↦ coordinateMetricValue u y v w) z) :
    HasDerivWithinAt (coordinateMetricHeatOrbit u z v w)
      (coordinateMetricLaplacianValue u z v w) (Set.Ici 0) 0 := by
  have hscalar :=
    scalarBUCHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
      (E := E) (coordinateMetricScalarBUC u v w) z (by
        simpa only [coordinateMetricScalarBUC_apply] using hu)
  simpa only [coordinateMetricHeatOrbit_eq_scalarBUCHeatOrbit,
    coordinateMetricLaplacianValue, coordinateMetricScalarBUC_apply] using
    hscalar

/-- Operator-valued local `C²` regularity supplies every scalar coordinate
heat trace at the tested point. -/
theorem coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
    (u : CoordinateBUCTensor E) (z v w : E)
    (hu : ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u y) z) :
    HasDerivWithinAt (coordinateMetricHeatOrbit u z v w)
      (coordinateMetricLaplacianValue u z v w) (Set.Ici 0) 0 := by
  exact
    coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two_scalar
      u z v w (coordinateMetricValue_contDiffAt_two u hu v w)

/-- A strong tensor-valued `BUC` heat-generator value agrees pointwise with
the classical flat coordinate Laplacian under only a local `C²` hypothesis.
-/
theorem coordinateMetricValue_generator_eq_laplacian_of_contDiffAt_two
    (u Au : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E)
    (hC2 : ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u y) z) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
    u Au hu z v w
      (coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
        u z v w hC2)

end TensorHeatGeneratorLocality

section GeometricGeneratorLocality

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {iota kappa : Type*}

/-- A strong generator-domain witness and honest smooth metric germs identify
the complete local Ricci--DeTurck coordinate rate.  Locality supplies the
principal `Au = Δu` identity, so neither a second Laplacian generator graph
nor caller-supplied scalar heat traces remain. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_domain_and_metric_germs
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
  apply
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_metric_germs
      D u₀ Au₀ gt bg anchor hz hfullGerm hbackgroundGerm
  · intro v w
    exact coordinateMetricValue_generator_eq_laplacian_of_contDiffAt_two
      u₀ Au₀ hu₀ z v w hu₀C2
  · exact hremainder

/-- End-to-end initial reconstructed-metric evolution from one strong
generator-domain witness and honest metric germs.  The conclusion is already
transported to an overlapping preferred chart, and no auxiliary Laplacian
coefficient or scalar heat-trace family is assumed. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_generator_domain_and_metric_germs
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
    reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_bilinearForm_eq
      (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
      (gt := gt) (bg := bg) (anchor₁ := anchor₁) (anchor₂ := anchor₂)
      (z := z) (hz := hz) (hy := hy)
  exact
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_generator_domain_and_metric_germs
      D (u₀ : CoordinateBUCTensor E) Au₀ hu₀ gt bg anchor₁ hz
      hfullGerm hbackgroundGerm hremainder

end GeometricGeneratorLocality

end Poincare
