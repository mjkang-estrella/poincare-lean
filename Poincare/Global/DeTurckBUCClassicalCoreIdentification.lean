import Poincare.Global.HeatLaplacianZeroTime

/-!
# Classical-core closure of the DeTurck `BUC` coefficient boundary

The coefficient-identification capstones previously accepted either an
abstract scalar heat trace at time zero or a positive-time commutation
hypothesis.  This file discharges both from concrete classical data:

* every scalar coordinate of the initial `BUC` coefficient is globally `C²`;
* its first and second Frechet derivatives are bounded (coordinatewise);
* a second `BUC` coefficient represents its classical flat Laplacian at every
  spatial point.

The Laplacian representative is not required to lie in a second heat-generator
graph.  The only generator graph retained by the geometric capstones is the
one already produced for the semilinear initial coefficient.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace Laplacian ContDiff
  BoundedContinuousFunction Manifold BigOperators

namespace Poincare

section ClassicalCore

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Coordinatewise bounded classical data identifying a `BUC` coefficient
with the flat Laplacian of another `BUC` coefficient.  Bounds may depend on
the two tested vectors; no unnecessary uniformity over all coordinates is
imposed. -/
structure CoordinateBUCLaplacianClassicalCore
    (u lapu : CoordinateBUCTensor E) : Prop where
  contDiff_two (v w : E) :
    ContDiff ℝ 2 (fun y : E ↦ coordinateMetricValue u y v w)
  fderiv_bounded (v w : E) :
    ∃ C₁ : ℝ, ∀ y : E,
      ‖fderiv ℝ (fun x : E ↦ coordinateMetricValue u x v w) y‖ ≤ C₁
  second_fderiv_bounded (v w : E) :
    ∃ C₂ : ℝ, ∀ y : E,
      ‖fderiv ℝ
        (fderiv ℝ (fun x : E ↦ coordinateMetricValue u x v w)) y‖ ≤ C₂
  represents_laplacian (y v w : E) :
    coordinateMetricValue lapu y v w =
      coordinateMetricLaplacianValue u y v w

/-- The packaged classical core supplies the positive-time commutation
criterion previously exposed as an abstract capstone premise. -/
theorem CoordinateBUCLaplacianClassicalCore.positiveTime_commutes
    {u lapu : CoordinateBUCTensor E}
    (hcore : CoordinateBUCLaplacianClassicalCore u lapu)
    {t : ℝ} (ht : 0 < t) (z v w : E) :
    coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w =
      coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t lapu) z v w := by
  obtain ⟨C₁, hC₁⟩ := hcore.fderiv_bounded v w
  obtain ⟨C₂, hC₂⟩ := hcore.second_fderiv_bounded v w
  exact coordinateMetricLaplacianValue_heatSemigroup_eq_of_bounded_derivatives
    u lapu v w (hcore.contDiff_two v w) hC₁ hC₂
      (fun y ↦ hcore.represents_laplacian y v w) ht z

/-- The packaged classical core supplies the one-sided scalar heat trace at
zero, without a generator-domain assumption. -/
theorem CoordinateBUCLaplacianClassicalCore.heatTrace
    {u lapu : CoordinateBUCTensor E}
    (hcore : CoordinateBUCLaplacianClassicalCore u lapu)
    (z v w : E) :
    HasDerivWithinAt
      (coordinateMetricHeatOrbit u z v w)
      (coordinateMetricLaplacianValue u z v w) (Set.Ici 0) 0 := by
  exact coordinateMetricValue_heatTrace_of_laplacian_commutes
    u lapu z v w (hcore.represents_laplacian z v w)
      (fun t ht ↦ hcore.positiveTime_commutes ht z v w)

/-- Consequently the unique strong heat-generator value is the classical
coordinate Laplacian.  There is no generator-graph premise for `lapu`. -/
theorem CoordinateBUCLaplacianClassicalCore.generator_eq_laplacian
    {u Au lapu : CoordinateBUCTensor E}
    (hcore : CoordinateBUCLaplacianClassicalCore u lapu)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
    u Au hu z v w (hcore.heatTrace z v w)

end ClassicalCore

section RicciDeTurckClassicalCore

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {iota kappa : Type*}

/-- Coefficient identification from concrete bounded classical-core data.
This replaces all scalar heat-trace and positive-time commutation premises in
the local coefficient boundary. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_classicalCore
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (hcore : CoordinateBUCLaplacianClassicalCore u₀ lapu₀)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z : E)
    (hu₀C2 :
      ContDiffAt ℝ 2 (fun y ↦ coordinateBilinearFormAt u₀ y) z)
    (hbackgroundC2 :
      ContDiffAt ℝ 2
        (fun y ↦ coordinateBilinearFormAt D.background y) z)
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
    exact hcore.generator_eq_laplacian hu₀ z v w
  · exact hremainder

/-- Metric-germ coefficient capstone with the abstract analytic premises
replaced by a bounded classical core and a `BUC` Laplacian representative. -/
theorem coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_classicalCore_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (u₀ Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u₀ Au₀)
    (hcore : CoordinateBUCLaplacianClassicalCore u₀ lapu₀)
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
  apply
    coordinateBilinearFormAt_generator_add_remainder_eq_deTurckChartRHS_of_metric_germs
      D u₀ Au₀ gt bg anchor hz hfullGerm hbackgroundGerm
  · intro v w
    exact hcore.generator_eq_laplacian hu₀ z v w
  · exact hremainder

/-- End-to-end reconstructed-metric evolution from bounded global `C²`
coordinate data and a `BUC` representative of the classical Laplacian.  This
is the concrete closure of the former heat-trace/Laplacian-commutation
capstones. -/
theorem reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_classicalCore_and_metric_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := CoordinateTwoTensor E) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      (F := CoordinateTwoTensor E) K)
    (Au₀ lapu₀ : CoordinateBUCTensor E)
    (hu₀ : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) (u₀ : CoordinateBUCTensor E) Au₀)
    (hcore : CoordinateBUCLaplacianClassicalCore
      (u₀ : CoordinateBUCTensor E) lapu₀)
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
    reconstructedMetricValue_hasDerivWithinAt_zero_eq_transitionedDeTurckChartRHS_of_heatTrace_and_metric_germs
      (D := D) (K := K) (u₀ := u₀) (Au₀ := Au₀) (hu₀ := hu₀)
      (gt := gt) (bg := bg) (anchor₁ := anchor₁) (anchor₂ := anchor₂)
      (z := z) (hz := hz) (hy := hy) (hfullGerm := hfullGerm)
      (hbackgroundGerm := hbackgroundGerm)
  · intro v w
    exact hcore.heatTrace z v w
  · exact hremainder

end RicciDeTurckClassicalCore

end Poincare
