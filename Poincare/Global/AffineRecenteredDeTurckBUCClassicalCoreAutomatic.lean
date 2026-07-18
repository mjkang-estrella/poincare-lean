import Poincare.Global.AffineRecenteredDeTurckBUCAutomaticClassical
import Poincare.Global.DeTurckBUCClassicalCoreIdentification
import Poincare.Global.DeTurckBUCGeneratorLocality

/-!
# Spatial identification of the automatic affine DeTurck generator

Automatic positive-time classicality selects a canonical strong heat-generator
value for the affine bounded-ball solution.  This module exposes its graph
witness and then identifies its scalar coordinates with the flat coordinate
Laplacian from either of the two honest spatial inputs already available:

* a one-sided scalar heat trace at zero; or
* a global bounded `CoordinateBUCLaplacianClassicalCore`.

After that identification, the automatic reconstructed-metric derivative is
the coordinate Laplacian of the perturbation plus the shifted DeTurck
remainder.  Local `C²` coefficient data, or honest full/background metric
germs which imply it, perform the final Laplacian split and give the geometric
Ricci--DeTurck chart rate.

Joint metric-entry regularity is intentionally not used as a substitute for a
classical core.  It is local near a manifold chart point, whereas the heat
trace theorem requires global bounded Euclidean first and second derivatives
and a global `BUC` Laplacian representative.  The metric-germ conclusions below
therefore leave precisely that genuinely spatial heat-trace/classical-core
boundary explicit.  No time-zero derivative claim is made.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace Laplacian ContDiff
  BoundedContinuousFunction Manifold

namespace Poincare

section AffineGeneratorGraph

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- The affine solution state selected at a real time, clamped to its compact
existence interval. -/
def uniformInteriorState
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : ℝ) : BUC :=
  D.uniformSolution K u₀
    (Set.projIcc 0 (D.uniformLifespan K : ℝ)
      (D.uniformLifespan K).property t)

/-- The canonical strong heat-generator value selected for the affine state
at a real time. -/
def uniformInteriorGeneratorValue
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : ℝ) : BUC :=
  semilinearHeatBUCInteriorGeneratorValue
    (E := E) (F := F) (D.uniformLifespan K) (u₀ : BUC)
    D.nonlinearity (D.uniformSolution K u₀) t

/-- The canonical selected generator really lies in the strong heat-generator
graph of every state in the positive target window.  No caller-supplied `Au`
or graph witness remains. -/
theorem uniformInteriorGeneratorValue_mem_heatGeneratorDomain
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    {c a b α : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ (D.uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ t ∈ Set.Icc a b,
      IsInBUCHeatGeneratorDomain (E := E) (F := F)
        (D.uniformInteriorState K u₀ t)
        (D.uniformInteriorGeneratorValue K u₀ t) := by
  simpa only [uniformInteriorState, uniformInteriorGeneratorValue,
    uniformSolution, uniformLifespan] using
    semilinearHeatBUCUniformLocalSolution_mem_heatGeneratorDomain_interior
      (E := E) (F := F) K D.nonlinearity D.localData u₀
      hc hca hab hbT hα0 hα1

end AffineRecenteredDeTurckShapedBUCRemainderData

end AffineGeneratorGraph

section TensorGeneratorIdentification

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "T₂" => CoordinateTwoTensor E
local notation "BUCT₂" => CoordinateBUCTensor E

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- A scalar one-sided heat trace identifies the automatic selected generator
with the coordinate Laplacian at the tested spatial and tangent data. -/
theorem ofShiftedBackground_uniformInteriorGeneratorValue_eq_laplacian_of_heatTrace
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (z v w : E)
    (hheatTrace : HasDerivWithinAt
      (coordinateMetricHeatOrbit
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (Set.Ici 0) 0) :
    coordinateMetricValue
        ((ofShiftedBackground D).uniformInteriorGeneratorValue K u₀ t)
        z v w =
      coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w := by
  have hgraph :=
    (ofShiftedBackground D).uniformInteriorGeneratorValue_mem_heatGeneratorDomain
      K u₀ hc hca hab hbT hα0 hα1 t ⟨ht.1.le, ht.2.le⟩
  exact coordinateMetricValue_generator_eq_laplacian_of_heatTrace
    ((ofShiftedBackground D).uniformInteriorState K u₀ t)
    ((ofShiftedBackground D).uniformInteriorGeneratorValue K u₀ t)
    hgraph z v w hheatTrace

/-- Local `C²` regularity of the current perturbation coefficient identifies
the automatic selected generator with its classical coordinate Laplacian.
No global classical core or separately supplied scalar heat trace is needed.
-/
theorem ofShiftedBackground_uniformInteriorGeneratorValue_eq_laplacian_of_contDiffAt_two
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (z v w : E)
    (hstateC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) y) z) :
    coordinateMetricValue
        ((ofShiftedBackground D).uniformInteriorGeneratorValue K u₀ t)
        z v w =
      coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w := by
  have hgraph :=
    (ofShiftedBackground D).uniformInteriorGeneratorValue_mem_heatGeneratorDomain
      K u₀ hc hca hab hbT hα0 hα1 t ⟨ht.1.le, ht.2.le⟩
  exact coordinateMetricValue_generator_eq_laplacian_of_contDiffAt_two
    ((ofShiftedBackground D).uniformInteriorState K u₀ t)
    ((ofShiftedBackground D).uniformInteriorGeneratorValue K u₀ t)
    hgraph z v w hstateC2

/-- A bounded global classical core supplies the heat trace in the preceding
theorem.  The only remaining assumptions are genuinely spatial data for the
current positive-time coefficient. -/
theorem ofShiftedBackground_uniformInteriorGeneratorValue_eq_laplacian_of_classicalCore
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (lapu : BUCT₂)
    (hcore : CoordinateBUCLaplacianClassicalCore
      ((ofShiftedBackground D).uniformInteriorState K u₀ t) lapu)
    (z v w : E) :
    coordinateMetricValue
        ((ofShiftedBackground D).uniformInteriorGeneratorValue K u₀ t)
        z v w =
      coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w := by
  exact
    ofShiftedBackground_uniformInteriorGeneratorValue_eq_laplacian_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht z v w
      (hcore.heatTrace z v w)

/-- With a scalar heat trace, automatic reconstructed-metric classicality has
the explicit principal-plus-remainder rate `Δu + N(u + background)`. -/
theorem ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_heatTrace
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (z v w : E)
    (hheatTrace : HasDerivWithinAt
      (coordinateMetricHeatOrbit
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (Set.Ici 0) 0) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (coordinateMetricLaplacianValue
          ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w +
        coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w) t := by
  have hgenerator :=
    ofShiftedBackground_uniformInteriorGeneratorValue_eq_laplacian_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht z v w hheatTrace
  have hderiv :=
    ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior
      D K u₀ hc hca hab hbT hα0 hα1 z v w t ht
  have hgenerator' :
      coordinateMetricValue
          (semilinearHeatBUCInteriorGeneratorValue
            ((ofShiftedBackground D).uniformLifespan K) (u₀ : BUCT₂)
            (ofShiftedBackground D).nonlinearity
            ((ofShiftedBackground D).uniformSolution K u₀) t) z v w =
        coordinateMetricLaplacianValue
          ((ofShiftedBackground D).uniformSolution K u₀
            (Set.projIcc 0
              ((ofShiftedBackground D).uniformLifespan K : ℝ)
              ((ofShiftedBackground D).uniformLifespan K).property t))
          z v w := by
    simpa only [uniformInteriorState, uniformInteriorGeneratorValue] using
      hgenerator
  rw [coordinateMetricValue_add, hgenerator'] at hderiv
  simpa only [uniformInteriorState] using hderiv

/-- Local `C²` regularity of the current perturbation coefficient makes the
automatic reconstructed-metric derivative explicit without a global
classical core. -/
theorem ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_contDiffAt_two
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (z v w : E)
    (hstateC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) y) z) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (coordinateMetricLaplacianValue
          ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w +
        coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w) t := by
  exact
    ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht z v w
      (coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w hstateC2)

/-- Classical-core form of the explicit principal-plus-remainder positive-time
rate. -/
theorem ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_classicalCore
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (lapu : BUCT₂)
    (hcore : CoordinateBUCLaplacianClassicalCore
      ((ofShiftedBackground D).uniformInteriorState K u₀ t) lapu)
    (z v w : E) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (coordinateMetricLaplacianValue
          ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w +
        coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w) t := by
  exact
    ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht z v w
      (hcore.heatTrace z v w)

end AffineRecenteredDeTurckShapedBUCRemainderData

end TensorGeneratorIdentification

section GeometricPositiveTimeRate

open Bundle FiberBundle

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUCT₂" => CoordinateBUCTensor E

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {iota kappa : Type*}

/-- A scalar heat trace, local `C²` perturbation/background coefficients, and
the lower-order DeTurck coefficient identity turn the automatic derivative
into the geometric chart rate at the same positive time. -/
theorem ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_heatTrace
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z v w : E)
    (hheatTrace : HasDerivWithinAt
      (coordinateMetricHeatOrbit
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (Set.Ici 0) 0)
    (hstateC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) y) z)
    (hbackgroundC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hremainder :
      coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor t z v w) t := by
  have hderiv :=
    ofShiftedBackground_reconstructedMetricValue_hasDerivAt_interior_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht z v w hheatTrace
  have hlaplacianAdd := coordinateMetricLaplacianValue_add
    ((ofShiftedBackground D).uniformInteriorState K u₀ t)
    D.background hstateC2 hbackgroundC2 v w
  have hslope :
      coordinateMetricLaplacianValue
          ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w +
        coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w := by
    rw [hremainder, hlaplacianAdd]
    ring
  rw [hslope] at hderiv
  exact hderiv

/-- Local `C²` perturbation/background coefficients and the lower-order
DeTurck identity suffice for the geometric positive-time rate.  The scalar
heat trace is generated automatically from the perturbation germ. -/
theorem ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_contDiffAt_two
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) (z v w : E)
    (hstateC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) y) z)
    (hbackgroundC2 : ContDiffAt ℝ 2
      (fun y ↦ coordinateBilinearFormAt D.background y) z)
    (hremainder :
      coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor t z v w) t := by
  exact
    ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht gt bg anchor z v w
      (coordinateMetricHeatOrbit_hasDerivWithinAt_laplacian_of_contDiffAt_two
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w hstateC2)
      hstateC2 hbackgroundC2 hremainder

/-- Honest full/background metric germs discharge both local `C²` premises in
the positive-time geometric-rate theorem.  The scalar heat trace remains the
only principal-part input. -/
theorem ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_heatTrace_and_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) (v w : E)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((ofShiftedBackground D).uniformInteriorState K u₀ t +
            D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hheatTrace : HasDerivWithinAt
      (coordinateMetricHeatOrbit
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (coordinateMetricLaplacianValue
        ((ofShiftedBackground D).uniformInteriorState K u₀ t) z v w)
      (Set.Ici 0) 0)
    (hremainder :
      coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor t z v w) t := by
  have hstateC2 :=
    coordinateBilinearFormAt_perturbation_contDiffAt_two_of_metric_germs
      ((ofShiftedBackground D).uniformInteriorState K u₀ t) D.background
      (gt t) bg anchor hz hfullGerm hbackgroundGerm
  have hbackgroundC2 :=
    coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
      D.background bg anchor hz hbackgroundGerm
  exact
    ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_heatTrace
      D K u₀ hc hca hab hbT hα0 hα1 ht gt bg anchor z v w
      hheatTrace hstateC2 hbackgroundC2 hremainder

/-- Honest full/background metric germs now discharge the complete principal
part of the automatic positive-time geometric-rate theorem.  No global
classical core and no caller-supplied scalar heat trace remain. -/
theorem ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) (v w : E)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((ofShiftedBackground D).uniformInteriorState K u₀ t +
            D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder :
      coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor t z v w) t := by
  have hstateC2 :=
    coordinateBilinearFormAt_perturbation_contDiffAt_two_of_metric_germs
      ((ofShiftedBackground D).uniformInteriorState K u₀ t) D.background
      (gt t) bg anchor hz hfullGerm hbackgroundGerm
  have hbackgroundC2 :=
    coordinateBilinearFormAt_contDiffAt_two_of_eventuallyEq_chartMetric
      D.background bg anchor hz hbackgroundGerm
  exact
    ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_contDiffAt_two
      D K u₀ hc hca hab hbT hα0 hα1 ht gt bg anchor z v w
      hstateC2 hbackgroundC2 hremainder

/-- A bounded classical core supplies the last scalar heat-trace premise in
the metric-germ geometric-rate theorem.  Thus only genuinely spatial
classical-core, metric-germ, and lower-order coefficient data remain. -/
theorem ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_classicalCore_and_germs
    (D : RecenteredDeTurckShapedBUCRemainderData
      (F := T₂) iota kappa)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (F := T₂) K)
    {c a b α t : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b)
    (hbT : b ≤ ((ofShiftedBackground D).uniformLifespan K : ℝ))
    (hα0 : 0 < α) (hα1 : α < 1) (ht : t ∈ Set.Ioo a b)
    (lapu : BUCT₂)
    (hcore : CoordinateBUCLaplacianClassicalCore
      ((ofShiftedBackground D).uniformInteriorState K u₀ t) lapu)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) (v w : E)
    (hfullGerm :
      (fun y ↦ coordinateBilinearFormAt
          ((ofShiftedBackground D).uniformInteriorState K u₀ t +
            D.background) y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hbackgroundGerm :
      (fun y ↦ coordinateBilinearFormAt D.background y) =ᶠ[nhds z]
        CovariantDerivative.chartMetric bg.inner anchor)
    (hremainder :
      coordinateMetricValue
          (D.base.nonlinearity
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background)) z v w =
        deTurckChartMetricEvolutionBilin gt bg anchor t z v w -
          coordinateMetricLaplacianValue
            ((ofShiftedBackground D).uniformInteriorState K u₀ t +
              D.background) z v w +
          coordinateMetricLaplacianValue D.background z v w) :
    HasDerivAt
      (fun r : ℝ ↦ coordinateMetricValue
        ((ofShiftedBackground D).reconstructedMetricCoefficient K u₀
          (Set.projIcc 0
            ((ofShiftedBackground D).uniformLifespan K : ℝ)
            ((ofShiftedBackground D).uniformLifespan K).property r)) z v w)
      (deTurckChartMetricEvolutionBilin gt bg anchor t z v w) t := by
  exact
    ofShiftedBackground_metricValue_hasDerivAt_interior_eq_deTurckChartRHS_of_heatTrace_and_germs
      D K u₀ hc hca hab hbT hα0 hα1 ht gt bg anchor hz v w
      hfullGerm hbackgroundGerm (hcore.heatTrace z v w) hremainder

end AffineRecenteredDeTurckShapedBUCRemainderData

end GeometricPositiveTimeRate

end Poincare
