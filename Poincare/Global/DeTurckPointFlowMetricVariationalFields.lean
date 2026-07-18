import Poincare.Global.DeTurckCoordinateJointRegularityThree
import Poincare.Global.DeTurckPointFlowVariationalFields

/-!
# Metric regularity inputs for the inverse DeTurck variational tower

This module joins the two regularity budgets proved separately upstream.
Joint `C⁴` entries of the evolving metric give a joint `C³` DeTurck
coordinate field; after inserting the inverse-gauge sign, its autonomous
time--point extension has the local `C³` regularity whose first three
variational augmentations are respectively `C²`, `C¹`, and `C⁰`.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Bundle
open scoped Manifold ContDiff

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "I" => closedSmoothModelWithCorners n
local notation "X₀" => ℝ × E
local notation "X₁" => FirstVariationalState X₀
local notation "X₂" => SecondVariationalState X₀

-- Name each finite operator-norm layer so typeclass search does not reject
-- the nested continuous-linear-map instances as a potential recursive loop.
local instance baseEndNormedGroup : NormedAddCommGroup (X₀ →L[ℝ] X₀) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseEndNormedSpace : NormedSpace ℝ (X₀ →L[ℝ] X₀) :=
  ContinuousLinearMap.toNormedSpace

local instance firstStateNormedGroup : NormedAddCommGroup X₁ := inferInstance
local instance firstStateNormedSpace : NormedSpace ℝ X₁ := inferInstance

local instance firstEndNormedGroup : NormedAddCommGroup (X₁ →L[ℝ] X₁) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance firstEndNormedSpace : NormedSpace ℝ (X₁ →L[ℝ] X₁) :=
  ContinuousLinearMap.toNormedSpace

local instance secondStateNormedGroup : NormedAddCommGroup X₂ := inferInstance
local instance secondStateNormedSpace : NormedSpace ℝ X₂ := inferInstance

local instance secondEndNormedGroup : NormedAddCommGroup (X₂ →L[ℝ] X₂) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance secondEndNormedSpace : NormedSpace ℝ (X₂ →L[ℝ] X₂) :=
  ContinuousLinearMap.toNormedSpace

/-- Joint `C⁴` metric entries give local `C³` regularity of the exact
autonomous field used by the two-restart inverse DeTurck point-flow core. -/
theorem inverseDeTurckPointExtendedField_contDiffAt_three_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {anchor : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ anchor 4) :
    ContDiffAt ℝ 3
      (fun p : ℝ × E ↦
        ((1 : ℝ), inverseDeTurckChartCoordinateField gt bg anchor p.1 p.2))
      (t₀, extChartAt I anchor anchor) := by
  have hW : ContDiffAt ℝ 3
      (Function.uncurry (fun t z ↦
        chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z))
      (t₀, extChartAt I anchor anchor) :=
    DeTurckCoordinateJointRegularityThree.deTurckChartCoordinateField_jointContDiffAt_three_of_metricEntries
      (bg := bg) hJoint
  simpa only [Function.uncurry, inverseDeTurckChartCoordinateField] using
    contDiffAt_const.prodMk hW.neg

/-- The first three variational fields of the concrete inverse DeTurck
autonomous point ODE have the local regularities needed to construct the
selector derivative tower. -/
theorem inverseDeTurckPoint_variationalAugmentedFields_regularitiesAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {anchor : M}
    (J : (ℝ × E) →L[ℝ] (ℝ × E))
    (K : FirstVariationalState (ℝ × E) →L[ℝ]
      FirstVariationalState (ℝ × E))
    (L : SecondVariationalState (ℝ × E) →L[ℝ]
      SecondVariationalState (ℝ × E))
    (hJoint : MetricEntriesJointContDiffAt gt t₀ anchor 4) :
    let F : ℝ × E → ℝ × E := fun p ↦
      ((1 : ℝ), inverseDeTurckChartCoordinateField gt bg anchor p.1 p.2)
    let q : E := extChartAt I anchor anchor
    ContDiffAt ℝ 2 (firstVariationalAugmentedField F) ((t₀, q), J) ∧
      ContDiffAt ℝ 1 (secondVariationalAugmentedField F) (((t₀, q), J), K) ∧
      ContDiffAt ℝ 0 (thirdVariationalAugmentedField F)
        ((((t₀, q), J), K), L) := by
  dsimp only
  let W : ℝ → E → E := fun t z ↦
    chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z
  have hW : ContDiffAt ℝ 3 (Function.uncurry W)
      (t₀, extChartAt I anchor anchor) := by
    simpa only [W] using
      (DeTurckCoordinateJointRegularityThree.deTurckChartCoordinateField_jointContDiffAt_three_of_metricEntries
        (bg := bg) hJoint)
  have hfields := inverseGaugePoint_variationalAugmentedFields_regularitiesAt
    W t₀ (extChartAt I anchor anchor) J K L hW
  simpa only [inverseGaugePointExtendedField, W,
    inverseDeTurckChartCoordinateField] using hfields

end Poincare
