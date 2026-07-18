import Poincare.Global.DeTurckCoordinateJointRegularityFour
import Poincare.Global.RegularCoherentVariationalTwoRestartPackage

/-!
# Two-restart inverse DeTurck point flow from metric regularity

The coordinate DeTurck field contains one spatial derivative of the metric.
Accordingly joint `C⁵` metric entries give a joint `C⁴` inverse DeTurck
time--point field.  The regular coherent variational hierarchy then constructs
a complete two-restart point-flow package, including the forward joint `C³`
and backward joint `C¹` selector regularity used by the physical-flow
assembly.

The `C⁵` hypothesis is intentional: the current generic third-variation
selector construction keeps one spare derivative so that its top augmented
field is locally Lipschitz.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000

open Bundle
open scoped Manifold ContDiff

namespace Poincare

universe u

section MetricTwoRestartPackage

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "I" => closedSmoothModelWithCorners n

/-- Joint `C⁵` metric entries at the anchor produce a complete local
two-restart package for the exact inverse DeTurck coordinate field. -/
theorem exists_inverseDeTurck_twoRestartPointFlowPackage_of_metricEntries_five
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (anchor : M)
    (Tmax : ℝ) (hTmax : 0 < Tmax)
    (hJoint : MetricEntriesJointContDiffAt gt 0 anchor 5) :
    ∃ t ∈ Set.Ioo (0 : ℝ) Tmax,
      ∃ Phi Psi : ℝ → E → E, ∃ y₁ : E,
        Nonempty (TwoRestartPointFlowPackage
          (fun s ↦ inverseDeTurckChartCoordinateField gt bg anchor s)
          Phi Psi t (extChartAt I anchor anchor) y₁) := by
  let z₀ : E := extChartAt I anchor anchor
  have hW : ContDiffAt ℝ 4
      (Function.uncurry (fun t z ↦
        chartCoordinateTangentField anchor (deTurckVectorField gt bg t) z))
      (0, z₀) := by
    simpa only [z₀] using
      (DeTurckCoordinateJointRegularityFour.deTurckChartCoordinateField_jointContDiffAt_four_of_metricEntries
        (bg := bg) hJoint)
  have hV : ContDiffAt ℝ 4
      (Function.uncurry
        (fun t z ↦ inverseDeTurckChartCoordinateField gt bg anchor t z))
      (0, z₀) := by
    simpa only [Function.uncurry, inverseDeTurckChartCoordinateField] using
      hW.neg
  have hG : ContDiffAt ℝ 4
      (fun q : ℝ × E ↦
        ((1 : ℝ), inverseDeTurckChartCoordinateField
          gt bg anchor q.1 q.2)) (0, z₀) := by
    exact contDiffAt_const.prodMk hV
  simpa only [z₀] using
    (exists_twoRestartPointFlowPackage_of_timePoint_contDiffAt_four
      (fun s ↦ inverseDeTurckChartCoordinateField gt bg anchor s)
      z₀ Tmax hTmax hG)

end MetricTwoRestartPackage

end Poincare
