import Poincare.Global.DeTurckBUCInteriorRicciAssembly
import Poincare.Global.CoordinateRicciFlowHamiltonScalarBridge

/-!
# Interior reconstructed inverse gauges to Hamilton scalar evolution

The generic coordinate-to-Hamilton bridge already contains the intrinsic
Ricci-flow and scalar-evolution argument.  This file specializes that bridge
to a point-indexed family of reconstructed inverse-gauge metrics, making the
remaining local-to-global boundary explicit in the theorem signature:

* every preferred chart has a reconstructed two-sided Ricci-flow germ;
* that germ agrees in time with one assembled metric family;
* its curvature trace is the assembled family's chart expression of
  `-2 Ric`; and
* the assembled metric entries are jointly `C³`.

No joint spacetime pullback germ is constructed here; its time and curvature
consequences are precisely the two explicit assembly premises below.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/--
Pointwise reconstructed inverse-gauge Ricci germs satisfying the honest time
and curvature assembly premises give Hamilton scalar evolution for the
assembled metric family.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_reconstructedInverseGaugeMetrics_germs_joint_entries
    (rt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x : M)
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (rt s).leviCivita 1]
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : M → ℝ≥0)
    (u₀ : ∀ y : M, SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) (K y))
    (phi : M → ℝ → E)
    (J : M → ℝ → E →L[ℝ] E)
    (anchor : M → M)
    (curv : M → E → E → (E →ₗ[ℝ] E))
    (hsource : ∀ y : M,
      y ∈ (extChartAt I (anchor y)).source)
    (hflow : ∀ y : M,
      IsCoordinateRicciFlowAt
        (reconstructedInverseGaugeMetric
          (D y) (K y) (u₀ y) (phi y) (J y)) (curv y) t)
    (hrate : ∀ y : M, ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv y p q) =
        CovariantDerivative.chartMetric
          (fun z : M ↦ (-2 : ℝ) • ricciContinuousBilinAt (rt t) z)
          (anchor y) (extChartAt I (anchor y) y) p q)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        (D y) (K y) (u₀ y) (phi y) (J y) s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt rt t y 3) :
    SatisfiesHamiltonScalarEvolutionAt rt t x := by
  exact
    satisfiesHamiltonScalarEvolutionAt_of_coordinateRicciFlow_charts_joint_entries
      rt t x anchor
      (fun y ↦ reconstructedInverseGaugeMetric
        (D y) (K y) (u₀ y) (phi y) (J y))
      curv hsource hflow hrate hmetric hJoint

end Poincare
