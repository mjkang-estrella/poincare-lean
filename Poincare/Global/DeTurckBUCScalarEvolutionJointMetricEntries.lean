import Poincare.Global.DeTurckBUCScalarEvolutionBridge
import Poincare.Global.MetricFlowJointIteratedConnectionRegularity

/-!
# DeTurck chart evolution to Hamilton scalar evolution via joint metric entries

The chartwise inverse-gauge reconstruction already produces a genuine Ricci
flow once its coordinate derivative is identified with `-2 Ric`.  Joint `C³`
canonical metric entries now discharge the former mixed iterated-connection
premise, giving Hamilton scalar evolution directly.
-/

noncomputable section

open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
A globally assembled chartwise coordinate metric evolution satisfying the
Ricci equation has Hamilton scalar evolution once its canonical metric entries
are jointly `C³`.  No separate `MetricFlowRegularAt` or mixed Koszul premise is
required.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_coordinateMetric_tensorField_charts_joint_entries
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hderiv : ∀ y : M, ∀ p q : E,
      HasDerivAt (fun t ↦ g y t p q)
        (CovariantDerivative.chartMetric H (anchor y)
          (extChartAt I (anchor y) y) p q) t₀)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hH : ∀ y : M,
      CovTensor2ExtContMDiffAt (fun z p q ↦ H z p q) y 2)
    (hRicci : ∀ y : M, ∀ v w : TM y,
      H y v w = -2 * (gt t₀).ricciAt y v w)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  rcases
      ricciFlow_scalarEvolution_regularities_of_coordinateMetric_tensorField_charts
        gt t₀ H anchor g hsource hderiv hmetric hH hRicci with
    ⟨hFlow, _hgt, _hEntries⟩
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
      hFlow hJoint

end Poincare
