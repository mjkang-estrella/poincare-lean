import Poincare.Global.PinchedLimitCore
import Poincare.Global.ConstantCurvatureEinstein

/-!
# The pinched Hamilton limit is exactly a positive Einstein metric

In dimension three, vanishing traceless Ricci together with positivity of the
scalar curvature at one point is not merely an input to the sphere theorem.
Schur connectedness first makes the metric a constant-curvature space form,
and contraction then gives an everywhere-Einstein metric with one positive
constant factor.  This file records the reverse implication missing from the
existing positive-Einstein-to-pinched-limit bridge.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- A reduced Hamilton limit is an everywhere positive-Einstein metric.

The Einstein constant is `R₀ / 3`, where `R₀` is the scalar curvature at the
point supplied by the positivity hypothesis.  Connected Schur rigidity makes
this choice independent of the point.
-/
theorem positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core
    (h : HamiltonConvergencePinchedLimit3Core M) :
    PositiveEinsteinMetric3 M := by
  rcases h with ⟨g, htr, x₀, hx₀⟩
  let R₀ : ℝ := g.scalarAt x₀
  have hcurv : HasConstantSectionalCurvature3 g (R₀ / 6) :=
    hasConstantSectionalCurvature3_of_tracelessRicciNormSqAt_eq_zero_connected
      (g := g) (R₀ := R₀)
      (fun x ↦ scalarAt_mdifferentiableAt (g := g) x)
      htr ⟨x₀, rfl⟩
  refine ⟨g, R₀ / 3, ?_, ?_⟩
  · exact div_pos hx₀ (by norm_num)
  · intro x
    have hEin :=
      isEinsteinAt_of_hasConstantSectionalCurvature3 g hcurv x
    convert hEin using 1 <;> ring

/-- On a closed connected smooth three-manifold, the reduced Hamilton limit
payload and positive-Einstein existence are equivalent propositions. -/
theorem hamiltonConvergencePinchedLimit3Core_iff_positiveEinsteinMetric3 :
    HamiltonConvergencePinchedLimit3Core M ↔ PositiveEinsteinMetric3 M := by
  constructor
  · exact positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core
  · exact hamiltonConvergencePinchedLimit3Core_of_positiveEinsteinMetric3

end Poincare
