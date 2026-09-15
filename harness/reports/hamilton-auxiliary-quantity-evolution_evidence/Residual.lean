import Poincare.Global.IntrinsicBochnerScalarGradient
import Poincare.Global.ClosedRiemannianParabolicExponentialMaximum
import Poincare.Global.NormalizedFlowInitialPinchingPreservation
#check Poincare.closedRiemannian_parabolic_exp_decay_continuousOn
#check Poincare.closed_parabolic_min_principle_var
#check Poincare.NormalizedFlowInitialPinchingPreservation.initial_pinching_improvement
open scoped Manifold ContDiff
example {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
    [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
    (g : Poincare.ClosedSmoothRiemannianMetric 3 M) (x : M) :
    -2 * Poincare.covRicciNormSqAt g x + (2 / 3 : ℝ) * g.scalarGradNormSqAt x ≤
      -(2 / 21 : ℝ) * Poincare.covRicciNormSqAt g x := by
  have htrace := g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
  linarith
