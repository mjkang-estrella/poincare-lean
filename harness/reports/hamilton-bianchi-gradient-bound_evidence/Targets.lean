import Poincare.Global.HamiltonScalarGradientEstimate
open scoped Manifold ContDiff
universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
example (g : Poincare.ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1] (x : M) :
    Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt g x ≤
      (20 / 7 : ℝ) * Poincare.covRicciNormSqAt g x :=
  Poincare.HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq g x
#check Poincare.HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq
variable [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
example {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint : ∀ s y, Poincare.MetricEntriesJointContDiffAt gt s y 3)
    (hFlow : ∀ y, Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t y) :
    deriv (fun s ↦ (gt s).tracelessRicciNormSqAt x) t -
        (gt t).laplacianAt (fun y ↦ (gt t).tracelessRicciNormSqAt y) x ≤
      -(2 / 21 : ℝ) * Poincare.covRicciNormSqAt (gt t) x +
      (gt t).pinchingTracelessRicciReactionTrace3At x
        ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) -
        (4 / 3 : ℝ) * Poincare.meanScalar (gt t) * (gt t).tracelessRicciNormSqAt x :=
  Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_damped x hJoint hFlow
#check Poincare.HamiltonScalarGradientEstimate.tracelessEnergy_evolution_damped
