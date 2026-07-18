import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction

/-!
# Scalar-time-derivative continuity from the Lichnerowicz expression

The local Hausdorff domination theorem consumes joint continuity of the
actual time derivative of scalar curvature.  The verified Lichnerowicz
assembly already identifies that derivative pointwise with the geometric
first-variation expression

`scalarVariationStokesBoundaryAt - metricVariationRicciPairingAt`.

This module therefore replaces continuity of an opaque `deriv` by continuity
of that explicit geometric expression.  No automatic continuity theorem for
the expression is asserted here: proving one requires a joint regularity
bridge for the divergence/Laplacian and raised Ricci-pairing terms.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Intrinsic joint continuity of the verified Lichnerowicz scalar-variation
expression.  Unlike `ScalarTimeDerivativeJointContinuous`, this predicate
contains no occurrence of the choice-based `deriv` operator. -/
def ScalarVariationStokesBoundaryJointContinuous
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) : Prop :=
  Continuous (fun p : ℝ × M ↦
    scalarVariationStokesBoundaryAt gt p.1 p.2 -
      metricVariationRicciPairingAt
        (gt p.1) (timeDerivAt gt p.1) p.2)

/-- The pointwise Lichnerowicz identity converts continuity of its geometric
right-hand side into continuity of the actual scalar time derivative. -/
theorem scalarTimeDerivativeJointContinuous_of_lichnerowicz_of_scalarVariationStokesBoundaryJointContinuous
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (L : GlobalLichnerowiczAssemblyRegularity gt)
    (hVariation : ScalarVariationStokesBoundaryJointContinuous gt) :
    ScalarTimeDerivativeJointContinuous gt := by
  change Continuous (fun p : ℝ × M ↦
    deriv (fun t ↦ (gt t).scalarAt p.2) p.1)
  rw [show (fun p : ℝ × M ↦
      deriv (fun t ↦ (gt t).scalarAt p.2) p.1) =
        (fun p : ℝ × M ↦
          scalarVariationStokesBoundaryAt gt p.1 p.2 -
            metricVariationRicciPairingAt
              (gt p.1) (timeDerivAt gt p.1) p.2) by
    funext p
    exact L.scalarVariation_stokes p.1 p.2]
  exact hVariation

/-- Joint `C³` metric entries construct the Lichnerowicz assembly, so the
geometric continuity predicate alone suffices at this interface. -/
theorem scalarTimeDerivativeJointContinuous_of_jointMetricEntriesThree_of_scalarVariationStokesBoundaryJointContinuous
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hVariation : ScalarVariationStokesBoundaryJointContinuous gt) :
    ScalarTimeDerivativeJointContinuous gt :=
  scalarTimeDerivativeJointContinuous_of_lichnerowicz_of_scalarVariationStokesBoundaryJointContinuous
    (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
    hVariation

end Poincare
