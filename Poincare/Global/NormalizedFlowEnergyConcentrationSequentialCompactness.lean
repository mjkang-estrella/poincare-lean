import Poincare.Global.ClosedRiemannianBallVolumeLower
import Poincare.Global.NormalizedFlowEnergyConcentrationCurvatureDerivative

/-!
# Energy concentration from eventual geometric comparison

A convergent metric sequence normally supplies uniform geometry only on a
tail.  `ClosedRiemannianBallVolumeLower` shows that this is enough: the finite
prefix has an independent positive ball-volume minimum.  Combining that fact
with the intrinsic curvature-derivative contraction gives a direct
`L¹`-to-`L∞` concentration theorem with no separately assumed noncollapse or
scalar Lipschitz bound.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Vanishing traceless-Ricci energy plus intrinsic `Ric°`/`∇ Ric°` bounds
converges uniformly once a tail of the metrics has fixed reference-distance
and reference-volume comparisons.

The first `N` metrics require no comparison hypothesis.  Their contribution
to qualitative noncollapse is supplied by compactness of the fixed closed
manifold.
-/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_covariantDerivativeBound_of_eventualReferenceComparison
    (g : ℕ → ClosedSmoothRiemannianMetric 3 M)
    (gref : ClosedSmoothRiemannianMetric 3 M)
    (N : ℕ) {C c A B : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hDistance : ∀ i, N ≤ i → ∀ x y,
      closedRiemannianDistance (g i) y x ≤
        C * closedRiemannianDistance gref y x)
    (hVolume : ∀ i, N ≤ i → ∀ (S : Set M), MeasurableSet S →
      c * (volumeMeasure gref).real S ≤
        (volumeMeasure (g i)).real S)
    (hCOne : UniformTracelessRicciEnergyCOne g)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound g A B)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M,
        (g i).tracelessRicciNormSqAt x < epsilon := by
  have hNoncollapse : UniformClosedRiemannianBallVolumeLower g :=
    uniformClosedRiemannianBallVolumeLower_nat_of_eventual_referenceComparison
      gref g N hC hc hDistance hVolume
  exact
    tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_covariantDerivativeBound
      g hCOne hBounds hNoncollapse hEnergyZero

end Poincare
