import Poincare.Global.FiniteExtinctionRicciFlowJointMetricEntries

/-!
# Finite extinction with Perelman's geometric width constant

The joint-metric-entry extinction theorem already derives Hamilton scalar
evolution, scalar-slice regularity, and the initial Riccati barrier scale from
an assembled Ricci-flow surgery family.  This module specializes its remaining
abstract positive width-forcing constant to the geometric Gauss--Bonnet value
`4 * pi`.

Thus the analytic conclusion below has no auxiliary constants: its remaining
inputs are precisely the alive-slice Ricci flows, joint `C^3` metric entries,
surgery monotonicity, and Perelman's raw width inequality.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

/--
A type-changing compact Ricci-flow surgery schedule satisfying Perelman's
`4*pi` width inequality has a first extinct segment.  Hamilton scalar
evolution and the scalar minimum barrier are derived internally from the
Ricci-flow equation and joint `C^3` metric entries; the positive barrier scale
is selected automatically from the initial scalar minimum.
-/
theorem exists_first_extinct_segment_of_ricciFlow_joint_metric_entries_perelman_width
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    (Alive : ℕ → Prop)
    (hCompact : ∀ k, Alive k → CompactSpace (X k))
    (hNonempty : ∀ k, Alive k → Nonempty (X k))
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hFlow : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        IsClosedRicciFlowSolutionAt (g k) (start k + τ) y)
    (hJoint : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        MetricEntriesJointContDiffAt (g k) (start k + τ) y 3)
    (hScalarSurgery : ∀ k, Alive k → Alive (k + 1) →
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (W dW : ℕ → ℝ → ℝ)
    (hWCont : ∀ k, Alive k →
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, Alive k →
      ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
        HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, Alive k →
      ∀ t ∈ Set.Icc (start k) (start (k + 1)), 0 ≤ W k t)
    (hWidthRaw : ∀ k, Alive k →
      ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
        dW k t ≤ -((4 : ℝ) * Real.pi) - ((1 : ℝ) / 2) *
          scalarMinimumAt (g k t) * W k t)
    (hWidthSurgery : ∀ k, Alive k → Alive (k + 1) →
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) :
    ∃ k, (¬ Alive k) ∧ ∀ j < k, Alive j := by
  exact
    exists_first_extinct_segment_of_ricciFlow_joint_metric_entries_compact_Ioc_auto_scale
      perelman_four_pi_pos Alive hCompact hNonempty g start hstart0 hmono
      hstartTop hFlow hJoint hScalarSurgery W dW hWCont hWDeriv hWNonneg
      hWidthRaw hWidthSurgery

end Poincare
