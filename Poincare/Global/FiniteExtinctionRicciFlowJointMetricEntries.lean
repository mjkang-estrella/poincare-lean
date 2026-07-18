import Poincare.Global.FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn
import Poincare.Global.FiniteExtinctionInitialScale
import Poincare.Global.MetricFlowJointIteratedConnectionRegularity
import Poincare.Global.MetricFlowJointScalarContinuity

/-!
# Finite extinction from joint C3 Ricci-flow metric entries

This module replaces the separate time differentiability, spatial variation,
mixed Koszul, and iterated-connection hypotheses in the interior Ricci-flow
finite-extinction theorem by one natural joint `C³` hypothesis on canonical
metric entries.  The remaining premises concern the surgery schedule, scalar
and width inequalities, and compactness of alive slices.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

/--
A type-changing Ricci-flow surgery schedule has a first extinct segment when
every alive smooth segment has jointly `C³` canonical metric entries.  This
single regularity premise produces joint scalar continuity on each compact
surgery slab, metric time derivatives, `C²` time variation, the mixed
metric-entry identity, and `MetricFlowRegularAt`.
-/
theorem exists_first_extinct_segment_of_ricciFlow_joint_metric_entries_compact_Ioc
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
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
    (hScalarInitial : Alive 0 →
      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
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
        dW k t ≤ -c - ((1 : ℝ) / 2) *
          scalarMinimumAt (g k t) * W k t)
    (hWidthSurgery : ∀ k, Alive k → Alive (k + 1) →
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) :
    ∃ k, (¬ Alive k) ∧ ∀ j < k, Alive j := by
  have hgt : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        TimeDifferentiableAt (g k) (start k + τ) y := by
    intro k hk τ hτ y
    exact timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
      ((hJoint k hk τ ⟨hτ.1.le, hτ.2⟩ y).of_le (by norm_num))
  have hEntries : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        TimeVariationExtContMDiffAt (g k) (start k + τ) y 2 := by
    intro k hk τ hτ y
    exact timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint k hk τ hτ y)
  have hNearRegExt : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ∀ᶠ y in nhds x,
          MetricFlowRegularAt (g k) (start k + τ) y ∧
          (∀ a b c : TangentSpace (closedSmoothModelWithCorners 3) y,
            HasDerivAt
              (fun t ↦
                extDerivFun
                  (fun z : X k ↦
                    (g k t).inner z
                      (extend (ClosedSmoothModel 3) b z)
                      (extend (ClosedSmoothModel 3) c z))
                  y a)
              (extDerivFun
                (fun z : X k ↦
                  timeDerivAt (g k) (start k + τ) z
                    (extend (ClosedSmoothModel 3) b z)
                    (extend (ClosedSmoothModel 3) c z))
                y a) (start k + τ)) := by
    intro k hk τ hτ x
    have hτIcc : τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k) :=
      ⟨hτ.1.le, hτ.2⟩
    filter_upwards [] with y
    constructor
    · exact metricFlowRegularAt_of_metricEntriesJointContDiffAt_three
        (x := y) (fun z ↦ hJoint k hk τ hτIcc z)
    · exact metricEntry_extDerivFun_hasDerivAt_of_jointContDiffAt_two
        ((hJoint k hk τ hτIcc y).of_le (by norm_num))
  have hRCont : ∀ k, Alive k →
      ContinuousOn
        (fun p : ℝ × X k ↦
          (g k (start k + p.1)).scalarAt p.2)
        (Set.Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ
          (Set.univ : Set (X k))) := by
    intro k hk
    exact continuousOn_scalarAt_timeShift_of_metricEntriesJointContDiffAt_three
      (fun τ hτ y ↦ hJoint k hk τ hτ y)
  exact
    exists_first_extinct_segment_of_ricciFlow_surgery_schedule_family_compact_Ioc_continuousOn
      hC hc Alive hCompact hNonempty g start hstart0 hmono hstartTop
      hRCont hFlow hgt hEntries hNearRegExt hScalarSurgery hScalarInitial W dW
      hWCont hWDeriv hWNonneg hWidthRaw hWidthSurgery

/--
The initial Hamilton barrier scale is automatic.  This form removes both the
external positive constant `C` and its scalar-lower-bound premise, selecting a
valid scale directly from the initial scalar minimum.
-/
theorem exists_first_extinct_segment_of_ricciFlow_joint_metric_entries_compact_Ioc_auto_scale
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    {c : ℝ} (hc : 0 < c)
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
        dW k t ≤ -c - ((1 : ℝ) / 2) *
          scalarMinimumAt (g k t) * W k t)
    (hWidthSurgery : ∀ k, Alive k → Alive (k + 1) →
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) :
    ∃ k, (¬ Alive k) ∧ ∀ j < k, Alive j := by
  rcases exists_positive_hamilton_scalar_barrier_scale
      (scalarMinimumAt (g 0 (start 0))) with ⟨C, hC, hScalarInitial⟩
  exact
    exists_first_extinct_segment_of_ricciFlow_joint_metric_entries_compact_Ioc
      hC hc Alive hCompact hNonempty g start hstart0 hmono hstartTop
      hFlow hJoint hScalarSurgery (fun _ ↦ hScalarInitial)
      W dW hWCont hWDeriv hWNonneg hWidthRaw hWidthSurgery

end Poincare
