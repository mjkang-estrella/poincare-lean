import Poincare.Global.FiniteExtinctionGeometricScalarWidth
import Poincare.Global.HamiltonScalarInteriorNegativeBarrier

/-!
# Finite extinction from strict positive-time Hamilton evolution

This module carries the interior-start scalar comparison through the
type-changing surgery width argument.  Hamilton scalar evolution is required
only on `Ioc 0 (start (k+1) - start k)` for each smooth segment; no two-sided
time derivative is asserted at a surgery or reconstruction start.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

/-- Type-changing Hamilton/width contradiction with scalar evolution needed
only at strict positive segment times.  Compactness supplies the scalar upper
bound internal to parabolic comparison. -/
theorem no_global_nonnegative_width_of_hamilton_surgery_schedule_family_compact_Ioc
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k,
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hScalarSurgery : ∀ k,
      scalarMinimumAt (g k (start (k + 1))) ≤
        scalarMinimumAt (g (k + 1) (start (k + 1))))
    (hScalarInitial :
      -(3 / (2 * C)) ≤ scalarMinimumAt (g 0 (start 0)))
    (W dW : ℕ → ℝ → ℝ)
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) *
        scalarMinimumAt (g k t) * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  have hscalar :=
    hamilton_scalar_segmented_negative_lower_bound_family_compact_Ioc
      hC g start hstart0 hmono hRCont hHam hScalar₂
        hScalarSurgery hScalarInitial
  have hstartNonneg : ∀ k, 0 ≤ start k := by
    intro k
    induction k with
    | zero => simp [hstart0]
    | succ k ih => exact ih.trans (hmono k)
  apply no_global_nonnegative_of_three_quarter_segmented_surgery_schedule
    hC hc W dW start hstart0 hmono hstartTop hWCont hWDeriv hWNonneg
  · intro k t ht
    have htIcc : t ∈ Set.Icc (start k) (start (k + 1)) :=
      ⟨ht.1.le, ht.2.le⟩
    have hτ : t - start k ∈
        Set.Icc (0 : ℝ) (start (k + 1) - start k) := by
      constructor <;> linarith [ht.1, ht.2]
    have hslice₂ : ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k t).scalarAt y) x := by
      intro x
      simpa using hScalar₂ k (t - start k) hτ x
    obtain ⟨xmin, hxmin⟩ :=
      exists_scalarAt_isMinOn (g := g k t) hslice₂
    have hrLower :
        -(3 / (2 * (C + t))) ≤ scalarMinimumAt (g k t) := by
      rw [scalarMinimumAt_eq_of_isMinOn (g := g k t) hxmin]
      exact hscalar k t htIcc xmin
    have htC : 0 < t + C := by
      have ht0 : 0 ≤ t := (hstartNonneg k).trans ht.1.le
      linarith
    exact three_quarter_width_inequality_of_scalar_lower_bound
      htC (hWNonneg k t htIcc) (by simpa [add_comm] using hrLower)
        (hWidthRaw k t ht)
  · intro k
    exact mul_le_mul_of_nonneg_left (hWidthSurgery k)
      (inv_nonneg.mpr
        (add_nonneg (hstartNonneg (k + 1)) hC.le))

/-- If the analytic and surgery hypotheses hold on every alive segment, the
schedule with strict-positive-time Hamilton evolution has an extinct segment. -/
theorem exists_extinct_segment_of_hamilton_surgery_schedule_family_compact_Ioc
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
    (hRCont : ∀ k, Alive k →
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
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
    ∃ k, ¬ Alive k := by
  by_contra hnone
  push Not at hnone
  letI : ∀ k, CompactSpace (X k) := fun k ↦ hCompact k (hnone k)
  letI : ∀ k, Nonempty (X k) := fun k ↦ hNonempty k (hnone k)
  exact
    no_global_nonnegative_width_of_hamilton_surgery_schedule_family_compact_Ioc
      hC hc g start hstart0 hmono hstartTop
      (fun k ↦ hRCont k (hnone k))
      (fun k ↦ hHam k (hnone k))
      (fun k ↦ hScalar₂ k (hnone k))
      (fun k ↦ hScalarSurgery k (hnone k) (hnone (k + 1)))
      (hScalarInitial (hnone 0)) W dW
      (fun k ↦ hWCont k (hnone k))
      (fun k ↦ hWDeriv k (hnone k))
      (fun k ↦ hWNonneg k (hnone k))
      (fun k ↦ hWidthRaw k (hnone k))
      (fun k ↦ hWidthSurgery k (hnone k) (hnone (k + 1)))

/-- The strict-positive-time Hamilton schedule has a first extinct segment,
with every earlier segment alive. -/
theorem exists_first_extinct_segment_of_hamilton_surgery_schedule_family_compact_Ioc
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
    (hRCont : ∀ k, Alive k →
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
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
  apply exists_first_extinction_index Alive
  exact
    exists_extinct_segment_of_hamilton_surgery_schedule_family_compact_Ioc
      hC hc Alive hCompact hNonempty g start hstart0 hmono hstartTop
      hRCont hHam hScalar₂ hScalarSurgery hScalarInitial W dW
      hWCont hWDeriv hWNonneg hWidthRaw hWidthSurgery

end Poincare
