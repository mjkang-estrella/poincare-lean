import Poincare.Global.FiniteExtinctionGeometricScalarWidthInterior
import Poincare.Global.ScalarEvolution

/-!
# Finite extinction from interior Ricci-flow regularity

This module discharges the Hamilton scalar-evolution and spatial scalar
regularity inputs of the type-changing finite-extinction theorem from genuine
Ricci-flow slices.  Time differentiability and the mixed time-space regularity
are assumed only at strict positive segment times (`Ioc`).  The Ricci-flow
equation and C² variation entries are retained on `Icc` because the scalar
minimum argument also uses the two endpoint slices.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

/--
The type-changing compact surgery schedule has a first extinct segment once
each alive slice is a sufficiently regular Ricci flow.  Hamilton evolution is
derived only on strict positive segment time; no two-sided time derivative is
requested at a reconstruction start.
-/
theorem exists_first_extinct_segment_of_ricciFlow_surgery_schedule_family_compact_Ioc
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
    (hFlow : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        IsClosedRicciFlowSolutionAt (g k) (start k + τ) y)
    (hgt : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        TimeDifferentiableAt (g k) (start k + τ) y)
    (hEntries : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ y : X k,
        TimeVariationExtContMDiffAt (g k) (start k + τ) y 2)
    (hNearRegExt : ∀ k, Alive k →
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
                y a) (start k + τ)))
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
  have hHam : ∀ k, Alive k →
      ∀ τ ∈ Set.Ioc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x := by
    intro k hk τ hτ x
    have hτIcc : τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k) :=
      ⟨hτ.1.le, hτ.2⟩
    exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_no_raise_hypothesis
      (fun y ↦ hFlow k hk τ hτIcc y)
      (hNearRegExt k hk τ hτ x)
      (fun y ↦ hgt k hk τ hτ y)
      (fun y ↦ hEntries k hk τ hτIcc y)
  have hScalar₂ : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x := by
    intro k hk τ hτ x
    exact scalarAt_contMDiffAt_two_of_ricciFlow
      (fun y ↦ hFlow k hk τ hτ y)
      (fun y ↦ hEntries k hk τ hτ y) x
  exact
    exists_first_extinct_segment_of_hamilton_surgery_schedule_family_compact_Ioc
      hC hc Alive hCompact hNonempty g start hstart0 hmono hstartTop
      hRCont hHam hScalar₂ hScalarSurgery hScalarInitial W dW
      hWCont hWDeriv hWNonneg hWidthRaw hWidthSurgery

end Poincare
