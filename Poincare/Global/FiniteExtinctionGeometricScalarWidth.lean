import Poincare.Global.FiniteExtinctionScalarWidth
import Poincare.Global.HamiltonScalarNegativeBarrier

/-!
# Intrinsic geometric scalar-to-width extinction

This file connects the scalar/width surgery argument to the repository's
intrinsic closed-Riemannian-metric vocabulary.  At each selected scalar
minimum it uses:

* `laplacianAt_nonneg_of_isLocalMin` for the spatial minimum;
* `hamilton_scalar_reaction_bound_at` for `R² ≤ 3 |Ric|²`;
* the supplied Hamilton minimum-track derivative identity.

These derive the `2/3` Riccati inequality consumed by
`no_global_nonnegative_width_of_scalar_riccati_surgery_schedule`.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory Filter Set
open scoped Manifold ContDiff Interval Topology

universe u

namespace Poincare

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "E" => ClosedSmoothModel 3

/-- If the differentiable scalar-minimum envelope has the same time
derivative as the scalar track at a frozen minimizing point, Hamilton's
intrinsic scalar evolution identifies that derivative with `ΔR + 2|Ric|²`.
This isolates the remaining envelope-theorem input from the already-proved
geometric evolution equation. -/
theorem hamilton_minimum_track_derivative_eq
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) (x : M) (R' : ℝ)
    (hEnvelope : HasDerivAt (fun s => (gt s).scalarAt x) R' t)
    (hHamilton : SatisfiesHamiltonScalarEvolutionAt gt t x) :
    R' = (gt t).laplacianAt (fun y : M => (gt t).scalarAt y) x +
      2 * (gt t).ricciNormSqAt x := by
  have hIntrinsic :
      HasDerivAt (fun s => (gt s).scalarAt x)
        ((gt t).laplacianAt (fun y : M => (gt t).scalarAt y) x +
          2 * (gt t).ricciNormSqAt x) t := by
    simpa [SatisfiesHamiltonScalarEvolutionAt] using hHamilton
  exact hEnvelope.unique hIntrinsic

/-- End-to-end width extinction from the actual Hamilton scalar PDE on every
smooth surgery segment.

The compact parabolic minimum principle supplies the negative scalar barrier
without differentiating a minimizing-point selection.  Scalar-nondecreasing
surgery restarts that barrier, and the raw width inequality is converted to
Perelman's three-quarter inequality before applying the segmented
integrating-factor contradiction. -/
theorem no_global_nonnegative_width_of_hamilton_surgery_schedule
    [CompactSpace M] [Nonempty M]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (g : ℕ → ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : M) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k),
      ∀ x : M,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : M,
        (g k (start k + τ)).scalarAt x ≤ B k)
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
  have hscalar := hamilton_scalar_segmented_negative_lower_bound
    hC g start B hstart0 hmono hRCont hHam hScalar₂ hRB
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
    have hslice₂ : ∀ x : M,
        ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ (g k t).scalarAt y) x := by
      intro x
      simpa using hScalar₂ k (t - start k) hτ x
    obtain ⟨xmin, hxmin⟩ := exists_scalarAt_isMinOn (g := g k t) hslice₂
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

/-- Fully type-changing surgery version of the Hamilton/width extinction
contradiction.  Smooth components before and after a surgery may have
different underlying manifold types; only scalar-minimum and width jump
inequalities cross the surgery boundary. -/
theorem no_global_nonnegative_width_of_hamilton_surgery_schedule_family
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hRCont : ∀ k,
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B k)
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
  have hscalar := hamilton_scalar_segmented_negative_lower_bound_family
    hC g start B hstart0 hmono hRCont hHam hScalar₂ hRB
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
    obtain ⟨xmin, hxmin⟩ := exists_scalarAt_isMinOn (g := g k t) hslice₂
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

/-- Compactness-derived type-changing Hamilton/width contradiction.  Joint
scalar continuity on each compact time slab supplies the scalar upper bounds
used internally by the parabolic minimum principle. -/
theorem no_global_nonnegative_width_of_hamilton_surgery_schedule_family_compact
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
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
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
  classical
  have hBound : ∀ k, ∃ B : ℝ,
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B := by
    intro k
    let f : ℝ × X k → ℝ := fun p ↦ (g k (start k + p.1)).scalarAt p.2
    let K : Set (ℝ × X k) :=
      Set.Icc (0 : ℝ) (start (k + 1) - start k) ×ˢ Set.univ
    have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
    have hf : Continuous f := by simpa [f] using hRCont k
    obtain ⟨B, hB⟩ := hK.bddAbove_image hf.continuousOn
    refine ⟨B, ?_⟩
    intro τ hτ x
    have hmem : f (τ, x) ∈ f '' K :=
      mem_image_of_mem f (show (τ, x) ∈ K by exact ⟨hτ, Set.mem_univ x⟩)
    simpa [f] using hB hmem
  let B : ℕ → ℝ := fun k ↦ Classical.choose (hBound k)
  exact no_global_nonnegative_width_of_hamilton_surgery_schedule_family
    hC hc g start B hstart0 hmono hstartTop hRCont hHam hScalar₂
      (fun k ↦ by simpa [B] using Classical.choose_spec (hBound k))
      hScalarSurgery hScalarInitial W dW hWCont hWDeriv hWNonneg
      hWidthRaw hWidthSurgery

/-- Finite extinction for a type-changing surgery schedule, with all scalar
upper bounds discharged by compactness. -/
theorem exists_extinct_segment_of_hamilton_surgery_schedule_family_compact
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
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
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
  exact no_global_nonnegative_width_of_hamilton_surgery_schedule_family_compact
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

/-- Finite-extinction conclusion for a type-changing Hamilton surgery
schedule.  Analytic and surgery hypotheses are required only for segments
declared alive.  If every segment were alive, the preceding global theorem
would give a contradiction. -/
theorem exists_extinct_segment_of_hamilton_surgery_schedule_family
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (Alive : ℕ → Prop)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hRCont : ∀ k, Alive k →
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B k)
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
  exact no_global_nonnegative_width_of_hamilton_surgery_schedule_family
    hC hc g start B hstart0 hmono hstartTop
    (fun k ↦ hRCont k (hnone k))
    (fun k ↦ hHam k (hnone k))
    (fun k ↦ hScalar₂ k (hnone k))
    (fun k ↦ hRB k (hnone k))
    (fun k ↦ hScalarSurgery k (hnone k) (hnone (k + 1)))
    (hScalarInitial (hnone 0)) W dW
    (fun k ↦ hWCont k (hnone k))
    (fun k ↦ hWDeriv k (hnone k))
    (fun k ↦ hWNonneg k (hnone k))
    (fun k ↦ hWidthRaw k (hnone k))
    (fun k ↦ hWidthSurgery k (hnone k) (hnone (k + 1)))

/-- The type-changing Hamilton surgery schedule has a first extinct segment,
and every preceding segment is alive. -/
theorem exists_first_extinct_segment_of_hamilton_surgery_schedule_family
    {X : ℕ → Type u}
    [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (ClosedSmoothModel 3) (X k)]
    [∀ k, IsManifold (closedSmoothModelWithCorners 3) ∞ (X k)]
    [∀ k, CompactSpace (X k)] [∀ k, Nonempty (X k)]
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (Alive : ℕ → Prop)
    (g : (k : ℕ) → ℝ → ClosedSmoothRiemannianMetric 3 (X k))
    [∀ k : ℕ, ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (g k t).leviCivita 1]
    (start : ℕ → ℝ) (B : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hRCont : ∀ k, Alive k →
      Continuous ↿(fun τ (x : X k) ↦
        (g k (start k + τ)).scalarAt x))
    (hHam : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        SatisfiesHamiltonScalarEvolutionAt (g k) (start k + τ) x)
    (hScalar₂ : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
          (fun y : X k ↦ (g k (start k + τ)).scalarAt y) x)
    (hRB : ∀ k, Alive k →
      ∀ τ ∈ Set.Icc (0 : ℝ) (start (k + 1) - start k), ∀ x : X k,
        (g k (start k + τ)).scalarAt x ≤ B k)
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
  exact exists_extinct_segment_of_hamilton_surgery_schedule_family
    hC hc Alive g start B hstart0 hmono hstartTop hRCont hHam hScalar₂ hRB
      hScalarSurgery hScalarInitial W dW hWCont hWDeriv hWNonneg
      hWidthRaw hWidthSurgery

/-- Intrinsic end-to-end finite-extinction contradiction.  The time derivative
of the scalar minimum track is supplied explicitly; all spatial and curvature
terms are discharged using the actual closed metric at that time. -/
theorem no_global_nonnegative_width_of_intrinsic_hamilton_minimum_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (g : ℕ → ℝ → ClosedSmoothRiemannianMetric 3 M)
    (xmin : ℕ → ℝ → M)
    (r dr W dW : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hrValue : ∀ k t, r k t = (g k t).scalarAt (xmin k t))
    (hScalar₂ : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M => (g k t).scalarAt y) (xmin k t))
    (hScalarGrad : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((g k t).gradient (fun y : M => (g k t).scalarAt y)))
        (xmin k t))
    (hScalarMin : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      IsLocalMin (fun y : M => (g k t).scalarAt y) (xmin k t))
    (hHamiltonMinimumTrack : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dr k t =
        (g k t).laplacianAt (fun y : M => (g k t).scalarAt y) (xmin k t) +
          2 * (g k t).ricciNormSqAt (xmin k t))
    (hrSurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  apply no_global_nonnegative_width_of_scalar_riccati_surgery_schedule
    hC hc r dr W dW start hstart0 hmono hstartTop hrCont hrDeriv
  · intro k t ht
    have hlap :
        0 ≤ (g k t).laplacianAt
          (fun y : M => (g k t).scalarAt y) (xmin k t) :=
      laplacianAt_nonneg_of_isLocalMin
        (g := g k t) (f := fun y : M => (g k t).scalarAt y)
        (x := xmin k t) (hScalar₂ k t ht) (hScalarGrad k t ht)
        (hScalarMin k t ht)
    have hreact := hamilton_scalar_reaction_bound_at
      (g := g k t) (x := xmin k t) (show 0 < (3 : ℝ) by norm_num)
    rw [hrValue k t, hHamiltonMinimumTrack k t ht]
    linarith
  · exact hrSurgery
  · exact hrInitial
  · exact hWCont
  · exact hWDeriv
  · exact hWNonneg
  · exact hWidthRaw
  · exact hWidthSurgery

/-- Intrinsic finite extinction directly from Hamilton's scalar evolution.

The only time-dependent minimum input left explicit is the envelope derivative:
at a minimizing point selected at time `t`, differentiating the minimum value is
the same as differentiating the scalar curvature while freezing that point.
Hamilton's actual scalar evolution then supplies the reaction/diffusion identity;
the spatial minimum and three-dimensional Ricci estimates are discharged by
`no_global_nonnegative_width_of_intrinsic_hamilton_minimum_schedule`. -/
theorem no_global_nonnegative_width_of_intrinsic_hamilton_evolution_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (g : ℕ → ℝ → ClosedSmoothRiemannianMetric 3 M)
    (xmin : ℕ → ℝ → M)
    (r dr W dW : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hrValue : ∀ k t, r k t = (g k t).scalarAt (xmin k t))
    (hScalar₂ : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M => (g k t).scalarAt y) (xmin k t))
    (hScalarGrad : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((g k t).gradient (fun y : M => (g k t).scalarAt y)))
        (xmin k t))
    (hScalarMin : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      IsLocalMin (fun y : M => (g k t).scalarAt y) (xmin k t))
    (hEnvelopeDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivAt (fun s => (g k s).scalarAt (xmin k t)) (dr k t) t)
    (hHamilton : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      SatisfiesHamiltonScalarEvolutionAt (g k) t (xmin k t))
    (hrSurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  apply no_global_nonnegative_width_of_intrinsic_hamilton_minimum_schedule
    hC hc g xmin r dr W dW start hstart0 hmono hstartTop hrCont hrDeriv
      hrValue hScalar₂ hScalarGrad hScalarMin
  · intro k t ht
    exact hamilton_minimum_track_derivative_eq
      (gt := g k) (t := t) (x := xmin k t) (R' := dr k t)
      (hEnvelopeDeriv k t ht) (hHamilton k t ht)
  · exact hrSurgery
  · exact hrInitial
  · exact hWCont
  · exact hWDeriv
  · exact hWNonneg
  · exact hWidthRaw
  · exact hWidthSurgery

end Poincare
