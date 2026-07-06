import Poincare.Global.DeTurckField

/-!
# Regularity decomposition for the DeTurck vector field

This module isolates the finite-sum and tensoriality reductions needed for the
regularity of the concrete DeTurck field.  The remaining analytic bridge is the
`C²` regularity of each connection-difference contraction.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

section General

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
One summand of the DeTurck vector field trace, indexed by the fixed model
finite basis cardinality.
-/
noncomputable def deTurckVectorFieldSummand
    (g bg : ClosedSmoothRiemannianMetric n M) (i : Fin (Module.finrank ℝ E)) :
    ∀ x : M, TM x :=
  fun x ↦
    letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    deTurckConnectionDifferenceAt g bg x
      ((Module.finBasis ℝ (TM x)) i)
      (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i))

/--
The pointwise connection-difference spelling agrees with Mathlib's tensorial
`CovariantDerivative.difference`.
-/
theorem deTurckConnectionDifferenceAt_eq_difference
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) (u w : TM x) :
    deTurckConnectionDifferenceAt g bg x u w =
      ((g.leviCivita.difference bg.leviCivita) x w) u := by
  have hσ :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (fun y : M ↦ ((extend E w) y : TotalSpace E TM)) x := by
    simpa using (mdifferentiableAt_extend I E w)
  have hdiff := IsCovariantDerivativeOn.difference_apply
    (g.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (bg.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (x := x) (σ := (show (y : M) → TM y from extend E w))
    (s := Set.univ) (by trivial) hσ
  have happly := congrArg (fun L : TM x →L[ℝ] TM x ↦ L u) hdiff
  simpa [deTurckConnectionDifferenceAt, CovariantDerivative.difference] using
    happly.symm

theorem deTurckVectorFieldSummand_eq_difference
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckVectorFieldSummand g bg i x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      ((g.leviCivita.difference bg.leviCivita) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)))
        ((Module.finBasis ℝ (TM x)) i)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  simp [deTurckVectorFieldSummand, deTurckConnectionDifferenceAt_eq_difference]

theorem deTurckConnectionDifferenceAt_add_left
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (u₁ u₂ w : TM x) :
    deTurckConnectionDifferenceAt g bg x (u₁ + u₂) w =
      deTurckConnectionDifferenceAt g bg x u₁ w +
        deTurckConnectionDifferenceAt g bg x u₂ w := by
  simp [deTurckConnectionDifferenceAt_eq_difference]

theorem deTurckConnectionDifferenceAt_smul_left
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (c : ℝ) (u w : TM x) :
    deTurckConnectionDifferenceAt g bg x (c • u) w =
      c • deTurckConnectionDifferenceAt g bg x u w := by
  simp [deTurckConnectionDifferenceAt_eq_difference]

theorem deTurckConnectionDifferenceAt_add_right
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w₁ w₂ : TM x) :
    deTurckConnectionDifferenceAt g bg x u (w₁ + w₂) =
      deTurckConnectionDifferenceAt g bg x u w₁ +
        deTurckConnectionDifferenceAt g bg x u w₂ := by
  simp [deTurckConnectionDifferenceAt_eq_difference]

theorem deTurckConnectionDifferenceAt_smul_right
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (c : ℝ) (u w : TM x) :
    deTurckConnectionDifferenceAt g bg x u (c • w) =
      c • deTurckConnectionDifferenceAt g bg x u w := by
  simp [deTurckConnectionDifferenceAt_eq_difference]

/-- The DeTurck vector field is the finite sum of its named trace summands. -/
theorem deTurckVectorFieldAt_eq_sum_summands
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    deTurckVectorFieldAt g bg x =
      ∑ i, deTurckVectorFieldSummand g bg i x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rfl

omit [T2Space M] in
/-- Finite sums of closed `C²` tangent fields are closed `C²`. -/
theorem closedC2TangentField_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Z : ι → ∀ x : M, TM x}
    (hZ : ∀ i, ClosedC2TangentField (n := n) (M := M) (Z i)) :
    ClosedC2TangentField (n := n) (M := M) (fun x ↦ ∑ i, Z i x) := by
  classical
  unfold ClosedC2TangentField at *
  simpa using
    (ContMDiff.sum_section
      (s := (Finset.univ : Finset ι)) (t := Z)
      (fun i _ ↦ hZ i))

/--
If each named DeTurck trace summand is a closed `C²` tangent field, then the
concrete DeTurck vector field is regular.
-/
theorem deTurckVectorFieldRegularAt_holds_of_summand_regularity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (hSummand : ∀ i : Fin (Module.finrank ℝ E),
      ClosedC2TangentField (n := n) (M := M)
        (deTurckVectorFieldSummand (gt t) bg i)) :
    DeTurckVectorFieldRegularAt gt bg t := by
  have hsum :
      ClosedC2TangentField (n := n) (M := M)
        (fun x ↦ ∑ i : Fin (Module.finrank ℝ E),
          deTurckVectorFieldSummand (gt t) bg i x) :=
    closedC2TangentField_sum (n := n) (M := M) hSummand
  simpa [DeTurckVectorFieldRegularAt, deTurckVectorField,
    deTurckVectorFieldAt_eq_sum_summands] using hsum

/--
The concrete gauged-flow predicate exposes the DeTurck field regularity clause
for its chosen vector-field family.
-/
theorem isDeTurckGaugedFlowAt.deTurckField
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t : ℝ} {x : M}
    (h : IsDeTurckGaugedFlowAt gt bg t x) :
    DeTurckVectorFieldRegularAt gt bg t := by
  simpa [IsDeTurckGaugedFlowAt, DeTurckVectorFieldRegularAt] using h.deTurckField

end General

end Poincare
