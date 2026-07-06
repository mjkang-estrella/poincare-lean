import Poincare.Global.DeTurckFieldRegularity

/-!
# Conditional regularity bridge for DeTurck trace summands

This module isolates the exact `C²` section regularity inputs needed to turn
the tensorial connection-difference spelling of a DeTurck trace summand into a
closed `C²` tangent field.

The unconditional summand theorem is intentionally not stated here: the two
analytic inputs below are the current frontier.
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

/-- The raw model finite-basis vector field used by the frozen summand. -/
noncomputable def deTurckModelBasisField
    (i : Fin (Module.finrank ℝ E)) : ∀ x : M, TM x :=
  fun x ↦
    letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    (Module.finBasis ℝ (TM x)) i

/-- The metric-raised raw finite-basis coordinate covector field. -/
noncomputable def deTurckRaisedFinBasisField
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ E)) : ∀ x : M, TM x :=
  fun x ↦
    letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)

/--
`C²` regularity of the tensorial connection-difference section
`Γ(g) - Γ(bg)`.
-/
def ClosedC2ConnectionDifferenceSection
    (g bg : ClosedSmoothRiemannianMetric n M) : Prop :=
  ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
    (fun x : M =>
      (⟨x, (g.leviCivita.difference bg.leviCivita) x⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] E)
          (fun x : M => TM x →L[ℝ] TM x →L[ℝ] TM x)))

@[simp] theorem deTurckModelBasisField_apply
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckModelBasisField (n := n) (M := M) i x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      (Module.finBasis ℝ (TM x)) i) :=
  rfl

/-- The moving finite basis reduces to the fixed model finite basis. -/
theorem deTurckModelBasisField_apply_eq_model
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckModelBasisField (n := n) (M := M) i x =
      (Module.finBasis ℝ E) i := by
  rfl

@[simp] theorem deTurckRaisedFinBasisField_apply
    (g : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    deTurckRaisedFinBasisField (n := n) (M := M) g i x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) :=
  rfl

/-- The moving finite basis reduces to the fixed model finite basis. -/
theorem deTurck_finBasis_apply_eq_model
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ((Module.finBasis ℝ (TM x)) i : E)) =
      (Module.finBasis ℝ E) i := by
  rfl

/-- The moving finite coordinate covector reduces to the fixed model coordinate covector. -/
theorem deTurck_finBasis_coord_eq_model
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    ((Module.finBasis ℝ (TM x)).coord i : E →ₗ[ℝ] ℝ)) =
      ((Module.finBasis ℝ E).coord i : E →ₗ[ℝ] ℝ) := by
  rfl

/-- Smooth metrics give `C²` inverse-Gram scalar entries in an anchored extension frame. -/
theorem gramMatrix_inv_entry_contMDiffAt_two
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x :=
  gramMatrix_inv_entry_contMDiffAt_two_of_metricExtContMDiffAt
    (g := g) (x := x) (metricExtContMDiffAt_two g x) i j

/-- The frozen summand is the tensorial difference applied to the two named fields. -/
theorem deTurckVectorFieldSummand_eq_bridge_fields
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ E)) :
    deTurckVectorFieldSummand g bg i =
      fun x : M =>
        ((g.leviCivita.difference bg.leviCivita) x
          (deTurckRaisedFinBasisField (n := n) (M := M) g i x))
          (deTurckModelBasisField (n := n) (M := M) i x) := by
  funext x
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  simp [deTurckVectorFieldSummand, deTurckConnectionDifferenceAt_eq_difference,
    deTurckRaisedFinBasisField, deTurckModelBasisField]

/--
Conditional summand regularity from the three honest section-regularity
bridges: connection difference, raw finite-basis field, and raised finite-basis
field.
-/
theorem deTurckVectorFieldSummand_closedC2_of_bridge_regularities
    (g bg : ClosedSmoothRiemannianMetric n M)
    (i : Fin (Module.finrank ℝ E))
    (hDiff : ClosedC2ConnectionDifferenceSection (n := n) (M := M) g bg)
    (hBasis : ClosedC2TangentField (n := n) (M := M)
      (deTurckModelBasisField (n := n) (M := M) i))
    (hRaised : ClosedC2TangentField (n := n) (M := M)
      (deTurckRaisedFinBasisField (n := n) (M := M) g i)) :
    ClosedC2TangentField (n := n) (M := M)
      (deTurckVectorFieldSummand g bg i) := by
  unfold ClosedC2ConnectionDifferenceSection at hDiff
  unfold ClosedC2TangentField at hBasis hRaised ⊢
  have hOnce :
      ContMDiff I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun x : M =>
          (⟨x,
            (g.leviCivita.difference bg.leviCivita) x
              (deTurckRaisedFinBasisField (n := n) (M := M) g i x)⟩ :
            TotalSpace (E →L[ℝ] E)
              (fun x : M => TM x →L[ℝ] TM x))) :=
    hDiff.clm_bundle_apply hRaised
  have hTwice :
      ContMDiff I ((I).prod 𝓘(ℝ, E)) 2
        (fun x : M =>
          (⟨x,
            ((g.leviCivita.difference bg.leviCivita) x
              (deTurckRaisedFinBasisField (n := n) (M := M) g i x))
              (deTurckModelBasisField (n := n) (M := M) i x)⟩ :
            TotalSpace E TM)) :=
    hOnce.clm_bundle_apply hBasis
  simpa [deTurckVectorFieldSummand_eq_bridge_fields] using hTwice

/-- Conditional regularity of the whole DeTurck field from the bridge inputs. -/
theorem deTurckVectorFieldRegularAt_holds_of_bridge_regularities
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (hDiff : ClosedC2ConnectionDifferenceSection (n := n) (M := M) (gt t) bg)
    (hBasis : ∀ i : Fin (Module.finrank ℝ E),
      ClosedC2TangentField (n := n) (M := M)
        (deTurckModelBasisField (n := n) (M := M) i))
    (hRaised : ∀ i : Fin (Module.finrank ℝ E),
      ClosedC2TangentField (n := n) (M := M)
        (deTurckRaisedFinBasisField (n := n) (M := M) (gt t) i)) :
    DeTurckVectorFieldRegularAt gt bg t := by
  refine deTurckVectorFieldRegularAt_holds_of_summand_regularity
    (gt := gt) (bg := bg) (t := t) ?_
  intro i
  exact deTurckVectorFieldSummand_closedC2_of_bridge_regularities
    (g := gt t) (bg := bg) (i := i) hDiff (hBasis i) (hRaised i)

end General

end Poincare
