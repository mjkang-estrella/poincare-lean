import Poincare.Global.SemilinearHeatBUCRegularity

/-!
# Initial regularity for local semilinear heat fixed points

The initial-time regularity argument does not require a globally Lipschitz
nonlinearity or the canonical global contraction solution.  Any fixed point of
the corrected Picard map has right derivative `A u₀ + N(u₀)` whenever the
initial datum belongs to the strong heat-generator domain.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Mild-to-classical initial-time upgrade for an arbitrary local fixed point
of the corrected semilinear heat Picard map. -/
theorem semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (T : ℝ≥0) (u₀ Au₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) u₀ Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ u (Set.projIcc 0 (T : ℝ) T.property t))
      (Au₀ + N u₀) (Set.Icc 0 (T : ℝ)) 0 := by
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, ⟨le_rfl, T.property⟩⟩
  have huzero : u z = u₀ := by
    have hz := congrArg (fun w : DuhamelPath T BUC ↦ w z) hu
    simpa [z] using hz.symm
  let D : ℝ → BUC := fun t ↦ ∫ s : ℝ in (0 : ℝ)..t,
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (t - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  have hD : HasDerivWithinAt D (N u₀) (Set.Ici 0) 0 := by
    have h := hasDerivWithinAt_heatDuhamelBUCIntrinsic_zero
      (E := E) (F := F) T N hN u
    simpa [D, z, huzero] using h
  have hsum := hu₀.add hD
  have hsumIcc : HasDerivWithinAt
      (fun t : ℝ ↦
        vectorHeatSemigroupBUCExtended (E := E) (F := F) t u₀ + D t)
      (Au₀ + N u₀) (Set.Icc 0 (T : ℝ)) 0 := by
    apply hsum.mono
    intro t ht
    exact ht.1
  apply hsumIcc.congr
  · intro t ht
    have hproj : Set.projIcc 0 (T : ℝ) T.property t =
        (⟨t, ht⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := by
      apply Subtype.ext
      simp [Set.coe_projIcc, max_eq_right ht.1, min_eq_right ht.2]
    have hfixed := congrArg
      (fun w : DuhamelPath T BUC ↦ w (⟨t, ht⟩ : Set.Icc (0 : ℝ) (T : ℝ))) hu
    rw [hproj]
    simpa [D] using hfixed.symm
  · simp [D, z, huzero, vectorHeatSemigroupBUCExtended]

end Poincare
