import Poincare.Global.SemilinearHeatBUC

/-!
# Restart identities for semilinear heat mild solutions on `BUC`

A mild solution on `[0,T]`, shifted by an intermediate time `a`, is again a
mild solution with initial datum `u(a)` on the remaining interval.  This file
proves the identity directly from the heat semigroup law, interval-integral
splitting, and translation of the second integral.
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

/-- The remaining nonnegative time after an intermediate point of `[0,T]`. -/
def remainingDuhamelTime (T : ℝ≥0) (a : Set.Icc (0 : ℝ) (T : ℝ)) : ℝ≥0 :=
  ⟨(T : ℝ) - (a : ℝ), sub_nonneg.mpr a.property.2⟩

@[simp, norm_cast]
theorem coe_remainingDuhamelTime
    (T : ℝ≥0) (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    (remainingDuhamelTime T a : ℝ) = (T : ℝ) - (a : ℝ) :=
  rfl

/-- Addition of an intermediate time embeds the remaining interval into the
original time interval. -/
def restartDuhamelTimeMap
    (T : ℝ≥0) (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    C(Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ),
      Set.Icc (0 : ℝ) (T : ℝ)) where
  toFun τ := ⟨(a : ℝ) + (τ : ℝ), by
    constructor
    · exact add_nonneg a.property.1 τ.property.1
    · change (a : ℝ) + (τ : ℝ) ≤ (T : ℝ)
      have hτ := τ.property.2
      change (τ : ℝ) ≤ (T : ℝ) - (a : ℝ) at hτ
      linarith⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_const.add continuous_subtype_val) _

@[simp]
theorem restartDuhamelTimeMap_coe
    (T : ℝ≥0) (a : Set.Icc (0 : ℝ) (T : ℝ))
    (τ : Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ)) :
    ((restartDuhamelTimeMap T a τ : Set.Icc (0 : ℝ) (T : ℝ)) : ℝ) =
      (a : ℝ) + (τ : ℝ) :=
  rfl

/-- Shift a Duhamel path to begin at an intermediate time. -/
def restartDuhamelPath
    (T : ℝ≥0) (u : DuhamelPath T BUC)
    (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    DuhamelPath (remainingDuhamelTime T a) BUC :=
  u.comp (restartDuhamelTimeMap T a)

@[simp]
theorem restartDuhamelPath_apply
    (T : ℝ≥0) (u : DuhamelPath T BUC)
    (a : Set.Icc (0 : ℝ) (T : ℝ))
    (τ : Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ)) :
    restartDuhamelPath T u a τ = u (restartDuhamelTimeMap T a τ) :=
  rfl

/-- Algebraic restart identity for the heat-propagated integral of a
continuous forcing. -/
theorem vectorHeatSemigroupBUCExtended_restart_integral
    (G : ℝ → BUC) (hG : Continuous G)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    vectorHeatSemigroupBUCExtended (E := E) (F := F) b
        (∫ s : ℝ in (0 : ℝ)..a,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) +
      ∫ r : ℝ in (0 : ℝ)..b,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (b - r) (G (a + r)) =
      ∫ s : ℝ in (0 : ℝ)..(a + b),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (a + b - s) (G s) := by
  let g : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) (a + b - s) (G s)
  have hg : Continuous g := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact (continuous_const.add continuous_const).sub continuous_id
    · exact hG
  have hk : Continuous (fun s : ℝ ↦
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hG
  have hfirst :
      vectorHeatSemigroupBUCExtended (E := E) (F := F) b
          (∫ s : ℝ in (0 : ℝ)..a,
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) =
        ∫ s : ℝ in (0 : ℝ)..a, g s := by
    calc
      vectorHeatSemigroupBUCExtended (E := E) (F := F) b
          (∫ s : ℝ in (0 : ℝ)..a,
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) =
          ∫ s : ℝ in (0 : ℝ)..a,
            vectorHeatSemigroupBUCExtended (E := E) (F := F) b
              (vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) := by
        exact (ContinuousLinearMap.intervalIntegral_comp_comm
          (vectorHeatSemigroupBUCExtended (E := E) (F := F) b)
          (hk.intervalIntegrable (0 : ℝ) a)).symm
      _ = ∫ s : ℝ in (0 : ℝ)..a, g s := by
        apply intervalIntegral.integral_congr
        intro s hs
        have hsa : s ≤ a := by
          simpa [max_eq_right ha] using hs.2
        change vectorHeatSemigroupBUCExtended (E := E) (F := F) b
            (vectorHeatSemigroupBUCExtended (E := E) (F := F) (a - s) (G s)) =
          g s
        rw [vectorHeatSemigroupBUCExtended_add_apply
          (E := E) (F := F) hb (sub_nonneg.mpr hsa)]
        congr 2
        ring
  have hsecond :
      (∫ r : ℝ in (0 : ℝ)..b,
        vectorHeatSemigroupBUCExtended (E := E) (F := F) (b - r) (G (a + r))) =
        ∫ s : ℝ in a..(a + b), g s := by
    have hshift := intervalIntegral.integral_comp_add_left
      (a := (0 : ℝ)) (b := b) g a
    convert hshift using 1 <;> simp [g] <;> ring
  rw [hfirst, hsecond]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (0 : ℝ) a)
    (hg.intervalIntegrable a (a + b))

/-- A fixed point of the corrected semilinear heat map satisfies the mild
formula after restart at every intermediate time. -/
theorem semilinearHeatBUCFixedPoint_restart_mild
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (a : Set.Icc (0 : ℝ) (T : ℝ))
    (τ : Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ)) :
    restartDuhamelPath T u a τ =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (τ : ℝ) (u a) +
        ∫ r : ℝ in (0 : ℝ)..(τ : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((τ : ℝ) - r)
            (N (restartDuhamelPath T u a
              (Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
                (remainingDuhamelTime T a).property r))) := by
  let G : ℝ → BUC := fun s ↦
    N (u (Set.projIcc 0 (T : ℝ) T.property s))
  have hG : Continuous G :=
    hN.comp (u.continuous.comp (continuous_projIcc (h := T.property)))
  have hmild : ∀ t : Set.Icc (0 : ℝ) (T : ℝ),
      u t = vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s) (G s) := by
    intro t
    have ht := congrArg (fun w : DuhamelPath T BUC ↦ w t) hu
    simpa [G] using ht.symm
  let t : Set.Icc (0 : ℝ) (T : ℝ) := restartDuhamelTimeMap T a τ
  have htcoe : (t : ℝ) = (a : ℝ) + (τ : ℝ) := rfl
  have hrestart := vectorHeatSemigroupBUCExtended_restart_integral
    (E := E) (F := F) G hG (a : ℝ) (τ : ℝ) a.property.1 τ.property.1
  have htranslated :
      (∫ r : ℝ in (0 : ℝ)..(τ : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((τ : ℝ) - r)
          (N (restartDuhamelPath T u a
            (Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
              (remainingDuhamelTime T a).property r)))) =
      ∫ r : ℝ in (0 : ℝ)..(τ : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((τ : ℝ) - r)
          (G ((a : ℝ) + r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := by
      simpa [min_eq_left τ.property.1] using hr.1
    have hrτ : r ≤ (τ : ℝ) := by
      simpa [max_eq_right τ.property.1] using hr.2
    have hrRemain : r ≤ (remainingDuhamelTime T a : ℝ) :=
      hrτ.trans τ.property.2
    have hprojRemain :
        Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
            (remainingDuhamelTime T a).property r =
          (⟨r, ⟨hr0, hrRemain⟩⟩ :
            Set.Icc (0 : ℝ) (remainingDuhamelTime T a : ℝ)) := by
      apply Subtype.ext
      simp only [Set.coe_projIcc]
      rw [min_eq_right hrRemain, max_eq_right hr0]
    have harT : (a : ℝ) + r ≤ (T : ℝ) := by
      change r ≤ (T : ℝ) - (a : ℝ) at hrRemain
      linarith
    have hprojT :
        Set.projIcc 0 (T : ℝ) T.property ((a : ℝ) + r) =
          (⟨(a : ℝ) + r, ⟨add_nonneg a.property.1 hr0, harT⟩⟩ :
            Set.Icc (0 : ℝ) (T : ℝ)) := by
      apply Subtype.ext
      simp [Set.coe_projIcc, max_eq_right (add_nonneg a.property.1 hr0),
        min_eq_right harT]
    change vectorHeatSemigroupBUCExtended (E := E) (F := F) ((τ : ℝ) - r)
        (N (restartDuhamelPath T u a
          (Set.projIcc 0 (remainingDuhamelTime T a : ℝ)
            (remainingDuhamelTime T a).property r))) = _
    rw [hprojRemain]
    change vectorHeatSemigroupBUCExtended (E := E) (F := F) ((τ : ℝ) - r)
        (N (u ⟨(a : ℝ) + r, ⟨add_nonneg a.property.1 hr0, harT⟩⟩)) = _
    simp only [G, hprojT]
  rw [restartDuhamelPath_apply]
  change u t = _
  rw [hmild t, htcoe]
  rw [hmild a]
  rw [map_add]
  rw [vectorHeatSemigroupBUCExtended_add_apply
    (E := E) (F := F) τ.property.1 a.property.1]
  rw [htranslated]
  rw [add_assoc, hrestart]
  congr 2
  ring

/-- Equivalently, the restarted path is a fixed point of the corrected
semilinear heat Picard map based at `u(a)`. -/
theorem semilinearHeatBUCFixedPoint_restart_isFixedPt
    (T : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (a : Set.Icc (0 : ℝ) (T : ℝ)) :
    semilinearHeatBUCPicard (remainingDuhamelTime T a) (u a) N hN
        (restartDuhamelPath T u a) = restartDuhamelPath T u a := by
  apply ContinuousMap.ext
  intro τ
  rw [semilinearHeatBUCPicard_apply]
  exact (semilinearHeatBUCFixedPoint_restart_mild
    (E := E) (F := F) T u₀ N hN u hu a τ).symm

end Poincare
