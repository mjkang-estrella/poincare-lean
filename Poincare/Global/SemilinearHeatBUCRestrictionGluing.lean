import Poincare.Global.SemilinearHeatBUCRestart

/-!
# Restriction and gluing of semilinear heat mild paths on `BUC`

This module supplies the compact-interval bookkeeping needed for half-open
lifespan arguments.  Mild fixed points restrict to shorter intervals, and two
mild fixed points with matching endpoint/initial values concatenate to a mild
fixed point on the sum interval.
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

/-- Inclusion of a shorter compact time interval into a longer one. -/
def restrictDuhamelTimeMap (S T : ℝ≥0) (hST : S ≤ T) :
    C(Set.Icc (0 : ℝ) (S : ℝ), Set.Icc (0 : ℝ) (T : ℝ)) where
  toFun t := ⟨(t : ℝ), ⟨t.property.1,
    t.property.2.trans (by exact_mod_cast hST)⟩⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp]
theorem restrictDuhamelTimeMap_coe
    (S T : ℝ≥0) (hST : S ≤ T) (t : Set.Icc (0 : ℝ) (S : ℝ)) :
    ((restrictDuhamelTimeMap S T hST t : Set.Icc (0 : ℝ) (T : ℝ)) : ℝ) =
      (t : ℝ) :=
  rfl

/-- Restriction of a Duhamel path to a shorter compact interval. -/
def restrictDuhamelPath (S T : ℝ≥0) (hST : S ≤ T)
    (u : DuhamelPath T BUC) : DuhamelPath S BUC :=
  u.comp (restrictDuhamelTimeMap S T hST)

@[simp]
theorem restrictDuhamelPath_apply
    (S T : ℝ≥0) (hST : S ≤ T) (u : DuhamelPath T BUC)
    (t : Set.Icc (0 : ℝ) (S : ℝ)) :
    restrictDuhamelPath S T hST u t = u (restrictDuhamelTimeMap S T hST t) :=
  rfl

@[simp]
theorem restrictDuhamelPath_self (T : ℝ≥0) (u : DuhamelPath T BUC) :
    restrictDuhamelPath T T le_rfl u = u := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Restricting in two stages agrees with direct restriction. -/
theorem restrictDuhamelPath_trans
    (R S T : ℝ≥0) (hRS : R ≤ S) (hST : S ≤ T)
    (u : DuhamelPath T BUC) :
    restrictDuhamelPath R S hRS (restrictDuhamelPath S T hST u) =
      restrictDuhamelPath R T (hRS.trans hST) u := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Fixed points of the corrected semilinear heat map restrict to shorter
compact intervals. -/
theorem semilinearHeatBUCFixedPoint_restrict_isFixedPt
    (S T : ℝ≥0) (hST : S ≤ T)
    (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u) :
    semilinearHeatBUCPicard S u₀ N hN (restrictDuhamelPath S T hST u) =
      restrictDuhamelPath S T hST u := by
  apply ContinuousMap.ext
  intro t
  rw [semilinearHeatBUCPicard_apply]
  have hut :
      semilinearHeatBUCPicard T u₀ N hN u
          (restrictDuhamelTimeMap S T hST t) =
        u (restrictDuhamelTimeMap S T hST t) := by
    exact DFunLike.congr_fun hu (restrictDuhamelTimeMap S T hST t)
  rw [restrictDuhamelPath_apply]
  rw [← hut]
  rw [semilinearHeatBUCPicard_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by
    simpa [min_eq_left t.property.1] using hs.1
  have hst : s ≤ (t : ℝ) := by
    simpa [max_eq_right t.property.1] using hs.2
  have hsS : s ≤ (S : ℝ) := hst.trans t.property.2
  have hsT : s ≤ (T : ℝ) := hsS.trans (by exact_mod_cast hST)
  have hprojS :
      Set.projIcc 0 (S : ℝ) S.property s =
        (⟨s, ⟨hs0, hsS⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) := by
    apply Subtype.ext
    simp [Set.coe_projIcc, max_eq_right hs0, min_eq_right hsS]
  have hprojT :
      Set.projIcc 0 (T : ℝ) T.property s =
        (⟨s, ⟨hs0, hsT⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) := by
    apply Subtype.ext
    simp [Set.coe_projIcc, max_eq_right hs0, min_eq_right hsT]
  change
    (vectorHeatSemigroupBUCExtended ((t : ℝ) - s))
        (N ((restrictDuhamelPath S T hST u)
          (Set.projIcc 0 (S : ℝ) S.property s))) =
      (vectorHeatSemigroupBUCExtended ((t : ℝ) - s))
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))
  rw [hprojS, hprojT]
  rfl

/-- The endpoint of the left interval, viewed in a sum interval. -/
def sumDuhamelJoinTime (T S : ℝ≥0) :
    Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ) :=
  ⟨(T : ℝ), ⟨T.property, by norm_num⟩⟩

/-- The right endpoint of a compact Duhamel interval.  This local name avoids
coupling the general restriction/gluing layer to the quadratic continuation
module. -/
def compactDuhamelEndTime (T : ℝ≥0) : Set.Icc (0 : ℝ) (T : ℝ) :=
  ⟨(T : ℝ), ⟨T.property, le_rfl⟩⟩

@[simp]
theorem compactDuhamelEndTime_coe (T : ℝ≥0) :
    ((compactDuhamelEndTime T : Set.Icc (0 : ℝ) (T : ℝ)) : ℝ) = (T : ℝ) :=
  rfl

/-- Concatenate two continuous paths whose endpoint and initial value match. -/
def appendDuhamelPath
    (T S : ℝ≥0) (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T)) :
    DuhamelPath (T + S) BUC where
  toFun t := if (t : ℝ) ≤ (T : ℝ) then
      u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ))
    else
      v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ)))
  continuous_toFun := by
    let f : Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ) → BUC := fun t ↦
      u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ))
    let g : Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ) → BUC := fun t ↦
      v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ)))
    have hf : Continuous f := u.continuous.comp
      ((continuous_projIcc (h := T.property)).comp continuous_subtype_val)
    have hg : Continuous g := v.continuous.comp
      ((continuous_projIcc (h := S.property)).comp
        (continuous_subtype_val.sub continuous_const))
    apply hf.if
    · intro t ht
      have ht' : (t : ℝ) ∈ frontier (Set.Iic (T : ℝ)) :=
        continuous_subtype_val.frontier_preimage_subset _ ht
      have hteq : (t : ℝ) = (T : ℝ) :=
        Set.mem_singleton_iff.mp (frontier_Iic_subset _ ht')
      simpa [f, g, hteq, compactDuhamelEndTime] using hjoin.symm
    · exact hg

@[simp]
theorem appendDuhamelPath_apply_of_le
    (T S : ℝ≥0) (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T))
    (t : Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ)) (ht : (t : ℝ) ≤ (T : ℝ)) :
    appendDuhamelPath T S u v hjoin t =
      u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ)) := by
  change (if (t : ℝ) ≤ (T : ℝ) then
      u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ))
    else v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ)))) = _
  rw [if_pos ht]

@[simp]
theorem appendDuhamelPath_apply_of_ge
    (T S : ℝ≥0) (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T))
    (t : Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ)) (ht : (T : ℝ) ≤ (t : ℝ)) :
    appendDuhamelPath T S u v hjoin t =
      v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ))) := by
  rcases ht.eq_or_lt with h | h
  · have h' : (t : ℝ) = (T : ℝ) := h.symm
    change (if (t : ℝ) ≤ (T : ℝ) then
        u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ))
      else v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ)))) = _
    rw [if_pos (by simpa [h'])]
    simpa [h', compactDuhamelEndTime] using hjoin.symm
  · change (if (t : ℝ) ≤ (T : ℝ) then
        u (Set.projIcc 0 (T : ℝ) T.property (t : ℝ))
      else v (Set.projIcc 0 (S : ℝ) S.property ((t : ℝ) - (T : ℝ)))) = _
    rw [if_neg (not_le_of_gt h)]

/-- On the first integration interval, projection into the concatenated path
recovers projection into the left path. -/
theorem appendDuhamelPath_proj_left
    (T S : ℝ≥0) (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T))
    (s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ (T : ℝ)) :
    appendDuhamelPath T S u v hjoin
        (Set.projIcc 0 ((T + S : ℝ≥0) : ℝ) (T + S).property s) =
      u (Set.projIcc 0 (T : ℝ) T.property s) := by
  have hsSum : s ≤ ((T + S : ℝ≥0) : ℝ) := by
    exact hsT.trans (by norm_num)
  have hprojSum :
      Set.projIcc 0 ((T + S : ℝ≥0) : ℝ) (T + S).property s =
        (⟨s, ⟨hs0, hsSum⟩⟩ :
          Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ)) := by
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by simpa using hsSum), max_eq_right hs0]
  rw [hprojSum, appendDuhamelPath_apply_of_le T S u v hjoin _ hsT]

/-- On the translated second integration interval, projection into the
concatenated path recovers projection into the right path. -/
theorem appendDuhamelPath_proj_right
    (T S : ℝ≥0) (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T))
    (r : ℝ) (hr0 : 0 ≤ r) (hrS : r ≤ (S : ℝ)) :
    appendDuhamelPath T S u v hjoin
        (Set.projIcc 0 ((T + S : ℝ≥0) : ℝ) (T + S).property
          ((T : ℝ) + r)) =
      v (Set.projIcc 0 (S : ℝ) S.property r) := by
  have hTr0 : 0 ≤ (T : ℝ) + r := add_nonneg T.property hr0
  have hTrSum : (T : ℝ) + r ≤ ((T + S : ℝ≥0) : ℝ) := by
    change (T : ℝ) + r ≤ (T : ℝ) + (S : ℝ)
    linarith
  have hprojSum :
      Set.projIcc 0 ((T + S : ℝ≥0) : ℝ) (T + S).property
          ((T : ℝ) + r) =
        (⟨(T : ℝ) + r, ⟨hTr0, hTrSum⟩⟩ :
          Set.Icc (0 : ℝ) ((T + S : ℝ≥0) : ℝ)) := by
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by simpa using hTrSum), max_eq_right hTr0]
  rw [hprojSum,
    appendDuhamelPath_apply_of_ge T S u v hjoin _ (le_add_of_nonneg_right hr0)]
  congr 3
  ring

/-- Restricting a concatenated path to a horizon contained in the left piece
is exactly restriction of that left piece. -/
theorem restrictDuhamelPath_append_of_le_left
    (R T S : ℝ≥0) (hRT : R ≤ T)
    (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T)) :
    restrictDuhamelPath R (T + S) (hRT.trans (by norm_num))
        (appendDuhamelPath T S u v hjoin) =
      restrictDuhamelPath R T hRT u := by
  apply ContinuousMap.ext
  intro r
  rw [restrictDuhamelPath_apply, restrictDuhamelPath_apply]
  rw [appendDuhamelPath_apply_of_le T S u v hjoin _]
  · congr 2
    apply Subtype.ext
    change max 0 (min (T : ℝ) (r : ℝ)) = (r : ℝ)
    rw [min_eq_right (r.property.2.trans (by exact_mod_cast hRT)),
      max_eq_right r.property.1]
  · exact r.property.2.trans (by exact_mod_cast hRT)

/-- Two semilinear mild fixed points concatenate to a mild fixed point when
the second datum is the endpoint of the first.  This is the converse of the
restart theorem and is the analytic gluing statement used by lifespan
extensions. -/
theorem semilinearHeatBUCFixedPoint_append_isFixedPt
    (T S : ℝ≥0) (u₀ : BUC) (N : BUC → BUC) (hN : Continuous N)
    (u : DuhamelPath T BUC) (v : DuhamelPath S BUC)
    (hu : semilinearHeatBUCPicard T u₀ N hN u = u)
    (hv : semilinearHeatBUCPicard S (u (compactDuhamelEndTime T)) N hN v = v)
    (hjoin : v (⟨0, ⟨le_rfl, S.property⟩⟩ : Set.Icc (0 : ℝ) (S : ℝ)) =
      u (compactDuhamelEndTime T)) :
    semilinearHeatBUCPicard (T + S) u₀ N hN
        (appendDuhamelPath T S u v hjoin) =
      appendDuhamelPath T S u v hjoin := by
  let w : DuhamelPath (T + S) BUC := appendDuhamelPath T S u v hjoin
  let G : ℝ → BUC := fun s ↦
    N (w (Set.projIcc 0 ((T + S : ℝ≥0) : ℝ) (T + S).property s))
  have hG : Continuous G :=
    hN.comp (w.continuous.comp (continuous_projIcc (h := (T + S).property)))
  have hmildU : ∀ q : Set.Icc (0 : ℝ) (T : ℝ),
      u q = vectorHeatSemigroupBUCExtended (E := E) (F := F) (q : ℝ) u₀ +
        ∫ s : ℝ in (0 : ℝ)..(q : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((q : ℝ) - s)
            (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
    intro q
    have hq := DFunLike.congr_fun hu q
    simpa using hq.symm
  have hmildV : ∀ q : Set.Icc (0 : ℝ) (S : ℝ),
      v q = vectorHeatSemigroupBUCExtended (E := E) (F := F) (q : ℝ)
          (u (compactDuhamelEndTime T)) +
        ∫ r : ℝ in (0 : ℝ)..(q : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((q : ℝ) - r)
            (N (v (Set.projIcc 0 (S : ℝ) S.property r))) := by
    intro q
    have hq := DFunLike.congr_fun hv q
    simpa using hq.symm
  change semilinearHeatBUCPicard (T + S) u₀ N hN w = w
  apply ContinuousMap.ext
  intro t
  rw [semilinearHeatBUCPicard_apply]
  change vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) u₀ +
      (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (G s)) = w t
  rcases le_total (t : ℝ) (T : ℝ) with ht | ht
  · let q : Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨(t : ℝ), ⟨t.property.1, ht⟩⟩
    have hforce :
        (∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (G s)) =
          ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
            vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
              (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by
        simpa [min_eq_left t.property.1] using hs.1
      have hst : s ≤ (t : ℝ) := by
        simpa [max_eq_right t.property.1] using hs.2
      have hsT : s ≤ (T : ℝ) := hst.trans ht
      simp only [G]
      rw [show w = appendDuhamelPath T S u v hjoin by rfl]
      rw [appendDuhamelPath_proj_left T S u v hjoin s hs0 hsT]
    have hwq : w t = u q := by
      rw [show w = appendDuhamelPath T S u v hjoin by rfl]
      rw [appendDuhamelPath_apply_of_le T S u v hjoin t ht]
      congr 2
      apply Subtype.ext
      simp [q, Set.coe_projIcc, max_eq_right t.property.1, min_eq_right ht]
    rw [hforce]
    exact (hmildU q).symm.trans hwq.symm
  · let b : ℝ := (t : ℝ) - (T : ℝ)
    have hb0 : 0 ≤ b := sub_nonneg.mpr ht
    have hbS : b ≤ (S : ℝ) := by
      dsimp [b]
      have httop := t.property.2
      norm_num at httop ⊢
      linarith
    let q : Set.Icc (0 : ℝ) (S : ℝ) := ⟨b, ⟨hb0, hbS⟩⟩
    have htb : (t : ℝ) = (T : ℝ) + b := by
      dsimp [b]
      linarith
    have hwq : w t = v q := by
      rw [show w = appendDuhamelPath T S u v hjoin by rfl]
      rw [appendDuhamelPath_apply_of_ge T S u v hjoin t ht]
      congr 2
      apply Subtype.ext
      simp [q, b, Set.coe_projIcc, max_eq_right hb0, min_eq_right hbS]
    have hleft :
        (∫ s : ℝ in (0 : ℝ)..(T : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((T : ℝ) - s)
            (G s)) =
          ∫ s : ℝ in (0 : ℝ)..(T : ℝ),
            vectorHeatSemigroupBUCExtended (E := E) (F := F) ((T : ℝ) - s)
              (N (u (Set.projIcc 0 (T : ℝ) T.property s))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by
        simpa [min_eq_left T.property] using hs.1
      have hsT : s ≤ (T : ℝ) := by
        simpa [max_eq_right T.property] using hs.2
      simp only [G]
      rw [show w = appendDuhamelPath T S u v hjoin by rfl]
      rw [appendDuhamelPath_proj_left T S u v hjoin s hs0 hsT]
    have hright :
        (∫ r : ℝ in (0 : ℝ)..b,
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (b - r)
            (G ((T : ℝ) + r))) =
          ∫ r : ℝ in (0 : ℝ)..b,
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (b - r)
              (N (v (Set.projIcc 0 (S : ℝ) S.property r))) := by
      apply intervalIntegral.integral_congr
      intro r hr
      have hr0 : 0 ≤ r := by
        simpa [min_eq_left hb0] using hr.1
      have hrb : r ≤ b := by
        simpa [max_eq_right hb0] using hr.2
      have hrS : r ≤ (S : ℝ) := hrb.trans hbS
      simp only [G]
      rw [show w = appendDuhamelPath T S u v hjoin by rfl]
      rw [appendDuhamelPath_proj_right T S u v hjoin r hr0 hrS]
    have hrestart := vectorHeatSemigroupBUCExtended_restart_integral
      (E := E) (F := F) G hG (T : ℝ) b T.property hb0
    have hmildU' :
        u (compactDuhamelEndTime T) =
          vectorHeatSemigroupBUCExtended (E := E) (F := F) (T : ℝ) u₀ +
            ∫ s : ℝ in (0 : ℝ)..(T : ℝ),
              vectorHeatSemigroupBUCExtended (E := E) (F := F) ((T : ℝ) - s)
                (G s) := by
      rw [hleft]
      exact hmildU (compactDuhamelEndTime T)
    have hmildV' :
        v q = vectorHeatSemigroupBUCExtended (E := E) (F := F) b
            (u (compactDuhamelEndTime T)) +
          ∫ r : ℝ in (0 : ℝ)..b,
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (b - r)
              (G ((T : ℝ) + r)) := by
      rw [hright]
      exact hmildV q
    rw [htb]
    rw [← hrestart]
    have hheat :
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((T : ℝ) + b) u₀ =
          vectorHeatSemigroupBUCExtended (E := E) (F := F) b
            (vectorHeatSemigroupBUCExtended (E := E) (F := F) (T : ℝ) u₀) := by
      calc
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((T : ℝ) + b) u₀ =
            vectorHeatSemigroupBUCExtended (E := E) (F := F) (b + (T : ℝ)) u₀ := by
          congr 2
          ring
        _ = vectorHeatSemigroupBUCExtended (E := E) (F := F) b
              (vectorHeatSemigroupBUCExtended (E := E) (F := F) (T : ℝ) u₀) :=
          (vectorHeatSemigroupBUCExtended_add_apply
            (E := E) (F := F) hb0 T.property u₀).symm
    rw [hheat, ← add_assoc]
    rw [← map_add]
    rw [← hmildU']
    rw [← hmildV']
    exact hwq.symm

end Poincare
