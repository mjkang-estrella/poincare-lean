import Poincare.Global.SemilinearHeatBUCLocalContinuation

/-!
# Maximal semilinear `BUC` lifespans under local Lipschitz hypotheses

A solution on `[0,Tmax)` is represented by compatible mild paths on every
compact subinterval.  The bounded-ball local theory gives a uniform restart
time whenever the family has a global norm bound.  Restriction, restart, and
gluing then produce a strict compatible extension.  Consequently every
finite maximal lifespan satisfies the norm blow-up alternative.
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

/-- Compact terminal times strictly below a half-open lifespan. -/
abbrev SemilinearBUCCompactTime (Tmax : ℝ≥0) :=
  {T : ℝ≥0 // T < Tmax}

/-- A semilinear mild solution on `[0,Tmax)`, represented without assuming a
terminal trace. -/
structure SemilinearHeatBUCCompactFamily
    (Tmax : ℝ≥0) (N : BUC → BUC) (hN : Continuous N) (u₀ : BUC) where
  path : ∀ T : SemilinearBUCCompactTime Tmax, DuhamelPath (T : ℝ≥0) BUC
  mild : ∀ T : SemilinearBUCCompactTime Tmax,
    IsSemilinearHeatBUCMildPath (T : ℝ≥0) N hN u₀ (path T)
  compatible : ∀ (S T : SemilinearBUCCompactTime Tmax)
    (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)),
    restrictDuhamelPath (S : ℝ≥0) (T : ℝ≥0) hST (path T) = path S

/-- A strict extension agrees on every old compact interval. -/
def SemilinearHeatBUCCompactFamily.IsStrictExtension
    {Tmax Tmax' : ℝ≥0} {N : BUC → BUC} {hN : Continuous N} {u₀ : BUC}
    (fam : SemilinearHeatBUCCompactFamily Tmax N hN u₀)
    (fam' : SemilinearHeatBUCCompactFamily Tmax' N hN u₀) : Prop :=
  ∃ hTT : Tmax < Tmax',
    ∀ T : SemilinearBUCCompactTime Tmax,
      fam'.path
        (⟨(T : ℝ≥0), T.property.trans hTT⟩ :
          SemilinearBUCCompactTime Tmax') = fam.path T

/-- Maximality among compatible compact families. -/
def SemilinearHeatBUCCompactFamily.IsMaximal
    {Tmax : ℝ≥0} {N : BUC → BUC} {hN : Continuous N} {u₀ : BUC}
    (fam : SemilinearHeatBUCCompactFamily Tmax N hN u₀) : Prop :=
  ¬ ∃ (Tmax' : ℝ≥0)
      (fam' : SemilinearHeatBUCCompactFamily Tmax' N hN u₀),
    fam.IsStrictExtension fam'

/-- Uniform boundedness of every value represented by the family. -/
def SemilinearHeatBUCCompactFamily.IsNormBoundedBy
    {Tmax : ℝ≥0} {N : BUC → BUC} {hN : Continuous N} {u₀ : BUC}
    (fam : SemilinearHeatBUCCompactFamily Tmax N hN u₀)
    (K : ℝ≥0) : Prop :=
  ∀ (T : SemilinearBUCCompactTime Tmax)
    (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
    ‖fam.path T t‖ ≤ (K : ℝ)

/-- A pointwise norm bound is a zero-centered uniform path bound. -/
theorem semilinearDuhamelPath_mem_zero_closedBall_of_forall_norm_le
    (T K : ℝ≥0) (u : DuhamelPath T BUC)
    (hu : ∀ t : Set.Icc (0 : ℝ) (T : ℝ), ‖u t‖ ≤ (K : ℝ)) :
    u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC)) (K : ℝ) := by
  rw [Metric.mem_closedBall]
  apply (ContinuousMap.dist_le K.property).mpr
  intro t
  simpa [dist_eq_norm] using hu t

/-- Restriction preserves a zero-centered uniform path bound. -/
theorem restrictSemilinearDuhamelPath_mem_zero_closedBall
    (S T R : ℝ≥0) (hST : S ≤ T) (u : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) (R : ℝ)) :
    restrictDuhamelPath S T hST u ∈ Metric.closedBall
      (constantDuhamelPathGeneric S (0 : BUC)) (R : ℝ) := by
  rw [Metric.mem_closedBall] at hu ⊢
  apply (ContinuousMap.dist_le R.property).mpr
  intro t
  calc
    dist (restrictDuhamelPath S T hST u t)
        (constantDuhamelPathGeneric S (0 : BUC) t) =
        dist (u (restrictDuhamelTimeMap S T hST t))
          (constantDuhamelPathGeneric T (0 : BUC)
            (restrictDuhamelTimeMap S T hST t)) := by rfl
    _ ≤ dist u (constantDuhamelPathGeneric T (0 : BUC)) :=
      ContinuousMap.dist_apply_le_dist _
    _ ≤ (R : ℝ) := hu

/-- Local uniqueness for two mild paths in the same zero-centered ball. -/
theorem semilinearHeatBUCFixedPoints_eq_of_mem_uniform_zero_ball
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u v : DuhamelPath T BUC)
    (huBall : u ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + R : ℝ≥0) : ℝ))
    (hvBall : v ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + R : ℝ≥0) : ℝ))
    (hu : IsSemilinearHeatBUCMildPath T N data.continuous u₀ u)
    (hv : IsSemilinearHeatBUCMildPath T N data.continuous u₀ v)
    (hsmall : T * semilinearHeatBUCUniformBallLipschitzConstant data K R < 1) :
    u = v := by
  let q : ℝ≥0 := T * semilinearHeatBUCUniformBallLipschitzConstant data K R
  have hdist : dist u v ≤ (q : ℝ) * dist u v := by
    calc
      dist u v = dist
          (semilinearHeatBUCPicard T u₀ N data.continuous u)
          (semilinearHeatBUCPicard T u₀ N data.continuous v) := by
        rw [hu, hv]
      _ ≤ (q : ℝ) * dist u v := by
        apply (ContinuousMap.dist_le
          (mul_nonneg q.property dist_nonneg)).mpr
        intro t
        rw [dist_eq_norm, dist_eq_norm u v]
        exact norm_semilinearHeatBUCPicard_sub_le_uniform_zero_ball
          (E := E) (F := F) T K R N data u₀ u v huBall hvBall t
  have hq : (q : ℝ) < 1 := by exact_mod_cast hsmall
  have hzero : dist u v = 0 := by
    have hd0 := dist_nonneg (x := u) (y := v)
    nlinarith
  exact dist_eq_zero.mp hzero

/-- One mild path determines the family of all strict compact restrictions. -/
def semilinearHeatBUCCompactFamilyOfMildPath
    (H : ℝ≥0) (N : BUC → BUC) (hN : Continuous N) (u₀ : BUC)
    (w : DuhamelPath H BUC)
    (hw : IsSemilinearHeatBUCMildPath H N hN u₀ w) :
    SemilinearHeatBUCCompactFamily H N hN u₀ where
  path T := restrictDuhamelPath (T : ℝ≥0) H (le_of_lt T.property) w
  mild T := semilinearHeatBUCFixedPoint_restrict_isFixedPt
    (E := E) (F := F) (T : ℝ≥0) H (le_of_lt T.property) u₀ N hN w hw
  compatible S T hST := by
    exact (restrictDuhamelPath_trans (E := E) (F := F)
      (S : ℝ≥0) (T : ℝ≥0) H hST (le_of_lt T.property) w).trans (by rfl)

/-- A crossing mild path agreeing with an old family gives a strict
extension. -/
theorem exists_semilinear_strictExtension_of_crossing_mildPath
    (Tmax H : ℝ≥0) (hcross : Tmax < H)
    (N : BUC → BUC) (hN : Continuous N) (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N hN u₀)
    (w : DuhamelPath H BUC)
    (hw : IsSemilinearHeatBUCMildPath H N hN u₀ w)
    (hagrees : ∀ T : SemilinearBUCCompactTime Tmax,
      restrictDuhamelPath (T : ℝ≥0) H
        (le_of_lt (T.property.trans hcross)) w = fam.path T) :
    ∃ fam' : SemilinearHeatBUCCompactFamily H N hN u₀,
      fam.IsStrictExtension fam' := by
  let fam' := semilinearHeatBUCCompactFamilyOfMildPath
    (E := E) (F := F) H N hN u₀ w hw
  exact ⟨fam', hcross, hagrees⟩

/-- A bounded compatible family on a positive half-open lifespan has a
strict extension. -/
theorem exists_semilinear_strictExtension_of_isNormBoundedBy
    (Tmax K : ℝ≥0) (hTmax : 0 < Tmax)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hbound : fam.IsNormBoundedBy K) :
    ∃ (H : ℝ≥0)
      (fam' : SemilinearHeatBUCCompactFamily H N data.continuous u₀),
      fam.IsStrictExtension fam' := by
  let δ : ℝ≥0 := semilinearHeatBUCUniformLifespan data K
  have hδ : 0 < δ := semilinearHeatBUCUniformLifespan_pos data K
  let ε : ℝ := min ((Tmax : ℝ) / 2) ((δ : ℝ) / 2)
  have hTmaxR : 0 < (Tmax : ℝ) := by exact_mod_cast hTmax
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by positivity) (by positivity)
  have hεT : ε ≤ (Tmax : ℝ) := by
    calc
      ε ≤ (Tmax : ℝ) / 2 := min_le_left _ _
      _ ≤ (Tmax : ℝ) := by linarith
  have hεδ : ε < (δ : ℝ) := by
    calc
      ε ≤ (δ : ℝ) / 2 := min_le_right _ _
      _ < (δ : ℝ) := by linarith
  let t : ℝ≥0 := ⟨(Tmax : ℝ) - ε, sub_nonneg.mpr hεT⟩
  have htTmax : t < Tmax := by
    rw [← NNReal.coe_lt_coe]
    change (Tmax : ℝ) - ε < (Tmax : ℝ)
    linarith
  let τ : SemilinearBUCCompactTime Tmax := ⟨t, htTmax⟩
  let u : DuhamelPath t BUC := fam.path τ
  have hu : IsSemilinearHeatBUCMildPath t N data.continuous u₀ u := fam.mild τ
  let e : Set.Icc (0 : ℝ) (t : ℝ) := compactDuhamelEndTime t
  have hend : ‖u e‖ ≤ (K : ℝ) := hbound τ e
  rcases exists_semilinearHeatBUC_fixedPoint_uniform_local
      (E := E) (F := F) δ K 1 N data (u e) hend
      (semilinearHeatBUCUniformLifespan_mul_bound_le_one data K)
      (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K) with
    ⟨v, hvBall, hv, _hvuniq⟩
  have hv0 :
      v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) = u e := by
    have h := congrArg
      (fun w : DuhamelPath δ BUC ↦
        w (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ))) hv
    simpa using h.symm
  let H : ℝ≥0 := t + δ
  have hcross : Tmax < H := by
    rw [← NNReal.coe_lt_coe]
    change (Tmax : ℝ) < ((t + δ : ℝ≥0) : ℝ)
    change (Tmax : ℝ) < ((Tmax : ℝ) - ε) + (δ : ℝ)
    linarith
  let w : DuhamelPath H BUC := appendDuhamelPath t δ u v hv0
  have hw : IsSemilinearHeatBUCMildPath H N data.continuous u₀ w := by
    exact semilinearHeatBUCFixedPoint_append_isFixedPt
      (E := E) (F := F) t δ u₀ N data.continuous u v hu hv hv0
  have hagrees : ∀ Sidx : SemilinearBUCCompactTime Tmax,
      restrictDuhamelPath (Sidx : ℝ≥0) H
        (le_of_lt (Sidx.property.trans hcross)) w = fam.path Sidx := by
    intro Sidx
    by_cases hSt : (Sidx : ℝ≥0) ≤ t
    · calc
        restrictDuhamelPath (Sidx : ℝ≥0) H
            (le_of_lt (Sidx.property.trans hcross)) w =
            restrictDuhamelPath (Sidx : ℝ≥0) t hSt u := by
          exact restrictDuhamelPath_append_of_le_left
            (E := E) (F := F) (Sidx : ℝ≥0) t δ hSt u v hv0
        _ = fam.path Sidx := fam.compatible Sidx τ hSt
    · have htS : t ≤ (Sidx : ℝ≥0) := le_of_not_ge hSt
      let aS : Set.Icc (0 : ℝ) ((Sidx : ℝ≥0) : ℝ) :=
        ⟨(t : ℝ), ⟨t.property, by exact_mod_cast htS⟩⟩
      let R : ℝ≥0 := remainingDuhamelTime (Sidx : ℝ≥0) aS
      have hRδ : R ≤ δ := by
        rw [← NNReal.coe_le_coe]
        change ((Sidx : ℝ≥0) : ℝ) - (t : ℝ) ≤ (δ : ℝ)
        have hSlt : ((Sidx : ℝ≥0) : ℝ) < (Tmax : ℝ) := by
          exact_mod_cast Sidx.property
        have htcoe : (t : ℝ) = (Tmax : ℝ) - ε := rfl
        linarith
      let oldTail : DuhamelPath R BUC :=
        restartDuhamelPath (Sidx : ℝ≥0) (fam.path Sidx) aS
      let newTail : DuhamelPath R BUC := restrictDuhamelPath R δ hRδ v
      have hbase : fam.path Sidx aS = u e := by
        have hp := DFunLike.congr_fun (fam.compatible τ Sidx htS)
          (compactDuhamelEndTime t)
        simpa [u, τ, aS, e, compactDuhamelEndTime, restrictDuhamelPath_apply,
          restrictDuhamelTimeMap] using hp
      have hold : IsSemilinearHeatBUCMildPath R N data.continuous
          (fam.path Sidx aS) oldTail := by
        exact semilinearHeatBUCFixedPoint_restart_isFixedPt
          (E := E) (F := F) (Sidx : ℝ≥0) u₀ N data.continuous
          (fam.path Sidx) (fam.mild Sidx) aS
      have hnew : IsSemilinearHeatBUCMildPath R N data.continuous
          (fam.path Sidx aS) newTail := by
        have hr := semilinearHeatBUCFixedPoint_restrict_isFixedPt
          (E := E) (F := F) R δ hRδ (u e) N data.continuous v hv
        simpa [newTail, hbase] using hr
      have holdBall : oldTail ∈ Metric.closedBall
          (constantDuhamelPathGeneric R (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) := by
        apply Metric.closedBall_subset_closedBall
          (show (K : ℝ) ≤ ((K + 1 : ℝ≥0) : ℝ) by norm_num)
        apply semilinearDuhamelPath_mem_zero_closedBall_of_forall_norm_le
          R K oldTail
        intro r
        exact hbound Sidx (restartDuhamelTimeMap (Sidx : ℝ≥0) aS r)
      have hvZero : v ∈ Metric.closedBall
          (constantDuhamelPathGeneric δ (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
        mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
          (E := E) (F := F) δ K 1 (u e) hend hvBall
      have hnewBall : newTail ∈ Metric.closedBall
          (constantDuhamelPathGeneric R (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
        restrictSemilinearDuhamelPath_mem_zero_closedBall
          (E := E) (F := F) R δ (K + 1) hRδ v hvZero
      have hsmall :
          R * semilinearHeatBUCUniformBallLipschitzConstant data K 1 < 1 :=
        lt_of_le_of_lt
          (by gcongr)
          (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K)
      have htails : newTail = oldTail :=
        semilinearHeatBUCFixedPoints_eq_of_mem_uniform_zero_ball
          (E := E) (F := F) R K 1 N data (fam.path Sidx aS)
          newTail oldTail hnewBall holdBall hnew hold hsmall
      apply ContinuousMap.ext
      intro q
      rw [restrictDuhamelPath_apply]
      change w (restrictDuhamelTimeMap (Sidx : ℝ≥0) H
        (le_of_lt (Sidx.property.trans hcross)) q) = fam.path Sidx q
      by_cases hqt : (q : ℝ) ≤ (t : ℝ)
      · rw [show w = appendDuhamelPath t δ u v hv0 by rfl]
        rw [appendDuhamelPath_apply_of_le t δ u v hv0 _ hqt]
        change u (Set.projIcc 0 (t : ℝ) t.property (q : ℝ)) = fam.path Sidx q
        have hp := DFunLike.congr_fun (fam.compatible τ Sidx htS)
          (⟨(q : ℝ), ⟨q.property.1, hqt⟩⟩ : Set.Icc (0 : ℝ) (t : ℝ))
        have hproj :
            Set.projIcc 0 (t : ℝ) t.property (q : ℝ) =
              (⟨(q : ℝ), ⟨q.property.1, hqt⟩⟩ :
                Set.Icc (0 : ℝ) (t : ℝ)) := by
          apply Subtype.ext
          simp [Set.coe_projIcc, max_eq_right q.property.1, min_eq_right hqt]
        rw [hproj]
        simpa [u, τ, restrictDuhamelPath_apply, restrictDuhamelTimeMap] using
          hp.symm
      · have htq : (t : ℝ) ≤ (q : ℝ) := le_of_not_ge hqt
        rw [show w = appendDuhamelPath t δ u v hv0 by rfl]
        rw [appendDuhamelPath_apply_of_ge t δ u v hv0 _ htq]
        change v (Set.projIcc 0 (δ : ℝ) δ.property
          ((q : ℝ) - (t : ℝ))) = fam.path Sidx q
        let r : Set.Icc (0 : ℝ) (R : ℝ) :=
          ⟨(q : ℝ) - (t : ℝ), ⟨sub_nonneg.mpr htq, by
            change (q : ℝ) - (t : ℝ) ≤
              ((Sidx : ℝ≥0) : ℝ) - (t : ℝ)
            linarith [q.property.2]⟩⟩
        have hr := DFunLike.congr_fun htails r
        change v (restrictDuhamelTimeMap R δ hRδ r) =
          fam.path Sidx (restartDuhamelTimeMap (Sidx : ℝ≥0) aS r) at hr
        have hproj :
            Set.projIcc 0 (δ : ℝ) δ.property ((q : ℝ) - (t : ℝ)) =
              restrictDuhamelTimeMap R δ hRδ r := by
          apply Subtype.ext
          change max 0 (min (δ : ℝ) ((q : ℝ) - (t : ℝ))) =
            (q : ℝ) - (t : ℝ)
          rw [min_eq_right, max_eq_right (sub_nonneg.mpr htq)]
          exact (r.property.2.trans (by exact_mod_cast hRδ))
        have hrestart :
            restartDuhamelTimeMap (Sidx : ℝ≥0) aS r = q := by
          apply Subtype.ext
          change (t : ℝ) + ((q : ℝ) - (t : ℝ)) = (q : ℝ)
          ring
        rw [hproj]
        rw [hrestart] at hr
        exact hr
  rcases exists_semilinear_strictExtension_of_crossing_mildPath
      (E := E) (F := F) Tmax H hcross N data.continuous u₀ fam w hw hagrees with
    ⟨fam', hext⟩
  exact ⟨H, fam', hext⟩

/-- A positive-lifespan bounded family is not maximal. -/
theorem not_semilinear_isMaximal_of_isNormBoundedBy
    (Tmax K : ℝ≥0) (hTmax : 0 < Tmax)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hbound : fam.IsNormBoundedBy K) :
    ¬ fam.IsMaximal := by
  intro hmax
  rcases exists_semilinear_strictExtension_of_isNormBoundedBy
      (E := E) (F := F) Tmax K hTmax N data u₀ fam hbound with
    ⟨H, fam', hext⟩
  exact hmax ⟨H, fam', hext⟩

/-- The zero lifespan is not maximal, by local existence at the initial
datum. -/
theorem not_semilinear_isMaximal_zero
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily 0 N data.continuous u₀) :
    ¬ fam.IsMaximal := by
  let K : ℝ≥0 := ⟨‖u₀‖, norm_nonneg u₀⟩
  let u₀K : SemilinearBUCBoundedData (E := E) (F := F) K := ⟨u₀, le_rfl⟩
  let H : ℝ≥0 := semilinearHeatBUCUniformLifespan data K
  let w : DuhamelPath H BUC :=
    semilinearHeatBUCUniformLocalSolution K N data u₀K
  have hH : 0 < H := semilinearHeatBUCUniformLifespan_pos data K
  have hw : IsSemilinearHeatBUCMildPath H N data.continuous u₀ w := by
    exact semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀K
  have hagrees : ∀ T : SemilinearBUCCompactTime 0,
      restrictDuhamelPath (T : ℝ≥0) H
        (le_of_lt (T.property.trans hH)) w = fam.path T := by
    intro T
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ (T : ℝ≥0) from bot_le)
      T.property).elim
  intro hmax
  rcases exists_semilinear_strictExtension_of_crossing_mildPath
      (E := E) (F := F) 0 H hH N data.continuous u₀ fam w hw hagrees with
    ⟨fam', hext⟩
  exact hmax ⟨H, fam', hext⟩

/-- Every maximal compatible family has positive lifespan. -/
theorem SemilinearHeatBUCCompactFamily.maximal_lifespan_pos
    (Tmax : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hmax : fam.IsMaximal) :
    0 < Tmax := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  subst Tmax
  exact (not_semilinear_isMaximal_zero
    (E := E) (F := F) N data u₀ fam) hmax

/-- **Finite maximal-time norm blow-up alternative.** Every proposed norm
bound is exceeded before a positive maximal terminal time. -/
theorem semilinearHeatBUC_maximalTime_norm_unbounded
    (Tmax : ℝ≥0) (hTmax : 0 < Tmax)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : SemilinearBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ := by
  intro K
  have hnot : ¬ fam.IsNormBoundedBy K := by
    intro hbound
    exact (not_semilinear_isMaximal_of_isNormBoundedBy
      (E := E) (F := F) Tmax K hTmax N data u₀ fam hbound) hmax
  simpa only [SemilinearHeatBUCCompactFamily.IsNormBoundedBy,
    not_forall, not_le] using hnot

/-- Maximality alone implies both positivity and norm blow-up. -/
theorem semilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (Tmax : ℝ≥0)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : SemilinearBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ := by
  exact semilinearHeatBUC_maximalTime_norm_unbounded
    (E := E) (F := F) Tmax
    (SemilinearHeatBUCCompactFamily.maximal_lifespan_pos
      (E := E) (F := F) Tmax N data u₀ fam hmax)
    N data u₀ fam hmax

/-- The blow-up is a genuine terminal-time phenomenon: after every compact
time `S < Tmax`, every proposed norm bound is exceeded at a later time. -/
theorem semilinearHeatBUC_maximalTime_norm_unbounded_after
    (Tmax : ℝ≥0) (hTmax : 0 < Tmax)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hmax : fam.IsMaximal)
    (S : SemilinearBUCCompactTime Tmax) (K : ℝ≥0) :
    ∃ (T : SemilinearBUCCompactTime Tmax)
      (_hST : (S : ℝ≥0) ≤ (T : ℝ≥0))
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      ((S : ℝ≥0) : ℝ) < (t : ℝ) ∧ (K : ℝ) < ‖fam.path T t‖ := by
  let K' : ℝ≥0 := max K ‖fam.path S‖₊
  rcases semilinearHeatBUC_maximalTime_norm_unbounded
      (E := E) (F := F) Tmax hTmax N data u₀ fam hmax K' with
    ⟨T, t, htLarge⟩
  have hprefix : ‖fam.path S‖ ≤ (K' : ℝ) := by
    change ‖fam.path S‖ ≤ ((max K ‖fam.path S‖₊ : ℝ≥0) : ℝ)
    exact_mod_cast le_max_right K ‖fam.path S‖₊
  have hnotTS : ¬ (T : ℝ≥0) ≤ (S : ℝ≥0) := by
    intro hTS
    let tS : Set.Icc (0 : ℝ) ((S : ℝ≥0) : ℝ) :=
      ⟨(t : ℝ), ⟨t.property.1, t.property.2.trans (by exact_mod_cast hTS)⟩⟩
    have hp := DFunLike.congr_fun (fam.compatible T S hTS) t
    have hmap :
        restrictDuhamelTimeMap (T : ℝ≥0) (S : ℝ≥0) hTS t = tS := by
      apply Subtype.ext
      rfl
    have hval : fam.path T t = fam.path S tS := by
      simpa [restrictDuhamelPath_apply, hmap] using hp.symm
    have hpathNorm : ‖fam.path T t‖ ≤ ‖fam.path S‖ := by
      rw [hval]
      exact ContinuousMap.norm_coe_le_norm _ _
    linarith
  have hST : (S : ℝ≥0) ≤ (T : ℝ≥0) := le_of_not_ge hnotTS
  have hSt : ((S : ℝ≥0) : ℝ) < (t : ℝ) := by
    apply lt_of_not_ge
    intro htS
    let tS : Set.Icc (0 : ℝ) ((S : ℝ≥0) : ℝ) :=
      ⟨(t : ℝ), ⟨t.property.1, htS⟩⟩
    have hp := DFunLike.congr_fun (fam.compatible S T hST) tS
    have hmap :
        restrictDuhamelTimeMap (S : ℝ≥0) (T : ℝ≥0) hST tS = t := by
      apply Subtype.ext
      rfl
    have hval : fam.path T t = fam.path S tS := by
      simpa [restrictDuhamelPath_apply, hmap] using hp
    have hpathNorm : ‖fam.path T t‖ ≤ ‖fam.path S‖ := by
      rw [hval]
      exact ContinuousMap.norm_coe_le_norm _ _
    linarith
  have hKK' : (K : ℝ) ≤ (K' : ℝ) := by
    exact_mod_cast le_max_left K ‖fam.path S‖₊
  exact ⟨T, hST, t, hSt, hKK'.trans_lt htLarge⟩

/-- Assumption-free terminal form: maximality supplies positivity and then
forces every norm threshold to be crossed after every compact time. -/
theorem semilinearHeatBUC_maximalTime_norm_unbounded_after_of_maximal
    (Tmax : ℝ≥0)
    (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC)
    (fam : SemilinearHeatBUCCompactFamily Tmax N data.continuous u₀)
    (hmax : fam.IsMaximal)
    (S : SemilinearBUCCompactTime Tmax) (K : ℝ≥0) :
    ∃ (T : SemilinearBUCCompactTime Tmax)
      (_hST : (S : ℝ≥0) ≤ (T : ℝ≥0))
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      ((S : ℝ≥0) : ℝ) < (t : ℝ) ∧ (K : ℝ) < ‖fam.path T t‖ := by
  exact semilinearHeatBUC_maximalTime_norm_unbounded_after
    (E := E) (F := F) Tmax
    (SemilinearHeatBUCCompactFamily.maximal_lifespan_pos
      (E := E) (F := F) Tmax N data u₀ fam hmax)
    N data u₀ fam hmax S K

end Poincare
