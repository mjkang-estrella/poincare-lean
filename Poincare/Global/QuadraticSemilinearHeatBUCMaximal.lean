import Poincare.Global.SemilinearHeatBUCRestrictionGluing
import Poincare.Global.QuadraticSemilinearHeatBUCContinuation

/-!
# Compatible compact families and maximal quadratic `BUC` lifespans

A solution on a half-open interval `[0,Tmax)` is represented without an
unjustified terminal trace: it is a compatible family of mild paths on every
compact interval `[0,T]` with `T < Tmax`.  This module packages strict
extensions of such families and proves the finite-maximal-time norm blow-up
alternative from the uniform bounded-data continuation theorem.
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
abbrev QuadraticBUCCompactTime (Tmax : ℝ≥0) :=
  {T : ℝ≥0 // T < Tmax}

/-- A quadratic mild solution on `[0,Tmax)` represented by all of its
compatible compact restrictions. -/
structure QuadraticSemilinearHeatBUCCompactFamily
    (Tmax : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (u₀ : BUC) where
  path : ∀ T : QuadraticBUCCompactTime Tmax, DuhamelPath (T : ℝ≥0) BUC
  mild : ∀ T : QuadraticBUCCompactTime Tmax,
    IsQuadraticSemilinearHeatBUCMildPath (T : ℝ≥0) B u₀ (path T)
  compatible : ∀ (S T : QuadraticBUCCompactTime Tmax)
    (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)),
    restrictDuhamelPath (S : ℝ≥0) (T : ℝ≥0) hST (path T) = path S

/-- A strict extension agrees with the old family on every old compact
interval, not merely at one selected restart time. -/
def QuadraticSemilinearHeatBUCCompactFamily.IsStrictExtension
    {Tmax Tmax' : ℝ≥0} {B : BUC →L[ℝ] BUC →L[ℝ] BUC} {u₀ : BUC}
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (fam' : QuadraticSemilinearHeatBUCCompactFamily Tmax' B u₀) : Prop :=
  ∃ hTT : Tmax < Tmax',
    ∀ T : QuadraticBUCCompactTime Tmax,
      fam'.path
        (⟨(T : ℝ≥0), T.property.trans hTT⟩ :
          QuadraticBUCCompactTime Tmax') = fam.path T

/-- A compatible compact family is maximal if it has no strict compatible
extension to a larger half-open lifespan. -/
def QuadraticSemilinearHeatBUCCompactFamily.IsMaximal
    {Tmax : ℝ≥0} {B : BUC →L[ℝ] BUC →L[ℝ] BUC} {u₀ : BUC}
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀) : Prop :=
  ¬ ∃ (Tmax' : ℝ≥0)
      (fam' : QuadraticSemilinearHeatBUCCompactFamily Tmax' B u₀),
    fam.IsStrictExtension fam'

/-- Uniform boundedness of all values on all compact subintervals. -/
def QuadraticSemilinearHeatBUCCompactFamily.IsNormBoundedBy
    {Tmax : ℝ≥0} {B : BUC →L[ℝ] BUC →L[ℝ] BUC} {u₀ : BUC}
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (K : ℝ≥0) : Prop :=
  ∀ (T : QuadraticBUCCompactTime Tmax)
    (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
    ‖fam.path T t‖ ≤ (K : ℝ)

/-- A pointwise `K`-bound puts the entire compact path in the zero-centered
closed path ball of radius `K`. -/
theorem DuhamelPath_mem_zero_closedBall_of_forall_norm_le
    (T K : ℝ≥0) (u : DuhamelPath T BUC)
    (hu : ∀ t : Set.Icc (0 : ℝ) (T : ℝ), ‖u t‖ ≤ (K : ℝ)) :
    u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC)) (K : ℝ) := by
  rw [Metric.mem_closedBall]
  apply (ContinuousMap.dist_le K.property).mpr
  intro t
  simpa [dist_eq_norm] using hu t

/-- Restriction preserves membership in a zero-centered uniform path ball. -/
theorem restrictDuhamelPath_mem_zero_closedBall
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

/-- Uniqueness on a common zero-centered ball follows directly from the
localized quadratic contraction estimate. -/
theorem quadraticSemilinearHeatBUCFixedPoints_eq_of_mem_uniform_zero_ball
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u v : DuhamelPath T BUC)
    (huBall : u ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + R : ℝ≥0) : ℝ))
    (hvBall : v ∈ Metric.closedBall
      (constantDuhamelPathGeneric T (0 : BUC)) ((K + R : ℝ≥0) : ℝ))
    (hu : IsQuadraticSemilinearHeatBUCMildPath T B u₀ u)
    (hv : IsQuadraticSemilinearHeatBUCMildPath T B u₀ v)
    (hsmall : T * quadraticBUCUniformBallLipschitzConstant β K R < 1) :
    u = v := by
  let q : ℝ≥0 := T * quadraticBUCUniformBallLipschitzConstant β K R
  have hdist : dist u v ≤ (q : ℝ) * dist u v := by
    calc
      dist u v = dist
          (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) u)
          (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) v) := by rw [hu, hv]
      _ ≤ (q : ℝ) * dist u v := by
        apply (ContinuousMap.dist_le
          (mul_nonneg q.property dist_nonneg)).mpr
        intro t
        rw [dist_eq_norm, dist_eq_norm u v]
        exact norm_semilinearHeatBUCPicard_quadratic_sub_le_uniform_zero_ball
          (E := E) (F := F) T K R B β hB u₀ u v huBall hvBall t
  have hq : (q : ℝ) < 1 := by exact_mod_cast hsmall
  have hzero : dist u v = 0 := by
    have hd0 := dist_nonneg (x := u) (y := v)
    nlinarith
  exact dist_eq_zero.mp hzero

/-- A single mild path canonically determines the compatible family of all
of its strict compact restrictions. -/
def quadraticSemilinearHeatBUCCompactFamilyOfMildPath
    (H : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (u₀ : BUC)
    (w : DuhamelPath H BUC)
    (hw : IsQuadraticSemilinearHeatBUCMildPath H B u₀ w) :
    QuadraticSemilinearHeatBUCCompactFamily H B u₀ where
  path T := restrictDuhamelPath (T : ℝ≥0) H (le_of_lt T.property) w
  mild T := semilinearHeatBUCFixedPoint_restrict_isFixedPt
    (E := E) (F := F) (T : ℝ≥0) H (le_of_lt T.property) u₀
    (quadraticOfCLM B) (continuous_quadraticOfCLM B) w hw
  compatible S T hST := by
    exact (restrictDuhamelPath_trans (E := E) (F := F)
      (S : ℝ≥0) (T : ℝ≥0) H hST (le_of_lt T.property) w).trans
        (by rfl)

/-- A crossing mild path that agrees with an old compatible family on every
old compact interval packages into a genuine strict extension. -/
theorem exists_strictExtension_of_crossing_mildPath
    (Tmax H : ℝ≥0) (hcross : Tmax < H)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (w : DuhamelPath H BUC)
    (hw : IsQuadraticSemilinearHeatBUCMildPath H B u₀ w)
    (hagrees : ∀ T : QuadraticBUCCompactTime Tmax,
      restrictDuhamelPath (T : ℝ≥0) H
        (le_of_lt (T.property.trans hcross)) w = fam.path T) :
    ∃ fam' : QuadraticSemilinearHeatBUCCompactFamily H B u₀,
      fam.IsStrictExtension fam' := by
  let fam' := quadraticSemilinearHeatBUCCompactFamilyOfMildPath
    (E := E) (F := F) H B u₀ w hw
  refine ⟨fam', hcross, ?_⟩
  intro T
  exact hagrees T

/-- A uniformly norm-bounded compatible family on a positive finite
half-open lifespan has a strict compatible extension.  The construction
restarts sufficiently near `Tmax`, uses the common bounded-data lifespan, and
identifies the new tail with every old overlap by localized uniqueness. -/
theorem exists_strictExtension_of_isNormBoundedBy
    (Tmax K : ℝ≥0) (hTmax : 0 < Tmax)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hbound : fam.IsNormBoundedBy K) :
    ∃ (H : ℝ≥0)
      (fam' : QuadraticSemilinearHeatBUCCompactFamily H B u₀),
      fam.IsStrictExtension fam' := by
  let δ : ℝ≥0 := quadraticBUCUniformLifespan β K
  have hδ : 0 < δ := quadraticBUCUniformLifespan_pos β K
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
  let τ : QuadraticBUCCompactTime Tmax := ⟨t, htTmax⟩
  let u : DuhamelPath t BUC := fam.path τ
  have hu : IsQuadraticSemilinearHeatBUCMildPath t B u₀ u := fam.mild τ
  have hend : ‖u (duhamelEndTime t)‖ ≤ (K : ℝ) := hbound τ _
  have hcont := exists_quadraticSemilinearHeatBUCLocalContinuation_of_end_norm_le
    (E := E) (F := F) t K B β hB u₀ u hu hend
  change 0 < δ ∧ ∃ v ∈ Metric.closedBall
      (heatLinearBUCPath δ (u (duhamelEndTime t))) (1 : ℝ),
      v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
          u (duhamelEndTime t) ∧
        semilinearHeatBUCPicard δ (u (duhamelEndTime t))
            (quadraticOfCLM B) (continuous_quadraticOfCLM B) v = v ∧
        ∀ w ∈ Metric.closedBall
            (heatLinearBUCPath δ (u (duhamelEndTime t))) (1 : ℝ),
          semilinearHeatBUCPicard δ (u (duhamelEndTime t))
              (quadraticOfCLM B) (continuous_quadraticOfCLM B) w = w →
            w = v at hcont
  rcases hcont.2 with ⟨v, hvBall, hv0, hv, _hvuniq⟩
  have hjoin :
      v (⟨0, ⟨le_rfl, δ.property⟩⟩ : Set.Icc (0 : ℝ) (δ : ℝ)) =
        u (compactDuhamelEndTime t) := by
    simpa [duhamelEndTime, compactDuhamelEndTime] using hv0
  let H : ℝ≥0 := t + δ
  have hcross : Tmax < H := by
    rw [← NNReal.coe_lt_coe]
    change (Tmax : ℝ) < ((t + δ : ℝ≥0) : ℝ)
    change (Tmax : ℝ) < ((Tmax : ℝ) - ε) + (δ : ℝ)
    linarith
  let w : DuhamelPath H BUC := appendDuhamelPath t δ u v hjoin
  have hw : IsQuadraticSemilinearHeatBUCMildPath H B u₀ w := by
    exact semilinearHeatBUCFixedPoint_append_isFixedPt
      (E := E) (F := F) t δ u₀ (quadraticOfCLM B)
      (continuous_quadraticOfCLM B) u v hu hv hjoin
  have hagrees : ∀ Sidx : QuadraticBUCCompactTime Tmax,
      restrictDuhamelPath (Sidx : ℝ≥0) H
        (le_of_lt (Sidx.property.trans hcross)) w = fam.path Sidx := by
    intro Sidx
    by_cases hSt : (Sidx : ℝ≥0) ≤ t
    · calc
        restrictDuhamelPath (Sidx : ℝ≥0) H
            (le_of_lt (Sidx.property.trans hcross)) w =
            restrictDuhamelPath (Sidx : ℝ≥0) t hSt u := by
          exact restrictDuhamelPath_append_of_le_left
            (E := E) (F := F) (Sidx : ℝ≥0) t δ hSt u v hjoin
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
      let newTail : DuhamelPath R BUC :=
        restrictDuhamelPath R δ hRδ v
      have hbase : fam.path Sidx aS = u (duhamelEndTime t) := by
        have hp := DFunLike.congr_fun (fam.compatible τ Sidx htS)
          (duhamelEndTime t)
        simpa [u, τ, aS, duhamelEndTime, restrictDuhamelPath_apply,
          restrictDuhamelTimeMap] using hp
      have hold : IsQuadraticSemilinearHeatBUCMildPath R B
          (fam.path Sidx aS) oldTail := by
        exact quadraticSemilinearHeatBUCMildPath_restart
          (E := E) (F := F) (Sidx : ℝ≥0) B u₀ (fam.path Sidx)
          (fam.mild Sidx) aS
      have hnew : IsQuadraticSemilinearHeatBUCMildPath R B
          (fam.path Sidx aS) newTail := by
        have hr := semilinearHeatBUCFixedPoint_restrict_isFixedPt
          (E := E) (F := F) R δ hRδ (u (duhamelEndTime t))
          (quadraticOfCLM B) (continuous_quadraticOfCLM B) v hv
        simpa [newTail, hbase] using hr
      have holdBall : oldTail ∈ Metric.closedBall
          (constantDuhamelPathGeneric R (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) := by
        apply Metric.closedBall_subset_closedBall
          (show (K : ℝ) ≤ ((K + 1 : ℝ≥0) : ℝ) by norm_num)
        apply DuhamelPath_mem_zero_closedBall_of_forall_norm_le R K oldTail
        intro r
        exact hbound Sidx (restartDuhamelTimeMap (Sidx : ℝ≥0) aS r)
      have hvZero : v ∈ Metric.closedBall
          (constantDuhamelPathGeneric δ (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
        mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
          (E := E) (F := F) δ K 1 (u (duhamelEndTime t)) hend hvBall
      have hnewBall : newTail ∈ Metric.closedBall
          (constantDuhamelPathGeneric R (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
        restrictDuhamelPath_mem_zero_closedBall
          (E := E) (F := F) R δ (K + 1) hRδ v hvZero
      have hsmall : R * quadraticBUCUniformBallLipschitzConstant β K 1 < 1 :=
        lt_of_le_of_lt
          (mul_le_mul_right' hRδ
            (quadraticBUCUniformBallLipschitzConstant β K 1))
          (quadraticBUCUniformLifespan_mul_lipschitz_lt_one β K)
      have htails : newTail = oldTail :=
        quadraticSemilinearHeatBUCFixedPoints_eq_of_mem_uniform_zero_ball
          (E := E) (F := F) R K 1 B β hB (fam.path Sidx aS)
          newTail oldTail hnewBall holdBall hnew hold hsmall
      apply ContinuousMap.ext
      intro q
      rw [restrictDuhamelPath_apply]
      change w (restrictDuhamelTimeMap (Sidx : ℝ≥0) H
        (le_of_lt (Sidx.property.trans hcross)) q) = fam.path Sidx q
      by_cases hqt : (q : ℝ) ≤ (t : ℝ)
      · rw [show w = appendDuhamelPath t δ u v hjoin by rfl]
        rw [appendDuhamelPath_apply_of_le t δ u v hjoin _ hqt]
        change u (Set.projIcc 0 (t : ℝ) t.property (q : ℝ)) =
          fam.path Sidx q
        have hp := DFunLike.congr_fun (fam.compatible τ Sidx htS)
          (⟨(q : ℝ), ⟨q.property.1, hqt⟩⟩ :
            Set.Icc (0 : ℝ) (t : ℝ))
        have hproj :
            Set.projIcc 0 (t : ℝ) t.property (q : ℝ) =
              (⟨(q : ℝ), ⟨q.property.1, hqt⟩⟩ :
                Set.Icc (0 : ℝ) (t : ℝ)) := by
          apply Subtype.ext
          simp [Set.coe_projIcc, max_eq_right q.property.1, min_eq_right hqt]
        rw [hproj]
        simpa [u, τ, restrictDuhamelPath_apply, restrictDuhamelTimeMap] using hp.symm
      · have htq : (t : ℝ) ≤ (q : ℝ) := le_of_not_ge hqt
        rw [show w = appendDuhamelPath t δ u v hjoin by rfl]
        rw [appendDuhamelPath_apply_of_ge t δ u v hjoin _ htq]
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
  rcases exists_strictExtension_of_crossing_mildPath
      (E := E) (F := F) Tmax H hcross B u₀ fam w hw hagrees with
    ⟨fam', hext⟩
  exact ⟨H, fam', hext⟩

/-- A positive-lifespan family satisfying a uniform norm bound cannot be
maximal. -/
theorem not_isMaximal_of_isNormBoundedBy
    (Tmax K : ℝ≥0) (hTmax : 0 < Tmax)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hbound : fam.IsNormBoundedBy K) :
    ¬ fam.IsMaximal := by
  intro hmax
  rcases exists_strictExtension_of_isNormBoundedBy
      (E := E) (F := F) Tmax K hTmax B β hB u₀ fam hbound with
    ⟨H, fam', hext⟩
  exact hmax ⟨H, fam', hext⟩

/-- The zero half-open lifespan is never maximal: local existence from the
initial datum supplies a positive strict extension, while compatibility with
the empty old family is vacuous. -/
theorem not_isMaximal_zero
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily 0 B u₀) :
    ¬ fam.IsMaximal := by
  let K : ℝ≥0 := ⟨‖u₀‖, norm_nonneg u₀⟩
  let u₀K : QuadraticBUCBoundedData (E := E) (F := F) K := ⟨u₀, le_rfl⟩
  let H : ℝ≥0 := quadraticBUCUniformLifespan β K
  let w : DuhamelPath H BUC :=
    quadraticSemilinearHeatBUCUniformSolution K B β hB u₀K
  have hH : 0 < H := quadraticBUCUniformLifespan_pos β K
  have hw : IsQuadraticSemilinearHeatBUCMildPath H B u₀ w := by
    exact quadraticSemilinearHeatBUCUniformSolution_isFixedPt
      (E := E) (F := F) K B β hB u₀K
  have hagrees : ∀ T : QuadraticBUCCompactTime 0,
      restrictDuhamelPath (T : ℝ≥0) H
        (le_of_lt (T.property.trans hH)) w = fam.path T := by
    intro T
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ (T : ℝ≥0) from bot_le)
      T.property).elim
  intro hmax
  rcases exists_strictExtension_of_crossing_mildPath
      (E := E) (F := F) 0 H hH B u₀ fam w hw hagrees with
    ⟨fam', hext⟩
  exact hmax ⟨H, fam', hext⟩

/-- Every maximal compatible family has a positive lifespan. -/
theorem QuadraticSemilinearHeatBUCCompactFamily.maximal_lifespan_pos
    (Tmax : ℝ≥0)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hmax : fam.IsMaximal) :
    0 < Tmax := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  subst Tmax
  exact (not_isMaximal_zero (E := E) (F := F) B β hB u₀ fam) hmax

/-- **Finite maximal-time norm blow-up alternative.**  If a compatible
quadratic mild family has positive finite maximal lifespan, its `BUC` norm is
unbounded on `[0,Tmax)`: every proposed bound is exceeded on some compact
subinterval. -/
theorem quadraticSemilinearHeatBUC_maximalTime_norm_unbounded
    (Tmax : ℝ≥0) (hTmax : 0 < Tmax)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : QuadraticBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ := by
  intro K
  have hnot : ¬ fam.IsNormBoundedBy K := by
    intro hbound
    exact (not_isMaximal_of_isNormBoundedBy
      (E := E) (F := F) Tmax K hTmax B β hB u₀ fam hbound) hmax
  simpa only [QuadraticSemilinearHeatBUCCompactFamily.IsNormBoundedBy,
    not_forall, not_le] using hnot

/-- Assumption-free form of the maximal-time alternative: maximality itself
forces positivity of the lifespan, then forces norm unboundedness. -/
theorem quadraticSemilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (Tmax : ℝ≥0)
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC)
    (fam : QuadraticSemilinearHeatBUCCompactFamily Tmax B u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : QuadraticBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ := by
  exact quadraticSemilinearHeatBUC_maximalTime_norm_unbounded
    (E := E) (F := F) Tmax
    (QuadraticSemilinearHeatBUCCompactFamily.maximal_lifespan_pos
      (E := E) (F := F) Tmax B β hB u₀ fam hmax)
    B β hB u₀ fam hmax

end Poincare
