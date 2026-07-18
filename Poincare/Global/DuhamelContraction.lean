import Poincare.Global.VectorHeatCauchy
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Duhamel contraction estimates

This module supplies the first nonlinear layer above the finite-dimensional
vector heat equation.  It treats a positive-time path as a continuous map on a
compact interval and estimates the difference of two Duhamel iterates

`∫₀ᵗ S(t-s) (N(u(s)) - N(v(s))) ds`.

If the linear propagator is bounded by `A` and the nonlinearity is Lipschitz
with constant `L`, then the Duhamel map has contraction constant `T A L` in the
uniform norm.  Consequently, for `T A L < 1`, Mathlib's Banach fixed-point
theorem produces a unique mild solution.  The statement is deliberately
finite-time and Banach-valued, so it can be instantiated by coordinate Ricci--
DeTurck tensors after the geometric nonlinear estimate is supplied.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal

namespace Poincare

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Continuous Banach-valued paths on the closed positive time interval. -/
abbrev DuhamelPath (T : ℝ≥0) (X : Type*) [TopologicalSpace X] :=
  C(Set.Icc (0 : ℝ) (T : ℝ), X)

/-- Difference of two projected Duhamel iterates.  `projIcc` makes the
integrand a total function on `ℝ`; on the actual integration interval it is
the original path evaluation. -/
def projectedDuhamelDifference
    (T : ℝ≥0) (S : ℝ → X →L[ℝ] X) (N : X → X)
    (u v : DuhamelPath T X) (t : Set.Icc (0 : ℝ) (T : ℝ)) : X :=
  ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
    S ((t : ℝ) - s)
      (N (u (Set.projIcc 0 (T : ℝ) T.property s)) -
        N (v (Set.projIcc 0 (T : ℝ) T.property s)))

/-- The concrete `T A L` Duhamel difference estimate in the uniform path
norm. -/
theorem norm_projectedDuhamelDifference_le
    (T A L : ℝ≥0) (S : ℝ → X →L[ℝ] X) (N : X → X)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ‖S r‖ ≤ (A : ℝ))
    (hN : LipschitzWith L N)
    (u v : DuhamelPath T X) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ‖projectedDuhamelDifference T S N u v t‖ ≤
      ((T * A * L : ℝ≥0) : ℝ) * ‖u - v‖ := by
  let C : ℝ := (A : ℝ) * (L : ℝ) * ‖u - v‖
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖S ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)) -
          N (v (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤ C := by
    intro s hs
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) (t : ℝ) := by
      simpa [Set.uIoc_of_le ht0] using hs
    have hr : (t : ℝ) - s ∈ Set.Icc (0 : ℝ) (T : ℝ) := by
      constructor
      · exact sub_nonneg.mpr hsIoc.2
      · exact (sub_le_self _ hsIoc.1.le).trans t.property.2
    let p : Set.Icc (0 : ℝ) (T : ℝ) :=
      Set.projIcc 0 (T : ℝ) T.property s
    have hpath : ‖u p - v p‖ ≤ ‖u - v‖ := by
      simpa using ContinuousMap.norm_coe_le_norm (u - v) p
    have hnonlin : ‖N (u p) - N (v p)‖ ≤ (L : ℝ) * ‖u p - v p‖ := by
      simpa [dist_eq_norm] using hN.dist_le_mul (u p) (v p)
    calc
      ‖S ((t : ℝ) - s) (N (u p) - N (v p))‖
          ≤ ‖S ((t : ℝ) - s)‖ * ‖N (u p) - N (v p)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (A : ℝ) * ((L : ℝ) * ‖u p - v p‖) := by
        exact mul_le_mul (hS _ hr) hnonlin (norm_nonneg _) A.property
      _ ≤ (A : ℝ) * ((L : ℝ) * ‖u - v‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpath L.property) A.property
      _ = C := by simp [C, mul_assoc]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [projectedDuhamelDifference]
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        S ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)) -
            N (v (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ C * |(t : ℝ) - 0| := hint
    _ = ((t : ℝ) * (A : ℝ) * (L : ℝ)) * ‖u - v‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      simp [C]
      ring
    _ ≤ (((T : ℝ) * (A : ℝ) * (L : ℝ)) * ‖u - v‖) := by
      gcongr
      exact t.property.2
    _ = ((T * A * L : ℝ≥0) : ℝ) * ‖u - v‖ := by norm_num

omit [NormedSpace ℝ X] in
/-- A pointwise uniform-norm estimate promotes to a Lipschitz estimate on the
continuous-path Banach space. -/
theorem continuousMap_lipschitzWith_of_pointwise_norm
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (q : ℝ≥0) (Φ : C(K, X) → C(K, X))
    (hΦ : ∀ (u v : C(K, X)) (t : K),
      ‖Φ u t - Φ v t‖ ≤ (q : ℝ) * ‖u - v‖) :
    LipschitzWith q Φ := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg q.property (norm_nonneg _))).mpr
  intro t
  simpa using hΦ u v t

/-- A Duhamel Picard map whose differences are represented by the projected
integral is a contraction whenever `T A L < 1`. -/
theorem contractingWith_of_projectedDuhamelDifference
    [CompleteSpace X]
    (T A L : ℝ≥0) (S : ℝ → X →L[ℝ] X) (N : X → X)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ‖S r‖ ≤ (A : ℝ))
    (hN : LipschitzWith L N)
    (Φ : DuhamelPath T X → DuhamelPath T X)
    (hΦ : ∀ (u v : DuhamelPath T X) (t : Set.Icc (0 : ℝ) (T : ℝ)),
      Φ u t - Φ v t = projectedDuhamelDifference T S N u v t)
    (hsmall : T * A * L < 1) :
    ContractingWith (T * A * L) Φ := by
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  refine ⟨hsmall, continuousMap_lipschitzWith_of_pointwise_norm
    (q := T * A * L) Φ ?_⟩
  intro u v t
  rw [hΦ u v t]
  exact norm_projectedDuhamelDifference_le T A L S N hS hN u v t

/-- Banach's fixed-point theorem gives a unique mild solution of any Duhamel
Picard map satisfying the concrete short-time estimate above. -/
theorem exists_unique_fixedPoint_of_projectedDuhamelDifference
    [CompleteSpace X]
    (T A L : ℝ≥0) (S : ℝ → X →L[ℝ] X) (N : X → X)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ‖S r‖ ≤ (A : ℝ))
    (hN : LipschitzWith L N)
    (Φ : DuhamelPath T X → DuhamelPath T X)
    (hΦ : ∀ (u v : DuhamelPath T X) (t : Set.Icc (0 : ℝ) (T : ℝ)),
      Φ u t - Φ v t = projectedDuhamelDifference T S N u v t)
    (hsmall : T * A * L < 1) :
    ∃! u : DuhamelPath T X, Φ u = u := by
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  let hcontract : ContractingWith (T * A * L) Φ :=
    contractingWith_of_projectedDuhamelDifference T A L S N hS hN Φ hΦ hsmall
  let u : DuhamelPath T X := hcontract.fixedPoint Φ
  refine ⟨u, hcontract.fixedPoint_isFixedPt, ?_⟩
  intro v hv
  exact hcontract.fixedPoint_unique' hv hcontract.fixedPoint_isFixedPt

omit [NormedSpace ℝ X] in
/-- Local Banach fixed-point theorem in the uniform path norm.  This is the
version used for nonlinear geometric systems, where the nonlinearity is only
Lipschitz on a closed ball and the Picard map must first be shown to preserve
that ball. -/
theorem exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [CompleteSpace X]
    (q : ℝ≥0) (Φ : C(K, X) → C(K, X))
    (center : C(K, X)) {R : ℝ} (hR : 0 ≤ R)
    (hmaps : MapsTo Φ (Metric.closedBall center R) (Metric.closedBall center R))
    (hpoint : ∀ (u v : C(K, X)),
      u ∈ Metric.closedBall center R →
      v ∈ Metric.closedBall center R →
      ∀ t : K, ‖Φ u t - Φ v t‖ ≤ (q : ℝ) * ‖u - v‖)
    (hq : q < 1) :
    ∃ u ∈ Metric.closedBall center R, Φ u = u ∧
      ∀ v ∈ Metric.closedBall center R, Φ v = v → v = u := by
  let s : Set C(K, X) := Metric.closedBall center R
  let Φs : s → s := hmaps.restrict Φ s s
  letI : CompleteSpace s := Metric.isClosed_closedBall.completeSpace_coe
  letI : Nonempty s := ⟨⟨center, Metric.mem_closedBall_self hR⟩⟩
  have hlip : LipschitzWith q Φs := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Subtype.dist_eq, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (mul_nonneg q.property (norm_nonneg _))).mpr
    intro t
    simpa [Φs, s] using hpoint u v u.property v.property t
  have hc : ContractingWith q Φs := ⟨hq, hlip⟩
  let uₛ : s := hc.fixedPoint Φs
  have huₛ : IsFixedPt Φs uₛ := hc.fixedPoint_isFixedPt
  have hu : Φ (uₛ : C(K, X)) = (uₛ : C(K, X)) := by
    exact congrArg Subtype.val huₛ
  refine ⟨uₛ, uₛ.property, hu, ?_⟩
  intro v hv hfix
  let vₛ : s := ⟨v, hv⟩
  have hvₛ : IsFixedPt Φs vₛ := by
    apply Subtype.ext
    exact hfix
  exact congrArg Subtype.val (hc.fixedPoint_unique' hvₛ huₛ)

end Poincare
