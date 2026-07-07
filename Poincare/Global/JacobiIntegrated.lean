import Poincare.Global.JacobiNormClose

/-!
# Integrated Jacobi norm system

This file isolates the scalar integration stage after the pointwise Jacobi norm
bridge.  Once the three scalars satisfy the closed system on an interval and
start from `(0,0,q)`, Picard-Lindelöf uniqueness pins them to the classical
sine/cosine solution.
-/

noncomputable section

open Set Metric
open scoped NNReal

namespace Poincare

namespace JacobiIntegrated

/--
The closed Jacobi norm system integrates to the pinned sine/cosine solution on
the Picard-Lindelöf interval.

This is the scalar ODE stage used after
`JacobiNormClose.chart_linearized_state_feeds_norm_system_at`: if
`a' = 2b`, `b' = c - a`, `c' = -2b` on `Icc tmin tmax` with initial data
`(0,0,q)`, then the three scalars agree with the pinned model functions.
-/
theorem closed_norm_system_eq_pinned_on_Icc
    {tmin tmax q : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (Aop : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ))
    {radius r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : ℝ), (0 : ℝ), q) radius r L K)
    (hAop : ∀ x : ℝ × ℝ × ℝ,
      Aop x = (2 * x.2.1, x.2.2 - x.1, -2 * x.2.1))
    {a b c : ℝ → ℝ}
    (ha : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt a (2 * b s) (Icc tmin tmax) s)
    (hb : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt b (c s - a s) (Icc tmin tmax) s)
    (hc : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt c (-2 * b s) (Icc tmin tmax) s)
    (hmem : ∀ s ∈ Icc tmin tmax,
      (a s, b s, c s) ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (hpinnedmem : ∀ s ∈ Icc tmin tmax,
      (JacobiNormSystem.pinnedA q s,
        JacobiNormSystem.pinnedB q s,
        JacobiNormSystem.pinnedC q s) ∈
          closedBall ((0 : ℝ), (0 : ℝ), q) radius)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0) (hc0 : c 0 = q)
    {t : ℝ} (ht : t ∈ Icc tmin tmax) :
    a t = Real.sin t ^ 2 * q ∧
      b t = (Real.sin t * Real.cos t) * q ∧
      c t = Real.cos t ^ 2 * q := by
  let state : ℝ → ℝ × ℝ × ℝ := fun s => (a s, b s, c s)
  let pinned : ℝ → ℝ × ℝ × ℝ := fun s =>
    (JacobiNormSystem.pinnedA q s,
      JacobiNormSystem.pinnedB q s,
      JacobiNormSystem.pinnedC q s)
  have hstate : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt state (Aop (state s)) (Icc tmin tmax) s := by
    intro s hs
    have hprod := (ha s hs).prodMk ((hb s hs).prodMk (hc s hs))
    simpa [state, hAop] using hprod
  have hpinned : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt pinned (Aop (pinned s)) (Icc tmin tmax) s := by
    intro s _hs
    have hA : HasDerivWithinAt (JacobiNormSystem.pinnedA q)
        (2 * JacobiNormSystem.pinnedB q s) (Icc tmin tmax) s :=
      (JacobiNormSystem.pinnedA_hasDerivAt q s).hasDerivWithinAt
    have hB : HasDerivWithinAt (JacobiNormSystem.pinnedB q)
        (JacobiNormSystem.pinnedC q s - JacobiNormSystem.pinnedA q s)
        (Icc tmin tmax) s :=
      (JacobiNormSystem.pinnedB_hasDerivAt q s).hasDerivWithinAt
    have hC : HasDerivWithinAt (JacobiNormSystem.pinnedC q)
        (-2 * JacobiNormSystem.pinnedB q s) (Icc tmin tmax) s :=
      (JacobiNormSystem.pinnedC_hasDerivAt q s).hasDerivWithinAt
    have hprod := hA.prodMk (hB.prodMk hC)
    simpa [pinned, hAop] using hprod
  have hstatemem : ∀ s ∈ Icc tmin tmax,
      state s ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [state] using hmem s hs
  have hpinnedmem' : ∀ s ∈ Icc tmin tmax,
      pinned s ∈ closedBall ((0 : ℝ), (0 : ℝ), q) radius := by
    intro s hs
    simpa [pinned] using hpinnedmem s hs
  have hinit : state 0 = pinned 0 := by
    simp [state, pinned, ha0, hb0, hc0]
  have heq : EqOn state pinned (Icc tmin tmax) :=
    linearODE_solution_uniqueOn_Icc
      (A := fun _ : ℝ => Aop)
      (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : ℝ), (0 : ℝ), q))
      hpl hstate hstatemem hpinned hpinnedmem' hinit
  have htstate := heq ht
  constructor
  · have h := congrArg Prod.fst htstate
    simpa [state, pinned, JacobiNormSystem.pinnedA] using h
  constructor
  · have h := congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) htstate
    simpa [state, pinned, JacobiNormSystem.pinnedB] using h
  · have h := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) htstate
    simpa [state, pinned, JacobiNormSystem.pinnedC] using h

end JacobiIntegrated

end Poincare
