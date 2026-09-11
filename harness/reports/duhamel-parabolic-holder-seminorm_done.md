# Duhamel parabolic Hölder seminorm: verified worker result

Date: 2026-09-11. Branch: `worker/duhamel-parabolic-holder-seminorm`.
Base: `ae66c744c8298a301cb47539824b162a83990667`.

Both requested theorems are proved in the single new Lean module
`Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.
The domain is `Poincare.ClosedSmoothModel 3`, exactly as in the landed estimates.
The constant is the sum of their positive constants. The proof splits at
`(p.1, q.2)` and uses real-power monotonicity on both distance terms.
The corollary uses the original `HasHolderBound` by definitional equality.
No existing Lean file, root import, or frozen contract was edited.

Proof commits:
- `2e220870`: `duhamel_hessian_parabolic_holder`.
- `610b2e15`: `hasHolderBound_duhamel_hessian`.

The worker result awaits independent review; it is not merged or accepted.
First reviewer action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.

## Gate results

- Focused Lean check after each theorem: exit 0, empty output.
- Frozen first statement copied from the read-only task and assigned the theorem: exit 0.
- Both new declarations have exactly `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token scan: exit 1, empty output, as expected for no matches.
- `git diff --check`: exit 0, empty output.

There are exactly two new declarations and no new instances or definitions.
The initial compiler attempt failed because the local `E` notation interfered
with parsing the named argument `(E := E)`. Writing `(«E» := E)` resolves the
parser issue without changing the type. The exponent rewrite passed unchanged.

## Recorded probes

Probe files below were run with `LEAN_NUM_THREADS=1 lake env lean <path>`.
All outputs are preserved verbatim, including the initial failed attempt.
The context print includes proof terms because Lean's default `#print` emits them.

### context

<details><summary>Probe source</summary>

```lean
import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.ParabolicHolderSpace
#print Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder
#print Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder
#print Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound
#print Poincare.ParabolicHolder.HasHolderBound
#print Poincare.ParabolicHolder.cylinder
#print Poincare.ParabolicHolder.parabolicDist
#check Real.rpow_mul
#check Real.rpow_le_rpow
#check Real.sqrt_eq_rpow
#check norm_sub_le
```

</details>

<details><summary>Actual output; exit 0</summary>

```text
theorem Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t ∈ Set.Icc 0 T,
                              ∀ (x z : Poincare.ClosedSmoothModel 3),
                                ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u t)) z‖ ≤ C * K * ‖x - z‖ ^ α :=
fun α hα hα1 =>
  let N :=
    (2 *
        ∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
      (2 / α);
  let F :=
    ((∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖ *
            ‖y‖ ^ α) +
        ∫ (y : Poincare.ClosedSmoothModel 3),
          ‖(fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y‖) *
      (2 / (1 - α));
  have hN :=
    mul_nonneg
      (mul_nonneg
        (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl true))
        (MeasureTheory.integral_nonneg fun y =>
          mul_nonneg (norm_nonneg ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y))
            (Real.rpow_nonneg (norm_nonneg y) α)))
      (div_nonneg
        (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl true))
        (LT.lt.le hα));
  have hF :=
    mul_nonneg
      (add_nonneg
        (MeasureTheory.integral_nonneg fun y =>
          mul_nonneg
            (norm_nonneg
              ((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y))
            (Real.rpow_nonneg (norm_nonneg y) α))
        (MeasureTheory.integral_nonneg fun y =>
          norm_nonneg
            ((fun t x => fderiv ℝ ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) t) x) 1 y)))
      (div_nonneg
        (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl true))
        (le_of_not_gt fun a =>
          Mathlib.Tactic.Linarith.lt_irrefl
            (Eq.mp
              (congrArg (fun _a => _a < 0)
                (Mathlib.Tactic.Ring.of_eq
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            Mathlib.Tactic.Ring.Common.neg_zero)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
              (Mathlib.Tactic.Linarith.add_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα1)
                (Mathlib.Tactic.Linarith.sub_neg_of_lt a)))));
  Exists.intro (max 1 (N + F))
    ⟨lt_of_lt_of_le zero_lt_one (le_max_left 1 (N + F)), fun T a a_1 f M K a_2 hK0 hf hM hK =>
      id fun t ht x z =>
        have hC := le_max_right 1 (N + F);
        have hpow := Real.rpow_nonneg (norm_nonneg (x - z)) α;
        have hraw :=
          if he : x = z then
            Eq.ndrec (motive := fun z =>
              0 ≤ ‖x - z‖ ^ α →
                ‖fderiv ℝ (fderiv ℝ fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x) x -
                      fderiv ℝ
                        (fderiv ℝ fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x) z‖ ≤
                  (N + F) * K * ‖x - z‖ ^ α)
              (fun hpow =>
                of_eq_true
                  (Eq.trans
                    (congr
                      (congrArg LE.le
                        (Eq.trans
                          (congrArg norm
                            (Eq.trans
                              (congr
                                (congrArg HSub.hSub
                                  (congrFun'
                                    (congrArg (fderiv ℝ)
                                      (congrArg (fderiv ℝ)
                                        (funext fun x =>
                                          congrFun'
                                            (congrFun'
                                              (congrFun'
                                                (congrArg intervalIntegral
                                                  (funext fun s =>
                                                    Poincare.heatSolution_apply (t - s) (fun y => f (s, y)) x))
                                                0)
                                              t)
                                            MeasureTheory.volume)))
                                    x))
                                (congrFun'
                                  (congrArg (fderiv ℝ)
                                    (congrArg (fderiv ℝ)
                                      (funext fun x =>
                                        congrFun'
                                          (congrFun'
                                            (congrFun'
                                              (congrArg intervalIntegral
                                                (funext fun s =>
                                                  Poincare.heatSolution_apply (t - s) (fun y => f (s, y)) x))
                                              0)
                                            t)
                                          MeasureTheory.volume)))
                                  x))
                              (sub_self
                                (fderiv ℝ
                                  (fderiv ℝ fun x =>
                                    ∫ (s : ℝ) in 0..t,
                                      ∫ (y : Poincare.ClosedSmoothModel 3),
                                        Poincare.heatKernel (t - s) y * f (s, x - y))
                                  x))))
                          norm_zero))
                      (Eq.trans
                        (congrArg (HMul.hMul ((N + F) * K))
                          (Eq.trans (congrFun' (congrArg HPow.hPow (Eq.trans (congrArg norm (sub_self x)) norm_zero)) α)
                            (Real.zero_rpow (LT.lt.ne' hα))))
                        (mul_zero ((N + F) * K))))
                    (Std.le_refl._simp_1 0)))
              he hpow
          else
            have hρ := norm_pos_iff.mpr (sub_ne_zero.mpr he);
            if htime : t ≤ ‖x - z‖ ^ 2 then
              LE.le.trans
                (Poincare.HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht
                  hK0 hf hM hK x z htime)
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (have this :=
                      le_of_not_gt fun a =>
                        Mathlib.Tactic.Linarith.lt_irrefl
                          (Eq.mp
                            (congrArg (fun _a => _a < 0)
                              (Mathlib.Tactic.Ring.of_eq
                                (Mathlib.Tactic.Ring.Common.add_congr
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                    (Mathlib.Tactic.Ring.Common.mul_congr
                                      (Mathlib.Tactic.Ring.Common.add_congr
                                        (Mathlib.Tactic.Ring.Common.atom_pf
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x =>
                                                    fderiv ℝ
                                                      ((fun t x =>
                                                          fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                        t)
                                                      x)
                                                  1 y‖ *
                                              ‖y‖ ^ α)
                                          rfl
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                  fderiv ℝ
                                                                    ((fun t x =>
                                                                        fderiv ℝ
                                                                          (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                      t)
                                                                    x)
                                                                1 y‖ *
                                                            ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 1 =
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                  fderiv ℝ
                                                                    ((fun t x =>
                                                                        fderiv ℝ
                                                                          (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                      t)
                                                                    x)
                                                                1 y‖ *
                                                            ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))))
                                        (Mathlib.Tactic.Ring.Common.atom_pf
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x =>
                                                  fderiv ℝ
                                                    ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                      t)
                                                    x)
                                                1 y‖)
                                          rfl
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                fderiv ℝ
                                                                  ((fun t x =>
                                                                      fderiv ℝ
                                                                        (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                    t)
                                                                  x)
                                                              1 y‖) ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 1 =
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                fderiv ℝ
                                                                  ((fun t x =>
                                                                      fderiv ℝ
                                                                        (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                    t)
                                                                  x)
                                                              1 y‖) ^
                                                        Nat.rawCast 1 *
                                                      _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖ *
                                                  ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1)
                                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1 +
                                              0))))
                                      (Mathlib.Tactic.Ring.Common.div_congr
                                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Tactic.Ring.Common.sub_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                          (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.sub_pf
                                            (Mathlib.Tactic.Ring.Common.neg_add
                                              (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                    (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                    (Eq.refl (Int.negOfNat 1)))))
                                              Mathlib.Tactic.Ring.Common.neg_zero)
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                                        (Mathlib.Tactic.Ring.Common.div_pf
                                          (Mathlib.Tactic.Ring.Common.atom_pf'
                                            (Eq.refl
                                              (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (Nat.rawCast 1 +
                                                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (Nat.rawCast 1 +
                                                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((Nat.rawCast 1 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2 +
                                                  0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 +
                                                0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2 +
                                                0)))))
                                      (Mathlib.Tactic.Ring.Common.add_mul
                                        (Mathlib.Tactic.Ring.Common.mul_add
                                          (Mathlib.Tactic.Ring.Common.mul_pf_left
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖ *
                                                ‖y‖ ^ α)
                                            (Nat.rawCast 1)
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right
                                              (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                              (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                          (Mathlib.Tactic.Ring.Common.mul_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 1))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                ((Nat.rawCast 1 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2) +
                                              0)))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_left
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖)
                                              (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2) +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.zero_mul
                                            ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 2 +
                                              0))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖) ^
                                                  Nat.rawCast 1 *
                                                ((Nat.rawCast 1 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2) +
                                              0)))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖ *
                                                  ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2))
                                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖) ^
                                                  Nat.rawCast 1 *
                                                ((Nat.rawCast 1 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2) +
                                              0)))))
                                    (Mathlib.Tactic.Ring.Common.sub_pf
                                      (Mathlib.Tactic.Ring.Common.neg_add
                                        (Mathlib.Tactic.Ring.Common.neg_mul
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x =>
                                                    fderiv ℝ
                                                      ((fun t x =>
                                                          fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                        t)
                                                      x)
                                                  1 y‖ *
                                              ‖y‖ ^ α)
                                          (Nat.rawCast 1)
                                          (Mathlib.Tactic.Ring.Common.neg_mul
                                            (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                            (Nat.rawCast 1)
                                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                (Eq.refl (Int.negOfNat 2))))))
                                        (Mathlib.Tactic.Ring.Common.neg_add
                                          (Mathlib.Tactic.Ring.Common.neg_mul
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                    fderiv ℝ
                                                      ((fun t x =>
                                                          fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                        t)
                                                      x)
                                                  1 y‖)
                                            (Nat.rawCast 1)
                                            (Mathlib.Tactic.Ring.Common.neg_mul
                                              (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                              (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                  (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                  (Eq.refl (Int.negOfNat 2))))))
                                          Mathlib.Tactic.Ring.Common.neg_zero))
                                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖ *
                                                  ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              (Int.negOfNat 2).rawCast) +
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖) ^
                                                Nat.rawCast 1 *
                                              ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                  Nat.rawCast 1 *
                                                (Int.negOfNat 2).rawCast) +
                                            0)))))
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.Common.add_congr
                                      (Mathlib.Tactic.Ring.Common.mul_congr
                                        (Mathlib.Tactic.Ring.Common.mul_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                          (Mathlib.Tactic.Ring.Common.atom_pf
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                    y‖ *
                                                ‖y‖ ^ α)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                    fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                      x)
                                                                  1 y‖ *
                                                              ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                    fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                      x)
                                                                  1 y‖ *
                                                              ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                        y‖ *
                                                    ‖y‖ ^ α)
                                                (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                        ‖(fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              1 y‖ *
                                                          ‖y‖ ^ α) ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2 +
                                                  0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 +
                                                0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2 +
                                                0))))
                                        (Mathlib.Tactic.Ring.Common.div_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                          (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.div_pf
                                            (Mathlib.Tactic.Ring.Common.inv_single
                                              (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                                (Eq.symm
                                                    (Eq.mpr
                                                      (id
                                                        (congrArg
                                                          (fun _a =>
                                                            α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                                              α⁻¹ ^ Nat.rawCast 1 * _a)
                                                          (Eq.symm rfl)))
                                                      (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                                  Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                            (Mathlib.Tactic.Ring.Common.add_mul
                                              (Mathlib.Tactic.Ring.Common.mul_add
                                                (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                              (Mathlib.Tactic.Ring.Common.zero_mul
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_left
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                      y‖ *
                                                  ‖y‖ ^ α)
                                              (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 4)))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 2))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.zero_mul
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                              0))))
                                      (Mathlib.Tactic.Ring.Common.mul_congr
                                        (Mathlib.Tactic.Ring.Common.add_congr
                                          (Mathlib.Tactic.Ring.Common.atom_pf
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖ *
                                                ‖y‖ ^ α)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                    fderiv ℝ
                                                                      ((fun t x =>
                                                                          fderiv ℝ
                                                                            (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                            x)
                                                                        t)
                                                                      x)
                                                                  1 y‖ *
                                                              ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                    fderiv ℝ
                                                                      ((fun t x =>
                                                                          fderiv ℝ
                                                                            (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                            x)
                                                                        t)
                                                                      x)
                                                                  1 y‖ *
                                                              ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ
                                                                ((fun t x =>
                                                                    fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                      x)
                                                                  t)
                                                                x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.atom_pf
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                    fderiv ℝ
                                                      ((fun t x =>
                                                          fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                        t)
                                                      x)
                                                  1 y‖)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                  fderiv ℝ
                                                                    ((fun t x =>
                                                                        fderiv ℝ
                                                                          (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                      t)
                                                                    x)
                                                                1 y‖) ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x =>
                                                                  fderiv ℝ
                                                                    ((fun t x =>
                                                                        fderiv ℝ
                                                                          (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                                      t)
                                                                    x)
                                                                1 y‖) ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 1)
                                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 +
                                                0))))
                                        (Mathlib.Tactic.Ring.Common.div_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                          (Mathlib.Tactic.Ring.Common.sub_congr
                                            (Mathlib.Tactic.Ring.cast_pos
                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                            (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                            (Mathlib.Tactic.Ring.Common.sub_pf
                                              (Mathlib.Tactic.Ring.Common.neg_add
                                                (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                      (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                      (Eq.refl (Int.negOfNat 1)))))
                                                Mathlib.Tactic.Ring.Common.neg_zero)
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                                  (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                                          (Mathlib.Tactic.Ring.Common.div_pf
                                            (Mathlib.Tactic.Ring.Common.atom_pf'
                                              (Eq.refl
                                                (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹)
                                              rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      (Nat.rawCast 1 +
                                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                            Nat.rawCast 1 *
                                                          Nat.rawCast 1 =
                                                        (Nat.rawCast 1 +
                                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                            Nat.rawCast 1 *
                                                          _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl
                                                  ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 1))))
                                            (Mathlib.Tactic.Ring.Common.add_mul
                                              (Mathlib.Tactic.Ring.Common.mul_add
                                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                  (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                  (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                  ((Nat.rawCast 1 +
                                                            (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 2 +
                                                    0)))
                                              (Mathlib.Tactic.Ring.Common.zero_mul
                                                ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 1 +
                                                  0))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2 +
                                                  0)))))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_left
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖ *
                                                  ‖y‖ ^ α)
                                              (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ
                                                                ((fun t x =>
                                                                    fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                      x)
                                                                  t)
                                                                x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2) +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_left
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                        fderiv ℝ
                                                          ((fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            t)
                                                          x)
                                                      1 y‖)
                                                (Nat.rawCast 1)
                                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                  (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                  (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                        ‖(fun t x =>
                                                              fderiv ℝ
                                                                ((fun t x =>
                                                                    fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                      x)
                                                                  t)
                                                                x)
                                                            1 y‖) ^
                                                      Nat.rawCast 1 *
                                                    ((Nat.rawCast 1 +
                                                            (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 2) +
                                                  0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2 +
                                                0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2) +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          fderiv ℝ
                                                            ((fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              t)
                                                            x)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 2))
                                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                            fderiv ℝ
                                                              ((fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                t)
                                                              x)
                                                          1 y‖) ^
                                                    Nat.rawCast 1 *
                                                  ((Nat.rawCast 1 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2) +
                                                0)))))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖ *
                                                ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 2))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖) ^
                                              Nat.rawCast 1 *
                                            ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                              0)))))
                                    (Mathlib.Tactic.Ring.Common.mul_congr
                                      (Mathlib.Tactic.Ring.Common.mul_congr
                                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Tactic.Ring.Common.atom_pf
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ *
                                              ‖y‖ ^ α)
                                          rfl
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                1 y‖ *
                                                            ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 1 =
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x =>
                                                                  fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z)
                                                                    x)
                                                                1 y‖ *
                                                            ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                      y‖ *
                                                  ‖y‖ ^ α)
                                              (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2 +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.zero_mul
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1 +
                                              0))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 2 +
                                              0))))
                                      (Mathlib.Tactic.Ring.Common.div_congr
                                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                        (Mathlib.Tactic.Ring.Common.div_pf
                                          (Mathlib.Tactic.Ring.Common.inv_single
                                            (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                  (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                              (Eq.symm
                                                  (Eq.mpr
                                                    (id
                                                      (congrArg
                                                        (fun _a =>
                                                          α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                                            α⁻¹ ^ Nat.rawCast 1 * _a)
                                                        (Eq.symm rfl)))
                                                    (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                                Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                      (Mathlib.Tactic.Ring.Common.add_mul
                                        (Mathlib.Tactic.Ring.Common.mul_add
                                          (Mathlib.Tactic.Ring.Common.mul_pf_left
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                    y‖ *
                                                ‖y‖ ^ α)
                                            (Nat.rawCast 1)
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 4)))))
                                          (Mathlib.Tactic.Ring.Common.mul_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                        y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                              0)))
                                        (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                        y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                            0))))
                                    (Mathlib.Tactic.Ring.Common.sub_pf
                                      (Mathlib.Tactic.Ring.Common.neg_add
                                        (Mathlib.Tactic.Ring.Common.neg_mul
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ *
                                              ‖y‖ ^ α)
                                          (Nat.rawCast 1)
                                          (Mathlib.Tactic.Ring.Common.neg_mul α⁻¹ (Nat.rawCast 1)
                                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4))
                                                (Eq.refl (Int.negOfNat 4))))))
                                        Mathlib.Tactic.Ring.Common.neg_zero)
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖ *
                                                ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 2))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                      fderiv ℝ
                                                        ((fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          t)
                                                        x)
                                                    1 y‖) ^
                                              Nat.rawCast 1 *
                                            ((Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                      y‖ *
                                                  ‖y‖ ^ α)
                                              (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α⁻¹ (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                                    (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4))
                                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 4))
                                                    (Eq.refl (Int.ofNat 0))))))
                                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                        ‖(fun t x =>
                                                fderiv ℝ
                                                  ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                    t)
                                                  x)
                                              1 y‖ *
                                          ‖y‖ ^ α)
                                      (Nat.rawCast 1)
                                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                        (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                        (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                                            (Mathlib.Meta.NormNum.IsNat.to_isInt
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                            (Eq.refl (Int.ofNat 0))))))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                        (∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖(fun t x =>
                                                fderiv ℝ
                                                  ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                    t)
                                                  x)
                                              1 y‖)
                                        (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                          (Nat.rawCast 1 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                          (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                                              (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                              (Eq.refl (Int.ofNat 0))))))
                                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                            (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg (Mathlib.Tactic.Linarith.sub_nonpos_of_le hF)
                              (Mathlib.Tactic.Linarith.sub_neg_of_lt a)));
                    this)
                    hK0)
                  hpow)
            else
              have hscale := lt_of_not_ge htime;
              let a := t - ‖x - z‖ ^ 2;
              let H := fun s p =>
                ∫ (y : Poincare.ClosedSmoothModel 3),
                  (f (s, p - y) - f (s, p)) •
                    (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y;
              have ha := sub_pos.mpr hscale;
              have hat := sub_le_self t (sq_nonneg ‖x - z‖);
              have h0t := fun p =>
                (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.left enorm_ne_top enorm_ne_top).mpr
                  (Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 ht hf hK p);
              have h0a := fun p =>
                (intervalIntegrable_iff_integrableOn_Ioo_of_le (LT.lt.le ha) enorm_ne_top enorm_ne_top).mpr
                  (MeasureTheory.IntegrableOn.mono_set
                    (Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 ht hf hK p)
                    (Set.Ioo_subset_Ioo le_rfl hat));
              have hsplit := fun p =>
                Eq.symm
                  (intervalIntegral.integral_add_adjacent_intervals (h0a p)
                    (IntervalIntegrable.trans (IntervalIntegrable.symm (h0a p)) (h0t p)));
              Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      ‖_a -
                            fderiv ℝ
                              (fderiv ℝ fun x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x)
                              z‖ ≤
                        (N + F) * K * ‖x - z‖ ^ α)
                    (Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x)))
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a =>
                        ‖(∫ (s : ℝ) in 0..t,
                                ∫ (y : Poincare.ClosedSmoothModel 3),
                                  (f (s, x - y) - f (s, x)) •
                                    (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (t - s) y) -
                              _a‖ ≤
                          (N + F) * K * ‖x - z‖ ^ α)
                      (Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK z)))
                  (id
                    (Eq.mpr
                      (id (congrArg (fun _a => ‖_a - ∫ (s : ℝ) in 0..t, H s z‖ ≤ (N + F) * K * ‖x - z‖ ^ α) (hsplit x)))
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              ‖((∫ (s : ℝ) in 0..a, H s x) + ∫ (s : ℝ) in a..t, H s x) - _a‖ ≤
                                (N + F) * K * ‖x - z‖ ^ α)
                            (hsplit z)))
                        (have hnear :=
                          Poincare.HeatDuhamelHessianSpatialHolder.near_hessian_difference_le hα hα1 hK0 hat
                            (fun s hs =>
                              hK s
                                ⟨LE.le.trans (LT.lt.le ha) (LT.lt.le hs.left),
                                  LE.le.trans (LT.lt.le hs.right) ht.right⟩)
                            x z
                            (id
                              (le_of_not_gt fun a =>
                                Mathlib.Tactic.Linarith.lt_irrefl
                                  (Eq.mp
                                    (congrArg (fun _a => _a < 0)
                                      (Mathlib.Tactic.Ring.of_eq
                                        (Mathlib.Tactic.Ring.Common.sub_congr
                                          (Mathlib.Tactic.Ring.Common.pow_congr
                                            (Mathlib.Tactic.Ring.Common.atom_pf ‖x - z‖ rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      ‖x - z‖ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                                        ‖x - z‖ ^ Nat.rawCast 1 * _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl (⋯ * ⋯))))
                                            ⋯ ⋯)
                                          ⋯ ⋯)
                                        ⋯))
                                    ⋯)));
                        ⋯)))));
        ⋯⟩
theorem Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t₁ ∈ Set.Icc 0 T,
                              ∀ t₂ ∈ Set.Icc 0 T,
                                ∀ (x : Poincare.ClosedSmoothModel 3),
                                  ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
                                    C * K * |t₁ - t₂| ^ (α / 2) :=
fun α hα hα1 =>
  let B :=
    (∫ (y : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
      (2 / α);
  let F :=
    (∫ (y : Poincare.ClosedSmoothModel 3),
        ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1 y‖ *
          ‖y‖ ^ α) *
      (2 / (2 - α));
  have hB :=
    mul_nonneg
      (MeasureTheory.integral_nonneg fun y =>
        mul_nonneg (norm_nonneg ((fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y))
          (Real.rpow_nonneg (norm_nonneg y) α))
      (div_nonneg
        (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl true))
        (LT.lt.le hα));
  have hF :=
    mul_nonneg
      (MeasureTheory.integral_nonneg fun y =>
        mul_nonneg
          (norm_nonneg
            ((fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) r x) t) 1
              y))
          (Real.rpow_nonneg (norm_nonneg y) α))
      (div_nonneg
        (Mathlib.Meta.NormNum.isNat_le_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl true))
        (le_of_not_gt fun a =>
          Mathlib.Tactic.Linarith.lt_irrefl
            (Eq.mp
              (congrArg (fun _a => _a < 0)
                (Mathlib.Tactic.Ring.of_eq
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                        (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            Mathlib.Tactic.Ring.Common.neg_zero)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.sub_pf
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1))))
                              Mathlib.Tactic.Ring.Common.neg_zero)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.negOfNat 2))))
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 2))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 2).rawCast
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            ((Int.negOfNat 1).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            ((Int.negOfNat 2).rawCast + (α ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 2).rawCast
                        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf α (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                  (Eq.refl (Int.ofNat 1))))))
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                        (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            Mathlib.Tactic.Ring.Common.neg_zero)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                          (Eq.refl (Int.ofNat 0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
              (Mathlib.Tactic.Linarith.add_neg
                (Mathlib.Tactic.Linarith.add_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                  (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt hα1)
                    (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))))
                (Mathlib.Tactic.Linarith.sub_neg_of_lt a)))));
  Exists.intro (max 1 (3 * B + F))
    ⟨lt_of_lt_of_le zero_lt_one (le_max_left 1 (3 * B + F)), fun T a a_1 f M K a_2 hK0 hf hM hK =>
      let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
      id
        (have ordered := fun t₁ ht₁ t₂ ht₂ h12 x =>
          if he : t₁ = t₂ then
            Eq.ndrec (motive := fun t₂ =>
              t₂ ∈ Set.Icc 0 T →
                t₁ ≤ t₂ →
                  ‖fderiv ℝ (fderiv ℝ (u t₂)) x - fderiv ℝ (fderiv ℝ (u t₁)) x‖ ≤ (3 * B + F) * K * (t₂ - t₁) ^ (α / 2))
              (fun ht₂ h12 =>
                of_eq_true
                  (Eq.trans
                    (congr
                      (congrArg LE.le (Eq.trans (congrArg norm (sub_self (fderiv ℝ (fderiv ℝ (u t₁)) x))) norm_zero))
                      (Eq.trans
                        (congrArg (HMul.hMul ((3 * B + F) * K))
                          (Eq.trans (congrFun' (congrArg HPow.hPow (sub_self t₁)) (α / 2))
                            (Real.zero_rpow
                              (have this :=
                                Not.intro fun a =>
                                  Mathlib.Tactic.Linarith.lt_irrefl
                                    (Eq.mp
                                      (congrArg (fun _a => _a < 0)
                                        (Mathlib.Tactic.Ring.of_eq
                                          (Mathlib.Tactic.Ring.Common.add_congr
                                            (Mathlib.Tactic.Ring.Common.sub_congr
                                              (Mathlib.Tactic.Ring.cast_zero
                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                                (Eq.mpr
                                                  (id
                                                    (congrArg
                                                      (fun _a =>
                                                        α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                      (Eq.symm rfl)))
                                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                              (Mathlib.Tactic.Ring.Common.sub_pf
                                                (Mathlib.Tactic.Ring.Common.neg_add
                                                  (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                        (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                        (Eq.refl (Int.negOfNat 1)))))
                                                  Mathlib.Tactic.Ring.Common.neg_zero)
                                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                                  (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                                            (Mathlib.Tactic.Ring.Common.sub_congr
                                              (Mathlib.Tactic.Ring.Common.mul_congr
                                                (Mathlib.Tactic.Ring.cast_pos
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                                  (Eq.mpr
                                                    (id
                                                      (congrArg
                                                        (fun _a =>
                                                          α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                        (Eq.symm rfl)))
                                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                                (Mathlib.Tactic.Ring.Common.add_mul
                                                  (Mathlib.Tactic.Ring.Common.mul_add
                                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α (Nat.rawCast 1)
                                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                      (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                                  (Mathlib.Tactic.Ring.Common.zero_mul
                                                    (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                    (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                              (Mathlib.Tactic.Ring.Common.mul_congr
                                                (Mathlib.Tactic.Ring.cast_pos
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                                (Mathlib.Tactic.Ring.cast_zero
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                                (Mathlib.Tactic.Ring.Common.add_mul
                                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                                  (Mathlib.Tactic.Ring.Common.zero_mul 0)
                                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                                              (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                  (α ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero α (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                                    (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                    (Eq.refl (Int.ofNat 0)))))
                                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                                          (Mathlib.Tactic.Ring.cast_zero
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                                      (Mathlib.Tactic.Linarith.lt_of_lt_of_eq (Mathlib.Tactic.Linarith.sub_neg_of_lt hα)
                                        (Eq.mp
                                          (congrArg (fun _a => _a = 0)
                                            (Mathlib.Tactic.CancelDenoms.sub_subst
                                              (Mathlib.Tactic.CancelDenoms.div_subst rfl
                                                (Mathlib.Meta.NormNum.isNat_eq_true
                                                  (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                    (Mathlib.Meta.NormNum.isNNRat_div
                                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                        (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                          (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                                            (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                                            (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                                (Mathlib.Meta.NormNum.isNat_eq_true
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                              rfl))
                                          (Mathlib.Tactic.Linarith.mul_eq (sub_eq_zero_of_eq a)
                                            (Mathlib.Meta.NormNum.isNat_lt_true
                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))))));
                              this))))
                        (mul_zero ((3 * B + F) * K))))
                    (Std.le_refl._simp_1 0)))
              he ht₂ h12
          else
            have hlt := lt_of_le_of_ne h12 he;
            let H := fun r s =>
              ∫ (y : Poincare.ClosedSmoothModel 3),
                (f (s, x - y) - f (s, x)) •
                  (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) (r - s) y;
            have hi := fun r hr b hb hbr =>
              (intervalIntegrable_iff_integrableOn_Ioo_of_le hb enorm_ne_top enorm_ne_top).mpr
                (MeasureTheory.IntegrableOn.mono_set
                  (Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 hr hf hK x)
                  (Set.Ioo_subset_Ioo le_rfl hbr));
            have hsplit :=
              Eq.symm
                (intervalIntegral.integral_add_adjacent_intervals (hi t₂ ht₂ t₁ ht₁.left h12)
                  (IntervalIntegrable.trans (IntervalIntegrable.symm (hi t₂ ht₂ t₁ ht₁.left h12))
                    (hi t₂ ht₂ t₂ ht₂.left le_rfl)));
            have htail :=
              Eq.mp
                (congrArg
                  (LE.le
                    ‖∫ (s : ℝ) in t₁..t₂,
                        ∫ (y : Poincare.ClosedSmoothModel 3),
                          (f (s, x - y) - f (s, x)) • fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel (t₂ - s) z) y‖)
                  (congrArg
                    (HMul.hMul
                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) *
                          (2 / α) *
                        K))
                    (congrFun' (congrArg HPow.hPow (abs_of_nonneg (sub_nonneg.mpr h12))) (α / 2))))
                (Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound hα hα1 ht₁ ht₂ h12 hK x);
            have hoverlap :=
              if hsmall : t₁ ≤ t₂ - t₁ then
                have hn :=
                  Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le hα hα1 hK0 ht₁.left h12
                    (Eq.mpr (id (congrFun' (congrArg LE.le (sub_zero t₁)) (t₂ - t₁))) hsmall)
                    (fun s hs => hK s ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht₁.right⟩) x;
                have hn' :=
                  Eq.mpr
                    (eq_of_heq
                      ((fun α self a a_3 a' e'_4 =>
                          Eq.casesOn (motive := fun a_4 x => a' = a_4 → e'_4 ≍ x → (a ≤ a_3) ≍ (a ≤ a')) e'_4
                            (fun h =>
                              Eq.ndrec (motive := fun a' =>
                                ∀ (e_4 : a_3 = a'), e_4 ≍ Eq.refl a_3 → (a ≤ a_3) ≍ (a ≤ a'))
                                (fun e_4 h => HEq.refl (a ≤ a_3)) (Eq.symm h) e'_4)
                            (Eq.refl a') (HEq.refl e'_4))
                        ℝ Real.instLE ‖(∫ (s : ℝ) in 0..t₁, H t₂ s) - ∫ (s : ℝ) in 0..t₁, H t₁ s‖
                        (2 * B * K * (t₂ - t₁) ^ (α / 2))
                        ((2 *
                                ∫ (y : Poincare.ClosedSmoothModel 3),
                                  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α) *
                              (2 / α) *
                            K *
                          (t₂ - t₁) ^ (α / 2))
                        (id
                          (Mathlib.Tactic.Ring.of_eq
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                  (Mathlib.Tactic.Ring.Common.mul_congr
                                    (Mathlib.Tactic.Ring.Common.atom_pf
                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                        ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                      rfl
                                      (Eq.mpr
                                        (id
                                          (congrArg
                                            (fun _a =>
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 =
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1))))
                                    (Mathlib.Tactic.Ring.Common.div_congr
                                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                      (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                      (Mathlib.Tactic.Ring.Common.div_pf
                                        (Mathlib.Tactic.Ring.Common.inv_single
                                          (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                              (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                            (Eq.symm
                                                (Eq.mpr
                                                  (id
                                                    (congrArg
                                                      (fun _a =>
                                                        α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                                      (Eq.symm rfl)))
                                                  (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                              Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                          (Mathlib.Tactic.Ring.Common.zero_mul
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                    (Mathlib.Tactic.Ring.Common.add_mul
                                      (Mathlib.Tactic.Ring.Common.mul_add
                                        (Mathlib.Tactic.Ring.Common.mul_pf_left
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                          (Nat.rawCast 1)
                                          (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                        (Mathlib.Tactic.Ring.Common.mul_zero
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                            0)))
                                      (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                          0))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right
                                        (∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                        (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 4)))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                          0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                        0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                        0))))
                                (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left
                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                        ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                      (Nat.rawCast 1)
                                      (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 4))))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4)))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4)) +
                                        0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4)) +
                                      0))))
                              (Mathlib.Tactic.Ring.Common.atom_pf ((t₂ - t₁) ^ (α / 2)) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        ((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                          ((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                    (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right ((t₂ - t₁) ^ (α / 2)) (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 4)))))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                        Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 *
                                          (K ^ Nat.rawCast 1 *
                                            (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4))) +
                                      0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                        Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 *
                                        (K ^ Nat.rawCast 1 * (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4))) +
                                    0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.Common.mul_congr
                                  (Mathlib.Tactic.Ring.Common.mul_congr
                                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                    (Mathlib.Tactic.Ring.Common.atom_pf
                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                        ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                      rfl
                                      (Eq.mpr
                                        (id
                                          (congrArg
                                            (fun _a =>
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 =
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1))))
                                    (Mathlib.Tactic.Ring.Common.add_mul
                                      (Mathlib.Tactic.Ring.Common.mul_add
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                          (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                        (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2 +
                                            0)))
                                      (Mathlib.Tactic.Ring.Common.zero_mul
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1 +
                                          0))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 2 +
                                          0))))
                                  (Mathlib.Tactic.Ring.Common.div_congr
                                    (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                    (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                      (Eq.mpr
                                        (id
                                          (congrArg
                                            (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                    (Mathlib.Tactic.Ring.Common.div_pf
                                      (Mathlib.Tactic.Ring.Common.inv_single
                                        (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                          (Eq.symm
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                            Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                      (Mathlib.Tactic.Ring.Common.add_mul
                                        (Mathlib.Tactic.Ring.Common.mul_add
                                          (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                          (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                        (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_left
                                        (∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                        (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 4)))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                          0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                        0))))
                                (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left
                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                        ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                      (Nat.rawCast 1)
                                      (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 4))))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4)))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                            Nat.rawCast 1 *
                                          (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4)) +
                                        0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4)) +
                                      0))))
                              (Mathlib.Tactic.Ring.Common.atom_pf ((t₂ - t₁) ^ (α / 2)) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        ((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                          ((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                      ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α)
                                    (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                        (Mathlib.Tactic.Ring.Common.mul_pf_right ((t₂ - t₁) ^ (α / 2)) (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 4)))))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                        Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * (K ^ Nat.rawCast 1 * Nat.rawCast 4))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                          Nat.rawCast 1 *
                                        (α⁻¹ ^ Nat.rawCast 1 *
                                          (K ^ Nat.rawCast 1 *
                                            (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4))) +
                                      0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel 1 z) y‖ * ‖y‖ ^ α) ^
                                        Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 *
                                        (K ^ Nat.rawCast 1 * (((t₂ - t₁) ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4))) +
                                    0))))))))
                    hn;
                LE.le.trans hn'
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right
                      (le_of_not_gt fun a =>
                        Mathlib.Tactic.Linarith.lt_irrefl
                          (Eq.mp
                            (congrArg (fun _a => _a < 0)
                              (Mathlib.Tactic.Ring.of_eq
                                (Mathlib.Tactic.Ring.Common.add_congr
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                                    (Mathlib.Tactic.Ring.Common.mul_congr
                                      (Mathlib.Tactic.Ring.Common.atom_pf
                                        (∫ (y : Poincare.ClosedSmoothModel 3),
                                          ‖(fun t x =>
                                                  deriv
                                                    (fun r =>
                                                      (fun t x =>
                                                          fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                        r x)
                                                    t)
                                                1 y‖ *
                                            ‖y‖ ^ α)
                                        rfl
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a =>
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                        ‖(fun t x => deriv (fun r => (fun t x => ⋯) r x) t) 1 y‖ *
                                                          ‖y‖ ^ α) ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 1 =
                                                  (∫ (y : Poincare.ClosedSmoothModel 3),
                                                        ‖(fun t x => deriv (fun r => (fun t x => ⋯) r x) t) 1 y‖ *
                                                          ‖y‖ ^ α) ^
                                                      Nat.rawCast 1 *
                                                    _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          deriv
                                                            (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => ⋯) x) r x)
                                                            t)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 1))))
                                      (Mathlib.Tactic.Ring.Common.div_congr
                                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Tactic.Ring.Common.sub_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                          (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.sub_pf
                                            (Mathlib.Tactic.Ring.Common.neg_add
                                              (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                    (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                    (Eq.refl (Int.negOfNat 1)))))
                                              Mathlib.Tactic.Ring.Common.neg_zero)
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                                        (Mathlib.Tactic.Ring.Common.div_pf
                                          (Mathlib.Tactic.Ring.Common.atom_pf'
                                            (Eq.refl
                                              (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (Nat.rawCast 2 +
                                                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (Nat.rawCast 2 +
                                                              (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((Nat.rawCast 2 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((Nat.rawCast 2 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 2 +
                                                  0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              ((Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1 +
                                                0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2 +
                                                0)))))
                                      (Mathlib.Tactic.Ring.Common.add_mul
                                        (Mathlib.Tactic.Ring.Common.mul_add
                                          (Mathlib.Tactic.Ring.Common.mul_pf_left
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x =>
                                                      deriv
                                                        (fun r =>
                                                          (fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            r x)
                                                        t)
                                                    1 y‖ *
                                                ‖y‖ ^ α)
                                            (Nat.rawCast 1)
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right
                                              (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                              (Nat.rawCast 1)
                                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                          (Mathlib.Tactic.Ring.Common.mul_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          deriv
                                                            (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => ⋯) x) r x)
                                                            t)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 1))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                            deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ ⋯) x) r x) t)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                ((Nat.rawCast 2 +
                                                        (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 2) +
                                              0)))
                                        (Mathlib.Tactic.Ring.Common.zero_mul
                                          ((Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              Nat.rawCast 2 +
                                            0))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x =>
                                                          deriv
                                                            (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => ⋯) x) r x)
                                                            t)
                                                        1 y‖ *
                                                    ‖y‖ ^ α) ^
                                                Nat.rawCast 1 *
                                              ((Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 2) +
                                            0))))
                                    (Mathlib.Tactic.Ring.Common.sub_pf
                                      (Mathlib.Tactic.Ring.Common.neg_add
                                        (Mathlib.Tactic.Ring.Common.neg_mul
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x =>
                                                    deriv
                                                      (fun r =>
                                                        (fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          r x)
                                                      t)
                                                  1 y‖ *
                                              ‖y‖ ^ α)
                                          (Nat.rawCast 1)
                                          (Mathlib.Tactic.Ring.Common.neg_mul
                                            (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                            (Nat.rawCast 1)
                                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                                (Eq.refl (Int.negOfNat 2))))))
                                        Mathlib.Tactic.Ring.Common.neg_zero)
                                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                        ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x =>
                                                        deriv
                                                          (fun r =>
                                                            (fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              r x)
                                                          t)
                                                      1 y‖ *
                                                  ‖y‖ ^ α) ^
                                              Nat.rawCast 1 *
                                            ((Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                Nat.rawCast 1 *
                                              (Int.negOfNat 2).rawCast) +
                                          0))))
                                  (Mathlib.Tactic.Ring.Common.sub_congr
                                    (Mathlib.Tactic.Ring.Common.add_congr
                                      (Mathlib.Tactic.Ring.Common.mul_congr
                                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Tactic.Ring.Common.mul_congr
                                          (Mathlib.Tactic.Ring.Common.atom_pf
                                            (∫ (y : Poincare.ClosedSmoothModel 3),
                                              ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                    y‖ *
                                                ‖y‖ ^ α)
                                            rfl
                                            (Eq.mpr
                                              (id
                                                (congrArg
                                                  (fun _a =>
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x => fderiv ℝ (fderiv ℝ ⋯) x) 1 y‖ * ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        Nat.rawCast 1 =
                                                      (∫ (y : Poincare.ClosedSmoothModel 3),
                                                            ‖(fun t x => fderiv ℝ (fderiv ℝ ⋯) x) 1 y‖ * ‖y‖ ^ α) ^
                                                          Nat.rawCast 1 *
                                                        _a)
                                                  (Eq.symm rfl)))
                                              (Eq.refl
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))))
                                          (Mathlib.Tactic.Ring.Common.div_congr
                                            (Mathlib.Tactic.Ring.cast_pos
                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                            (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                            (Mathlib.Tactic.Ring.Common.div_pf
                                              (Mathlib.Tactic.Ring.Common.inv_single
                                                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                                  (Eq.symm
                                                      (Eq.mpr
                                                        (id
                                                          (congrArg
                                                            (fun _a =>
                                                              α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                                                α⁻¹ ^ Nat.rawCast 1 * _a)
                                                            (Eq.symm rfl)))
                                                        (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                                    Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                              (Mathlib.Tactic.Ring.Common.add_mul
                                                (Mathlib.Tactic.Ring.Common.mul_add
                                                  (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                    (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                                (Mathlib.Tactic.Ring.Common.zero_mul
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                                          (Mathlib.Tactic.Ring.Common.add_mul
                                            (Mathlib.Tactic.Ring.Common.mul_add
                                              (Mathlib.Tactic.Ring.Common.mul_pf_left
                                                (∫ (y : Poincare.ClosedSmoothModel 3),
                                                  ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                        y‖ *
                                                    ‖y‖ ^ α)
                                                (Nat.rawCast 1)
                                                (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                              (Mathlib.Tactic.Ring.Common.mul_zero
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  Nat.rawCast 1))
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                        ‖(fun t x =>
                                                                fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                              1 y‖ *
                                                          ‖y‖ ^ α) ^
                                                      Nat.rawCast 1 *
                                                    (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                                  0)))
                                            (Mathlib.Tactic.Ring.Common.zero_mul
                                              (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                                0))))
                                        (Mathlib.Tactic.Ring.Common.add_mul
                                          (Mathlib.Tactic.Ring.Common.mul_add
                                            (Mathlib.Tactic.Ring.Common.mul_pf_right
                                              (∫ (y : Poincare.ClosedSmoothModel 3),
                                                ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1
                                                      y‖ *
                                                  ‖y‖ ^ α)
                                              (Nat.rawCast 1)
                                              (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 4)))))
                                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                      ‖(fun t x =>
                                                              fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                            1 y‖ *
                                                        ‖y‖ ^ α) ^
                                                    Nat.rawCast 1 *
                                                  (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                                0)))
                                          (Mathlib.Tactic.Ring.Common.zero_mul
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) +
                                              0))
                                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                            ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 4) +
                                              0))))
                                      (Mathlib.Tactic.Ring.Common.mul_congr
                                        (Mathlib.Tactic.Ring.Common.atom_pf
                                          (∫ (y : Poincare.ClosedSmoothModel 3),
                                            ‖(fun t x =>
                                                    deriv
                                                      (fun r =>
                                                        (fun t x =>
                                                            fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                          r x)
                                                      t)
                                                  1 y‖ *
                                              ‖y‖ ^ α)
                                          rfl
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x => deriv (fun r => ⋯ r x) t) 1 y‖ * ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 1 =
                                                    (∫ (y : Poincare.ClosedSmoothModel 3),
                                                          ‖(fun t x => deriv (fun r => ⋯ r x) t) 1 y‖ * ‖y‖ ^ α) ^
                                                        Nat.rawCast 1 *
                                                      _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl
                                              ((∫ (y : Poincare.ClosedSmoothModel 3),
                                                    ‖(fun t x =>
                                                            deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ ⋯) x) r x) t)
                                                          1 y‖ *
                                                      ‖y‖ ^ α) ^
                                                  Nat.rawCast 1 *
                                                Nat.rawCast 1))))
                                        (Mathlib.Tactic.Ring.Common.div_congr
                                          (Mathlib.Tactic.Ring.cast_pos
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                          (Mathlib.Tactic.Ring.Common.sub_congr
                                            (Mathlib.Tactic.Ring.cast_pos
                                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                            (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                            (Mathlib.Tactic.Ring.Common.sub_pf
                                              (Mathlib.Tactic.Ring.Common.neg_add
                                                (Mathlib.Tactic.Ring.Common.neg_mul α (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                                      (Mathlib.Meta.NormNum.IsNat.to_isInt
                                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                                      (Eq.refl (Int.negOfNat 1)))))
                                                Mathlib.Tactic.Ring.Common.neg_zero)
                                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                                  (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                                          (Mathlib.Tactic.Ring.Common.div_pf
                                            (Mathlib.Tactic.Ring.Common.atom_pf'
                                              (Eq.refl
                                                (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹)
                                              rfl
                                              (Eq.mpr
                                                (id
                                                  (congrArg
                                                    (fun _a =>
                                                      (Nat.rawCast 2 +
                                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                            Nat.rawCast 1 *
                                                          Nat.rawCast 1 =
                                                        (Nat.rawCast 2 +
                                                                (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                            Nat.rawCast 1 *
                                                          _a)
                                                    (Eq.symm rfl)))
                                                (Eq.refl
                                                  ((Nat.rawCast 2 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      Nat.rawCast 1 *
                                                    Nat.rawCast 1))))
                                            (Mathlib.Tactic.Ring.Common.add_mul
                                              (Mathlib.Tactic.Ring.Common.mul_add
                                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                                  (Nat.rawCast 2 + (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                                  (Nat.rawCast 1)
                                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                                  ((Nat.rawCast 2 +
                                                            (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                        Nat.rawCast 1 *
                                                      Nat.rawCast 2 +
                                                    0)))
                                              (Mathlib.Tactic.Ring.Common.zero_mul
                                                ((Nat.rawCast 2 +
                                                          (α ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                                      ⋯ *
                                                    ⋯ +
                                                  ⋯))
                                              ⋯)))
                                        ⋯)
                                      ⋯)
                                    ⋯ ⋯)
                                  ⋯)
                                ⋯))
                            ⋯))
                      ⋯)
                    ⋯)
              else ⋯;
            ⋯;
        ⋯)⟩
theorem Poincare.HeatDuhamelHessianDifferentiation.duhamel_hessian_bound : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                        (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                          (∀ t ∈ Set.Icc 0 T,
                              ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                            (∀ (x : Poincare.ClosedSmoothModel 3), u 0 x = 0) ∧
                              ∀ t ∈ Set.Icc 0 T,
                                ∀ (x : Poincare.ClosedSmoothModel 3),
                                  ContDiff ℝ 2 (u t) ∧
                                    MeasureTheory.IntegrableOn
                                        (fun s =>
                                          ∫ (y : Poincare.ClosedSmoothModel 3),
                                            (f (s, x - y) - f (s, x)) •
                                              (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                (t - s) y)
                                        (Set.Ioo 0 t) MeasureTheory.volume ∧
                                      fderiv ℝ (fderiv ℝ (u t)) x =
                                          ∫ (s : ℝ) in 0..t,
                                            ∫ (y : Poincare.ClosedSmoothModel 3),
                                              (f (s, x - y) - f (s, x)) •
                                                (fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x)
                                                  (t - s) y ∧
                                        ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C * K * t ^ (α / 2) :=
fun α hα hα1 =>
  let J :=
    ∫ (y : Poincare.ClosedSmoothModel 3),
      ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => Poincare.heatKernel t z) x) 1 y‖ * ‖y‖ ^ α;
  Exists.intro (max 1 (J * (2 / α)))
    ⟨lt_of_lt_of_le zero_lt_one (le_max_left 1 (J * (2 / α))), fun T a a_1 f M K a_2 hK0 hf hM hK =>
      id
        ⟨fun x => intervalIntegral.integral_same, fun t ht x =>
          ⟨Poincare.HeatDuhamelHessianDifferentiation.contDiff_two_duhamel hα hα1 ht hf hM hK,
            ⟨Poincare.HeatDuhamelSpatialHolderHessian.integrableOn_cancelled_hessian_time hα hα1 ht hf hK x,
              ⟨Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x,
                Eq.mpr
                  (id
                    (congrArg (fun _a => ‖_a‖ ≤ max 1 (J * (2 / α)) * K * t ^ (α / 2))
                      (Poincare.HeatDuhamelHessianDifferentiation.hessian_duhamel_eq_integral hα hα1 ht hf hM hK x)))
                  (Trans.trans
                    (Trans.trans
                      (Poincare.HeatDuhamelSpatialHolderHessian.norm_integral_cancelled_hessian_time_le hα hα1 ht.left
                        (fun s hs => hK s ⟨LT.lt.le hs.left, LE.le.trans (LT.lt.le hs.right) ht.right⟩) x)
                      (Mathlib.Tactic.Ring.of_eq
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right J (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (K ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (J ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                            (Mathlib.Tactic.Ring.Common.div_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_pf
                                (Mathlib.Tactic.Ring.Common.inv_single
                                  (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                        (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                    (Eq.symm
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a => α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                      Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * Nat.rawCast 1)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf J rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => J ^ Nat.rawCast 1 * Nat.rawCast 1 = J ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (J ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.atom_pf α rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => α ^ Nat.rawCast 1 * Nat.rawCast 1 = α ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (α ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl α⁻¹)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                          (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                      (Eq.symm
                                          (Eq.mpr
                                            (id
                                              (congrArg
                                                (fun _a =>
                                                  α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 = α⁻¹ ^ Nat.rawCast 1 * _a)
                                                (Eq.symm rfl)))
                                            (Eq.refl (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1))) ▸
                                        Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (J ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                            (Mathlib.Tactic.Ring.Common.atom_pf K rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => K ^ Nat.rawCast 1 * Nat.rawCast 1 = K ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (K ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right K (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (K ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2)) + 0))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (t ^ (α / 2)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    (t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (t ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left K (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left J (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left α⁻¹ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (t ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (K ^ Nat.rawCast 1 * (J ^ Nat.rawCast 1 * (α⁻¹ ^ Nat.rawCast 1 * Nat.rawCast 2))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (K ^ Nat.rawCast 1 *
                                    (J ^ Nat.rawCast 1 *
                                      (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (K ^ Nat.rawCast 1 *
                                  (J ^ Nat.rawCast 1 *
                                    (α⁻¹ ^ Nat.rawCast 1 * ((t ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2))) +
                                0))))))
                    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 (J * (2 / α))) hK0)
                      (Real.rpow_nonneg ht.left (α / 2))))⟩⟩⟩⟩⟩
def Poincare.ParabolicHolder.HasHolderBound.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup E] → [NormedAddCommGroup F] → ℝ → Set (ℝ × E) → (ℝ × E → F) → ℝ → Prop :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] α S f K =>
  ∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * Poincare.ParabolicHolder.parabolicDist p q ^ α
def Poincare.ParabolicHolder.cylinder.{u_1} : {E : Type u_1} → ℝ → Set (ℝ × E) :=
fun {E} T => Set.Icc 0 T ×ˢ Set.univ
def Poincare.ParabolicHolder.parabolicDist.{u_1} : {E : Type u_1} → [NormedAddCommGroup E] → ℝ × E → ℝ × E → ℝ :=
fun {E} [NormedAddCommGroup E] p q => ‖p.2 - q.2‖ + √|p.1 - q.1|
Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z
Real.rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z
Real.sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / 2)
norm_sub_le.{u_5} {E : Type u_5} [SeminormedAddGroup E] (a b : E) : ‖a - b‖ ≤ ‖a‖ + ‖b‖
```

</details>

### lemma1

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.

<details><summary>Actual output; exit 1</summary>

```text
Poincare/Global/DuhamelParabolicHolderSeminorm.lean:26:35: error: unexpected token ':='; expected ')', ',' or ':'
```

</details>

### lemma1-retry

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.

<details><summary>Actual output; exit 0</summary>

```text
```

</details>

### first-audit

<details><summary>Probe source</summary>

```lean
import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.ParabolicHolderSpace

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.DuhamelParabolicHolderSeminorm

local notation "E" => Poincare.ClosedSmoothModel 3

/-- Spatial and temporal Hessian estimates give the parabolic Hölder bound. -/
theorem duhamel_hessian_parabolic_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := by
  intro α hα hα1
  obtain ⟨C₁, hC₁, hspace⟩ :=
    HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1
  obtain ⟨C₂, hC₂, htime⟩ :=
    HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 p.2 q.2
  have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 q.1 hq.1 q.2
  have hspow : ‖p.2 - q.2‖ ^ α ≤ ParabolicHolder.parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htpow : |p.1 - q.1| ^ (α / 2) ≤ ParabolicHolder.parabolicDist p q ^ α := by
    calc
      |p.1 - q.1| ^ (α / 2) = (Real.sqrt |p.1 - q.1|) ^ α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ ParabolicHolder.parabolicDist p q ^ α :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
        ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
        (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
    _ ≤ C₁ * K * ‖p.2 - q.2‖ ^ α + C₂ * K * |p.1 - q.1| ^ (α / 2) :=
      add_le_add hs ht
    _ ≤ C₁ * K * ParabolicHolder.parabolicDist p q ^ α +
        C₂ * K * ParabolicHolder.parabolicDist p q ^ α :=
      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
    _ = (C₁ + C₂) * K * ParabolicHolder.parabolicDist p q ^ α := by ring

end Poincare.DuhamelParabolicHolderSeminorm

#print axioms Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
```

</details>

<details><summary>Actual output; exit 0</summary>

```text
'Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

</details>

### lemma2

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.

<details><summary>Actual output; exit 0</summary>

```text
```

</details>

### final-audit

<details><summary>Probe source</summary>

```lean
import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.ParabolicHolderSpace

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.DuhamelParabolicHolderSeminorm

local notation "E" => Poincare.ClosedSmoothModel 3

/-- Spatial and temporal Hessian estimates give the parabolic Hölder bound. -/
theorem duhamel_hessian_parabolic_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := by
  intro α hα hα1
  obtain ⟨C₁, hC₁, hspace⟩ :=
    HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1
  obtain ⟨C₂, hC₂, htime⟩ :=
    HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 p.2 q.2
  have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 q.1 hq.1 q.2
  have hspow : ‖p.2 - q.2‖ ^ α ≤ ParabolicHolder.parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htpow : |p.1 - q.1| ^ (α / 2) ≤ ParabolicHolder.parabolicDist p q ^ α := by
    calc
      |p.1 - q.1| ^ (α / 2) = (Real.sqrt |p.1 - q.1|) ^ α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ ParabolicHolder.parabolicDist p q ^ α :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
        ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
        (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
    _ ≤ C₁ * K * ‖p.2 - q.2‖ ^ α + C₂ * K * |p.1 - q.1| ^ (α / 2) :=
      add_le_add hs ht
    _ ≤ C₁ * K * ParabolicHolder.parabolicDist p q ^ α +
        C₂ * K * ParabolicHolder.parabolicDist p q ^ α :=
      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
    _ = (C₁ + C₂) * K * ParabolicHolder.parabolicDist p q ^ α := by ring

/-- The Duhamel Hessian satisfies the landed parabolic Hölder predicate. -/
theorem hasHolderBound_duhamel_hessian :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder («E» := E) T)
    (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K) := by
  intro α hα hα1
  obtain ⟨C, hC, hbound⟩ := duhamel_hessian_parabolic_holder α hα hα1
  exact ⟨C, hC, hbound⟩

end Poincare.DuhamelParabolicHolderSeminorm

open Poincare
local notation "E" => Poincare.ClosedSmoothModel 3
example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
#print axioms Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder
#print axioms Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian
#check Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian
```

</details>

<details><summary>Actual output; exit 0</summary>

```text
'Poincare.DuhamelParabolicHolderSeminorm.duhamel_hessian_parabolic_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.DuhamelParabolicHolderSeminorm.hasHolderBound_duhamel_hessian (α : ℝ) :
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × E → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Icc 0 T ×ˢ univ) →
                        (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                          (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            have u := fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x;
                            ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder T)
                              (fun p => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K)
```

</details>

### Name searches

Names were checked with `rg -n` in the landed modules and Mathlib.

```text
Poincare/Global/ParabolicHolderSpace.lean:29:def parabolicDist (p q : ℝ × E) : ℝ :=
Poincare/Global/ParabolicHolderSpace.lean:47:def cylinder (T : ℝ) : Set (ℝ × E) := Icc 0 T ×ˢ univ
Poincare/Global/ParabolicHolderSpace.lean:49:def HasHolderBound (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) (K : ℝ) : Prop :=
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:267:theorem duhamel_hessian_spatial_holder_of_time_le_dist_sq {α T t M K : ℝ}
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:638:theorem duhamel_hessian_spatial_holder :
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:677:  · exact (duhamel_hessian_spatial_holder_of_time_le_dist_sq hα hα1 ht hK0 hf hM hK x z htime).trans
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:580:theorem duhamel_hessian_time_holder :
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:418:theorem duhamel_hessian_bound :
```

```text
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:195:  obtain hx | hx := (abs_nonneg x).eq_or_lt'
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:990:  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1010:  exacts [norm_nonneg _, (neg_pi_lt_arg _).le, arg_le_pi _]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1015:    ← Real.sqrt_eq_rpow, sin_half_eq_sqrt, ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1023:    ← Real.sqrt_eq_rpow, sin_half_eq_neg_sqrt, mul_neg, ← sqrt_mul (norm_nonneg _),
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1030:    ← Real.sqrt_eq_rpow, abs_mul, abs_of_nonneg (sqrt_nonneg _), abs_sin_half,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1031:    ← sqrt_mul (norm_nonneg _), ← mul_div_assoc, mul_sub, mul_one, norm_mul_cos_arg]
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:100:  /-- Do not use this. Use `_root_.mul_le_mul_of_nonneg_left` instead. -/
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:101:  protected mul_le_mul_of_nonneg_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b c : α⦄ (hbc : b ≤ c) : a * b ≤ a * c
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:169:  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2 hbc
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:177:  elim a _b _c hbc := PosMulMono.mul_le_mul_of_nonneg_left a.2.le hbc
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:200:    PosMulMono α where mul_le_mul_of_nonneg_left _ _ _ _ := ‹MulLeftMono α›.elim _
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:226:theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:227:  PosMulMono.mul_le_mul_of_nonneg_left ha hbc
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:261:  mul_le_mul_of_nonneg_left a ha b c hbc := by
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:262:    rw [← le, mul, mul]; exact mul_le_mul_of_nonneg_left (le.2 hbc) (by rwa [← zero, le])
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:314:  (mul_le_mul_of_nonneg_left h₂ a0).trans (mul_le_mul_of_nonneg_right h₁ d0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:318:  (mul_le_mul_of_nonneg_right h₁ c0).trans (mul_le_mul_of_nonneg_left h₂ b0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:334:  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:340:  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:361:  (mul_le_mul_of_nonneg_left hle a0).trans h
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:365:  (mul_le_mul_of_nonneg_left hle a0).trans_lt h
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:369:  h.trans (mul_le_mul_of_nonneg_left hle b0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:373:  h.trans_le (mul_le_mul_of_nonneg_left hle b0)
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:447:  mul_le_mul_of_nonneg_left _a ha _b _c hbc :=
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:456:    fun a _b _c hbc ↦ mul_le_mul_of_nonneg_left hbc a.2
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:97:@[to_additive norm_add_le /-- **Triangle inequality** for the norm. -/]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:104:  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:123:@[to_additive (attr := simp) norm_nonneg]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:124:theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:128:attribute [bound] norm_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:129:attribute [grind .] norm_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:132:theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:159:  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:379:  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:403:  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:409:  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:661:  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:805:  m.le_sum_of_subadditive norm norm_zero.le norm_add_le
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:831:  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:921:  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:997:lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1007:  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1020:  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1088:    | none => return .nonnegative q(norm_nonneg' $a)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1110:    | none => return .nonnegative q(norm_nonneg $a)
```

```text
34:  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
43:    Real.rpow_le_rpow (norm_nonneg _)
44:      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
48:        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
52:        Real.rpow_le_rpow (Real.sqrt_nonneg _)
53:          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
58:      simpa only [sub_add_sub_cancel] using norm_add_le
62:      add_le_add hs ht
65:      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
66:        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
```

### Token and whitespace checks

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelParabolicHolderSeminorm.lean
# exit 1; stdout and stderr empty
git diff --check
# exit 0; stdout and stderr empty
```

## Final proof diff

```diff
diff --git a/Poincare/Global/DuhamelParabolicHolderSeminorm.lean b/Poincare/Global/DuhamelParabolicHolderSeminorm.lean
new file mode 100644
index 00000000..d2d9deb4
--- /dev/null
+++ b/Poincare/Global/DuhamelParabolicHolderSeminorm.lean
@@ -0,0 +1,85 @@
+import Poincare.Global.HeatDuhamelHessianTimeHolder
+import Poincare.Global.HeatDuhamelHessianSpatialHolder
+import Poincare.Global.ParabolicHolderSpace
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Interval
+
+namespace Poincare.DuhamelParabolicHolderSeminorm
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+
+/-- Spatial and temporal Hessian estimates give the parabolic Hölder bound. -/
+theorem duhamel_hessian_parabolic_holder :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
+    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
+      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := by
+  intro α hα hα1
+  obtain ⟨C₁, hC₁, hspace⟩ :=
+    HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1
+  obtain ⟨C₂, hC₂, htime⟩ :=
+    HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1
+  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
+  intro T hT hT1 f M K hM hK hf hfM hfK
+  dsimp only
+  intro p hp q hq
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 p.2 q.2
+  have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 q.1 hq.1 q.2
+  have hspow : ‖p.2 - q.2‖ ^ α ≤ ParabolicHolder.parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _)
+      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
+  have htpow : |p.1 - q.1| ^ (α / 2) ≤ ParabolicHolder.parabolicDist p q ^ α := by
+    calc
+      |p.1 - q.1| ^ (α / 2) = (Real.sqrt |p.1 - q.1|) ^ α := by
+        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
+        congr 1
+        ring
+      _ ≤ ParabolicHolder.parabolicDist p q ^ α :=
+        Real.rpow_le_rpow (Real.sqrt_nonneg _)
+          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
+  calc
+    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
+        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
+        ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
+      simpa only [sub_add_sub_cancel] using norm_add_le
+        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
+        (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
+    _ ≤ C₁ * K * ‖p.2 - q.2‖ ^ α + C₂ * K * |p.1 - q.1| ^ (α / 2) :=
+      add_le_add hs ht
+    _ ≤ C₁ * K * ParabolicHolder.parabolicDist p q ^ α +
+        C₂ * K * ParabolicHolder.parabolicDist p q ^ α :=
+      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
+        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
+    _ = (C₁ + C₂) * K * ParabolicHolder.parabolicDist p q ^ α := by ring
+
+/-- The Duhamel Hessian satisfies the landed parabolic Hölder predicate. -/
+theorem hasHolderBound_duhamel_hessian :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder («E» := E) T)
+    (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (u p.1)) p.2) (C * K) := by
+  intro α hα hα1
+  obtain ⟨C, hC, hbound⟩ := duhamel_hessian_parabolic_holder α hα hα1
+  exact ⟨C, hC, hbound⟩
+
+end Poincare.DuhamelParabolicHolderSeminorm
```
