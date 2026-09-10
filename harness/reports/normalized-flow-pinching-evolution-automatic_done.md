# Automatic normalized pinching evolution

Date: 2026-09-10. Base: `babccd85e15cdd3a58cd922b1118bf8d1dff3f0c`.
Branch: `worker/normalized-flow-pinching-evolution-automatic`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

Both requested evolution predicates are proved at the frozen types, with the invariant cubic reaction trace. The module is `Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`, in namespace `Poincare.NormalizedFlowPinchingEvolutionAutomatic`.

- `satisfiesPinchingQuotientEvolutionAt`, committed as `71e0329f`, constructs ordinary quotient evolution.
- `satisfiesTracelessPinchingImprovementEvolutionAt`, committed as `c2e6a747a04eaa2e1fe18e2ab046f93ec2206121`, constructs improved evolution for `0 < delta ≤ 1`.

Each theorem uses all-real-time joint C³ metric entries, the normalized equation only on the specified slice, and positive scalar curvature on that slice. There is no raw evolution premise, extra connection instance, scalar equation premise, negative-time flow equation, or new definition. The proof introduces `Nonempty M` locally using the point being proved. The ambient hypotheses omit the unused simply-connected assumption from the frozen target; both exact target assignments still elaborate.

The ordinary proof obtains lower-Ricci evolution, its motion trace `C - (4/3) r N`, and normalized scalar evolution `R_t = ΔR + 2N - (2/3) r R`. It reconstructs the spatial regularity needed by the existing completed-square identity, differentiates `N/R²`, and proves the normalization cancellation by field algebra.

The improved proof uses the landed exact evolution of `U = |Ric°|²`, the normalized scalar equation, and the real-power quotient derivative. The existing spatial expansion and numerator bridge give the drift. Local field algebra identifies the full derivative with spatial terms, the invariant cubic reaction, the gradient numerator divided by `R^(4-delta)`, and `-(2/3) delta r F_delta`. The landed gradient estimate makes the gradient contribution nonpositive. Compact slice positivity gives a positive mean scalar; nonnegative U and positive R make the normalization contribution nonpositive. These two inequalities produce the unchanged improved predicate.

Only the new Lean module and this requested report are delivered. Existing Lean files, `Poincare.lean`, frozen contracts, and HANDOFF remain unchanged under the task-specific scope. The branch was initially clean, and `git status --short --branch`, `git worktree list --porcelain`, and `git rev-parse HEAD` were checked before editing. README, HANDOFF top, PROJECT_MAP, the task, the specified survey sections and Appendix C, and neighboring source definitions/imports were read. No merge, task acceptance, root build, or service operation was performed.

First action for the orchestrator: independently run `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean` on proof commit `c2e6a747a04eaa2e1fe18e2ab046f93ec2206121`, then reproduce the exact-target/dependency probe below. Acceptance and integration remain the orchestrator's decision.

## Gate results

| Command | Exit | Actual output |
| --- | --- | --- |
| `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean` | 0 | Empty, no warnings |
| Exact-target assignments and dependency prints | 0 | Full output below; both lists are exactly `[propext, Classical.choice, Quot.sound]` |
| `rg -n '\b(sorry\|admit\|axiom\|opaque)\b\|native_decide' Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean` | 1 | Empty, as required for no matches; the exact executed regex is below |
| `git diff --check` | 0 | Empty |

Exact source scan command:

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean
```

## Exact frozen target assignments and declaration dependencies

The probe concatenates the final module source with the following suffix and runs `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean`. Thus it checks the edited source directly without using a stale olean for the new module. Both proposition expressions are copied from the first two targets in the survey's Appendix C.

```lean

namespace ExactTargetProbe
open Poincare
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

example : (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ),
  (∀ s x, MetricEntriesJointContDiffAt gt s x 3) →
  (∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt t).scalarAt x) →
  ∀ x, ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
    gt t x ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x)) :=
  fun gt t hJoint hFlow hRpos x ↦
  Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt
    (gt := gt) (t₀ := t) hJoint hFlow hRpos x

example : (∀ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t delta : ℝ),
  (∀ s x, MetricEntriesJointContDiffAt gt s x 3) →
  (∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt t).scalarAt x) → 0 < delta → delta ≤ 1 →
  ∀ x, ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
    gt t x delta ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x)) :=
  fun gt t delta hJoint hFlow hRpos hdelta hdelta1 x ↦
  Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt
    (gt := gt) (t₀ := t) (δ := delta) hJoint hFlow hRpos hdelta hdelta1 x

end ExactTargetProbe

#check @Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt
#print axioms Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt

#check @Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt
#print axioms Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt
```

Actual output, exit 0:

```text
@Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ},
  (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        ∀ (x : M),
          Poincare.ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
            ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t₀ δ : ℝ},
  (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        0 < δ →
          δ ≤ 1 →
            ∀ (x : M),
              Poincare.ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt t₀ x δ
                ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Probe record

The Appendix C `partial-dependencies.lean` was extracted verbatim from the survey into `/tmp/normalized-flow-pinching-evolution-automatic/partial-dependencies.lean` and successfully elaborated before implementation. `targets.lean` and `residuals.lean` were also extracted; their full proposition inventories were not rerun. The two relevant targets were proved by the final assignment probe above.

All Lean invocations in this attempt are recorded below, including failed elaborations and linter warnings. Empty fenced output means the command emitted no text. The temporary evidence directory is `/tmp/normalized-flow-pinching-evolution-automatic`.

<details>
<summary>Appendix C reproduction, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/partial-dependencies.lean`.
Evidence log: `reproduction.log`.

```text
/tmp/normalized-flow-pinching-evolution-automatic/partial-dependencies.lean:38:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/normalized-flow-pinching-evolution-automatic/partial-dependencies.lean:82:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.constantRateFromGap`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.PinchingReactionSurvey.movingDerivatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.meanFloorFromEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.constantRateFromGap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

</details>

<details>
<summary>Initial consumer types and derivative signatures, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/types.lean`.
Evidence log: `types.log`.

```text
theorem Poincare.hamilton_pinching_preserved.{u} : ∀ {n : ℕ} {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : T2Space M] [inst_2 : ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [inst_3 : IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M] [Nonempty M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
  [inst_6 : ∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1],
  n = 3 →
    0 ≤ T →
      (Continuous ↿fun τ x => (gt (t₀ + τ)).pinchingQuotientAt x) →
        (∀ τ ∈ Set.Icc 0 T,
            ∀ (x : M),
              ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2
                (fun y => (gt (t₀ + τ)).pinchingQuotientAt y) x) →
          (∀ τ ∈ Set.Icc 0 T,
              ∀ (x : M),
                Poincare.ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt (t₀ + τ) x
                  ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x)) →
            ∀ τ ∈ Set.Icc 0 T, Poincare.pinchingMaximumTrack gt t₀ τ ≤ Poincare.pinchingMaximumTrack gt t₀ 0 :=
fun {n} {M} [⋯] [⋯] [⋯] [⋯] [⋯] [⋯] {gt} {t₀ T} [⋯] hn hT0 hQ_cont hQ₂ hEvol =>
  let Q := fun τ x => (gt (t₀ + τ)).pinchingQuotientAt x;
  let C := Poincare.pinchingMaximumTrack gt t₀ 0;
  let u := fun τ x => C - Q τ x;
  let Q' := fun τ x => if hτ : τ ∈ Set.Icc 0 T then Classical.choose (hEvol τ hτ x).right else 0;
  let u' := fun τ x => -Q' τ x;
  let L := fun τ f x =>
    let g := gt (t₀ + τ);
    g.laplacianAt f x + 2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt f x);
  have hQd := fun x τ hτ =>
    have hτpair := ⟨hτ.left, hτ.right⟩;
    have hspec := Classical.choose_spec (hEvol τ hτpair x).right;
    have hbase :=
      Eq.mpr
        (id
          (HasDerivAt.congr_simp (fun t => (gt t).pinchingQuotientAt x) (fun t => (gt t).pinchingQuotientAt x)
            (Eq.refl fun t => (gt t).pinchingQuotientAt x) (Q' τ x)
            (Classical.choose
              (hEvol τ
                  (Eq.mpr_prop Set.mem_Icc._simp_1
                    (of_eq_true
                      (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True))))
                  x).right)
            (Eq.trans
              (congrFun'
                (congrFun'
                  (funext fun τ =>
                    funext fun x =>
                      dite_congr Set.mem_Icc._simp_1
                        (fun h => Eq.refl (Classical.choose (hEvol τ (Eq.mpr_prop Set.mem_Icc._simp_1 h) x).right))
                        fun h => Eq.refl 0)
                  τ)
                x)
              (dite_cond_eq_true
                (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True))))
            (t₀ + τ) (t₀ + τ) (Eq.refl (t₀ + τ))))
        hspec.left;
    have hshift := HasDerivAt.const_add t₀ (hasDerivAt_id τ);
    id
      (Eq.mp
        (HasDerivAt.congr_simp ((fun t => (gt t).pinchingQuotientAt x) ∘ HAdd.hAdd t₀)
          ((fun t => (gt t).pinchingQuotientAt x) ∘ HAdd.hAdd t₀)
          (Eq.refl ((fun t => (gt t).pinchingQuotientAt x) ∘ HAdd.hAdd t₀)) (Q' τ x * 1) (Q' τ x) (mul_one (Q' τ x)) τ τ
          (Eq.refl τ))
        (HasDerivAt.comp τ hbase hshift));
  have hud := fun x τ hτ =>
    have hconst := hasDerivAt_const τ C;
    id
      (Eq.mp
        (HasDerivAt.congr_simp ((fun x => C) - fun s => Q s x) ((fun x => C) - fun s => Q s x)
          (Eq.refl ((fun x => C) - fun s => Q s x)) (0 - Q' τ x) (-Q' τ x) (zero_sub (Q' τ x)) τ τ (Eq.refl τ))
        (HasDerivAt.sub hconst (hQd x τ hτ)));
  have hQ0₂ := fun x =>
    Eq.mp
      (congrFun'
        (congrArg (ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2)
          (funext fun y =>
            Poincare.ClosedSmoothRiemannianMetric.pinchingQuotientAt.congr_simp (gt (t₀ + 0)) (gt t₀)
              (congrArg gt (add_zero t₀)) y y (Eq.refl y)))
        x)
      (hQ₂ 0 ⟨le_refl 0, hT0⟩ x);
  have h0point := fun x =>
    have hle := Poincare.pinchingQuotientAt_le_pinchingMaximumAt (gt t₀) hQ0₂ x;
    Eq.mpr
      (id
        (Eq.trans
          (Eq.trans
            (congrArg (LE.le 0)
              (Eq.trans
                (congrFun'
                  (congrFun'
                    (funext fun τ =>
                      funext fun x =>
                        congrFun'
                          (congrArg HSub.hSub
                            (Poincare.pinchingMaximumAt.congr_simp (gt (t₀ + 0)) (gt t₀) (congrArg gt (add_zero t₀))))
                          ((gt (t₀ + τ)).pinchingQuotientAt x))
                    0)
                  x)
                (congrArg (HSub.hSub (Poincare.pinchingMaximumAt (gt t₀)))
                  (Poincare.ClosedSmoothRiemannianMetric.pinchingQuotientAt.congr_simp (gt (t₀ + 0)) (gt t₀)
                    (congrArg gt (add_zero t₀)) x x (Eq.refl x)))))
            sub_nonneg._simp_1)
          ge_iff_le._simp_1))
      (Eq.mp sub_nonneg._simp_1 (sub_nonneg.mpr hle));
  have hQtoU₂ := fun τ hτ x =>
    have hconst := contMDiffAt_const;
    id (ContMDiffAt.sub hconst (hQ₂ τ hτ x));
  have hlap_add_const := fun τ hτ k x =>
    let g := gt (t₀ + τ);
    have hf := hQtoU₂ τ hτ;
    have hk := fun x => contMDiffAt_const;
    have hlap :=
      id
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = g.laplacianAt (u τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_add' g hf hk)))
          (Eq.mpr
            (id
              (congrArg (fun _a => g.laplacianAt (u τ) x + _a = g.laplacianAt (u τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const g k x)))
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (u τ) x) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                            g.laplacianAt (u τ) x ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
              (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (u τ) x) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a =>
                        g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                          g.laplacianAt (u τ) x ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)))))));
    have hgrad :=
      id
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = g.gradientAt (u τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g (ContMDiffAt.mdifferentiableAt (hf x) two_ne_zero)
                mdifferentiableAt_const)))
          (Eq.mpr
            (id
              (congrArg (fun _a => g.gradientAt (u τ) x + _a = g.gradientAt (u τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const g k x)))
            (of_eq_true
              (Eq.trans (congrFun' (congrArg Eq (add_zero (g.gradientAt (u τ) x))) (g.gradientAt (u τ) x))
                (eq_self (g.gradientAt (u τ) x))))));
    id
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a +
                  2 / g.scalarAt x *
                    ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (fun y => u τ y + k) x) =
                g.laplacianAt (u τ) x +
                  2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x))
            hlap))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                g.laplacianAt (u τ) x + 2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a =
                  g.laplacianAt (u τ) x +
                    2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x))
              hgrad))
          (Eq.refl
            (g.laplacianAt (u τ) x +
              2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x)))));
  have hsuper := fun τ hτ x =>
    let g := gt (t₀ + τ);
    have hfQ := fun y => id (hQ₂ τ hτ y);
    have hfU := hQtoU₂ τ hτ;
    have hτpair := ⟨hτ.left, hτ.right⟩;
    have hspec := Classical.choose_spec (hEvol τ hτpair x).right;
    have hRpos := id (hEvol τ hτ x).left;
    have hQineq :=
      Eq.mpr
        (id
          (congrFun'
            (congrArg LE.le
              (Eq.trans
                (congrFun'
                  (congrFun'
                    (funext fun τ =>
                      funext fun x =>
                        dite_congr Set.mem_Icc._simp_1
                          (fun h => Eq.refl (Classical.choose (hEvol τ (Eq.mpr_prop Set.mem_Icc._simp_1 h) x).right))
                          fun h => Eq.refl 0)
                    τ)
                  x)
                (dite_cond_eq_true
                  (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True)))))
            ((gt (t₀ + τ)).laplacianAt (fun x => (gt (t₀ + τ)).pinchingQuotientAt x) x +
                  (gt (t₀ + τ)).pinchingQuotientGradientDrift3At x +
                (gt (t₀ + τ)).pinchingGradientDampingAt x +
              2 / (gt (t₀ + τ)).scalarAt x ^ 4 *
                (gt (t₀ + τ)).pinchingReactionRemainderAt x
                  ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x))))
        hspec.right;
    have hdamp := Poincare.ClosedSmoothRiemannianMetric.pinchingGradientDampingAt_nonpos g hRpos;
    have hreact := Poincare.ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt_nonpos_of_scalar_pos g hn hRpos;
    have hcoef_nonneg :=
      have hpow := pow_pos hRpos 4;
      le_of_lt
        (div_pos
          (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))
          hpow);
    have hreactTerm := mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hreact;
    have hQineq' :=
      le_of_not_gt fun a =>
        Mathlib.Tactic.Linarith.lt_irrefl
          (Eq.mp
            (congrArg (fun _a => _a < 0)
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.atom_pf (Q' τ x) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a => Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 = Q' τ x ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (Q' τ x) (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.add_congr
                            (Mathlib.Tactic.Ring.Common.add_congr
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg
                                        (fun _a =>
                                          g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul
                                    (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingQuotientGradientDrift3At x) rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg
                                        (fun _a =>
                                          g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                            g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (g.pinchingQuotientGradientDrift3At x)
                                      (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul
                                    (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingGradientDampingAt x) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                          g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right (g.pinchingGradientDampingAt x)
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.div_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.pow_congr
                                  (Mathlib.Tactic.Ring.Common.atom_pf (g.scalarAt x) rfl
                                    (Eq.mpr
                                      (id
                                        (congrArg
                                          (fun _a =>
                                            g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                              g.scalarAt x ^ Nat.rawCast 1 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 4)))
                                  (Mathlib.Tactic.Ring.Common.pow_add
                                    (Mathlib.Tactic.Ring.Common.single_pow
                                      (Mathlib.Tactic.Ring.Common.mul_pow_mul
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 4) (Eq.refl 4)))
                                        (Mathlib.Tactic.Ring.Common.one_pow (Nat.rawCast 4) { out := rfl })
                                        (Eq.mpr
                                          (id
                                            (congrArg
                                              (fun _a =>
                                                g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 =
                                                  g.scalarAt x ^ Nat.rawCast 4 * _a)
                                              (Eq.symm rfl)))
                                          (Eq.refl (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1)))
                                        (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x) (Nat.rawCast 4)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                    (Mathlib.Tactic.Ring.Common.pow_zero
                                      (g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0) rfl)
                                    (Mathlib.Tactic.Ring.Common.add_mul
                                      (Mathlib.Tactic.Ring.Common.mul_add
                                        (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x) (Nat.rawCast 4)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                        (Mathlib.Tactic.Ring.Common.mul_zero
                                          (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1))
                                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                          (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 + 0)))
                                      (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 + 0)))))
                                (Mathlib.Tactic.Ring.Common.div_pf
                                  (Mathlib.Tactic.Ring.Common.inv_single
                                    (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (g.scalarAt x)⁻¹)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                          (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                            (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)))))
                                      (Eq.symm
                                          (Eq.mpr (id (congrArg (fun _a => ⋯ = ⋯) (Eq.symm rfl)))
                                            (Eq.refl ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 1))) ▸
                                        Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                  (Mathlib.Tactic.Ring.Common.add_mul
                                    (Mathlib.Tactic.Ring.Common.mul_add
                                      (Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                        ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))
                                    (Mathlib.Tactic.Ring.Common.zero_mul
                                      ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 1 + 0))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                        (Eq.refl 2))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x)) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        g.pinchingReactionRemainderAt x
                                                (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1 =
                                          g.pinchingReactionRemainderAt x
                                                (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                              Nat.rawCast 1 *
                                            _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 +
                                      0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 +
                                    0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 +
                                    0))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 2)))))
                                (Mathlib.Tactic.Ring.Common.mul_zero ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                      (g.pinchingReactionRemainderAt x
                                            (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 2) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 2) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                      (g.pinchingReactionRemainderAt x
                                            (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 2) +
                                    0))))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul (g.pinchingQuotientGradientDrift3At x) (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1)))))
                              (Mathlib.Tactic.Ring.Common.neg_add
                                (Mathlib.Tactic.Ring.Common.neg_mul (g.pinchingGradientDampingAt x) (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                    (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                      (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                      (Eq.refl (Int.negOfNat 1)))))
                                (Mathlib.Tactic.Ring.Common.neg_add
                                  (Mathlib.Tactic.Ring.Common.neg_mul (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                    (Mathlib.Tactic.Ring.Common.neg_mul
                                      (g.pinchingReactionRemainderAt x
                                        (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                      (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                          (Eq.refl (Int.negOfNat 2))))))
                                  Mathlib.Tactic.Ring.Common.neg_zero))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                                (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                                  (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                                    ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                        (g.pinchingReactionRemainderAt x
                                              (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                            Nat.rawCast 1 *
                                          (Int.negOfNat 2).rawCast) +
                                      0))))))))
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingGradientDampingAt x) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                    g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                        (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (g.pinchingGradientDampingAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.pinchingGradientDampingAt x)
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.ofNat 0)))))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                    (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                        Nat.rawCast 1 *
                                      (Int.negOfNat 2).rawCast) +
                                  0)))))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.div_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                            (Mathlib.Tactic.Ring.Common.pow_congr
                              (Mathlib.Tactic.Ring.Common.atom_pf (g.scalarAt x) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                          g.scalarAt x ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 4)))
                              (Mathlib.Tactic.Ring.Common.pow_add
                                (Mathlib.Tactic.Ring.Common.single_pow
                                  (Mathlib.Tactic.Ring.Common.mul_pow_mul
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 4)
                                        (Eq.refl 4)))
                                    (Mathlib.Tactic.Ring.Common.one_pow (Nat.rawCast 4) { out := rfl })
                                    (Eq.mpr
                                      (id
                                        (congrArg
                                          (fun _a =>
                                            g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 =
                                              g.scalarAt x ^ Nat.rawCast 4 * _a)
                                          (Eq.symm rfl)))
                                      (Eq.refl (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1)))
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x) (Nat.rawCast 4)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                                (Mathlib.Tactic.Ring.Common.pow_zero (g.scalarAt x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)
                                  rfl)
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x) (Nat.rawCast 4)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (g.scalarAt x ^ Nat.rawCast 4 * Nat.rawCast 1 + 0)))))
                            (Mathlib.Tactic.Ring.Common.div_pf
                              (Mathlib.Tactic.Ring.Common.inv_single
                                (Mathlib.Tactic.Ring.Common.inv_mul (Eq.refl (g.scalarAt x)⁻¹)
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
                                              (g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 1 =
                                                (g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * _a)
                                            (Eq.symm rfl)))
                                        (Eq.refl ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 1))) ▸
                                    Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 2))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                    (Eq.refl 2))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2 + 0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x)) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      g.pinchingReactionRemainderAt x
                                            (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 2)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 * Nat.rawCast 2))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                  (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 2) +
                                0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1 +
                              0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 2) +
                              0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                        (Mathlib.Tactic.Ring.Common.add_mul (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.zero_mul 0) (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                      (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          ((g.scalarAt x)⁻¹ ^ Nat.rawCast 4 *
                              (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 2) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.scalarAt x)⁻¹ (Nat.rawCast 4)
                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                (g.pinchingReactionRemainderAt x (g.pinchingRicciNormReactionMotionTraceCubicAt x))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 2))
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                    (Eq.refl (Int.ofNat 0))))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingQuotientGradientDrift3At x) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (Q' τ x) rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 = Q' τ x ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (Q' τ x) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Q' τ x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 +
                            (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (Q' τ x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.pinchingQuotientGradientDrift3At x)
                          (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.ofNat 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
            (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
              (Mathlib.Tactic.Linarith.add_nonpos
                (Mathlib.Tactic.Linarith.add_nonpos
                  (Eq.mp
                    (congrArg (fun _a => _a ≤ 0)
                      (Mathlib.Tactic.Linarith.without_one_mul
                        (Mathlib.Tactic.CancelDenoms.sub_subst rfl
                          (Mathlib.Tactic.CancelDenoms.add_subst
                            (Mathlib.Tactic.CancelDenoms.add_subst (Mathlib.Tactic.CancelDenoms.add_subst rfl rfl) rfl)
                            (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                              (Mathlib.Meta.NormNum.isNat_eq_true
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))))))
                    (Mathlib.Tactic.Linarith.sub_nonpos_of_le hQineq))
                  (Mathlib.Tactic.Linarith.sub_nonpos_of_le hdamp))
                (Eq.mp
                  (congrArg (fun _a => _a ≤ 0)
                    (Mathlib.Tactic.Linarith.without_one_mul
                      (Mathlib.Tactic.CancelDenoms.sub_subst
                        (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                          (Mathlib.Meta.NormNum.isNat_eq_true
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))
                        rfl)))
                  (Mathlib.Tactic.Linarith.sub_nonpos_of_le hreactTerm)))
              (Mathlib.Tactic.Linarith.sub_neg_of_lt a)));
    have hUfun :=
      funext fun y =>
        of_eq_true
          (Eq.trans
            (congr
              (congrArg Eq
                (congrFun'
                  (congrFun' (funext fun τ => funext fun x => sub_eq_add_neg C ((gt (t₀ + τ)).pinchingQuotientAt x)) τ)
                  y))
              (congrFun'
                (congrArg (HAdd.hAdd fun x => C)
                  (Eq.trans (neg_smul 1 fun x => (gt (t₀ + τ)).pinchingQuotientAt x)
                    (congrArg Neg.neg (one_smul ℝ fun x => (gt (t₀ + τ)).pinchingQuotientAt x))))
                y))
            (eq_self (C + -(gt (t₀ + τ)).pinchingQuotientAt y)));
    have hlapU :=
      Eq.mpr (id (congrArg (fun _a => g.laplacianAt _a x = -g.laplacianAt (Q τ) x) hUfun))
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = -g.laplacianAt (Q τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_add' g (fun x => contMDiffAt_const) fun y =>
                ContMDiffAt.smul contMDiffAt_const (hfQ y))))
          (Eq.mpr
            (id
              (congrArg (fun _a => _a + g.laplacianAt (-1 • Q τ) x = -g.laplacianAt (Q τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const g C x)))
            (Eq.mpr
              (id
                (congrArg (fun _a => 0 + _a = -g.laplacianAt (Q τ) x)
                  (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const_smul' g (-1) hfQ)))
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                  (Mathlib.Tactic.Ring.Common.mul_congr
                    (Mathlib.Tactic.Ring.Common.neg_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))
                        Mathlib.Tactic.Ring.Common.neg_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        (Mathlib.Tactic.Ring.Common.mul_zero (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))))));
    have hgradU :=
      Eq.mpr (id (congrArg (fun _a => g.gradientAt _a x = -g.gradientAt (Q τ) x) hUfun))
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = -g.gradientAt (Q τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g mdifferentiableAt_const
                (ContMDiffAt.mdifferentiableAt (ContMDiffAt.smul contMDiffAt_const (hfQ x)) two_ne_zero))))
          (Eq.mpr
            (id
              (congrArg (fun _a => _a + g.gradientAt (-1 • Q τ) x = -g.gradientAt (Q τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const g C x)))
            (Eq.mpr
              (id
                (congrArg (fun _a => 0 + _a = -g.gradientAt (Q τ) x)
                  (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const_smul g (-1)
                    (ContMDiffAt.mdifferentiableAt (hfQ x) two_ne_zero))))
              (of_eq_true
                (Eq.trans
                  (congrFun'
                    (congrArg Eq
                      (Eq.trans
                        (congrArg (HAdd.hAdd 0)
                          (Eq.trans (neg_smul 1 (g.gradientAt (Q τ) x))
                            (congrArg Neg.neg (one_smul ℝ (g.gradientAt (Q τ) x)))))
                        (zero_add (-g.gradientAt (Q τ) x))))
                    (-g.gradientAt (Q τ) x))
                  (eq_self (-g.gradientAt (Q τ) x)))))));
    have hdriftU :=
      have hQfun := funext fun y => of_eq_true (eq_self ((gt (t₀ + τ)).pinchingQuotientAt y));
      id
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a =
                  -(2 / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.pinchingQuotientAt y) x)))
              hgradU))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (-g.gradientAt _a x) =
                    -(2 / g.scalarAt x *
                        ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.pinchingQuotientAt y) x)))
                hQfun))
            (of_eq_true
              (Eq.trans
                (congrFun'
                  (congrArg Eq
                    (Eq.trans
                      (congrArg (HMul.hMul (2 / g.scalarAt x))
                        (map_neg ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.pinchingQuotientAt y) x)))
                      (mul_neg (2 / g.scalarAt x)
                        (((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.pinchingQuotientAt y) x)))))
                  (-(2 / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.pinchingQuotientAt y) x))))
                (eq_self
                  (-(2 / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.pinchingQuotientAt y) x))))))));
    have hL :=
      id
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                _a + 2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x) =
                  -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x))
              hlapU))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  -g.laplacianAt (Q τ) x + _a = -(g.laplacianAt (Q τ) x + g.pinchingQuotientGradientDrift3At x))
                hdriftU))
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingQuotientGradientDrift3At x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.pinchingQuotientGradientDrift3At x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
              (Mathlib.Tactic.Ring.Common.neg_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.pinchingQuotientGradientDrift3At x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (g.pinchingQuotientGradientDrift3At x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                (Mathlib.Tactic.Ring.Common.neg_add
                  (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.negOfNat 1)))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.pinchingQuotientGradientDrift3At x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))))));
    Eq.mpr (id (congrArg (fun _a => _a ≤ u' τ x) hL))
      (Eq.mpr
        (id
          (Eq.trans
            (Eq.trans
              (Eq.trans
                (congrFun' (congrArg LE.le (neg_add_rev (g.laplacianAt (Q τ) x) (g.pinchingQuotientGradientDrift3At x)))
                  (-Q' τ x))
                add_neg_le_iff_le_add._simp_1)
              (Eq.trans le_neg_add_iff_add_le._simp_1 add_neg_le_iff_le_add._simp_1))
            ge_iff_le._simp_1))
        (Eq.mp
          (Eq.trans
            (Eq.trans
              (congrFun' (congrArg LE.le (neg_add_rev (g.laplacianAt (Q τ) x) (g.pinchingQuotientGradientDrift3At x)))
                (-Q' τ x))
              add_neg_le_iff_le_add._simp_1)
            (Eq.trans le_neg_add_iff_add_le._simp_1 add_neg_le_iff_le_add._simp_1))
          (neg_le_neg hQineq')));
  have hmin_lap := fun τ hτ x hmin =>
    let g := gt (t₀ + τ);
    have hfU := hQtoU₂ τ hτ;
    have hlocalMin := IsMinOn.isLocalMin hmin Filter.univ_mem;
    have hlap :=
      Poincare.laplacianAt_nonneg_of_isLocalMin g (hfU x)
        (Poincare.ClosedSmoothRiemannianMetric.mdifferentiableAt_gradient g (hfU x)) hlocalMin;
    have hgrad := Poincare.gradientAt_eq_zero_of_isLocalMin g (hfU x) hlocalMin;
    id
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              0 ≤ g.laplacianAt (u τ) x + 2 / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a)
            hgrad))
        (Eq.mpr
          (id
            (congrArg (LE.le 0)
              (Eq.trans
                (congrArg (HAdd.hAdd (g.laplacianAt (u τ) x))
                  (Eq.trans
                    (congrArg (HMul.hMul (2 / g.scalarAt x))
                      (map_zero ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))))
                    (mul_zero (2 / g.scalarAt x))))
                (add_zero (g.laplacianAt (u τ) x)))))
          hlap));
  have hkey :=
    Poincare.closed_parabolic_min_principle_var (fun τ hτ x => le_refl 0) (id (Continuous.sub continuous_const hQ_cont))
      hud hlap_add_const
      (fun τ hτ x => Eq.mpr (id (congrFun' (congrArg LE.le (Eq.trans (congrArg (HAdd.hAdd (L τ (u τ) x)) ⋯) ⋯)) ⋯)) ⋯) ⋯
      ⋯;
  ⋯
theorem Poincare.hamilton_pinching_improvement.{u} : ∀ {n : ℕ} {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : T2Space M] [inst_2 : ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [inst_3 : IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M] [Nonempty M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M} {t₀ T ε δ : ℝ}
  [inst_6 : ∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1],
  n = 3 →
    0 ≤ T →
      0 < ε →
        ε ≤ 1 / 3 →
          0 ≤ δ →
            δ ≤ Poincare.PinchingAlgebra.pinchedTracelessAdmissibleDelta3 ε →
              (Continuous ↿fun τ x => (gt (t₀ + τ)).tracelessPinchingAt x δ) →
                (∀ τ ∈ Set.Icc 0 T,
                    ∀ (x : M),
                      ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2
                        (fun y => (gt (t₀ + τ)).tracelessPinchingAt y δ) x) →
                  (∀ τ ∈ Set.Icc 0 T,
                      ∀ (x : M),
                        Poincare.ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt
                          (t₀ + τ) x δ ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x)) →
                    (∀ τ ∈ Set.Icc 0 T,
                        ∀ (x : M)
                          (b : Module.Basis (Fin 3) ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners n) x))
                          (μ : Fin 3 → ℝ),
                          (∀ (i : Fin 3), ((gt (t₀ + τ)).ricciEndoAt x) (b i) = μ i • b i) →
                            ∀ (i : Fin 3), ε * (gt (t₀ + τ)).scalarAt x ≤ μ i) →
                      ∀ τ ∈ Set.Icc 0 T,
                        Poincare.tracelessPinchingMaximumTrack gt t₀ δ τ ≤
                          Poincare.tracelessPinchingMaximumTrack gt t₀ δ 0 :=
fun {n} {M} [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
    [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M] [Nonempty M] {gt} {t₀ T ε δ}
    [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] hn hT0 hεpos hεle hδnonneg hδadm hQ_cont hQ₂ hEvol
    hPin =>
  let Q := fun τ x => (gt (t₀ + τ)).tracelessPinchingAt x δ;
  let C := Poincare.tracelessPinchingMaximumTrack gt t₀ δ 0;
  let u := fun τ x => C - Q τ x;
  let Q' := fun τ x => if hτ : τ ∈ Set.Icc 0 T then Classical.choose (hEvol τ hτ x).right.right.right else 0;
  let u' := fun τ x => -Q' τ x;
  let L := fun τ f x =>
    let g := gt (t₀ + τ);
    g.laplacianAt f x +
      (2 - δ) / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt f x);
  have hQd := fun x τ hτ =>
    have hτpair := ⟨hτ.left, hτ.right⟩;
    have hspec := Classical.choose_spec (hEvol τ hτpair x).right.right.right;
    have hbase :=
      Eq.mpr
        (id
          (HasDerivAt.congr_simp (fun t => (gt t).tracelessPinchingAt x δ) (fun t => (gt t).tracelessPinchingAt x δ)
            (Eq.refl fun t => (gt t).tracelessPinchingAt x δ) (Q' τ x)
            (Classical.choose
              (hEvol τ
                      (Eq.mpr_prop Set.mem_Icc._simp_1
                        (of_eq_true
                          (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True))))
                      x).right.right.right)
            (Eq.trans
              (congrFun'
                (congrFun'
                  (funext fun τ =>
                    funext fun x =>
                      dite_congr Set.mem_Icc._simp_1
                        (fun h =>
                          Eq.refl (Classical.choose (hEvol τ (Eq.mpr_prop Set.mem_Icc._simp_1 h) x).right.right.right))
                        fun h => Eq.refl 0)
                  τ)
                x)
              (dite_cond_eq_true
                (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True))))
            (t₀ + τ) (t₀ + τ) (Eq.refl (t₀ + τ))))
        hspec.left;
    have hshift := HasDerivAt.const_add t₀ (hasDerivAt_id τ);
    id
      (Eq.mp
        (HasDerivAt.congr_simp ((fun t => (gt t).tracelessPinchingAt x δ) ∘ HAdd.hAdd t₀)
          ((fun t => (gt t).tracelessPinchingAt x δ) ∘ HAdd.hAdd t₀)
          (Eq.refl ((fun t => (gt t).tracelessPinchingAt x δ) ∘ HAdd.hAdd t₀)) (Q' τ x * 1) (Q' τ x) (mul_one (Q' τ x))
          τ τ (Eq.refl τ))
        (HasDerivAt.comp τ hbase hshift));
  have hud := fun x τ hτ =>
    have hconst := hasDerivAt_const τ C;
    id
      (Eq.mp
        (HasDerivAt.congr_simp ((fun x => C) - fun s => Q s x) ((fun x => C) - fun s => Q s x)
          (Eq.refl ((fun x => C) - fun s => Q s x)) (0 - Q' τ x) (-Q' τ x) (zero_sub (Q' τ x)) τ τ (Eq.refl τ))
        (HasDerivAt.sub hconst (hQd x τ hτ)));
  have hQ0₂ := fun x =>
    Eq.mp
      (congrFun'
        (congrArg (ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2)
          (funext fun y =>
            Poincare.ClosedSmoothRiemannianMetric.tracelessPinchingAt.congr_simp (gt (t₀ + 0)) (gt t₀)
              (congrArg gt (add_zero t₀)) y y (Eq.refl y) δ δ (Eq.refl δ)))
        x)
      (hQ₂ 0 ⟨le_refl 0, hT0⟩ x);
  have h0point := fun x =>
    have hle := Poincare.tracelessPinchingAt_le_tracelessPinchingMaximumAt (gt t₀) δ hQ0₂ x;
    Eq.mpr
      (id
        (Eq.trans
          (Eq.trans
            (congrArg (LE.le 0)
              (Eq.trans
                (congrFun'
                  (congrFun'
                    (funext fun τ =>
                      funext fun x =>
                        congrFun'
                          (congrArg HSub.hSub
                            (Poincare.tracelessPinchingMaximumAt.congr_simp (gt (t₀ + 0)) (gt t₀)
                              (congrArg gt (add_zero t₀)) δ δ (Eq.refl δ)))
                          ((gt (t₀ + τ)).tracelessPinchingAt x δ))
                    0)
                  x)
                (congrArg (HSub.hSub (Poincare.tracelessPinchingMaximumAt (gt t₀) δ))
                  (Poincare.ClosedSmoothRiemannianMetric.tracelessPinchingAt.congr_simp (gt (t₀ + 0)) (gt t₀)
                    (congrArg gt (add_zero t₀)) x x (Eq.refl x) δ δ (Eq.refl δ)))))
            sub_nonneg._simp_1)
          ge_iff_le._simp_1))
      (Eq.mp sub_nonneg._simp_1 (sub_nonneg.mpr hle));
  have hQtoU₂ := fun τ hτ x =>
    have hconst := contMDiffAt_const;
    id (ContMDiffAt.sub hconst (hQ₂ τ hτ x));
  have hlap_add_const := fun τ hτ k x =>
    let g := gt (t₀ + τ);
    have hf := hQtoU₂ τ hτ;
    have hk := fun x => contMDiffAt_const;
    have hlap :=
      id
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = g.laplacianAt (u τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_add' g hf hk)))
          (Eq.mpr
            (id
              (congrArg (fun _a => g.laplacianAt (u τ) x + _a = g.laplacianAt (u τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const g k x)))
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (u τ) x) rfl
                  (Eq.mpr
                    (id
                      (congrArg
                        (fun _a =>
                          g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                            g.laplacianAt (u τ) x ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
              (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (u τ) x) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a =>
                        g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                          g.laplacianAt (u τ) x ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl (g.laplacianAt (u τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)))))));
    have hgrad :=
      id
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = g.gradientAt (u τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g (ContMDiffAt.mdifferentiableAt (hf x) two_ne_zero)
                mdifferentiableAt_const)))
          (Eq.mpr
            (id
              (congrArg (fun _a => g.gradientAt (u τ) x + _a = g.gradientAt (u τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const g k x)))
            (of_eq_true
              (Eq.trans (congrFun' (congrArg Eq (add_zero (g.gradientAt (u τ) x))) (g.gradientAt (u τ) x))
                (eq_self (g.gradientAt (u τ) x))))));
    id
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a +
                  (2 - δ) / g.scalarAt x *
                    ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (fun y => u τ y + k) x) =
                g.laplacianAt (u τ) x +
                  (2 - δ) / g.scalarAt x *
                    ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x))
            hlap))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                g.laplacianAt (u τ) x +
                    (2 - δ) / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a =
                  g.laplacianAt (u τ) x +
                    (2 - δ) / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x))
              hgrad))
          (Eq.refl
            (g.laplacianAt (u τ) x +
              (2 - δ) / g.scalarAt x *
                ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x)))));
  have hsuper := fun τ hτ x =>
    let g := gt (t₀ + τ);
    have hfQ := fun y => id (hQ₂ τ hτ y);
    have hτpair := ⟨hτ.left, hτ.right⟩;
    have hspec := Classical.choose_spec (hEvol τ hτpair x).right.right.right;
    have hRpos := id (hEvol τ hτ x).right.right.left;
    have hQineq :=
      Eq.mpr
        (id
          (congrFun'
            (congrArg LE.le
              (Eq.trans
                (congrFun'
                  (congrFun'
                    (funext fun τ =>
                      funext fun x =>
                        dite_congr Set.mem_Icc._simp_1
                          (fun h =>
                            Eq.refl
                              (Classical.choose (hEvol τ (Eq.mpr_prop Set.mem_Icc._simp_1 h) x).right.right.right))
                          fun h => Eq.refl 0)
                    τ)
                  x)
                (dite_cond_eq_true
                  (Eq.trans (congr (congrArg And (eq_true hτpair.1)) (eq_true hτpair.2)) (and_self True)))))
            ((gt (t₀ + τ)).laplacianAt (fun x => (gt (t₀ + τ)).tracelessPinchingAt x δ) x +
                (gt (t₀ + τ)).tracelessPinchingGradientDrift3At x δ +
              (gt (t₀ + τ)).tracelessPinchingReactionTermAt x δ
                ((gt (t₀ + τ)).pinchingTracelessRicciReactionTrace3At x
                  ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x)))))
        hspec.right;
    have hreact :=
      Poincare.ClosedSmoothRiemannianMetric.tracelessPinchingReactionTermAt_nonpos_of_eigenvalue_pinched g hn hεpos hεle
        hδnonneg hδadm hRpos (hPin τ hτ x);
    have hQineq' :=
      le_of_not_gt fun a =>
        Mathlib.Tactic.Linarith.lt_irrefl
          (Eq.mp
            (congrArg (fun _a => _a < 0)
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (Q' τ x) rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 = Q' τ x ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                      g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf (g.tracelessPinchingGradientDrift3At x δ) rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                      g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.atom_pf
                          (g.tracelessPinchingReactionTermAt x δ
                            (g.pinchingTracelessRicciReactionTrace3At x
                              (g.pinchingRicciNormReactionMotionTraceCubicAt x)))
                          rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  g.tracelessPinchingReactionTermAt x δ
                                          (g.pinchingTracelessRicciReactionTrace3At x
                                            (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 =
                                    g.tracelessPinchingReactionTermAt x δ
                                          (g.pinchingTracelessRicciReactionTrace3At x
                                            (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                        Nat.rawCast 1 *
                                      _a)
                                (Eq.symm rfl)))
                            (Eq.refl
                              (g.tracelessPinchingReactionTermAt x δ
                                    (g.pinchingTracelessRicciReactionTrace3At x
                                      (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (g.tracelessPinchingReactionTermAt x δ
                                      (g.pinchingTracelessRicciReactionTrace3At x
                                        (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0)))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul (g.tracelessPinchingGradientDrift3At x δ)
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul
                                (g.tracelessPinchingReactionTermAt x δ
                                  (g.pinchingTracelessRicciReactionTrace3At x
                                    (g.pinchingRicciNormReactionMotionTraceCubicAt x)))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1)))))
                              Mathlib.Tactic.Ring.Common.neg_zero)))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                              (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast +
                                (g.tracelessPinchingReactionTermAt x δ
                                        (g.pinchingTracelessRicciReactionTrace3At x
                                          (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                      Nat.rawCast 1 *
                                    (Int.negOfNat 1).rawCast +
                                  0)))))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf
                        (g.tracelessPinchingReactionTermAt x δ
                          (g.pinchingTracelessRicciReactionTrace3At x
                            (g.pinchingRicciNormReactionMotionTraceCubicAt x)))
                        rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                g.tracelessPinchingReactionTermAt x δ
                                        (g.pinchingTracelessRicciReactionTrace3At x
                                          (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 =
                                  g.tracelessPinchingReactionTermAt x δ
                                        (g.pinchingTracelessRicciReactionTrace3At x
                                          (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                      Nat.rawCast 1 *
                                    _a)
                              (Eq.symm rfl)))
                          (Eq.refl
                            (g.tracelessPinchingReactionTermAt x δ
                                  (g.pinchingTracelessRicciReactionTrace3At x
                                    (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (g.tracelessPinchingReactionTermAt x δ
                                  (g.pinchingTracelessRicciReactionTrace3At x
                                    (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1 +
                            0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                              (g.tracelessPinchingReactionTermAt x δ
                                (g.pinchingTracelessRicciReactionTrace3At x
                                  (g.pinchingRicciNormReactionMotionTraceCubicAt x)))
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf (g.tracelessPinchingGradientDrift3At x δ) rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                  g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (Q' τ x) rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1 = Q' τ x ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Q' τ x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (Q' τ x) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Q' τ x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 +
                            (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (Q' τ x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (g.tracelessPinchingGradientDrift3At x δ)
                          (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.ofNat 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
            (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le hQineq)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le hreact))
              (Mathlib.Tactic.Linarith.sub_neg_of_lt a)));
    have hUfun :=
      funext fun y =>
        of_eq_true
          (Eq.trans
            (congr
              (congrArg Eq
                (congrFun'
                  (congrFun' (funext fun τ => funext fun x => sub_eq_add_neg C ((gt (t₀ + τ)).tracelessPinchingAt x δ))
                    τ)
                  y))
              (congrFun'
                (congrArg (HAdd.hAdd fun x => C)
                  (Eq.trans (neg_smul 1 fun x => (gt (t₀ + τ)).tracelessPinchingAt x δ)
                    (congrArg Neg.neg (one_smul ℝ fun x => (gt (t₀ + τ)).tracelessPinchingAt x δ))))
                y))
            (eq_self (C + -(gt (t₀ + τ)).tracelessPinchingAt y δ)));
    have hlapU :=
      Eq.mpr (id (congrArg (fun _a => g.laplacianAt _a x = -g.laplacianAt (Q τ) x) hUfun))
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = -g.laplacianAt (Q τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_add' g (fun x => contMDiffAt_const) fun y =>
                ContMDiffAt.smul contMDiffAt_const (hfQ y))))
          (Eq.mpr
            (id
              (congrArg (fun _a => _a + g.laplacianAt (-1 • Q τ) x = -g.laplacianAt (Q τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const g C x)))
            (Eq.mpr
              (id
                (congrArg (fun _a => 0 + _a = -g.laplacianAt (Q τ) x)
                  (Poincare.ClosedSmoothRiemannianMetric.laplacianAt_const_smul' g (-1) hfQ)))
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                  (Mathlib.Tactic.Ring.Common.mul_congr
                    (Mathlib.Tactic.Ring.Common.neg_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))
                        Mathlib.Tactic.Ring.Common.neg_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        (Mathlib.Tactic.Ring.Common.mul_zero (Int.negOfNat 1).rawCast)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))))));
    have hgradU :=
      Eq.mpr (id (congrArg (fun _a => g.gradientAt _a x = -g.gradientAt (Q τ) x) hUfun))
        (Eq.mpr
          (id
            (congrArg (fun _a => _a = -g.gradientAt (Q τ) x)
              (Poincare.ClosedSmoothRiemannianMetric.gradientAt_add g mdifferentiableAt_const
                (ContMDiffAt.mdifferentiableAt (ContMDiffAt.smul contMDiffAt_const (hfQ x)) two_ne_zero))))
          (Eq.mpr
            (id
              (congrArg (fun _a => _a + g.gradientAt (-1 • Q τ) x = -g.gradientAt (Q τ) x)
                (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const g C x)))
            (Eq.mpr
              (id
                (congrArg (fun _a => 0 + _a = -g.gradientAt (Q τ) x)
                  (Poincare.ClosedSmoothRiemannianMetric.gradientAt_const_smul g (-1)
                    (ContMDiffAt.mdifferentiableAt (hfQ x) two_ne_zero))))
              (of_eq_true
                (Eq.trans
                  (congrFun'
                    (congrArg Eq
                      (Eq.trans
                        (congrArg (HAdd.hAdd 0)
                          (Eq.trans (neg_smul 1 (g.gradientAt (Q τ) x))
                            (congrArg Neg.neg (one_smul ℝ (g.gradientAt (Q τ) x)))))
                        (zero_add (-g.gradientAt (Q τ) x))))
                    (-g.gradientAt (Q τ) x))
                  (eq_self (-g.gradientAt (Q τ) x)))))));
    have hdriftU :=
      have hQfun := funext fun y => of_eq_true (eq_self ((gt (t₀ + τ)).tracelessPinchingAt y δ));
      id
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                (2 - δ) / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a =
                  -((2 - δ) / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x)))
              hgradU))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  (2 - δ) / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (-g.gradientAt _a x) =
                    -((2 - δ) / g.scalarAt x *
                        ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x)))
                hQfun))
            (of_eq_true
              (Eq.trans
                (congrFun'
                  (congrArg Eq
                    (Eq.trans
                      (congrArg (HMul.hMul ((2 - δ) / g.scalarAt x))
                        (map_neg ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x)))
                      (mul_neg ((2 - δ) / g.scalarAt x)
                        (((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                          (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x)))))
                  (-((2 - δ) / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x))))
                (eq_self
                  (-((2 - δ) / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))
                        (g.gradientAt (fun y => g.tracelessPinchingAt y δ) x))))))));
    have hL :=
      id
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                _a +
                    (2 - δ) / g.scalarAt x *
                      ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) (g.gradientAt (u τ) x) =
                  -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ))
              hlapU))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  -g.laplacianAt (Q τ) x + _a = -(g.laplacianAt (Q τ) x + g.tracelessPinchingGradientDrift3At x δ))
                hdriftU))
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))
                (Mathlib.Tactic.Ring.Common.neg_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.tracelessPinchingGradientDrift3At x δ) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.tracelessPinchingGradientDrift3At x δ) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
              (Mathlib.Tactic.Ring.Common.neg_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.laplacianAt (Q τ) x) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (g.tracelessPinchingGradientDrift3At x δ) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (g.laplacianAt (Q τ) x ^ Nat.rawCast 1 * Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (g.tracelessPinchingGradientDrift3At x δ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                (Mathlib.Tactic.Ring.Common.neg_add
                  (Mathlib.Tactic.Ring.Common.neg_mul (g.laplacianAt (Q τ) x) (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.negOfNat 1)))))
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (g.tracelessPinchingGradientDrift3At x δ) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.negOfNat 1)))))
                    Mathlib.Tactic.Ring.Common.neg_zero))))));
    Eq.mpr (id (congrArg (fun _a => _a ≤ u' τ x) hL))
      (Eq.mpr
        (id
          (Eq.trans
            (Eq.trans
              (Eq.trans
                (congrFun'
                  (congrArg LE.le (neg_add_rev (g.laplacianAt (Q τ) x) (g.tracelessPinchingGradientDrift3At x δ)))
                  (-Q' τ x))
                add_neg_le_iff_le_add._simp_1)
              (Eq.trans le_neg_add_iff_add_le._simp_1 add_neg_le_iff_le_add._simp_1))
            ge_iff_le._simp_1))
        (Eq.mp
          (Eq.trans
            (Eq.trans
              (congrFun'
                (congrArg LE.le (neg_add_rev (g.laplacianAt (Q τ) x) (g.tracelessPinchingGradientDrift3At x δ)))
                (-Q' τ x))
              add_neg_le_iff_le_add._simp_1)
            (Eq.trans le_neg_add_iff_add_le._simp_1 add_neg_le_iff_le_add._simp_1))
          (neg_le_neg hQineq')));
  have hmin_lap := fun τ hτ x hmin =>
    let g := gt (t₀ + τ);
    have hfU := hQtoU₂ τ hτ;
    have hlocalMin := IsMinOn.isLocalMin hmin Filter.univ_mem;
    have hlap :=
      Poincare.laplacianAt_nonneg_of_isLocalMin g (hfU x)
        (Poincare.ClosedSmoothRiemannianMetric.mdifferentiableAt_gradient g (hfU x)) hlocalMin;
    have hgrad := Poincare.gradientAt_eq_zero_of_isLocalMin g (hfU x) hlocalMin;
    id
      (Eq.mpr
        (id
          (congrArg
            (fun _a =>
              0 ≤
                g.laplacianAt (u τ) x +
                  (2 - δ) / g.scalarAt x * ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x)) _a)
            hgrad))
        (Eq.mpr
          (id
            (congrArg (LE.le 0)
              (Eq.trans
                (congrArg (HAdd.hAdd (g.laplacianAt (u τ) x))
                  (Eq.trans
                    (congrArg (HMul.hMul ((2 - δ) / g.scalarAt x))
                      (map_zero ((g.inner x) (g.gradientAt (fun y => g.scalarAt y) x))))
                    (mul_zero ((2 - δ) / g.scalarAt x))))
                (add_zero (g.laplacianAt (u τ) x)))))
          hlap));
  have hkey :=
    Poincare.closed_parabolic_min_principle_var (fun τ hτ x => le_refl 0) (id (Continuous.sub continuous_const hQ_cont))
      hud hlap_add_const
      (fun τ hτ x =>
        Eq.mpr
          (id
            (congrFun'
              (congrArg LE.le
                (Eq.trans (congrArg (HAdd.hAdd (L τ (u τ) x)) (zero_mul (u τ x))) (add_zero (L τ (u τ) x))))
              (u' τ x)))
          (hsuper τ hτ x))
      hmin_lap h0point;
  fun τ hτ =>
  Exists.casesOn (Poincare.exists_tracelessPinchingAt_isMaxOn (gt (t₀ + τ)) δ (hQ₂ τ hτ)) fun xτ hxτmax =>
    have hnonneg := hkey τ hτ xτ;
    have hQle := Eq.mp sub_nonneg._simp_1 hnonneg;
    Eq.mpr
      (id
        (congrArg (fun _a => _a ≤ Poincare.tracelessPinchingMaximumTrack gt t₀ δ 0)
          (Poincare.tracelessPinchingMaximumTrack.eq_1 gt t₀ δ τ)))
      (Eq.mpr
        (id
          (congrArg (fun _a => _a ≤ Poincare.tracelessPinchingMaximumTrack gt t₀ δ 0)
            (Poincare.tracelessPinchingMaximumAt_eq_of_isMaxOn (gt (t₀ + τ)) δ hxτmax)))
        (Eq.mpr (id ge_iff_le._simp_1) hQle))
Poincare.satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz.{u} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
  [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1]
  (hFlow : ∀ (y : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t y)
  (hLichnerowicz : Poincare.GlobalLichnerowiczAssemblyRegularity gt) :
  Poincare.SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x
Poincare.hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (Poincare.ClosedSmoothModel n) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric n M}
  {t₀ : ℝ} {x : M} [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1]
  {raise' :
    (TangentSpace (Poincare.closedSmoothModelWithCorners n) x →L[ℝ] ℝ) →L[ℝ]
      TangentSpace (Poincare.closedSmoothModelWithCorners n) x}
  (hRaise : HasDerivAt (fun t => (gt t).metricRaiseContinuousAt x) raise' t₀)
  (hEvol : Poincare.SatisfiesRicciEvolutionAt gt t₀ x) (hn : n = 3)
  (hRicNorm₂ :
    ContMDiffAt (Poincare.closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2
      (fun y => (gt t₀).ricciNormSqAt y) x)
  (hPairDiff :
    ∀ (w : TangentSpace (Poincare.closedSmoothModelWithCorners n) x),
      (MDiffAt fun y =>
          Poincare.covRicciRicciPairingAt (gt t₀) y (FiberBundle.extend (Poincare.ClosedSmoothModel n) w y))
        x)
  (hRicSecond : Poincare.CovTensor2DerivExtDifferentiableAt (gt t₀) (Poincare.ricciVariationField (gt t₀)) x) :
  let g := gt t₀;
  let δRic3 := fun u w => Poincare.ricciEvolution3ReactionRHSAt g x u w;
  have hRic3 := ⋯;
  have fullTrace :=
    2 *
      (LinearMap.trace ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners n) x))
        ↑((raise'.comp (g.ricciDualContinuousAt x) +
                (g.metricRaiseContinuousAt x).comp
                  (Poincare.ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt δRic3 hRic3)).comp
            (g.ricciEndoContinuousAt x));
  HasDerivAt (fun t => (gt t).ricciNormSqAt x)
    (g.laplacianAt (fun y => g.ricciNormSqAt y) x - 2 * Poincare.covRicciNormSqAt g x +
      g.pinchingRicciNormReactionMotionTraceAt x fullTrace)
    t₀
```

</details>

<details>
<summary>Ordinary predicate, first attempt, exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Evidence log: `ordinary-01.log`.

```text
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:25:72: error: unexpected token 'set_option'; expected 'lemma'
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:147:4: error: 'change' tactic failed, pattern
  ?m.1604 = lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2 + 2 / R ^ 4 * (R ^ 2 / 2 * C - R * N * (2 * N))
is not definitionally equal to target
  ((lapN - 2 * A + C - 4 / 3 * r * N) * R ^ 2 - N * (2 * R ^ 1 * (lapR + 2 * N - 2 / 3 * r * R))) / (R ^ 2) ^ 2 =
    lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2 +
      2 / R ^ 4 * (1 / 2 * g.scalarAt x ^ 2 * C - g.scalarAt x * g.ricciNormSqAt x * (2 * g.ricciNormSqAt x))
```

</details>

<details>
<summary>Ordinary predicate, second attempt, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Evidence log: `ordinary-02.log`.

```text
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:134:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:134:55: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:151:4: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>Ordinary dependency probe, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/ordinary-dependencies.lean`.
Evidence log: `ordinary-dependencies.log`.

```text
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

</details>

<details>
<summary>Ordinary focused gate before first commit, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Evidence log: `ordinary-final.log`.

```text
```

</details>

<details>
<summary>Improved predicate, first attempt, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Evidence log: `improved-01.log`.

```text
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:311:4: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean:312:4: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
```

</details>

<details>
<summary>First exact-target scratch attempt, exit 1</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean`.
Evidence log: `dependencies-targets-01.log`.

```text
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:357:6: warning: unused variable `gt`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:357:9: warning: unused variable `t`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:367:6: warning: unused variable `gt`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:367:9: warning: unused variable `t`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:367:11: warning: unused variable `delta`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean:371:0: error: Unexpected name `ExactTargetProbe` after `end`: The current section is unnamed

Hint: Delete the name `ExactTargetProbe` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵E̵x̵a̵c̵t̵T̵a̵r̵g̵e̵t̵P̵r̵o̵b̵e̵
@NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (ClosedSmoothModel 3) M] [inst_8 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ},
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        ∀ (x : M),
          ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
            ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (ClosedSmoothModel 3) M] [inst_8 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ δ : ℝ},
  (∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        0 < δ →
          δ ≤ 1 →
            ∀ (x : M),
              ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt t₀ x δ
                ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

</details>

<details>
<summary>Corrected exact-target scratch and all dependencies, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/normalized-flow-pinching-evolution-automatic/dependencies-targets.lean`.
Evidence log: `dependencies-targets.log`.

```text
@Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ},
  (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        ∀ (x : M),
          Poincare.ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
            ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
@Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt : ∀ {M : Type u_1}
  [inst : TopologicalSpace M] [inst_1 : T2Space M] [SecondCountableTopology M] [inst_3 : CompactSpace M]
  [inst_4 : ConnectedSpace M] [inst_5 : MeasurableSpace M] [inst_6 : BorelSpace M]
  [inst_7 : ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [inst_8 : IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  {gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M} {t₀ δ : ℝ},
  (∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) →
    (∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t₀ x) →
      (∀ (x : M), 0 < (gt t₀).scalarAt x) →
        0 < δ →
          δ ≤ 1 →
            ∀ (x : M),
              Poincare.ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt t₀ x δ
                ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x)
'Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesTracelessPinchingImprovementEvolutionAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

</details>

<details>
<summary>Final focused module gate, exit 0</summary>

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Evidence log: `final-module.log`.

```text
```

</details>

The first ordinary attempt placed a documentation comment before `set_option` and wrote `R²/2` where the unfolded definition used `(1/2)*R²`. Moving the comment and matching the unfolded expression fixed those errors. The first target scratch attempt left an anonymous `noncomputable section` inside its named namespace; removing the redundant section fixed its closing command. All warnings were removed before the final checks. No resisting mathematical identity remains for this task.

The initial shell search using `Poincare/Global/RicciEvolution*.lean` reported `zsh:1: no matches found: Poincare/Global/RicciEvolution*.lean`. The search was corrected to repository-wide `rg` with a quoted glob and direct reads of ScalarEvolution and the normalized tensor modules. No unavailable symbol was used in the implementation.

The initial type probe source was:

```lean
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
#print Poincare.hamilton_pinching_preserved
#print Poincare.hamilton_pinching_improvement
#check Poincare.satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
#check Poincare.hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
```

The ordinary dependency probe copied the then-current module and appended:

```lean
#print axioms Poincare.NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt
```

## Name lookup evidence

The following actual output records a batched `rg` over repository and pinned Mathlib source. The lookup excludes the new module itself and emits the first matching source line for each referenced name. Local binders and tactics are excluded from the symbol set. The complete command and its exit code are included in the output. All selected names have matches.

```text
Command: rg -n --glob *.lean -w BorelSpace|ChartedSpace|ClosedSmoothModel|ClosedSmoothRiemannianMetric|CompactSpace|ConnectedSpace|ContDiff|ContMDiffAt|CovTensor2DerivExtDifferentiableAt|CovTensor2ExtContMDiffAt|FiberBundle|HasDerivAt|IsClosedNormalizedRicciFlowSolutionAt|IsManifold|MDifferentiableAt|MeasurableSpace|MeasureTheory|MetricEntriesJointContDiffAt|PinchingAlgebra|SatisfiesNormalizedHamiltonScalarEvolutionAt|SatisfiesPinchingQuotientEvolutionAt|SatisfiesRicciEvolutionAt|SatisfiesTracelessPinchingImprovementEvolutionAt|SecondCountableTopology|T2Space|TangentSpace|TimeDifferentiableAt|TimeVariationExtContMDiffAt|TopologicalSpace|closedSmoothModelWithCorners|congrArg|contMDiffAt_two_pinchingQuotientAt|contMDiffAt_two_ricciNormSqAt_of_ricci_entries|contMDiffAt_two_rpow_const_of_ne|contMDiffAt_two_tracelessPinchingAt|contMDiffAt_two_tracelessRicciNormSqAt|continuousAt|covRicciNormSqAt|covRicciRicciPairingAt|covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two|covTensor2DerivExtDifferentiableAt_of_extSecond|covTensor2ExtDifferentiableAt_of_contMDiffAt_two|covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two|div_nonneg|div_nonpos_of_nonpos_of_nonneg|exists_pos_scalar_floor_of_forall_scalarAt_pos|globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree|hFlow|hJoint|hRpos|hamilton_pinching_improvement|hamilton_pinching_preserved|hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt|hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm|hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3|hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm|hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries|laplacianAt|le_of_eq|le_of_lt|letI|mdifferentiableAt|mdifferentiableAt_gradient|meanScalar|meanScalar_pos_of_forall_scalarAt_ge|metricRaiseContinuousAt|metricRaiseDerivAt|mul_apply|mul_assoc|mul_comm|mul_left_comm|mul_nonneg|ne_of_gt|normalizedTracelessRicciEvolutionReactionAt|of_le|pinchingMixedGradientPairingAt|pinchingQuotientAt|pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions|pinchingQuotientDerivativeAt|pinchingQuotient_spatial_expansion|pinchingReactionRemainderAt|pinchingRicciNormReactionMotionTraceCubicAt|pinchingScalarReactionAt|pinchingTracelessRicciReactionTrace3At|quotientRpowDerivativeAt|ricciEvolutionPinchingReactionMotionTraceAt|ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization|ricciNormSqAt|ricciVariationField|ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow|rpow_add_one|rpow_pos_of_pos|satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz|satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three|scalarAt|scalarAt_contMDiffAt_two_of_normalizedRicciFlow|scalarGradNormSqAt|smul|tensor2AddLeft_ricciVariationField|tensor2AddRight_ricciVariationField|tensor2SMulLeft_ricciVariationField|tensor2SMulRight_ricciVariationField|timeDifferentiableAt_of_metricEntriesJointContDiffAt_one|timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three|tracelessPinchingAt|tracelessPinchingGradientDrift3At|tracelessPinchingGradientNumerator3|tracelessPinchingGradientNumerator3At_nonpos|tracelessPinchingReactionTermAt|tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion|tracelessPinching_spatial_expansion|tracelessPinching_spatial_expansion_with_numerator_bridge|tracelessRicciNormSqAt|tracelessRicciNormSqAt_nonneg|two_ne_zero Poincare .lake/packages/mathlib/Mathlib
rg exit: 0
BorelSpace: Poincare/Global/HeatCauchyFrechet.lean:37:variable [MeasurableSpace E] [BorelSpace E]
ChartedSpace: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:30:    [ChartedSpace ThreeManifoldModel M]
ClosedSmoothModel: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction.lean:31:local notation "E" => ClosedSmoothModel 3
ClosedSmoothRiemannianMetric: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction.lean:39:variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
CompactSpace: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:31:    [SimplyConnectedSpace M] [CompactSpace M],
ConnectedSpace: Poincare/ProofProgress/OnePointTwoPointComplementTopology.lean:33:    ConnectedSpace
ContDiff: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:20:open scoped Manifold ContDiff
ContMDiffAt: Poincare/LocalConnectionRegularity.lean:70:      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
CovTensor2DerivExtDifferentiableAt: Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:211:      CovTensor2DerivExtDifferentiableAt
CovTensor2ExtContMDiffAt: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:68:      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
FiberBundle: Poincare/KoszulExistence.lean:252:  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
HasDerivAt: Poincare/CurvatureConditions.lean:324:    have hder : HasDerivAt
IsClosedNormalizedRicciFlowSolutionAt: Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:42:      IsClosedNormalizedRicciFlowSolutionAt gt t x)
IsManifold: Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterVolume.lean:18:    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
MDifferentiableAt: Poincare/RiemannCurvatureOperator.lean:217:  have hϕ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E))
MeasurableSpace: .lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:42:variable {G : Type*} {mG : MeasurableSpace G}
MeasureTheory: .lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:8:public import Mathlib.MeasureTheory.Group.Prod
MetricEntriesJointContDiffAt: Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:47:      MetricEntriesJointContDiffAt gt t y 3)
PinchingAlgebra: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:324:      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
SatisfiesNormalizedHamiltonScalarEvolutionAt: Poincare/Global/NormalizedFlowScalarLowerProfile.lean:40:def SatisfiesNormalizedHamiltonScalarEvolutionAt
SatisfiesPinchingQuotientEvolutionAt: Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinScalarProfile.lean:81:      ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
SatisfiesRicciEvolutionAt: Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:167:    SatisfiesRicciEvolutionAt gt t₀ x := by
SatisfiesTracelessPinchingImprovementEvolutionAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:332:      ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
SecondCountableTopology: Poincare/Global/NormalizedFlowCompactScalarMeanComparison.lean:23:variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
T2Space: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:29:  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
TangentSpace: Poincare/RiemannCurvatureOperator.lean:34:variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
TimeDifferentiableAt: Poincare/Global/CoordinateVolumeDensityVariation.lean:230:    (hgt : TimeDifferentiableAt gt t₀ x)
TimeVariationExtContMDiffAt: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:64:      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
TopologicalSpace: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:29:  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
closedSmoothModelWithCorners: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction.lean:32:local notation "I" => closedSmoothModelWithCorners 3
congrArg: Poincare/KoszulExistence.lean:388:  have h2 := congrArg (fun ψ ↦ ψ z) h
contMDiffAt_two_pinchingQuotientAt: Poincare/Global/MetricFlowJointPinchingEvolution.lean:132:theorem contMDiffAt_two_pinchingQuotientAt
contMDiffAt_two_ricciNormSqAt_of_ricci_entries: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:73:    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x (hRicC2 x)
contMDiffAt_two_rpow_const_of_ne: Poincare/Global/MetricFlowJointPinchingEvolution.lean:171:theorem contMDiffAt_two_rpow_const_of_ne
contMDiffAt_two_tracelessPinchingAt: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:123:  exact contMDiffAt_two_tracelessPinchingAt
contMDiffAt_two_tracelessRicciNormSqAt: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:77:  exact contMDiffAt_two_tracelessRicciNormSqAt g x hNorm2 hScalar2
continuousAt: .lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean:115:  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
covRicciNormSqAt: Poincare/Global/CovRicciNormBasis.lean:104:    covRicciNormSqAt g x =
covRicciRicciPairingAt: Poincare/Global/ScalarEvolution.lean:771:    covRicciRicciPairingAt g x v =
covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two: Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:359:      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
covTensor2DerivExtDifferentiableAt_of_extSecond: Poincare/Global/DeltaGammaFieldRegularity.lean:135:theorem covTensor2DerivExtDifferentiableAt_of_extSecond
covTensor2ExtDifferentiableAt_of_contMDiffAt_two: Poincare/Global/DeltaGammaFieldRegularity.lean:225:    (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two
covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two: Poincare/Global/DeltaGammaFieldRegularity.lean:223:    (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two
div_nonneg: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:54:  exact div_nonneg
div_nonpos_of_nonpos_of_nonneg: Poincare/Global/ScalarEvolution.lean:2772:    exact div_nonpos_of_nonpos_of_nonneg hGrad
exists_pos_scalar_floor_of_forall_scalarAt_pos: Poincare/Global/NormalizedFlowScalarLowerProfile.lean:75:theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree: Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:63:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
hFlow: Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:41:    (hFlow : ∀ t : ℝ, ∀ x : M,
hJoint: Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:46:    (hJoint : ∀ t : ℝ, ∀ y : M,
hRpos: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:120:    (hRpos : ∀ x : M, 0 < (gt (t0 + tau)).scalarAt x)
hamilton_pinching_improvement: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:341:    hamilton_pinching_improvement
hamilton_pinching_preserved: Poincare/Global/ScalarEvolution.lean:4804:theorem hamilton_pinching_preserved
hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt: Poincare/Global/MetricRaiseTimeDerivative.lean:236:theorem hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm: Poincare/Global/ScalarEvolution.lean:2381:    ClosedSmoothRiemannianMetric.hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm
hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3: Poincare/Global/ScalarEvolution.lean:2091:theorem hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm: Poincare/Global/ScalarEvolution.lean:192:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries: Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:486:    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
laplacianAt: Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:232:    (gt (t₀ + τ)).laplacianAt (R τ) x +
le_of_eq: .lake/packages/mathlib/Mathlib/Testing/Plausible/Functions.lean:249:        rwa [List.map_fst_zip (le_of_eq h₆)]
le_of_lt: .lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Basic.lean:448:  · exact Nat.le_of_lt h
letI: Poincare/ProofProgress/GroundedPerelmanPoincareBoundary.lean:72:  letI := source.trace.smooth
mdifferentiableAt: Poincare/RiemannCurvatureOperator.lean:221:    (hcov.contMDiffAt Filter.univ_mem).mdifferentiableAt one_ne_zero
mdifferentiableAt_gradient: Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:401:        (x := x) hf ((gt (t₀ + τ)).mdifferentiableAt_gradient hf)
meanScalar: Poincare/Global/NormalizedFlowCompactScalarMeanComparison.lean:10:pointwise `R ≤ C * meanScalar` field.
meanScalar_pos_of_forall_scalarAt_ge: Poincare/Global/ScalarMeanLowerBound.lean:94:theorem meanScalar_pos_of_forall_scalarAt_ge
metricRaiseContinuousAt: Poincare/Global/MetricRaiseTimeDerivative.lean:7:`metricRaiseContinuousAt`.  On one fixed tangent fiber, the metric-raising map
metricRaiseDerivAt: Poincare/Global/MetricRaiseTimeDerivative.lean:240:      (metricRaiseDerivAt gt t₀ x hgt) t₀ := by
mul_apply: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:348:theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
mul_assoc: .lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:125:  · simp [mul_assoc]
mul_comm: .lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:148:  simp [mul_comm]
mul_left_comm: .lake/packages/mathlib/Mathlib/Combinatorics/Derangements/Finite.lean:120:      Int.natCast_mul, Int.natCast_add, mul_left_comm, Nat.cast_one]
mul_nonneg: .lake/packages/mathlib/Mathlib/Combinatorics/SetFamily/FourFunctions.lean:83:  obtain hcd | hcd := (mul_nonneg hc₀ hd₁).eq_or_lt'
ne_of_gt: Poincare/CurvatureConditions.lean:613:      rw [einstein_scaling_vanishes_at_extinctionTime (ne_of_gt hlam)] at hc
normalizedTracelessRicciEvolutionReactionAt: Poincare/Global/HamiltonChartDensityLocalDomination.lean:214:        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
of_le: Poincare/LocalConnectionRegularity.lean:54:      ((χ.contMDiff.of_le (by
pinchingMixedGradientPairingAt: Poincare/Global/ScalarEvolution.lean:642:noncomputable def pinchingMixedGradientPairingAt (x : M) : ℝ :=
pinchingQuotientAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:79:    g.pinchingQuotientAt x - 1 / 3 = g.relativeTracelessRicciAt x := by
pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions: Poincare/Global/ScalarEvolution.lean:2049:theorem pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions
pinchingQuotientDerivativeAt: Poincare/Global/ScalarEvolution.lean:2378:        (ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
pinchingQuotient_spatial_expansion: Poincare/Global/ScalarEvolution.lean:1861:theorem pinchingQuotient_spatial_expansion
pinchingReactionRemainderAt: Poincare/Global/ScalarEvolution.lean:2396:        (2 / R ^ 4) * (g.pinchingReactionRemainderAt x Mreact) := by
pinchingRicciNormReactionMotionTraceCubicAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:334:          ((gt (t0 + s)).pinchingRicciNormReactionMotionTraceCubicAt x))
pinchingScalarReactionAt: Poincare/Global/ScalarEvolution.lean:1845:          g.pinchingScalarReactionAt x /
pinchingTracelessRicciReactionTrace3At: Poincare/Global/ScalarEvolution.lean:2213:        + g.pinchingTracelessRicciReactionTrace3At x ricciReaction) t₀ := by
quotientRpowDerivativeAt: Poincare/Global/ScalarEvolution.lean:130:noncomputable def quotientRpowDerivativeAt
ricciEvolutionPinchingReactionMotionTraceAt: Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:129:    ricciEvolutionPinchingReactionMotionTraceAt
ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization: Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:122:    ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization
ricciNormSqAt: Poincare/Global/HamiltonScalarInteriorNegativeBarrier.lean:233:      2 * (gt (t₀ + τ)).ricciNormSqAt x
ricciVariationField: Poincare/Global/CovRicciNormBasis.lean:106:        covTensor2DerivAt g (ricciVariationField g) x
ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:69:    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
rpow_add_one: Poincare/Global/ScalarEvolution.lean:1696:    have h := Real.rpow_add_one hRne_x (p - 1)
rpow_pos_of_pos: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:198:      (Real.rpow_pos_of_pos hR delta).le).trans
satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz: Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:130:        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three: Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:161:theorem satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three
scalarAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:43:  g.tracelessRicciNormSqAt x / (g.scalarAt x) ^ 2
scalarAt_contMDiffAt_two_of_normalizedRicciFlow: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:44:  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
scalarGradNormSqAt: Poincare/Global/ScalarEvolution.lean:92:        - 2 * (gt t₀).scalarGradNormSqAt x
smul: Poincare/RiemannCurvatureOperator.lean:121:  smul {f X} hf hX := by
tensor2AddLeft_ricciVariationField: Poincare/Global/CovRicciNormBasis.lean:135:              (tensor2AddLeft_ricciVariationField g) v p p' q
tensor2AddRight_ricciVariationField: Poincare/Global/CovRicciNormBasis.lean:122:                  (tensor2AddRight_ricciVariationField g) v p q q'
tensor2SMulLeft_ricciVariationField: Poincare/Global/CovRicciNormBasis.lean:143:              (tensor2SMulLeft_ricciVariationField g) c v p q }
tensor2SMulRight_ricciVariationField: Poincare/Global/CovRicciNormBasis.lean:127:                  (tensor2SMulRight_ricciVariationField g) c v p q }
timeDifferentiableAt_of_metricEntriesJointContDiffAt_one: Poincare/Global/HamiltonChartDensityLocalDomination.lean:91:      (timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three: Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:47:      timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
tracelessPinchingAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:63:      g.tracelessPinchingAt x delta / (g.scalarAt x) ^ delta := by
tracelessPinchingGradientDrift3At: Poincare/Global/ScalarEvolution.lean:1743:        + g.tracelessPinchingGradientDrift3At x δ =
tracelessPinchingGradientNumerator3: Poincare/Global/ScalarEvolution.lean:150:        + PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ /
tracelessPinchingGradientNumerator3At_nonpos: Poincare/Global/ScalarEvolution.lean:1320:theorem tracelessPinchingGradientNumerator3At_nonpos
tracelessPinchingReactionTermAt: Poincare/Global/ScalarEvolution.lean:1847:      g.tracelessPinchingReactionTermAt x δ tracelessReactionTrace := by
tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion: Poincare/Global/ScalarEvolution.lean:1838:theorem tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion
tracelessPinching_spatial_expansion: Poincare/Global/ScalarEvolution.lean:1718:theorem tracelessPinching_spatial_expansion
tracelessPinching_spatial_expansion_with_numerator_bridge: Poincare/Global/ScalarEvolution.lean:1797:theorem tracelessPinching_spatial_expansion_with_numerator_bridge
tracelessRicciNormSqAt: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:43:  g.tracelessRicciNormSqAt x / (g.scalarAt x) ^ 2
tracelessRicciNormSqAt_nonneg: Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:55:    (g.tracelessRicciNormSqAt_nonneg x (by norm_num))
two_ne_zero: .lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Free.lean:87:    · rw [max_eq_left hα, max_eq_left (hα.trans <| Cardinal.le_mul_right two_ne_zero),
Missing names: []
```

## Preserved final proof diff

Command: `git diff babccd85e15cdd3a58cd922b1118bf8d1dff3f0c -- Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean`.
Exit: 0.

```diff
diff --git a/Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean b/Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean
new file mode 100644
index 00000000..b91e6f33
--- /dev/null
+++ b/Poincare/Global/NormalizedFlowPinchingEvolutionAutomatic.lean
@@ -0,0 +1,336 @@
+import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
+import Poincare.Global.NormalizedFlowJointPinchingRegularity
+
+noncomputable section
+
+open Bundle FiberBundle Filter MeasureTheory Set
+open scoped Manifold ContDiff Topology
+
+set_option autoImplicit false
+
+universe u
+
+namespace Poincare.NormalizedFlowPinchingEvolutionAutomatic
+
+variable {M : Type u} [TopologicalSpace M] [T2Space M]
+  [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
+  [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+
+local notation "I" => closedSmoothModelWithCorners 3
+local notation "E" => ClosedSmoothModel 3
+local notation "TM" => (TangentSpace I : M → Type _)
+
+set_option maxHeartbeats 8000000 in
+/-- The normalization terms cancel in the ordinary pinching quotient. -/
+theorem satisfiesPinchingQuotientEvolutionAt
+    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ : ℝ}
+    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
+    (hRpos : ∀ x, 0 < (gt t₀).scalarAt x) (x : M) :
+    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt
+      gt t₀ x ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
+  letI : Nonempty M := ⟨x⟩
+  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
+  let htime : TimeDifferentiableAt gt t₀ x :=
+    timeDifferentiableAt_of_metricEntriesJointContDiffAt_one
+      ((hJoint t₀ x).of_le (by norm_num))
+  let raise' := metricRaiseDerivAt gt t₀ x htime
+  let hRicci : SatisfiesRicciEvolutionAt gt t₀ x :=
+    satisfiesRicciEvolutionAt_of_normalizedRicciFlow_joint_metric_entries_three
+      hFlow (hJoint t₀)
+  have hRaise :
+      HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ :=
+    hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt htime
+  have hEntries : ∀ y : M,
+      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
+    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
+      (hJoint t₀ y)
+  have hRicC2 : ∀ y : M,
+      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
+    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
+  have hNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
+    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
+  have hScalar2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.scalarAt z) y := fun y ↦
+    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
+  have hQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.pinchingQuotientAt z) y := fun y ↦
+    contMDiffAt_two_pinchingQuotientAt
+      g y (hNorm2 y) (hScalar2 y) (hRpos y).ne'
+  have hPairDiff : ∀ w : TM x,
+      MDifferentiableAt I 𝓘(ℝ)
+        (fun y : M ↦ covRicciRicciPairingAt g y (extend E w y)) x :=
+    fun w ↦
+      covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two
+        g x (hNorm2 x) w
+  have hRicSecond :
+      CovTensor2DerivExtDifferentiableAt
+        g (ricciVariationField g) x :=
+    covTensor2DerivExtDifferentiableAt_of_extSecond
+      (g := g) (h := ricciVariationField g) (x := x)
+      (covTensor2ExtSecondDifferentiableAt_of_contMDiffAt_two (hRicC2 x))
+      (fun y ↦ covTensor2ExtDifferentiableAt_of_contMDiffAt_two (hRicC2 y))
+      (tensor2AddLeft_ricciVariationField g)
+      (tensor2SMulLeft_ricciVariationField g)
+      (tensor2AddRight_ricciVariationField g)
+      (tensor2SMulRight_ricciVariationField g)
+  have hScalar : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t₀ x :=
+    satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
+  have hScalarGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
+    g.mdifferentiableAt_gradient (hScalar2 x)
+  have hQuotGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient (fun y : M ↦ g.pinchingQuotientAt y))) x :=
+    g.mdifferentiableAt_gradient (hQuot2 x)
+  have hScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
+      (fun y : M ↦ g.scalarAt y * g.scalarAt y) x :=
+    (hScalar2 x).smul (hScalar2 x)
+  have hScalarSqGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient
+          (fun y : M ↦ g.scalarAt y * g.scalarAt y))) x :=
+    g.mdifferentiableAt_gradient hScalarSq2
+  have hQuotScalarSq2 : ContMDiffAt I 𝓘(ℝ) 2
+      ((fun y : M ↦ g.pinchingQuotientAt y) *
+        (fun y : M ↦ g.scalarAt y * g.scalarAt y)) x := by
+    simpa only [Pi.mul_apply] using (hQuot2 x).smul hScalarSq2
+  have hQuotScalarSqGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient
+          ((fun y : M ↦ g.pinchingQuotientAt y) *
+            (fun y : M ↦ g.scalarAt y * g.scalarAt y)))) x :=
+    g.mdifferentiableAt_gradient hQuotScalarSq2
+  have hSpatial := g.pinchingQuotient_spatial_expansion
+    x (hRpos x) (hScalar2 x).continuousAt
+    (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
+    (fun y ↦ (hQuot2 y).mdifferentiableAt two_ne_zero)
+    hScalarGrad hQuotGrad hScalarSqGrad hQuotScalarSqGrad
+    (g.mdifferentiableAt_gradient (hNorm2 x))
+  have hSquare := pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions
+    g x (fun _ ↦ hSpatial) (hRpos x).ne'
+  let R := g.scalarAt x
+  let N := g.ricciNormSqAt x
+  let r := meanScalar g
+  let lapN := g.laplacianAt (fun y ↦ g.ricciNormSqAt y) x
+  let lapR := g.laplacianAt (fun y ↦ g.scalarAt y) x
+  let A := covRicciNormSqAt g x
+  let C := g.pinchingRicciNormReactionMotionTraceCubicAt x
+  let Nrhs := lapN - 2 * A + C - (4 / 3 : ℝ) * r * N
+  let Rrhs := lapR + 2 * N - (2 / 3 : ℝ) * r * R
+  have hNraw : HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
+      (lapN - 2 * A + ricciEvolutionPinchingReactionMotionTraceAt raise' hRicci rfl) t₀ := by
+    simpa [g, lapN, A, ricciEvolutionPinchingReactionMotionTraceAt] using
+      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
+        hRaise hRicci rfl (hNorm2 x) hPairDiff hRicSecond
+  rw [ricciEvolutionPinchingReactionMotionTraceAt_eq_cubic_sub_normalization
+    htime (hFlow x) hRicci] at hNraw
+  have hN : HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x) Nrhs t₀ := by
+    convert hNraw using 1
+    dsimp [Nrhs, C, r, N, g]
+    ring
+  have hR : HasDerivAt (fun t ↦ (gt t).scalarAt x) Rrhs t₀ := hScalar
+  have hQ := ClosedSmoothRiemannianMetric.hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm
+    hN hR (hRpos x).ne'
+  refine ⟨hRpos x, _, hQ, ?_⟩
+  have hAlg : ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
+      (gt := gt) (t₀ := t₀) (x := x) Nrhs Rrhs =
+      (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2) +
+        (2 / R ^ 4) * g.pinchingReactionRemainderAt x C := by
+    change (Nrhs * R ^ 2 - N * (2 * R ^ (2 - 1) * Rrhs)) / (R ^ 2) ^ 2 = _
+    dsimp [Nrhs, Rrhs]
+    unfold ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt
+      ClosedSmoothRiemannianMetric.pinchingScalarReactionAt
+    change _ = (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2) +
+      (2 / R ^ 4) * (1 / 2 * R ^ 2 * C - R * N * (2 * N))
+    have hRne : R ≠ 0 := (hRpos x).ne'
+    field_simp [hRne]
+    ring
+  rw [hAlg]
+  exact le_of_eq (congrArg (fun z ↦ z + (2 / R ^ 4) * g.pinchingReactionRemainderAt x C)
+    hSquare)
+
+set_option maxHeartbeats 12000000 in
+/-- The improved quotient has an additional nonpositive normalization term. -/
+theorem satisfiesTracelessPinchingImprovementEvolutionAt
+    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t₀ δ : ℝ}
+    (hJoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hFlow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
+    (hRpos : ∀ x, 0 < (gt t₀).scalarAt x)
+    (hδpos : 0 < δ) (hδle : δ ≤ 1) (x : M) :
+    ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt
+      gt t₀ x δ ((gt t₀).pinchingRicciNormReactionMotionTraceCubicAt x) := by
+  letI : Nonempty M := ⟨x⟩
+  let g : ClosedSmoothRiemannianMetric 3 M := gt t₀
+  have hEntries : ∀ y : M,
+      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
+    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
+      (hJoint t₀ y)
+  have hRicC2 : ∀ y : M,
+      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
+    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
+  have hNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.ricciNormSqAt z) y := fun y ↦
+    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g y (hRicC2 y)
+  have hScalar2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.scalarAt z) y := fun y ↦
+    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries y
+  have hTraceNorm2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.tracelessRicciNormSqAt z) y := fun y ↦
+    contMDiffAt_two_tracelessRicciNormSqAt
+      g y (hNorm2 y) (hScalar2 y)
+  have hTraceQuot2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.tracelessPinchingAt z δ) y := fun y ↦
+    contMDiffAt_two_tracelessPinchingAt
+      g y δ (hTraceNorm2 y) (hScalar2 y) (hRpos y)
+  have hScalarPow2SubDelta2 : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
+      (fun z : M ↦ g.scalarAt z ^ (2 - δ)) y := fun y ↦
+    contMDiffAt_two_rpow_const_of_ne
+      (2 - δ) (hScalar2 y) (hRpos y).ne'
+  have hTraceQuotGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient (fun y : M ↦ g.tracelessPinchingAt y δ))) x :=
+    g.mdifferentiableAt_gradient (hTraceQuot2 x)
+  have hScalarGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x :=
+    g.mdifferentiableAt_gradient (hScalar2 x)
+  have hTraceProduct2 : ContMDiffAt I 𝓘(ℝ) 2
+      ((fun y : M ↦ g.tracelessPinchingAt y δ) *
+        (fun y : M ↦ g.scalarAt y ^ (2 - δ))) x := by
+    simpa only [Pi.mul_apply] using
+      (hTraceQuot2 x).smul (hScalarPow2SubDelta2 x)
+  have hTraceProductGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient
+          ((fun y : M ↦ g.tracelessPinchingAt y δ) *
+            (fun y : M ↦ g.scalarAt y ^ (2 - δ))))) x :=
+    g.mdifferentiableAt_gradient hTraceProduct2
+  have hTraceNormGrad :
+      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
+        (T% (g.gradient (fun y : M ↦ g.tracelessRicciNormSqAt y))) x :=
+    g.mdifferentiableAt_gradient (hTraceNorm2 x)
+  let R : ℝ := g.scalarAt x
+  let N : ℝ := g.ricciNormSqAt x
+  let U : ℝ := g.tracelessRicciNormSqAt x
+  let Q : ℝ := g.tracelessPinchingAt x δ
+  let p : ℝ := 2 - δ
+  let lapU : ℝ := g.laplacianAt (fun y : M ↦ g.tracelessRicciNormSqAt y) x
+  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
+  let A : ℝ := covRicciNormSqAt g x
+  let B : ℝ := g.pinchingMixedGradientPairingAt x
+  let S : ℝ := g.scalarGradNormSqAt x
+  let ricciReaction : ℝ := g.pinchingRicciNormReactionMotionTraceCubicAt x
+  let T : ℝ := g.pinchingTracelessRicciReactionTrace3At x ricciReaction
+  let Sreact : ℝ := g.pinchingScalarReactionAt x
+  let Urhs : ℝ := lapU - 2 * A + (2 / 3 : ℝ) * S + T - (4 / 3 : ℝ) * meanScalar g * U
+  let Rrhs : ℝ := lapR + Sreact - (2 / 3 : ℝ) * meanScalar g * R
+  have hUderiv :
+      HasDerivAt (fun t ↦ (gt t).tracelessRicciNormSqAt x) Urhs t₀ := by
+    convert hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
+      (x := x) hFlow hJoint using 1
+    dsimp [Urhs, lapU, A, S, T, ricciReaction, U, g,
+      normalizedTracelessRicciEvolutionReactionAt]
+    ring
+  have hRderiv :
+      HasDerivAt (fun t ↦ (gt t).scalarAt x) Rrhs t₀ := by
+    exact satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint)
+  have hF :
+      HasDerivAt (fun t ↦ (gt t).tracelessPinchingAt x δ)
+        (quotientRpowDerivativeAt R U Urhs Rrhs p) t₀ := by
+    simpa [g, R, U, p] using
+      ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
+        (gt := gt) (t₀ := t₀) (x := x) (δ := δ)
+        hUderiv hRderiv (hRpos x)
+  refine ⟨hδpos, hδle, hRpos x, ?_⟩
+  refine ⟨quotientRpowDerivativeAt R U Urhs Rrhs p, hF, ?_⟩
+  have hRicNormDiffX : MDifferentiableAt I 𝓘(ℝ)
+      (fun y : M ↦ g.ricciNormSqAt y) x :=
+    (hNorm2 x).mdifferentiableAt two_ne_zero
+  have hSpatialRaw :=
+    g.tracelessPinching_spatial_expansion
+      x δ (hRpos x) (hScalar2 x).continuousAt
+      (fun y ↦ (hScalar2 y).mdifferentiableAt two_ne_zero)
+      (fun y ↦ (hRpos y).ne')
+      (fun y ↦ (hTraceQuot2 y).mdifferentiableAt two_ne_zero)
+      hTraceQuotGrad hScalarGrad hTraceProductGrad hTraceNormGrad
+  have hSpatial :
+      g.laplacianAt (fun y : M ↦ g.tracelessPinchingAt y δ) x
+          + g.tracelessPinchingGradientDrift3At x δ =
+        lapU / R ^ p
+          - p * Q * lapR / R
+          - p * (2 * B - (2 / 3 : ℝ) * R * S) / (R * R ^ p)
+          + p * Q * S / R ^ 2 := by
+    have hBridge :=
+      g.tracelessPinching_spatial_expansion_with_numerator_bridge
+        x δ hRicNormDiffX ((hScalar2 x).mdifferentiableAt two_ne_zero) hSpatialRaw
+    simpa [g, R, Q, p, lapU, lapR, B, S] using hBridge
+  have hReaction :
+      T / R ^ p - p * U * Sreact / (R * R ^ p) =
+        g.tracelessPinchingReactionTermAt x δ T := by
+    simpa [g, R, U, p, T, Sreact, mul_comm, mul_left_comm, mul_assoc] using
+      g.tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion
+        x δ T (hRpos x)
+  have hQeq : Q = U / R ^ p := by
+    simp [Q, U, R, p, ClosedSmoothRiemannianMetric.tracelessPinchingAt]
+  have hUeq : U = N - R ^ 2 / 3 := by
+    simp [U, N, R, ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt]
+  have hRne : R ≠ 0 := ne_of_gt (by simpa [g, R] using hRpos x)
+  have hRpm1_ne : R ^ (p - 1) ≠ 0 :=
+    ne_of_gt (Real.rpow_pos_of_pos (by simpa [g, R] using hRpos x) (p - 1))
+  have hRp : R ^ p = R ^ (p - 1) * R := by
+    have h := Real.rpow_add_one hRne (p - 1)
+    convert h using 2
+    ring_nf
+  have hRp2 : R ^ (p + 2) = R ^ p * R ^ 2 := by
+    have h1 := Real.rpow_add_one hRne p
+    have h2 := Real.rpow_add_one hRne (p + 1)
+    rw [show p + 2 = p + 1 + 1 by ring, h2, h1]
+    ring
+  have hAlg :
+      quotientRpowDerivativeAt R U Urhs Rrhs p =
+        (lapU / R ^ p
+          - p * Q * lapR / R
+          - p * (2 * B - (2 / 3 : ℝ) * R * S) / (R * R ^ p)
+          + p * Q * S / R ^ 2)
+          + (T / R ^ p - p * U * Sreact / (R * R ^ p))
+          + PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ /
+            R ^ (p + 2) - (2 / 3 : ℝ) * δ * meanScalar g * Q := by
+    dsimp [Urhs, Rrhs]
+    unfold quotientRpowDerivativeAt PinchingAlgebra.tracelessPinchingGradientNumerator3
+    rw [hQeq, hUeq, hRp2, hRp]
+    field_simp [hRne, hRpm1_ne]
+    dsimp [p]
+    ring
+  have hGrad :
+      PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ ≤ 0 := by
+    have hδ0 : 0 ≤ δ := le_of_lt hδpos
+    have hδ2 : δ ≤ 2 := by linarith
+    simpa [g, R, N, A, B, S] using
+      g.tracelessPinchingGradientNumerator3At_nonpos rfl hδ0 hδ2 x
+  have hGradDiv :
+      PinchingAlgebra.tracelessPinchingGradientNumerator3 R N A B S δ /
+          R ^ (p + 2) ≤ 0 := by
+    exact div_nonpos_of_nonpos_of_nonneg hGrad
+      (le_of_lt (Real.rpow_pos_of_pos (by simpa [g, R] using hRpos x) (p + 2)))
+  have hMean : 0 ≤ meanScalar g := by
+    obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos g hRpos
+    exact (meanScalar_pos_of_forall_scalarAt_ge g hrho hlow).le
+  have hQnonneg : 0 ≤ Q := by
+    rw [hQeq]
+    exact div_nonneg (g.tracelessRicciNormSqAt_nonneg x (by norm_num))
+      (Real.rpow_pos_of_pos (hRpos x) p).le
+  have hNormalization : 0 ≤ (2 / 3 : ℝ) * δ * meanScalar g * Q :=
+    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδpos.le) hMean) hQnonneg
+  rw [hAlg, ← hSpatial, hReaction]
+  change _ ≤ g.laplacianAt (fun y ↦ g.tracelessPinchingAt y δ) x +
+    g.tracelessPinchingGradientDrift3At x δ + g.tracelessPinchingReactionTermAt x δ T
+  linarith
+
+end Poincare.NormalizedFlowPinchingEvolutionAutomatic
```
