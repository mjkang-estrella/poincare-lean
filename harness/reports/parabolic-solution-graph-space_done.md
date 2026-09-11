# Parabolic solution graph space: done

Date: 2026-09-11 UTC. Worker result, pending independent orchestrator review.

Base: `d64aaae6461d409a03ee25546ea11174f675295e`.
Verified proof head: `2e5510ea4e2389c0b7dc6f1452ea46615d218d03`.
Branch: `worker/parabolic-solution-graph-space`.
Worktree: `/private/tmp/poincare-workers/parabolic-solution-graph-space`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The exact stop condition was reached. The single new Lean module is
`Poincare/Global/ParabolicSolutionGraph.lean`, 304 lines. The only other added
file is this report. Existing Lean files, `Poincare.lean`, the frozen task,
central handoff, and ledgers were left unchanged under the worker scope.
This work is committed on the worker branch, not merged or marked accepted.

## Result

`Poincare.ParabolicSolutionGraph.Graph (E := E) α T` has the requested
`u`, `ut`, `du`, `ddu`, `zero_trace`, `hasFDeriv`, `hasFDeriv_du`, and
`hasDeriv_time` fields. Each component lies in the landed `ParabolicHolder.Y`.
The derivative fields are exactly the spatial derivatives and the time
derivative within `Icc 0 T`. All components retain the carrier's unique
zero extension outside the cylinder.

The construction works for any real normed vector space `E`, without finite
dimensionality or completeness of `E`. No sign or range assumption on `α`
or `T` is needed. In particular it applies to `ClosedSmoothModel 3` and the
survey's positive time and Hölder exponent range.

The instances are `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`,
`NormedSpace ℝ`, and `CompleteSpace`. `norm_eq` proves the exact formula

```lean
‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖
```

The four lemmas `norm_u_le`, `norm_ut_le`, `norm_du_le`, and `norm_ddu_le`
bound each component by the graph norm. For each component, `sup_*_le`
bounds every point evaluation and `holder_*_le` bounds increments on the
cylinder by the graph norm times `parabolicDist p q ^ α`. The landed
`ParabolicHolder.norm_le` and `ParabolicHolder.holder_le` supply the
component bounds directly.

`time_bound` proves, for `t ∈ Icc 0 T`,

```lean
‖g.u (t, x)‖ ≤ t * ‖g.ut‖
```

It uses the mean-value inequality on `Icc 0 T` and the actual zero trace.
`ofDerivatives` takes four raw functions, their separate support,
boundedness and Hölder witnesses, and exactly the four relation proofs.
It calls the landed `ofFunction` for each component. No approximation,
extension regularity, derivative continuity, or further analytic premise
is hidden in the carrier or constructor.

## Completeness proof

`Ambient` is a nested `WithLp 1` product of the four complete Hölder
carriers. `graphSubmodule` imposes exactly the initial trace and derivative
relations. `graphEquiv` identifies its subtype with the requested explicit
structure and transports the algebra and norm.

`holder_tendstoUniformly` proves that convergence in the landed Hölder
norm implies uniform convergence of the represented functions.
`isClosed_graphSubmodule` checks sequential closedness in the ambient
metric space. Bounded evaluation passes the zero trace to the limit.
Mathlib's `hasFDerivAt_of_tendstoUniformly` passes both spatial derivative
relations to the limit on all of `E`.

For time, the new theorem `closed_time_derivative` proves the needed
within-set version on any convex subset of the real line. Uniform
convergence of the derivatives bounds the difference of two approximating
functions by the mean-value inequality. Passing one index to the pointwise
limit gives a Lipschitz bound on the error relative to one approximant.
Combining this bound, the approximant's little-o remainder, and convergence
of its derivative at the point proves the limit's within-set derivative.
This argument includes both endpoints, and does not replace within-interval
derivatives by two-sided derivatives of the zero extension. It also handles
empty and singleton intervals without a separate analytic hypothesis.

The closed subtype is complete, and an isometry transports that completeness
to `Graph`. There is no remaining resisting derivative-limit step.
This proves the graph-space portion of L0, not the Schauder inverse or a
nonlinear PDE solution.

## Verification

| Check | Actual result |
| --- | --- |
| `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean` | Exit 0, empty output |
| Required forbidden-token `rg` scan | Exit 1, empty output, meaning no matches |
| `git diff --check` and base-to-proof-head whitespace check | Exit 0, empty output |
| Module-wide exact dependency scan | Exit 0, `EXACT_ALL_DECLARATIONS=84 PASS` |
| Generic and `ClosedSmoothModel 3` consumer probe | Exit 0 |

Every declaration emitted by the module, including generated internal
proofs and structure declarations, was checked with `#print axioms` and
has exactly `[propext, Classical.choice, Quot.sound]`.
The consumer also verifies the exact norm identity, time estimate,
pointwise addition and scalar multiplication, and constructor signature.

The cloned cache lacked `Mathlib.Analysis.Normed.Module.TransferInstance`.
A focused build of that dependency succeeded. No full project build or
root integration audit was launched. Initial typeclass synthesis failures
were resolved by giving the ambient normed-space instance explicitly and
raising elaboration limits. An unused-section-variable warning was resolved
with `omit`. The final source check has no diagnostics. Failed compiler
outputs remain in the transcript below.

Each verified lemma was committed separately. The initial commit also
contains the graph definitions and transported normed algebra. The final
instance commit includes the unused-variable cleanup.

```text
8c27f274 Define genuine parabolic graphs and their sum norm
7c74eb8a Prove parabolic graph norm_u_le
4a5ca7d7 Prove parabolic graph norm_ut_le
061edabc Prove parabolic graph norm_du_le
77da653f Prove parabolic graph norm_ddu_le
beb93b01 Prove parabolic graph sup_u_le
4020864d Prove parabolic graph holder_u_le
81554927 Prove parabolic graph sup_ut_le
5cb82e0a Prove parabolic graph holder_ut_le
88eda6e0 Prove parabolic graph sup_du_le
198f4f4e Prove parabolic graph holder_du_le
d53449fe Prove parabolic graph sup_ddu_le
54cf32b2 Prove parabolic graph holder_ddu_le
3d5a442e Prove parabolic graph time_bound
0b230ebf Construct parabolic graphs from supported raw derivatives
72439b6d Prove Holder norm convergence implies uniform convergence
1cfd3faa Close within-set derivatives under uniform derivative convergence
739a448f Prove the parabolic derivative graph submodule is closed
2e5510ea Prove completeness of the parabolic solution graph space
```

## Dated handoff

The proof head above was verified on 2026-09-11. The exact first action for
the independent reviewer is:

```sh
git diff d64aaae6461d409a03ee25546ea11174f675295e..2e5510ea4e2389c0b7dc6f1452ea46615d218d03 -- Poincare/Global/ParabolicSolutionGraph.lean
```

Then rerun the task gate and the two probes below at that proof head.
The worker did not perform root integration or decide acceptance.

## Reproducible exact dependency probe

```lean
import Poincare.Global.ParabolicSolutionGraph
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicSolutionGraph | throwError "module not found"
  let names := (env.constants.map₁.toList.filter fun (n, _) => env.getModuleIdxFor? n == some idx).map Prod.fst
  let mut count : Nat := 0
  for n in names.mergeSort Name.quickLt do
    let axs ← liftCoreM (collectAxioms n)
    unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
      throwError "unexpected dependencies for {n}: {axs}"
    elabCommand (← `(command| #print axioms $(mkIdent n)))
    count := count + 1
  logInfo m!"EXACT_ALL_DECLARATIONS={count} PASS"
```

## Reproducible consumer probe

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.CompactCoefficientEllipticity
open Poincare.ParabolicSolutionGraph
open Set
noncomputable section
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (α T : ℝ)
#synth AddCommGroup (Graph (E := E) α T)
#synth Module ℝ (Graph (E := E) α T)
#synth NormedAddCommGroup (Graph (E := E) α T)
#synth NormedSpace ℝ (Graph (E := E) α T)
#synth CompleteSpace (Graph (E := E) α T)
example (g : Graph (E := E) α T) : ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ := norm_eq g
example (g : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖g.u (t, x)‖ ≤ t * ‖g.ut‖ := time_bound g ht x
example (g h : Graph (E := E) α T) (p : ℝ × E) : (g + h).u p = g.u p + h.u p := rfl
example (c : ℝ) (g : Graph (E := E) α T) (p : ℝ × E) : (c • g).ut p = c • g.ut p := rfl
end General
section Concrete
variable (α T : ℝ)
#synth NormedSpace ℝ (Graph (E := Poincare.ClosedSmoothModel 3) α T)
#synth CompleteSpace (Graph (E := Poincare.ClosedSmoothModel 3) α T)
end Concrete
#check ofDerivatives
#check norm_u_le
#check norm_ut_le
#check norm_du_le
#check norm_ddu_le
#check isClosed_graphSubmodule
```

## Actual command transcripts

The following includes successful checks, unsuccessful compiler attempts,
source-name searches, and the final proof diff. Failed path guesses in source
searches are retained as diagnostics. The final passing check supersedes
an earlier failure of the same check.

### probe-001

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:1:0: error: object file '/private/tmp/poincare-workers/parabolic-solution-graph-space/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Normed/Module/TransferInstance.olean' of module Mathlib.Analysis.Normed.Module.TransferInstance does not exist

exit_code=1
```

### probe-002

```text
$ rg -n 'theorem hasFDerivAt_const|theorem hasDerivWithinAt_const|theorem HasFDerivAt.const_smul|theorem HasDerivWithinAt.const_smul|theorem HasFDerivAt.add|theorem HasDerivWithinAt.add|prod_norm_eq_of_L1|protected abbrev (normedCommGroup|module|normedSpace)' .lake/packages/mathlib/Mathlib/Analysis/Calculus .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Module/TransferInstance.lean .lake/packages/mathlib/Mathlib/Algebra/Module/TransferInstance.lean
.lake/packages/mathlib/Mathlib/Algebra/Module/TransferInstance.lean:41:protected abbrev module (e : α ≃ β) [AddCommMonoid β] [Module R β] :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/TransferInstance.lean:38:protected abbrev normedCommGroup [NormedCommGroup β] (e : α ≃ β) : NormedCommGroup α :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/TransferInstance.lean:44:protected abbrev normedSpace (𝕜 : Type*) [NormedField 𝕜]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:774:theorem prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:782:    exact prod_norm_eq_of_L1 x
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:786:  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:745:theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:67:theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:208:theorem HasFDerivAt.add (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:345:theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:54:theorem HasDerivWithinAt.add (hf : HasDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Add.lean:137:theorem hasDerivWithinAt_const_add_iff (c : F) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:114:theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:189:theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :

exit_code=0
```

### probe-003

```text
$ LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.Normed.Module.TransferInstance
✔ [1586/1587] Built Mathlib.Topology.MetricSpace.TransferInstance (2.1s)
✔ [1587/1587] Built Mathlib.Analysis.Normed.Module.TransferInstance (1.6s)
Build completed successfully (1587 jobs).

exit_code=0
```

### probe-004

```text
$ rg -n 'isLittleO_iff|def IsSeqClosed|tendstoUniformly_iff|tendsto_iff_norm_sub_tendsto_zero|theorem le_of_tendsto' .lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean .lake/packages/mathlib/Mathlib/Topology/Defs/Sequences.lean .lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean .lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean
.lake/packages/mathlib/Mathlib/Topology/Defs/Sequences.lean:61:def IsSeqClosed (s : Set X) : Prop :=
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:126:theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:131:theorem le_of_tendsto {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:136:theorem le_of_tendsto' {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:464:theorem le_of_tendsto_of_tendsto_of_frequently {f g : β → α} {b : Filter β} {a₁ a₂ : α}
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:469:theorem le_of_tendsto_of_tendsto {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean:477:theorem le_of_tendsto_of_tendsto' {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:119:theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:124:    TendstoUniformlyOnFilter F f p ⊤ := by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:138:theorem tendstoUniformly_iff_tendsto :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:140:  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:238:  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:317:  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:404:lemma tendstoUniformly_iff_of_uniformity {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:413:lemma tendstoUniformly_iff {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:418:  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:591:theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:194:theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:197:alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:200:theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:203:alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:206:  isLittleO_iff.1 h hc
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:209:  isBigOWith_iff.2 <| isLittleO_iff.1 h hc
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:287:theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:297:  · refine fun H => isLittleO_iff.2 fun ε ε0 => ?_
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:305:theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:306:  isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:308:theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:309:  isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:909:  simp only [isLittleO_iff, eventually_prod_iff]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:913:  simp only [isLittleO_iff, eventually_prod_iff]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1492:  rw [isLittleO_iff_forall_isBigOWith] at *

exit_code=0
```

### probe-005

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:76:65: error: failed to synthesize
  NormedSpace ℝ ↥(graphSubmodule α T)
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Poincare/Global/ParabolicSolutionGraph.lean:80:11: error: failed to synthesize
  CoeFun (Graph ?m.58 ?m.59 ≃ ↥(graphSubmodule ?m.58 ?m.59)) ?m.61
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

exit_code=1
```

### probe-006

```text
$ rg -n 'theorem.*tendstoUniformly_iff|theorem TendstoUniformly.comp|theorem TendstoUniformly.tendsto_at|theorem.*tendsto_nhds|theorem.*norm_sub' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/UniformConvergence.lean .lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:119:theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:138:theorem tendstoUniformly_iff_tendsto :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:157:theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:236:theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ → α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:591:theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :

exit_code=0
```

### probe-007

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:79:65: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  NormedSpace ℝ ↥(graphSubmodule α T)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

exit_code=1
```

### probe-008

```text
$ rg -n 'tendstoUniformly_iff|tendstoUniformlyOn_iff' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean .lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean; rg -n 'norm_sub.*tendsto|tendsto.*norm_sub' .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Topology.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Continuity.lean
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:46:`tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`), it is somewhat unwieldy to work with in
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:91:theorem tendstoUniformlyOn_iff_tendstoUniformlyOnFilter :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:99:  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:105:theorem tendstoUniformlyOn_iff_tendsto :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:108:  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:119:theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:121:  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, principal_univ]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:124:    TendstoUniformlyOnFilter F f p ⊤ := by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:126:theorem tendstoUniformlyOn_iff_tendstoUniformly_comp_coe :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:130:lemma tendstoUniformlyOn_iff_restrict {K : Set α} : TendstoUniformlyOn F f p K ↔
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:132:  tendstoUniformlyOn_iff_tendstoUniformly_comp_coe
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:138:theorem tendstoUniformly_iff_tendsto :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:140:  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:171:  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:189:  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:210:  rw [tendstoUniformlyOn_iff_tendsto, uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:232:  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:238:  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:272:  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:311:  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:317:  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:326:  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:340:  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:346:  rw [tendstoUniformlyOn_iff_tendsto]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:388:lemma tendstoUniformlyOn_iff_of_uniformity {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:393:  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:396:lemma tendstoUniformlyOn_iff {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:401:  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:404:lemma tendstoUniformly_iff_of_uniformity {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:409:  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:413:lemma tendstoUniformly_iff {F : X → α → β} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:418:  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:492:  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:574:  rw [tendstoUniformlyOn_iff_tendsto, tendsto_iff_seq_tendsto]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:578:  rw [tendstoUniformlyOn_iff_tendsto] at h
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:583:  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:586:theorem tendstoUniformlyOn_iff_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:591:theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:595:  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn
rg: .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Topology.lean: No such file or directory (os error 2)

exit_code=2
```

### probe-009

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-010

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-011

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-012

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-013

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-014

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-graph-evidence/time-limit.lean
/tmp/parabolic-graph-evidence/time-limit.lean:44:30: error: Application type mismatch: The argument
  add_le_add_right (norm_add_le ?m.636 ?m.637) ?m.638
has type
  ?m.638 + ‖?m.636 + ?m.637‖ ≤ ?m.638 + (‖?m.636‖ + ‖?m.637‖)
but is expected to have type
  ‖g y - f N y - (g x - f N x) + (f N y - f N x - (y - x) • d N x)‖ + ‖(y - x) * (d N x - e x)‖ ≤
    ‖g y - f N y - (g x - f N x)‖ + ‖f N y - f N x - (y - x) • d N x‖ + ‖(y - x) * (d N x - e x)‖
in the application
  LE.le.trans (norm_add_le (g y - f N y - (g x - f N x) + (f N y - f N x - (y - x) • d N x)) ((y - x) * (d N x - e x)))
    (add_le_add_right (norm_add_le ?m.636 ?m.637) ?m.638)

exit_code=1
```

### probe-015

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-016

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-017

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-018

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-019

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-020

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-021

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-022

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-023

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-024

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:210:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicSolutionGraph.holder_tendstoUniformly`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

exit_code=0
```

### probe-025

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:210:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicSolutionGraph.holder_tendstoUniformly`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

exit_code=0
```

### probe-026

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean
Poincare/Global/ParabolicSolutionGraph.lean:210:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicSolutionGraph.holder_tendstoUniformly`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

exit_code=0
```

### probe-1789165654491016000

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-1789165697648443000

```text
$ LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/ParabolicSolutionGraph.olean Poincare/Global/ParabolicSolutionGraph.lean

exit_code=0
```

### probe-1789165698811732000

```text
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicSolutionGraph.lean

exit_code=1
```

### probe-1789165698844712000

```text
$ git diff --check && git diff d64aaae6461d409a03ee25546ea11174f675295e..HEAD --check && git status --short --branch
## worker/parabolic-solution-graph-space

exit_code=0
```

### probe-1789165720998751000

```text
$ rg -n '(theorem|lemma|def|abbrev|alias).*\b(norm_sub_le_norm_sub_add_norm_sub|self_mem_nhdsWithin|completeSpace_coe|ofFunction|norm_le_of_bounds|parabolicDist_nonneg|holder_le|norm_le|isClosed_graphSubmodule|tendstoUniformly|tendstoUniformlyOn|tendsto_at|const_smul|hasFDerivAt_const|hasDerivWithinAt_const|norm_sub_rev|norm_nonneg|norm_mul|smul_eq_mul|convex_Icc|eventually_ge_atTop|eventually_atTop|isometry_toFun|collectAxioms|ClosedSmoothModel)\b' Poincare/Global/ParabolicHolderSpace.lean Poincare/Global/ClosedManifoldModel.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv .lake/packages/mathlib/Mathlib/Analysis/Normed/Group .lake/packages/mathlib/Mathlib/Topology/UniformSpace .lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean .lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean
rg: Poincare/Global/ClosedManifoldModel.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:126:lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:254:theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
Poincare/Global/ParabolicHolderSpace.lean:32:theorem parabolicDist_nonneg (p q : ℝ × E) : 0 ≤ parabolicDist p q := by
Poincare/Global/ParabolicHolderSpace.lean:129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
Poincare/Global/ParabolicHolderSpace.lean:134:theorem holder_le (f : Y (E := E) α T F) {p q : ℝ × E}
Poincare/Global/ParabolicHolderSpace.lean:164:def ofFunction (f : ℝ × E → F) (hoff : ∀ p, p ∉ cylinder T → f p = 0)
Poincare/Global/ParabolicHolderSpace.lean:290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Defs.lean:57:theorem eventually_ge_atTop [Preorder α] (a : α) : ∀ᶠ x in atTop, a ≤ x :=
.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean:72:@[simp] lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b := mem_atTop_sets
.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean:77:alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:98:alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:143:theorem TendstoUniformlyOnFilter.tendsto_at (h : TendstoUniformlyOnFilter F f p p')
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:151:theorem TendstoUniformlyOn.tendsto_at (h : TendstoUniformlyOn F f p s) (hx : x ∈ s) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:157:theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:219:protected theorem TendstoUniformly.tendstoUniformlyOn (h : TendstoUniformly F f p) :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:342:theorem UniformContinuousOn.tendstoUniformlyOn [UniformSpace α] [UniformSpace γ] {U : Set α}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:355:theorem UniformContinuousOn.tendstoUniformly [UniformSpace α] [UniformSpace γ] {U : Set α}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean:361:theorem UniformContinuous₂.tendstoUniformly [UniformSpace α] [UniformSpace γ] {f : α → β → γ}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/ZeroAtInfty.lean:27:theorem ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : ℝ) (hε : 0 < ε) :
.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean:39:protected theorem Tendsto.eventually_ge_atTop [Preorder β] {f : α → β} {l : Filter α}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/LocallyUniformConvergence.lean:292:theorem TendstoLocallyUniformlyOn.tendsto_at (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:318:alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:446:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero, mul_zero]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:448:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ← mul_add]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:632:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:635:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ← mul_add]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:685:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero p,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:688:        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean:95:theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean:106:theorem Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/ZPow.lean:52:    simp only [Function.comp_def, zpow_neg, inv_inv, smul_eq_mul] at this
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/CocompactMap.lean:33:theorem CocompactMapClass.norm_le [ProperSpace F] [FunLike 𝓕 E F] [CocompactMapClass 𝓕 E F]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:108:lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:112:lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:124:theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:132:theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:997:lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Quotient.lean:380:theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:114:theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:745:theorem hasDerivWithinAt_const : HasDerivWithinAt (fun _ => c) 0 s x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:179:theorem HasStrictDerivAt.const_smul (c : R) (hf : HasStrictDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:184:theorem HasDerivAtFilter.const_smul (c : R) (hf : HasDerivAtFilter f f' L) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:189:theorem HasDerivWithinAt.const_smul (c : R) (hf : HasDerivWithinAt f f' s x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Mul.lean:194:theorem HasDerivAt.const_smul (c : R) (hf : HasDerivAt f f' x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:52:theorem HasFDerivAtFilter.const_smul (h : HasFDerivAtFilter f f' L) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:57:theorem HasStrictFDerivAt.const_smul (h : HasStrictFDerivAt f f' x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:62:theorem HasFDerivWithinAt.const_smul (h : HasFDerivWithinAt f f' s x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:67:theorem HasFDerivAt.const_smul (h : HasFDerivAt f f' x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:72:theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:77:theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:82:theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:86:theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :

exit_code=2
```

### probe-1789165726492186000

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-graph-evidence/AllAxioms.lean
'Poincare.ParabolicSolutionGraph.graphEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.norm_ut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.sup_u_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.norm_u_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.norm_du_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.closed_time_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.isClosed_graphSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instCompleteSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.hasFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instModule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.norm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.ddu' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedAddCommGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.holder_du_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph._sizeOf_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.hasDeriv_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.sup_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.holder_tendstoUniformly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.sup_ut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.noConfusionType' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Ambient._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.holder_u_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.holder_ut_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.instNormedSpace._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk.noConfusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.ofDerivatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.mk._flat_ctor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.ut' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.sup_du_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.du' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph._sizeOf_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.Graph.u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphEquiv._proof_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.graphSubmodule._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicSolutionGraph.holder_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_ALL_DECLARATIONS=84 PASS

exit_code=0
```

### probe-1789165726496257000

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-graph-evidence/Consumer.lean
instNormedAddCommGroup.toAddCommGroup
instModule
instNormedAddCommGroup
instNormedSpace
instCompleteSpace
instNormedSpace
instCompleteSpace
Poincare.ParabolicSolutionGraph.ofDerivatives.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (u ut : ℝ × E → ℝ) (du : ℝ × E → E →L[ℝ] ℝ) (ddu : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
  (hu_off : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, u p = 0)
  (hu_bound : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖u p‖ ≤ M)
  (hu_holder : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) u K)
  (hut_off : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, ut p = 0)
  (hut_bound : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ut p‖ ≤ M)
  (hut_holder : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ut K)
  (hdu_off : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, du p = 0)
  (hdu_bound : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖du p‖ ≤ M)
  (hdu_holder : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) du K)
  (hddu_off : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, ddu p = 0)
  (hddu_bound : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖ddu p‖ ≤ M)
  (hddu_holder : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ddu K)
  (hzero : ∀ (x : E), u (0, x) = 0) (hdu : ∀ t ∈ Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => u (t, z)) (du (t, x)) x)
  (hddu : ∀ t ∈ Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => du (t, z)) (ddu (t, x)) x)
  (hut : ∀ t ∈ Icc 0 T, ∀ (x : E), HasDerivWithinAt (fun s => u (s, x)) (ut (t, x)) (Icc 0 T) t) : Graph α T
Poincare.ParabolicSolutionGraph.norm_u_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (g : Graph α T) : ‖g.u‖ ≤ ‖g‖
Poincare.ParabolicSolutionGraph.norm_ut_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (g : Graph α T) : ‖g.ut‖ ≤ ‖g‖
Poincare.ParabolicSolutionGraph.norm_du_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (g : Graph α T) : ‖g.du‖ ≤ ‖g‖
Poincare.ParabolicSolutionGraph.norm_ddu_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (g : Graph α T) : ‖g.ddu‖ ≤ ‖g‖
Poincare.ParabolicSolutionGraph.isClosed_graphSubmodule.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {α T : ℝ} : IsClosed ↑(graphSubmodule α T)

exit_code=0
```

### probe-1789165736598110000

```text
$ rg -n '^(abbrev|def) ClosedSmoothModel|norm_sub_le_norm_sub_add_norm_sub' Poincare .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Defs.lean | head -15
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
Poincare/Global/ParabolicSolutionGraph.lean:243:      ‖d n z - d N z‖ ≤ ‖d n z - e z‖ + ‖e z - d N z‖ := norm_sub_le_norm_sub_add_norm_sub ..

exit_code=0
```

### probe-1789165760809863000

```text
$ git diff d64aaae6461d409a03ee25546ea11174f675295e..HEAD -- Poincare/Global/ParabolicSolutionGraph.lean
diff --git a/Poincare/Global/ParabolicSolutionGraph.lean b/Poincare/Global/ParabolicSolutionGraph.lean
new file mode 100644
index 00000000..d99f6b1c
--- /dev/null
+++ b/Poincare/Global/ParabolicSolutionGraph.lean
@@ -0,0 +1,304 @@
+import Poincare.Global.ParabolicHolderSpace
+import Mathlib.Analysis.Calculus.UniformLimitsDeriv
+import Mathlib.Analysis.Normed.Module.TransferInstance
+
+/-! The zero initial trace space of genuine parabolic derivative graphs. -/
+
+noncomputable section
+
+set_option synthInstance.maxHeartbeats 200000
+set_option maxHeartbeats 800000
+
+namespace Poincare.ParabolicSolutionGraph
+
+open Set Filter
+open scoped Topology
+open ParabolicHolder
+
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+
+structure Graph (α T : ℝ) where
+  u : Y (E := E) α T ℝ
+  ut : Y (E := E) α T ℝ
+  du : Y (E := E) α T (E →L[ℝ] ℝ)
+  ddu : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)
+  zero_trace : ∀ x : E, u (0, x) = 0
+  hasFDeriv : ∀ t ∈ Icc 0 T, ∀ x : E,
+    HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x
+  hasFDeriv_du : ∀ t ∈ Icc 0 T, ∀ x : E,
+    HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x
+  hasDeriv_time : ∀ t ∈ Icc 0 T, ∀ x : E,
+    HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t
+
+abbrev Ambient (α T : ℝ) :=
+  WithLp 1 (WithLp 1 (Y (E := E) α T ℝ × Y (E := E) α T ℝ) ×
+    WithLp 1 (Y (E := E) α T (E →L[ℝ] ℝ) ×
+      Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)))
+
+def graphSubmodule (α T : ℝ) : Submodule ℝ (Ambient (E := E) α T) where
+  carrier := {v | (∀ x : E, v.fst.fst (0, x) = 0) ∧
+    (∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z : E => v.fst.fst (t, z)) (v.snd.fst (t, x)) x) ∧
+    (∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z : E => v.snd.fst (t, z)) (v.snd.snd (t, x)) x) ∧
+    (∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun s : ℝ => v.fst.fst (s, x)) (v.fst.snd (t, x)) (Icc 0 T) t)}
+  zero_mem' := by
+    refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
+    · intro t ht x; exact hasFDerivAt_const (0 : ℝ) x
+    · intro t ht x; exact hasFDerivAt_const (0 : E →L[ℝ] ℝ) x
+    · intro t ht x; exact hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)
+  add_mem' := by
+    intro v w hv hw
+    exact ⟨fun x => by change v.fst.fst (0,x) + w.fst.fst (0,x) = 0; rw [hv.1, hw.1, add_zero],
+      fun t ht x => (hv.2.1 t ht x).add (hw.2.1 t ht x),
+      fun t ht x => (hv.2.2.1 t ht x).add (hw.2.2.1 t ht x),
+      fun t ht x => (hv.2.2.2 t ht x).add (hw.2.2.2 t ht x)⟩
+  smul_mem' := by
+    intro c v hv
+    exact ⟨fun x => by change c • v.fst.fst (0,x) = 0; rw [hv.1, smul_zero],
+      fun t ht x => (hv.2.1 t ht x).const_smul c,
+      fun t ht x => (hv.2.2.1 t ht x).const_smul c,
+      fun t ht x => (hv.2.2.2 t ht x).const_smul c⟩
+
+variable {α T : ℝ}
+
+def graphEquiv : Graph (E := E) α T ≃ ↥(graphSubmodule (E := E) α T) where
+  toFun g := ⟨WithLp.toLp 1 (WithLp.toLp 1 (g.u, g.ut), WithLp.toLp 1 (g.du, g.ddu)),
+    g.zero_trace, g.hasFDeriv, g.hasFDeriv_du, g.hasDeriv_time⟩
+  invFun v := ⟨v.val.fst.fst, v.val.fst.snd, v.val.snd.fst, v.val.snd.snd,
+    v.property.1, v.property.2.1, v.property.2.2.1, v.property.2.2.2⟩
+  left_inv _ := rfl
+  right_inv _ := rfl
+
+instance instNormedAddCommGroup : NormedAddCommGroup (Graph (E := E) α T) :=
+  graphEquiv.normedAddCommGroup
+
+instance instModule : Module ℝ (Graph (E := E) α T) := graphEquiv.module ℝ
+
+instance instNormedSpace : NormedSpace ℝ (Graph (E := E) α T) := by
+  letI : NormedSpace ℝ (Ambient (E := E) α T) := inferInstance
+  exact graphEquiv.normedSpace ℝ
+
+theorem norm_eq (g : Graph (E := E) α T) :
+    ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ := by
+  change ‖(graphEquiv g).val‖ = _
+  simp only [WithLp.prod_norm_eq_of_L1]
+  exact (add_assoc _ _ _).symm
+
+theorem norm_u_le (g : Graph (E := E) α T) : ‖g.u‖ ≤ ‖g‖ := by
+  rw [norm_eq]
+  have := norm_nonneg g.u
+  have := norm_nonneg g.ut
+  have := norm_nonneg g.du
+  have := norm_nonneg g.ddu
+  linarith
+
+theorem norm_ut_le (g : Graph (E := E) α T) : ‖g.ut‖ ≤ ‖g‖ := by
+  rw [norm_eq]
+  have := norm_nonneg g.u
+  have := norm_nonneg g.ut
+  have := norm_nonneg g.du
+  have := norm_nonneg g.ddu
+  linarith
+
+theorem norm_du_le (g : Graph (E := E) α T) : ‖g.du‖ ≤ ‖g‖ := by
+  rw [norm_eq]
+  have := norm_nonneg g.u
+  have := norm_nonneg g.ut
+  have := norm_nonneg g.du
+  have := norm_nonneg g.ddu
+  linarith
+
+theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
+  rw [norm_eq]
+  have := norm_nonneg g.u
+  have := norm_nonneg g.ut
+  have := norm_nonneg g.du
+  have := norm_nonneg g.ddu
+  linarith
+
+theorem sup_u_le (g : Graph (E := E) α T) (p : ℝ × E) :
+    ‖g.u p‖ ≤ ‖g‖ :=
+  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)
+
+theorem holder_u_le (g : Graph (E := E) α T) {p q : ℝ × E}
+    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
+    ‖g.u p - g.u q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
+  (ParabolicHolder.holder_le g.u hp hq).trans
+    (mul_le_mul_of_nonneg_right (norm_u_le g)
+      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
+
+theorem sup_ut_le (g : Graph (E := E) α T) (p : ℝ × E) :
+    ‖g.ut p‖ ≤ ‖g‖ :=
+  (ParabolicHolder.norm_le g.ut p).trans (norm_ut_le g)
+
+theorem holder_ut_le (g : Graph (E := E) α T) {p q : ℝ × E}
+    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
+    ‖g.ut p - g.ut q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
+  (ParabolicHolder.holder_le g.ut hp hq).trans
+    (mul_le_mul_of_nonneg_right (norm_ut_le g)
+      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
+
+theorem sup_du_le (g : Graph (E := E) α T) (p : ℝ × E) :
+    ‖g.du p‖ ≤ ‖g‖ :=
+  (ParabolicHolder.norm_le g.du p).trans (norm_du_le g)
+
+theorem holder_du_le (g : Graph (E := E) α T) {p q : ℝ × E}
+    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
+    ‖g.du p - g.du q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
+  (ParabolicHolder.holder_le g.du hp hq).trans
+    (mul_le_mul_of_nonneg_right (norm_du_le g)
+      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
+
+theorem sup_ddu_le (g : Graph (E := E) α T) (p : ℝ × E) :
+    ‖g.ddu p‖ ≤ ‖g‖ :=
+  (ParabolicHolder.norm_le g.ddu p).trans (norm_ddu_le g)
+
+theorem holder_ddu_le (g : Graph (E := E) α T) {p q : ℝ × E}
+    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
+    ‖g.ddu p - g.ddu q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
+  (ParabolicHolder.holder_le g.ddu hp hq).trans
+    (mul_le_mul_of_nonneg_right (norm_ddu_le g)
+      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
+
+theorem time_bound (g : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T)
+    (x : E) : ‖g.u (t, x)‖ ≤ t * ‖g.ut‖ := by
+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun s hs => g.hasDeriv_time s hs x)
+    (fun s _ => ParabolicHolder.norm_le g.ut (s, x)) (convex_Icc (0 : ℝ) T)
+    (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht
+  simpa [g.zero_trace x, Real.norm_of_nonneg ht.1, mul_comm] using h
+
+/-- Bundle four supported bounded Hölder functions with exactly the derivative relations. -/
+def ofDerivatives
+    (u : ℝ × E → ℝ)
+    (ut : ℝ × E → ℝ)
+    (du : ℝ × E → E →L[ℝ] ℝ)
+    (ddu : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
+    (hu_off : ∀ p, p ∉ cylinder T → u p = 0)
+    (hu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖u p‖ ≤ M)
+    (hu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) u K)
+    (hut_off : ∀ p, p ∉ cylinder T → ut p = 0)
+    (hut_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖ut p‖ ≤ M)
+    (hut_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) ut K)
+    (hdu_off : ∀ p, p ∉ cylinder T → du p = 0)
+    (hdu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖du p‖ ≤ M)
+    (hdu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) du K)
+    (hddu_off : ∀ p, p ∉ cylinder T → ddu p = 0)
+    (hddu_bound : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖ddu p‖ ≤ M)
+    (hddu_holder : ∃ K : ℝ, HasHolderBound α (cylinder T) ddu K)
+    (hzero : ∀ x : E, u (0, x) = 0)
+    (hdu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x)
+    (hddu : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x)
+    (hut : ∀ t ∈ Icc 0 T, ∀ x : E,
+      HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t) :
+    Graph (E := E) α T where
+  u := ofFunction u hu_off hu_bound hu_holder
+  ut := ofFunction ut hut_off hut_bound hut_holder
+  du := ofFunction du hdu_off hdu_bound hdu_holder
+  ddu := ofFunction ddu hddu_off hddu_bound hddu_holder
+  zero_trace := hzero
+  hasFDeriv := hdu
+  hasFDeriv_du := hddu
+  hasDeriv_time := hut
+
+variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
+
+omit [NormedSpace ℝ E] in
+theorem holder_tendstoUniformly {v : ℕ → Y (E := E) α T F} {w : Y (E := E) α T F}
+    (h : Tendsto v atTop (𝓝 w)) : TendstoUniformly (fun n p => v n p) w atTop := by
+  apply Metric.tendstoUniformly_iff.2
+  intro ε hε
+  filter_upwards [(Metric.tendsto_nhds.1 h) ε hε] with n hn p
+  have hb := Poincare.ParabolicHolder.norm_le (w - v n) p
+  change ‖w p - v n p‖ ≤ ‖w - v n‖ at hb
+  rw [dist_eq_norm]
+  exact hb.trans_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hn)
+
+/-- Uniform convergence of the derivatives closes the derivative relation on a convex set. -/
+theorem closed_time_derivative {f d : ℕ → ℝ → ℝ} {g e : ℝ → ℝ} {s : Set ℝ}
+    (hs : Convex ℝ s) (hf : ∀ n t, t ∈ s → HasDerivWithinAt (f n) (d n t) s t)
+    (hfg : ∀ t ∈ s, Tendsto (fun n => f n t) atTop (𝓝 (g t)))
+    (hde : TendstoUniformlyOn d e atTop s) {x : ℝ} (hx : x ∈ s) :
+    HasDerivWithinAt g (e x) s x := by
+  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
+  intro ε hε
+  have hε4 : 0 < ε / 4 := by linarith
+  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hde) _ hε4)
+  have hnear (n : ℕ) (hn : N ≤ n) (y : ℝ) (hy : y ∈ s) :
+      ‖d n y - e y‖ ≤ ε / 4 := by
+    simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn y hy).le
+  have hdiff (y : ℝ) (hy : y ∈ s) :
+      ‖(g y - f N y) - (g x - f N x)‖ ≤ (ε / 2) * ‖y - x‖ := by
+    apply le_of_tendsto (((hfg y hy).sub tendsto_const_nhds).sub
+      ((hfg x hx).sub tendsto_const_nhds)).norm
+    filter_upwards [eventually_ge_atTop N] with n hn
+    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+      (fun z hz => (hf n z hz).sub (hf N z hz)) _ hs hx hy
+    intro z hz
+    calc
+      ‖d n z - d N z‖ ≤ ‖d n z - e z‖ + ‖e z - d N z‖ := norm_sub_le_norm_sub_add_norm_sub ..
+      _ ≤ ε / 2 := by rw [norm_sub_rev (e z)]; linarith [hnear n hn z hz, hnear N le_rfl z hz]
+  filter_upwards [(hf N x hx).isLittleO.bound hε4, self_mem_nhdsWithin] with y hy hys
+  have hlast : ‖(y - x) * (d N x - e x)‖ ≤ (ε / 4) * ‖y - x‖ := by
+    rw [norm_mul, mul_comm]
+    exact mul_le_mul_of_nonneg_right (hnear N le_rfl x hx) (norm_nonneg _)
+  calc
+    ‖g y - g x - (y - x) • e x‖ =
+        ‖((g y - f N y) - (g x - f N x)) +
+          (f N y - f N x - (y - x) • d N x) + (y - x) * (d N x - e x)‖ := by
+      congr 1
+      simp only [smul_eq_mul]
+      ring
+    _ ≤ ‖(g y - f N y) - (g x - f N x)‖ +
+        ‖f N y - f N x - (y - x) • d N x‖ + ‖(y - x) * (d N x - e x)‖ :=
+      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
+    _ ≤ ε * ‖y - x‖ := by linarith [hdiff y hys]
+
+/-- All three derivative relations and the initial trace are closed in the jet norm. -/
+theorem isClosed_graphSubmodule :
+    IsClosed (graphSubmodule (E := E) α T : Set (Ambient (E := E) α T)) := by
+  apply isSeqClosed_iff_isClosed.1
+  intro v w hv hw
+  have cu : Continuous (fun z : Ambient (E := E) α T => z.fst.fst) :=
+    (WithLp.continuous_fst ..).comp (WithLp.continuous_fst ..)
+  have ct : Continuous (fun z : Ambient (E := E) α T => z.fst.snd) :=
+    (WithLp.continuous_snd ..).comp (WithLp.continuous_fst ..)
+  have cd : Continuous (fun z : Ambient (E := E) α T => z.snd.fst) :=
+    (WithLp.continuous_fst ..).comp (WithLp.continuous_snd ..)
+  have cdd : Continuous (fun z : Ambient (E := E) α T => z.snd.snd) :=
+    (WithLp.continuous_snd ..).comp (WithLp.continuous_snd ..)
+  have hu := holder_tendstoUniformly ((cu.tendsto w).comp hw)
+  have ht := holder_tendstoUniformly ((ct.tendsto w).comp hw)
+  have hd := holder_tendstoUniformly ((cd.tendsto w).comp hw)
+  have hdd := holder_tendstoUniformly ((cdd.tendsto w).comp hw)
+  refine ⟨?_, ?_, ?_, ?_⟩
+  · intro x
+    apply tendsto_nhds_unique (hu.tendsto_at (0, x))
+    have heq : (fun n => (v n).fst.fst (0, x)) = fun _ : ℕ => (0 : ℝ) :=
+      funext fun n => (hv n).1 x
+    change Tendsto (fun n => (v n).fst.fst (0, x)) atTop (𝓝 0)
+    rw [heq]
+    exact tendsto_const_nhds
+  · intro t ht' x
+    exact hasFDerivAt_of_tendstoUniformly (hd.comp (fun z : E => (t, z)))
+      (fun n z => (hv n).2.1 t ht' z) (fun z => hu.tendsto_at (t, z)) x
+  · intro t ht' x
+    exact hasFDerivAt_of_tendstoUniformly (hdd.comp (fun z : E => (t, z)))
+      (fun n z => (hv n).2.2.1 t ht' z) (fun z => hd.tendsto_at (t, z)) x
+  · intro t ht' x
+    exact closed_time_derivative (convex_Icc 0 T)
+      (fun n s hs => (hv n).2.2.2 s hs x) (fun s _ => hu.tendsto_at (s, x))
+      (ht.comp (fun s : ℝ => (s, x))).tendstoUniformlyOn ht'
+
+instance instCompleteSpace : CompleteSpace (Graph (E := E) α T) := by
+  letI : CompleteSpace ↥(graphSubmodule (E := E) α T) :=
+    isClosed_graphSubmodule.isComplete.completeSpace_coe
+  let e : Graph (E := E) α T ≃ᵢ ↥(graphSubmodule (E := E) α T) :=
+    { graphEquiv with isometry_toFun := fun _ _ => rfl }
+  exact e.completeSpace
+
+end Poincare.ParabolicSolutionGraph

exit_code=0
```

### Successful standalone limit probes

These two successful outputs were returned by the tool during construction.
The initial sequential log naming overlapped concurrent commands; these
short outputs are retained here from that returned transcript. The failed
time-limit output and all final module checks are in the logs above.

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-graph-evidence/time-limit.lean

exit_code=0

$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-graph-evidence/uniform.lean

exit_code=0
```
