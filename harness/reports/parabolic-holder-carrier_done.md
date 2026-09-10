# Parabolic Hölder carrier: done

Date: 2026-09-10 UTC. Worker result, pending independent orchestrator review.

Base: `c46220fb2dea444a71cfdca3764dcb0370a2afee`.
Branch: `worker/parabolic-holder-carrier`.
Worktree: `/private/tmp/poincare-workers/parabolic-holder-carrier`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

Verified proof commits:

- `a3c0aed6592453cdc0d123fc80a77f01967eb5ae`: complete sum-norm carrier and its constructor, pointwise bounds, and supremum identities.
- `38a0cf0c2171d83b33054c0c2d7c186ca68df931`: sharp multiplication, contractive restriction, exact carrier characterization, and pointwise algebra laws.

The only added Lean module is `Poincare/Global/ParabolicHolderSpace.lean`, 444 lines. Existing Lean files, the root import, audit scripts, frozen task, missions, and ledgers are unchanged. This report is the worker handoff; the result is not merged or marked accepted.

## Result and representation

`Poincare.ParabolicHolder.Y (E := E) α T F` has `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ`, and, when `F` is complete, `CompleteSpace` instances. The construction needs only `NormedAddCommGroup E`; it therefore also applies to the requested real normed domain. Neither a restriction on `α` nor a sign condition on `T` is needed for the carrier. In particular it specializes to the survey's `0 < α < 1`, `0 < T ≤ 1`.

The representation is a submodule subtype, storing a bounded total function and its bounded scaled differences in `WithLp 1 (lp … ∞ × lp … ∞)`. A support equation requires the function to vanish off `Icc 0 T ×ˢ univ`. A graph equation forces every difference coordinate to equal

```lean
(parabolicDist p q ^ α)⁻¹ • (f p - f q)
```

for distinct points in the cylinder. Boundedness witnesses live in the two `lp` factors. The constructor `ofFunction` takes exactly the requested support equation and the two existential witnesses. `exists_rep_iff` proves that these conditions are equivalent to having a representative in `Y`. Thus this representation includes every bounded Hölder function on the cylinder, with its unique zero extension; it does not impose a smooth-approximation condition or any extra regularity.

Both norm pieces are defined as real `sSup` values with zero inserted to handle empty cylinders and empty pair sets. `supNorm_bddAbove` and `holderSeminorm_bddAbove` supply the bounds on `Y`. The exact formula is proved by `norm_eq`:

```lean
‖f‖ = supNorm (cylinder T) f + holderSeminorm α (cylinder T) f
```

The norm axioms come from the submodule of the sum-norm product, with the displayed formula identifying that norm with the requested one. `ext` shows that cylinder values determine the entire representation.

Completeness is proved by `isClosed_holderSubmodule`: every support and scaled-difference equation is closed, since evaluation in either `lp` factor is continuous. Their intersection is closed in the complete sum-norm product. The instance follows from `IsComplete.completeSpace_coe`. This carries both values and scaled differences through the limit, so convergence is in the full Hölder norm. It uses `lp` completeness, with no bounded-continuous-function carrier or theorem in the proof.

## Bridges

All requested bridge declarations compile:

| Declaration | Proved conclusion |
| --- | --- |
| `norm_eq` | Exact supremum-plus-seminorm formula |
| `norm_le` | `‖f p‖ ≤ ‖f‖`, even for points outside the cylinder |
| `holder_le` | `‖f p - f q‖ ≤ ‖f‖ * parabolicDist p q ^ α` for cylinder points |
| `mul_mem` | Pointwise real multiplication remains in `Y`, with `‖f * g‖ ≤ ‖f‖ * ‖g‖` |
| `restrict_le` | `‖restrict hT f‖ ≤ ‖f‖` whenever `hT : T' ≤ T` |

`product_holderBound` also keeps the sharper separate constants, giving a Hölder bound of `supNorm f * holderSeminorm g + holderSeminorm f * supNorm g`. Restriction agrees with the original function on the smaller cylinder and vanishes outside it. The product has a `Mul` instance and `mul_apply` identifies its values.

## What is proved where

- **Newly proved in this worker branch:** the parabolic distance lemmas, exact carrier characterization, sum-norm identification, closed-graph completeness, pointwise bounds, product estimate, and restriction estimate.
- **Already in the pinned Mathlib:** `lp` bounded-function spaces and completeness, `WithLp` sum-product norm and completeness, continuous coordinate evaluation, normed submodules, and completeness of closed subsets. Exact source searches and compiler outputs are below.
- **Absent from this delivered module:** the derivative graph `X_T`, K2/Duhamel regularity, the Schauder inverse, and a nonlinear PDE solution. No completion of those tasks or of the Poincaré conjecture is claimed.

## Acceptance evidence

The exact stop condition was reached. The final module has no Lean diagnostics.

| Check | Actual result |
| --- | --- |
| `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean` | Exit 0, empty output |
| Required `rg` forbidden-token scan | Exit 1, empty output, meaning no matches |
| `git diff --check` and base-to-proof-head whitespace check | Exit 0, empty output |
| Focused repository gate, including `lake build` | Exit 0, `GATE_SCAN declarations=54 nonstandard=[]`, `GATE: PASS` |
| Exact dependency check, including generated internal declarations | Exit 0, `EXACT_ALL_DECLARATIONS=72 PASS` |
| Generic and concrete consumer probe | Exit 0; all five instances, bounded evaluation, and Banach fixed-point application compile |

Every one of the 72 declarations emitted for the new module was checked with `#print axioms` and has exactly `[propext, Classical.choice, Quot.sound]`. The module contains 52 authored declarations, 54 noninternal declarations after generated equation/extensionality declarations, and 72 including internal generated proofs.

The consumer probe specializes the carrier to `ClosedSmoothModel 3`, including scalar and bilinear-form targets. It constructs bounded evaluation as a `ContinuousLinearMap` and applies Mathlib's `ContractingWith.fixedPoint` to a contracting self-map on the generic carrier.

The cloned cache initially lacked `Mathlib.Analysis.Normed.Lp.lpSpace.olean`. A focused build of that Mathlib module succeeded. No overlapping full project build was launched. Initial failed compiler probes and their actual diagnostics are retained below, including errors in temporary acceptance scripts that were corrected before their final passing runs.

## Dated handoff

As of 2026-09-10, proof head `38a0cf0c2171d83b33054c0c2d7c186ca68df931` is verified on the worker branch. The central handoff and ledgers were left unchanged for the orchestrator.

Exact first action for the reviewer:

```sh
git diff c46220fb2dea444a71cfdca3764dcb0370a2afee..38a0cf0c2171d83b33054c0c2d7c186ca68df931 -- Poincare/Global/ParabolicHolderSpace.lean
```

Then independently rerun the focused gate and the exact-dependency probe below in the review worktree. No root integration is performed by this worker.

## Reproducible exact-dependency probe

Save the following as `/tmp/parabolic-holder-evidence/AllAxioms.lean` after the focused module build. The actual command and full output are in the transcript.

```lean
import Poincare.Global.ParabolicHolderSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicHolderSpace | throwError "module not found"
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
import Poincare.Global.ParabolicHolderSpace
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Topology.MetricSpace.Contracting

open Poincare.ParabolicHolder
open scoped NNReal
noncomputable section
section General
variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (α T : ℝ)
#synth AddCommGroup (Y (E := E) α T F)
#synth Module ℝ (Y (E := E) α T F)
#synth NormedAddCommGroup (Y (E := E) α T F)
#synth NormedSpace ℝ (Y (E := E) α T F)
#synth CompleteSpace (Y (E := E) α T F)
example (p : ℝ × E) : ∃ L : Y (E := E) α T F →L[ℝ] F, ∀ f, L f = f p := by
  let L : Y (E := E) α T F →ₗ[ℝ] F :=
    { toFun := fun f => f p, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact ⟨L.mkContinuous 1 (fun f => by simpa using norm_le f p), fun _ => rfl⟩
example (f : Y (E := E) α T F → Y (E := E) α T F) {K : ℝ≥0}
    (hf : ContractingWith K f) : ∃ x, f x = x :=
  ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt⟩
end General

section Concrete
variable (α T : ℝ)
#synth NormedSpace ℝ (Y (E := Poincare.ClosedSmoothModel 3) α T ℝ)
#synth CompleteSpace (Y (E := Poincare.ClosedSmoothModel 3) α T ℝ)
#synth CompleteSpace (Y (E := Poincare.ClosedSmoothModel 3) α T
  (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
end Concrete

#check Poincare.ParabolicHolder.norm_eq
#check Poincare.ParabolicHolder.norm_le
#check Poincare.ParabolicHolder.holder_le
#check Poincare.ParabolicHolder.mul_mem
#check Poincare.ParabolicHolder.restrict_le
#check Poincare.ParabolicHolder.exists_rep_iff
```

## Actual probe transcript

The transcript preserves completed command outputs, including unsuccessful attempts. Each later passing run supersedes the earlier diagnostic for that command.

### Probe 2026-09-10T19:04:02.218760+00:00

```sh
sed -n '132,190p' harness/reports/parabolic-schauder-decomposition-survey_done.md; sed -n '350,460p' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean; sed -n '570,615p' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean
```

Exit: 0

```text
### 3.1 Choose a norm that can actually close the equation

Fix `0 < α < 1`, `0 < T ≤ 1`, `Q_T=[0,T]×ℝ³`, and

\[
 d_p((t,x),(s,y))=\|x-y\|+\sqrt{|t-s|},\qquad
 [f]_{\alpha;p}=\sup_{p\ne q}\frac{\|f(p)-f(q)\|}{d_p(p,q)^\alpha}.
\]

Define `Y_T` as bounded functions with finite displayed seminorm and norm `‖f‖∞+[f]α;p`. Define `X_T` as actual derivative graphs `(u,ut,Du,DDu)` with zero initial value, the three derivative relations of the frozen target, and finite `Y_T` norm for each component; use the sum of their four norms. Use functions on the cylinder, or identify total extensions that agree there, so that the norm is definite. Arbitrary values outside the cylinder must not create a kernel in the norm. Time derivatives at the endpoints are within `[0,T]`, exactly as in the frozen linear target.

This is an implementable carrier definition now, not an already proved Banach instance. Prove completeness by putting the jets in a finite product of complete Hölder spaces and proving that the actual derivative graph and initial trace are closed under uniform convergence. Uniform convergence of values alone is insufficient. Prove uniqueness of derivatives on the nondegenerate time interval and spatial domain. Do not define the space merely as the completion of smooth functions and assume that all big-Hölder forcing is approximable in the same exponent; that would instead impose a little-Hölder restriction.

These norms imply exactly the frozen `parabolicBound` conclusions after a harmless constant comparison. The raw `linearSchauderGoal` is re-elaborated unchanged in Appendix D using local bindings. It gives existence and bounds for each forcing, but does not by itself give uniqueness, linear dependence or operator bounds uniform as `T→0`. All three are needed for tasks 4 and 5 and must be proved by the construction. Preserve constants before the forcing quantifier and obtain a single estimate for restrictions to all sufficiently short intervals.

### 3.2 Constant coefficients, localization and correction

| Step | Exact mathematical target and proof route | Class / new gap / estimated effort |
| --- | --- | --- |
| L0. Hölder spaces and jets | Complete `Y_T` and the zero-trace graph `X_T`; bounded evaluation, trace, restriction and multiplication. Prove `[af]α ≤ ‖a‖∞[f]α+[a]α‖f‖∞`. | A for raw product inequalities; B for the graph/norm package and interpolation. No audited parabolic graph-completeness theorem. Roughly 2–5 weeks. |
| L1. Scaled kernel moments | K1 below: weighted L¹ Hessian bound and zero tensor integral, with constants independent of `0<t≤1`. Use the landed pointwise Hessian bound, Gaussian absorption and dilation. | A candidate, roughly 1–2 weeks. No new general PDE theory, but a nontrivial quantitative integral proof is still required. |
| L2. Canceling Duhamel Hessian | K2 below: actual C² spatial derivative and its integral formula, `‖D²u(t)‖∞ ≤ (2Cα/α) K t^(α/2)` from a uniform spatial Hölder constant `K` for the forcing. Work with truncated time integrals and pass actual derivatives to the limit. | B, bounded subtask, roughly 2–4 weeks. Missing endpoint differentiation/cancellation estimate, not the existing positive-time heat smoothing theorem. |
| L3. Full constant-coefficient inverse | For `u(t)=∫₀ᵗH_(t-s)f(s)ds`, prove the PDE, initial trace, `ut=f+Δu`, and `‖u‖X_T ≤ Cα‖f‖Y_T` uniformly for `T≤1`. In particular `[D²u]α;p` and `[ut]α;p` must be bounded. | B, roughly 1–3 months after L0–L2. Missing parabolic singular-integral Hölder estimate. Split increments at time scale `d_p(p,q)^2`; the far part needs higher spatial/time kernel difference bounds, beyond K1. |
| L4. Frozen elliptic matrix | Transport L3 through a linear coordinate equivalence for a fixed symmetric positive matrix `A₀`; prove measure/derivative/norm comparisons with constants controlled by ellipticity and the upper matrix bound. | B small, roughly 1–3 weeks; a supplied factorization transfer is A. The quantitative anisotropic heat-operator theorem is absent. No unprobed matrix-square-root name is assumed here. |
| L5. Coefficient error | On a localized cylinder, bound `(a-A₀):D²u` in `Y_T`, then compose with the local inverse. Prove an explicit bound less than one using spatial radius, time length, coefficient Hölder bounds and zero-trace interpolation. | B, roughly 3–6 weeks after L3. Uniform continuity alone does not give a Hölder multiplier estimate. The required product and interpolation bounds are not supplied by a BUC contraction. |
| L6. Parametrix on ℝ³ | Use a uniformly locally finite spatial covering with uniform buffers/cutoffs; sum localized frozen solvers and estimate principal errors and cutoff commutators. Construct bounded `P` with `L P=Id-R`, `‖R‖<1`. | B, roughly 1–3 months. A finite covering of all ℝ³ by bounded patches is unavailable. This is required for the literal whole-space task 3. |
| L7. Neumann correction | Set `S=P(Id-R)⁻¹`. Then `L S=Id`. The complete scratch proof in Appendix E compiles; it uses only completeness of the forcing space for the inverse. | A, already proved in scratch from the explicit norm/error hypotheses. This does not manufacture `P` or its error estimate. |
| L8. Uniqueness and time slabs | Prove uniqueness in the stated bounded class and the interval-consistent solution operator; concatenate controlled short intervals with nonzero initial trace estimates if the final prescribed `T` exceeds the first localization time. | B. The literal task 3 permits every `T≤1`; an existence theorem only on an unspecified shorter interval is not its completion. Trace/control and continuation add approximately 2–5 weeks. |

The crucial estimate at L2 is

\[
 D^2u(t,x)=\int_0^t\int D^2K_{t-s}(y)
       [f(s,x-y)-f(s,x)]\,dy\,ds,
\]

whose norm is bounded by `Cα K ∫₀ᵗ(t-s)^(α/2-1) ds`. This integral equals `(2/α)t^(α/2)`. Without the spatial difference, the Hessian-kernel bound has a nonintegrable `(t-s)⁻¹` singularity. A bound for the integral's value must accompany, rather than replace, integrability and passage to the actual derivative.

For L5, write `b=a-A₀`. Even if `‖b‖∞≤ε`, the product estimate contains

\[
 [bD^2u]_{\alpha;p}
 \le \varepsilon[D^2u]_{\alpha;p}+[a]_{\alpha;p}\|D^2u\|_\infty.
\]

The second term does not disappear when the sup oscillation is small. On a radius-`r` cylinder, use scaled Hölder norms `‖b‖∞+r^α[b]α;p` with parabolic time scale at most `r²`; then bounded Hölder coefficients give smallness as `r→0`. Alternatively, retain the unscaled norms and use K2/zero-trace estimates to make the Hessian sup term small after the local inverse, while keeping the full Hölder part controlled. These are estimates to prove, including cutoff terms, not a theorem inferred solely from uniform continuity.

For an explicit local norm target, use the maximum of the nine coefficient-entry norms, and suppose the extended supported error entries satisfy `‖bᵢⱼ‖∞≤ε` and `[bᵢⱼ]α;p≤Λb`. Let the frozen inverse have `‖D²S₀f‖Y_T≤Cs‖f‖Y_T` and K2 give `‖D²S₀f‖∞≤Ck T^(α/2)‖f‖Y_T`. The component contraction estimate to prove is

\[
 \|b:D^2S_0\|_{Y_T\to Y_T}
 \le 9\bigl(\varepsilon C_s+\Lambda_b C_k T^{\alpha/2}\bigr).
\]

Choosing `9 ε Cs≤1/4` and `9 Λb Ck T^(α/2)≤1/4` makes this error at most `1/2`. First choose the spatial support/buffer so the sup oscillation is small; then keep its finite Hölder/cutoff constants fixed while choosing time. The extension, anisotropic transfer and other parametrix commutators still need their own bounds. This displayed bound is a proposed lemma with explicit hypotheses, not a consequence asserted from uniform continuity alone.

Uniform continuity on the whole strip yields a common modulus of *local* oscillation. It does not make `a(t,x)` uniformly close to one fixed matrix as time shrinks: time-independent spatial variation survives. Continuous coefficients with no Hölder modulus also need not preserve `Y_T` under multiplication. Thus “uniform continuity plus short time implies a small endomorphism of the full Hölder space” is C as stated. The frozen target's bounded parabolic Hölder hypothesis is sufficient data for the intended localization proof.

### 3.3 Immediate consumer: task 4, compatible finite-atlas inverse
def lp (E : α → Type*) [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞) : AddSubgroup (PreLp E) where
  carrier := { f | Memℓp f p }
  zero_mem' := zero_memℓp
  add_mem' := Memℓp.add
  neg_mem' := Memℓp.neg

@[inherit_doc] scoped[lp] notation "ℓ^" p "(" ι ", " E ")" => lp (fun _ : ι ↦ E) p
/-- `ℓ⁰(ι, E)` is the space of finitely supported functions `ι → E`. In general, this should not
be used outside of the context of `ℓ^p(ι, E)` spaces, and one should instead prefer `Finsupp`
in other situations. -/
scoped[lp] notation "ℓ⁰(" ι ", " E ")" => lp (fun _ : ι ↦ E) 0
/-- `ℓ¹(ι, E)` is the space of summable functions `ι → E`. To be more precise, it is the space
of functions whose *norms* are summable, but when `E` is complete these coincide. -/
scoped[lp] notation "ℓ¹(" ι ", " E ")" => lp (fun _ : ι ↦ E) 1
/-- `ℓ²(ι, E)` is the space of square-summable functions `ι → E`. When `E := 𝕜`, with `RCLike 𝕜`,
this is a Hilbert space. -/
scoped[lp] notation "ℓ²(" ι ", " E ")" => lp (fun _ : ι ↦ E) 2

namespace lp

-- TODO: this instance is bad because it inserts `Subtype.val` as the casting function,
-- which abuses definitional equality.
instance coeFun : CoeFun (lp E p) fun _ => ∀ i, E i :=
  ⟨Subtype.val (α := ∀ i, E i)⟩

@[ext]
theorem ext {f g : lp E p} (h : (f : ∀ i, E i) = g) : f = g :=
  Subtype.ext h

theorem eq_zero' [IsEmpty α] (f : lp E p) : f = 0 :=
  Subsingleton.elim f 0

protected theorem monotone {p q : ℝ≥0∞} (hpq : q ≤ p) : lp E q ≤ lp E p :=
  fun _ hf => Memℓp.of_exponent_ge hf hpq

protected theorem memℓp (f : lp E p) : Memℓp f p :=
  f.prop

variable (E p)

@[simp]
theorem coeFn_zero : ⇑(0 : lp E p) = 0 :=
  rfl

variable {E p}

@[simp]
theorem coeFn_neg (f : lp E p) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem coeFn_add (f g : lp E p) : ⇑(f + g) = f + g :=
  rfl

variable (p E) in
/-- Coercion to function as an `AddMonoidHom`. -/
def coeFnAddMonoidHom : lp E p →+ (∀ i, E i) where
  toFun := (⇑)
  __ := AddSubgroup.subtype _

@[simp]
theorem coeFnAddMonoidHom_apply (x : lp E p) : coeFnAddMonoidHom E p x = ⇑x := rfl

theorem coeFn_sum {ι : Type*} (f : ι → lp E p) (s : Finset ι) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  (lp E p).val_finsetSum f s

@[simp]
theorem coeFn_sub (f g : lp E p) : ⇑(f - g) = f - g :=
  rfl

instance : Norm (lp E p) where
  norm f :=
    if hp : p = 0 then by
      subst hp
      exact ((lp.memℓp f).finite_dsupport.toFinset.card : ℝ)
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

theorem norm_eq_card_dsupport (f : lp E 0) : ‖f‖ = (lp.memℓp f).finite_dsupport.toFinset.card :=
  dif_pos rfl

theorem norm_eq_ciSup (f : lp E ∞) : ‖f‖ = ⨆ i, ‖f i‖ := rfl

theorem isLUB_norm [Nonempty α] (f : lp E ∞) : IsLUB (Set.range fun i => ‖f i‖) ‖f‖ := by
  rw [lp.norm_eq_ciSup]
  exact isLUB_ciSup (lp.memℓp f)

theorem norm_eq_tsum_rpow (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ = (∑' i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  dsimp [norm]
  rw [ENNReal.toReal_pos_iff] at hp
  rw [dif_neg hp.1.ne', if_neg hp.2.ne]

theorem norm_rpow_eq_tsum (hp : 0 < p.toReal) (f : lp E p) :
    ‖f‖ ^ p.toReal = ∑' i, ‖f i‖ ^ p.toReal := by
  rw [norm_eq_tsum_rpow hp, ← Real.rpow_mul]
  · field_simp
    simp
  positivity

theorem hasSum_norm (hp : 0 < p.toReal) (f : lp E p) :
    HasSum (fun i => ‖f i‖ ^ p.toReal) (‖f‖ ^ p.toReal) := by
  rw [norm_rpow_eq_tsum hp]
  exact ((lp.memℓp f).summable hp).hasSum

/-- The sequence of norms of `x : lp E p` as a term of `ℓ^p(α, ℝ)`. Here `E : α → Type*`
is a dependent type and `ℓ^p(α, ℝ)` is the non-dependent `ℝ`-valued `lp` space. -/
@[simps]
def toNorm {p : ℝ≥0∞} (x : lp E p) : ℓ^p(α, ℝ) :=
  ⟨fun i ↦ ‖x i‖, lp.memℓp x |>.norm⟩

  rw [← hC.tsum_eq] at hC'
  exact ⟨hC.summable, hC'⟩

protected theorem summable_mul {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : Summable fun i => ‖f i‖ * ‖g i‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).1

protected theorem tsum_mul_le_mul_norm' {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (f : lp E p) (g : lp E q) : ∑' i, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
  (lp.tsum_mul_le_mul_norm hpq f g).2

section ComparePointwise

theorem norm_apply_le_norm (hp : p ≠ 0) (f : lp E p) (i : α) : ‖f i‖ ≤ ‖f‖ := by
  rcases eq_or_ne p ∞ with (rfl | hp')
  · haveI : Nonempty α := ⟨i⟩
    exact (isLUB_norm f).1 ⟨i, rfl⟩
  have hp'' : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i ↦ by positivity
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg' _) hp'']
  convert le_hasSum (hasSum_norm hp'' f) i fun i _ => this i

lemma lipschitzWith_one_eval (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : α) :
    LipschitzWith 1 (fun x : lp E p ↦ x i) :=
  .mk_one fun _ _ ↦ by
    simp_rw [dist_eq_norm, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' ..

theorem sum_rpow_le_norm_rpow (hp : 0 < p.toReal) (f : lp E p) (s : Finset α) :
    ∑ i ∈ s, ‖f i‖ ^ p.toReal ≤ ‖f‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp f]
  have : ∀ i, 0 ≤ ‖f i‖ ^ p.toReal := fun i ↦ by positivity
  refine Summable.sum_le_tsum _ (fun i _ => this i) ?_
  exact (lp.memℓp f).summable hp

theorem norm_le_of_forall_le' [Nonempty α] {f : lp E ∞} (C : ℝ) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  refine (isLUB_norm f).2 ?_
  rintro - ⟨i, rfl⟩
  exact hCf i

theorem norm_le_of_forall_le {f : lp E ∞} {C : ℝ} (hC : 0 ≤ C) (hCf : ∀ i, ‖f i‖ ≤ C) :
    ‖f‖ ≤ C := by
  cases isEmpty_or_nonempty α
  · simpa [eq_zero' f] using hC
  · exact norm_le_of_forall_le' C hCf
```

### Probe 2026-09-10T19:04:02.323613+00:00

```sh
rg -n 'norm.*one|norm.*eq|linearEquiv|continuous.*(fst|snd)|completeSpace' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean; rg -n 'induced|isometry.*norm|completeSpace.*[Ii]s[Cc]losed|isClosed.*completeSpace|completeSpace_coe' .lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean .lake/packages/mathlib/Mathlib/Topology/UniformSpace/CompleteSeparated.lean
```

Exit: 0

```text
272:separate from `WithLp.instProdSeminormedAddCommGroup` since the latter requires the type class
289:theorem prod_norm_eq_card (f : WithLp 0 (α × β)) :
293:theorem prod_norm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := rfl
295:theorem prod_norm_eq_add (hp : 0 < p.toReal) (f : WithLp p (α × β)) :
494:protected lemma continuous_fst : Continuous (@WithLp.fst p α β) :=
495:  continuous_fst.comp <| prod_continuous_ofLp ..
498:protected lemma continuous_snd : Continuous (@WithLp.snd p α β) :=
499:  continuous_snd.comp <| prod_continuous_ofLp ..
542:  (uniformEquivProd p α β).completeSpace_iff.2 inferInstance
556:  toLinearEquiv := WithLp.linearEquiv _ _ _
568:  cont := WithLp.continuous_fst ..
574:  cont := WithLp.continuous_snd ..
680:    · simp only [prod_dist_eq_sup, prod_norm_eq_sup, dist_eq_norm, ← norm_neg_add]
683:        prod_norm_eq_add (zero_lt_one.trans_le h), dist_eq_norm, ← norm_neg_add]
743:theorem prod_norm_eq_of_nat [Norm α] [Norm β] (n : ℕ) (h : p = n) (f : WithLp p (α × β)) :
747:    prod_norm_eq_add this]
751:theorem prod_nnnorm_eq_add (hp : p ≠ ∞) (f : WithLp p (α × β)) :
754:  simp [prod_norm_eq_add (p.toReal_pos_iff_ne_top.mpr hp)]
756:theorem prod_nnnorm_eq_sup (f : WithLp ∞ (α × β)) : ‖f‖₊ = ‖f.fst‖₊ ⊔ ‖f.snd‖₊ := by
761:  rw [prod_nnnorm_eq_sup, Prod.nnnorm_def, ofLp_fst, ofLp_snd]
774:theorem prod_norm_eq_of_L1 (x : WithLp 1 (α × β)) :
776:  simp [prod_norm_eq_add]
778:theorem prod_nnnorm_eq_of_L1 (x : WithLp 1 (α × β)) :
782:    exact prod_norm_eq_of_L1 x
786:  simp_rw [dist_eq_norm, prod_norm_eq_of_L1, sub_fst, sub_snd]
802:theorem prod_norm_eq_of_L2 (x : WithLp 2 (α × β)) :
804:  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
807:theorem prod_nnnorm_eq_of_L2 (x : WithLp 2 (α × β)) :
811:    exact prod_norm_eq_of_L2 x
813:theorem prod_norm_sq_eq_of_L2 (x : WithLp 2 (α × β)) : ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 := by
816:  rw [prod_nnnorm_eq_of_L2, NNReal.sq_sqrt]
820:  simp_rw [dist_eq_norm, prod_norm_eq_of_L2, sub_fst, sub_snd]
843:    simp [prod_nnnorm_eq_sup]
846:    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
851:    simp [prod_nnnorm_eq_sup]
854:    simp [prod_nnnorm_eq_add, NNReal.zero_rpow hp0, ← NNReal.rpow_mul, mul_inv_cancel₀ hp0]
867:  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
873:  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← toLp_sub, Prod.mk_sub_mk, sub_zero,
906:      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_le_iff hp0,
931:      rw [prod_nnnorm_eq_add hpt, prod_nnnorm_eq_add hpt, one_div, NNReal.rpow_inv_eq_iff hp0.ne',
972:theorem prod_norm_eq_idemFst_sup_idemSnd (x : WithLp ∞ (α × β)) :
974:  rw [WithLp.prod_norm_eq_sup, ← WithLp.norm_toLp_fst ∞ α β x.fst,
978:lemma prod_norm_eq_add_idemFst [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (α × β)) :
980:  rw [WithLp.prod_norm_eq_add hp, ← WithLp.norm_toLp_fst p α β x.fst,
984:lemma prod_norm_eq_idemFst_of_L1 (x : WithLp 1 (α × β)) : ‖x‖ = ‖idemFst x‖ + ‖idemSnd x‖ := by
985:  rw [prod_norm_eq_add_idemFst (lt_of_lt_of_eq zero_lt_one toReal_one.symm)]
1035:    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
1082:    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
1227:  __ := (WithLp.linearEquiv _ _ _).trans LinearEquiv.prodUnique
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:714:abbrev SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:716:  fast_instance% { PseudoMetricSpace.induced f toPseudoMetricSpace with
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:725:abbrev SeminormedCommGroup.induced
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:728:  fast_instance% { SeminormedGroup.induced E F f with
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:736:abbrev NormedGroup.induced
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:739:  fast_instance% { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:746:abbrev NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:748:  fast_instance% { SeminormedCommGroup.induced E F f, MetricSpace.induced f h _ with }
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:268:induced metric space structure on the source space. -/
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:275:induced pseudometric space structure on the source space. -/
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:281:theorem PseudoEMetricSpace.isometry_induced (f : α → β) [m : PseudoEMetricSpace β] :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:282:    letI := m.induced f; Isometry f := fun _ _ ↦ rfl
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:284:theorem PseudoMetricSpace.isometry_induced (f : α → β) [m : PseudoMetricSpace β] :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:285:    letI := m.induced f; Isometry f := fun _ _ ↦ rfl
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:287:theorem EMetricSpace.isometry_induced (f : α → β) (hf : f.Injective) [m : EMetricSpace β] :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:288:    letI := m.induced f hf; Isometry f := fun _ _ ↦ rfl
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:290:theorem MetricSpace.isometry_induced (f : α → β) (hf : f.Injective) [m : MetricSpace β] :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:291:    letI := m.induced f hf; Isometry f := fun _ _ ↦ rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:106:  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:186:domain, using the `SeminormedAddCommGroup.induced` norm.
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:189:abbrev NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:191:    @NormedSpace 𝕜 E _ (SeminormedAddCommGroup.induced E G f) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:192:  letI := SeminormedAddCommGroup.induced E G f
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:393:`NormedAlgebra` structure on the domain, using the `SeminormedRing.induced` norm.
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:396:abbrev NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:399:    @NormedAlgebra 𝕜 R _ (SeminormedRing.induced R S f) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:400:  letI := SeminormedRing.induced R S f
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:405:  fast_instance% NormedAlgebra.induced 𝕜 S A S.val
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:600:already has an existing uniform space structure. This requires a proof that the uniformity induced
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:611:already has an existing topology. This requires a proof that the topology induced
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:624:that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise for
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:646:induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:657:induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:669:proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:705:induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:719:induced by the norm is equal to the preexisting uniformity. See note [reducible non-instances]. -/
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean:735:proofs that the uniformity induced by the norm is equal to the preexisting uniformity, and likewise
```

### Probe 2026-09-10T19:04:30.345766+00:00

```sh
rg -n 'isClosed_iInter|isClosed_setOf_forall|isClosed_eq|isClosed.*isComplete|IsClosed.completeSpace_coe' .lake/packages/mathlib/Mathlib/Topology/{Basic.lean,UniformSpace,MetricSpace} | head -55; sed -n '1235,1260p' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean; sed -n '530,575p' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean; rg -n 'toLp_(add|smul)|add_fst|smul_fst' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean; rg -n 'sqrt_eq_zero|rpow_pos_of_pos|sqrt_pos|norm_sub_rev|abs_sub_comm' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/{Pow/Real.lean,Sqrt.lean} .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean | head -35
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Topology/Basic.lean:147:theorem isClosed_iInter {f : ι → Set X} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
.lake/packages/mathlib/Mathlib/Topology/Basic.lean:152:  isClosed_iInter fun i => isClosed_iInter <| h i
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/AbstractCompletion.lean:112:  funext fun a => pkg.induction_on a (isClosed_eq hf hg) h
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/AbstractCompletion.lean:165:    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean:222:    isClosed_eq (continuous_eval_const _) continuous_const
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean:224:    isClosed_eq (continuous_eval_const _) continuous_const
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean:226:    isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean:230:    isClosed_eq (continuous_eval_const _) continuous_const
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/GromovHausdorffRealized.lean:245:      | apply isClosed_iInter _
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Closeds.lean:131:  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Completion.lean:60:  · refine isClosed_eq ?_ continuous_const
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Completion.lean:67:  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Completion.lean:195:    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ ↦ by
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Completion.lean:225:    | hp => exact isClosed_eq (continuous_dist.comp₂ (continuous_map.comp continuous_fst)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:320:instance IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s] :
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:563:    isClosed_closure.isComplete.completeSpace_coe
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean:580:    · exact isClosed_eq (SeparationQuotient.continuous_mk.comp (hg'.comp hfwd).continuous)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Polish.lean:87:    exact hf.isClosed_range.isComplete
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean:63:lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Closeds.lean:749:  isUniformEmbedding_toCompacts.completeSpace isClosedEmbedding_toCompacts.isClosed_range.isComplete
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Closeds.lean:768:        isClosedEmbedding_toCompacts.isClosed_range.isComplete
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean:800:  refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Pi.lean:140:  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Pi.lean:141:    isClosed_eq (continuous_apply _) (continuous_apply _)
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Completion.lean:533:  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Completion.lean:538:      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a ↦ ?_
section Eval

variable [NormedRing 𝕜] [∀ i, Module 𝕜 (E i)] [∀ i, IsBoundedSMul 𝕜 (E i)] {p q r : ℝ≥0∞}

variable (E p) in
/-- Evaluation at a single coordinate, as a linear map on `lp E p`. -/
@[simps]
def evalₗ (i : α) : lp E p →ₗ[𝕜] E i where
  toFun f := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E p) in
/-- Evaluation at a single coordinate, as a continuous linear map on `lp E p`. -/
def evalCLM [Fact (1 ≤ p)] (i : α) : lp E p →L[𝕜] E i :=
  (evalₗ E p i).mkContinuous 1 fun x ↦ by
    have hp : p ≠ 0 := zero_lt_one.trans_le Fact.out |>.ne'
    simpa only [evalₗ_apply, one_mul, ge_iff_le] using norm_apply_le_norm hp x i

end Eval

section Topology

open Filter

open scoped Topology uniformity
  uniformContinuous_invFun := prod_uniformContinuous_toLp p α β

@[simp]
lemma toHomeomorph_uniformEquivProd :
    (uniformEquivProd p α β).toHomeomorph = homeomorphProd p α β := rfl

@[simp]
lemma toEquiv_uniformEquivProd : (uniformEquivProd p α β).toEquiv = WithLp.equiv p (α × β) := rfl

variable [CompleteSpace α] [CompleteSpace β]

instance instProdCompleteSpace : CompleteSpace (WithLp p (α × β)) :=
  (uniformEquivProd p α β).completeSpace_iff.2 inferInstance

end UniformSpace

section ContinuousLinearEquiv

variable [TopologicalSpace α] [TopologicalSpace β]
variable [Semiring 𝕜] [AddCommGroup α] [AddCommGroup β]
variable [Module 𝕜 α] [Module 𝕜 β]

/-- `WithLp.equiv` as a continuous linear equivalence. -/
-- This is not specific to products and should be generalised!
@[simps!]
def prodContinuousLinearEquiv : WithLp p (α × β) ≃L[𝕜] α × β where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_toFun := prod_continuous_ofLp p α β
  continuous_invFun := prod_continuous_toLp p α β

@[simp]
lemma prodContinuousLinearEquiv_symm_apply (x : α × β) :
    (prodContinuousLinearEquiv p 𝕜 α β).symm x = toLp p x := rfl

/-- `WithLp.fst` as a continuous linear map. -/
@[simps! coe apply]
def fstL : WithLp p (α × β) →L[𝕜] α where
  __ := fstₗ ..
  cont := WithLp.continuous_fst ..

/-- `WithLp.snd` as a continuous linear map. -/
@[simps! coe apply]
def sndL : WithLp p (α × β) →L[𝕜] β where
  __ := sndₗ ..
  cont := WithLp.continuous_snd ..

.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:84:theorem add_fst : (x + y).fst = x.fst + y.fst :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:110:theorem smul_fst : (c • x).fst = c • x.fst :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:933:        ← NNReal.mul_rpow, ← NNReal.mul_rpow, smul_fst, smul_snd, nnnorm_smul, nnnorm_smul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:945:  map_add' := by simp [← toLp_add]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:951:  map_add' := by simp [← toLp_add]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:963:      ← toLp_add, Prod.mk_add_mk, zero_add, add_zero]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:1035:    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:1082:    rw [dist_pseudoMetricSpaceToProd, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean:161:@[simp] lemma toLp_add (x y : V) : toLp p (x + y) = toLp p x + toLp p y := rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean:175:@[simp] lemma toLp_smul [SMul K V] (c : K) (x : V) : toLp p (c • x) = c • (toLp p x) := rfl
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:39:  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:50:  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:51:    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:55:  · have : ↑2 * √x ^ (2 - 1) ≠ 0 := by simp [(sqrt_pos.2 hx).ne', @two_ne_zero ℝ]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:116:theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:360:  (norm_natCast_cpow_of_pos hn _).symm ▸ Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:395:        pure (.positive q(Real.rpow_pos_of_pos $pa $b))
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:492:  rw [exp_log (rpow_pos_of_pos hx y), ← exp_log hx, mul_comm, rpow_def_of_pos (exp_pos (log x)) y]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:496:  ⟨fun h ↦ log_injOn_pos (rpow_pos_of_pos hx _) hz <| log_rpow hx _ |>.trans h,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:537:    exact rpow_pos_of_pos (by rwa [← hx] at hxy) _
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:634:  rw [← log_le_log_iff (rpow_pos_of_pos x_pos y) (rpow_pos_of_pos x_pos z), log_rpow x_pos,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:652:  rw [← log_le_log_iff (rpow_pos_of_pos hx0 y) (rpow_pos_of_pos hx0 z), log_rpow hx0, log_rpow hx0,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:779:  rw [← log_le_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:789:  · exact hx.trans (rpow_pos_of_pos hy _).le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:799:  rw [← log_lt_log_iff hx (rpow_pos_of_pos hy z), log_rpow hy]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:809:  · exact hx.trans_lt (rpow_pos_of_pos hy _)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:819:  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:838:  · exact hx.trans (rpow_pos_of_pos hy _).le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:848:  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:867:  · exact hx.trans_lt (rpow_pos_of_pos hy _)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:883:  have := abs_log_mul_self_lt (x ^ t) (rpow_pos_of_pos h1 t) (rpow_le_one h1.le h2 ht.le)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:891:  exact (log_rpow h ε).symm.trans_le <| (log_le_sub_one_of_pos <| rpow_pos_of_pos h ε).trans
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:994:    rw [sqrt_eq_zero_of_nonpos h.le, rpow_def_of_neg h, this, cos_pi_div_two, mul_zero]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:1132:  apply (Real.rpow_pos_of_pos _ _).ne'
```

### Probe 2026-09-10T19:06:02.429857+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:1:0: error: object file '/private/tmp/poincare-workers/parabolic-holder-carrier/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Normed/Lp/lpSpace.olean' of module Mathlib.Analysis.Normed.Lp.lpSpace does not exist
```

### Probe 2026-09-10T19:06:10.632424+00:00

```sh
rg -n 'csSup_le|le_csSup|csSup_le_csSup|csSup_eq' .lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean | head -50; rg -n 'memℓp_infty_iff|bddAbove' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean | head -15; rg -n 'mem_insert_iff|range_nonempty|bddAbove_insert|norm_sub_le|mul_sub_mul' .lake/packages/mathlib/Mathlib/{Order/Bounds/Basic.lean,Algebra/Ring/Basic.lean,Analysis/Normed/Group/Basic.lean} | head -30
```

Exit: 0

```text
187:theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
191:theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
195:theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
196:  le_trans h (le_csSup hs hb)
199:theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
200:  csSup_le hs fun _ ha => le_csSup ht (h ha)
206:theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
208:  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩
214:theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
223:  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
225:theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
256:theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
258:  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
260:    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha
267:  csSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ)
275:  lt_of_lt_of_le h (le_csSup hs ha)
292:  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)
299:theorem csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s := by bddDefault)
303:theorem csInf_le_csSup_of_nonempty_inter (h : (s ∩ t).Nonempty) (hs : BddBelow s := by bddDefault)
311:  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl
323:  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)
335:  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)
358:  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)
362:  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
367:  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)
372:theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
374:  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)
395:  exact csSup_le hs hb
414:lemma csSup_eq_univ_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup univ := by
420:  csSup_eq_univ_of_not_bddAbove hf
429:  csSup_eq_univ_of_not_bddAbove (α := αᵒᵈ) hs
436:theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
459:    · apply csSup_le s_ne (fun x hx ↦ ?_)
461:      exact hxy.trans (le_csSup Bt yt)
462:    · apply csSup_le t_ne (fun y hy ↦ ?_)
464:      exact hyx.trans (le_csSup Bs xs)
472:  csSup_eq_csSup_of_forall_exists_le (α := αᵒᵈ) hs ht
475:  apply csSup_eq_csSup_of_forall_exists_le
487:theorem csSup_eq_top_of_top_mem [OrderTop α] {s : Set α} (hs : ⊤ ∈ s) : sSup s = ⊤ :=
551:from `csSup_le_iff`. -/
552:theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
555:theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
556:  (csSup_le_iff' ⟨a, h⟩).2 h
561:  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not
563:theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
565:  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩
575:  exact csSup_le' h
585:theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s ⊆ t) : sSup s ≤ sSup t := by
589:  · exact csSup_le_csSup h₁ h h₂
610:      exact le_csSup h₂ ha
90:theorem memℓp_infty_iff {f : ∀ i, E i} : Memℓp f ∞ ↔ BddAbove (Set.range fun i => ‖f i‖) := by
94:  memℓp_infty_iff.2 hf
109:    simpa using ((Set.Finite.of_summable_const (by simp) H).image fun i => ‖f i‖).bddAbove
142:    exact bddAbove_singleton.mono Set.range_const_subset
153:  · simp [memℓp_infty_iff]
166:  · rw [memℓp_infty_iff] at hg ⊢
185:theorem bddAbove {f : ∀ i, E i} (hf : Memℓp f ∞) : BddAbove (Set.range fun i => ‖f i‖) :=
186:  memℓp_infty_iff.1 hf
201:    simpa using hf.bddAbove
214:    obtain ⟨C, hC⟩ := (hfq.finite_dsupport.image fun i => ‖f i‖).bddAbove
228:    obtain ⟨A, hA⟩ := (hfq.summable hq).tendsto_cofinite_zero.bddAbove_range_of_cofinite
256:    obtain ⟨A, hA⟩ := hf.bddAbove
257:    obtain ⟨B, hB⟩ := hg.bddAbove
298:  · obtain ⟨A, hA⟩ := hf.bddAbove
777:    simpa using hf.bddAbove
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:155:attribute [bound] norm_sub_le
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:174:theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:283:@[to_additive norm_add_sub_norm_sub_le_two_mul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:289:@[to_additive norm_add_sub_norm_sub_le_two_mul_min]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1010:@[to_additive eq_of_norm_sub_le_zero]
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:625:theorem bddAbove_insert [IsDirectedOrder α] {s : Set α} {a : α} :
.lake/packages/mathlib/Mathlib/Order/Bounds/Basic.lean:632:  bddAbove_insert.2
```

### Probe 2026-09-10T19:06:19.069400+00:00

```sh
ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Normed/Lp; ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean; cat lakefile.toml; cat lean-toolchain; rg -n 'lpSpace|ProdLp' .lake/packages/mathlib/lakefile.lean
```

Exit: 1

```text
Matrix.ilean
Matrix.ilean.hash
Matrix.ir
Matrix.ir.hash
Matrix.olean
Matrix.olean.hash
Matrix.olean.private
Matrix.olean.private.hash
Matrix.olean.server
Matrix.olean.server.hash
Matrix.trace
MeasurableSpace.ilean
MeasurableSpace.ilean.hash
MeasurableSpace.ir
MeasurableSpace.ir.hash
MeasurableSpace.olean
MeasurableSpace.olean.hash
MeasurableSpace.olean.private
MeasurableSpace.olean.private.hash
MeasurableSpace.olean.server
MeasurableSpace.olean.server.hash
MeasurableSpace.trace
PiLp.ilean
PiLp.ilean.hash
PiLp.ir
PiLp.ir.hash
PiLp.olean
PiLp.olean.hash
PiLp.olean.private
PiLp.olean.private.hash
PiLp.olean.server
PiLp.olean.server.hash
PiLp.trace
ProdLp.ilean
ProdLp.ilean.hash
ProdLp.ir
ProdLp.ir.hash
ProdLp.olean
ProdLp.olean.hash
ProdLp.olean.private
ProdLp.olean.private.hash
ProdLp.olean.server
ProdLp.olean.server.hash
ProdLp.trace
WithLp.ilean
WithLp.ilean.hash
WithLp.ir
WithLp.ir.hash
WithLp.olean
WithLp.olean.hash
WithLp.olean.private
WithLp.olean.private.hash
WithLp.olean.server
WithLp.olean.server.hash
WithLp.trace
ls: .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean: No such file or directory
cat: lakefile.toml: No such file or directory
leanprover/lean4:v4.30.0-rc2
```

### Probe 2026-09-10T19:06:32.074410+00:00

```sh
LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.Normed.Lp.lpSpace Mathlib.Analysis.Normed.Lp.ProdLp
```

Exit: 0

```text
✔ [2016/2022] Built Mathlib.Analysis.Normed.Lp.lpSpace (9.7s)
Build completed successfully (2022 jobs).
```

### Probe 2026-09-10T19:06:33.140545+00:00

```sh
ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/{Abel,Linarith,Positivity,Ring,FunProp}.olean; sed -n '1,75p' lakefile.lean; rg -n '^import' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean
```

Exit: 1

```text
.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Abel.olean
.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/FunProp.olean
.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Linarith.olean
.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Positivity.olean
.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/Ring.olean
import Lake
open Lake DSL

package «poincare» where
  -- This project is a scaffold. It is not a completed formal proof.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Poincare where
  roots := #[`Poincare]

-- Checked-in audit payloads (formerly shell heredocs). Not a default target:
-- `lake build` is unchanged; `lake build PoincareAudit` elaborates the audit surface
-- and Lake caches the result. See scripts/audit_payload_equivalence.py.
lean_lib PoincareAudit where
  srcDir := "audit"
  roots := #[`PoincareAudit]
```

### Probe 2026-09-10T19:06:42.300205+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:65:36: error: expected token
Poincare/Global/ParabolicHolderSpace.lean:67:32: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  AddCommMonoid (Ambient T E F)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ParabolicHolderSpace.lean:99:20: error: Invalid argument name `E` for function `holderSubmodule`

Hint: Perhaps you meant one of the following parameter names:
  • `α`: E̵α̲
  • `T`: E̵T̲
Poincare/Global/ParabolicHolderSpace.lean:103:21: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:105:24: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:108:28: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:112:30: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:114:6: error(lean.unknownIdentifier): Unknown identifier `increment_eq`
Poincare/Global/ParabolicHolderSpace.lean:113:75: error: unsolved goals
α T : ℝ
x✝ : Sort u_3
Y : x✝
f : sorry
i : Pairs (cylinder T)
⊢ ‖sorry‖ = ‖sorry - sorry‖ / parabolicDist (↑i).1 (↑i).2 ^ α
Poincare/Global/ParabolicHolderSpace.lean:118:29: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:122:23: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:123:6: error(lean.unknownIdentifier): Unknown identifier `norm_eq_parts`
Poincare/Global/ParabolicHolderSpace.lean:122:68: error: unsolved goals
E : Type u_1
inst✝ : NormedAddCommGroup E
x✝ : Sort u_3
Y : x✝
f : sorry
p : ℝ × E
⊢ ‖sorry‖ ≤ ‖f‖
Poincare/Global/ParabolicHolderSpace.lean:135:49: error: expected token
Poincare/Global/ParabolicHolderSpace.lean:127:25: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:143:23: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:144:61: error(lean.unknownIdentifier): Unknown identifier `norm_le`
Poincare/Global/ParabolicHolderSpace.lean:144:44: error: Type mismatch
  Exists.intro ‖?m.34‖ ?m.40
has type
  Exists ?m.31
but is expected to have type
  ∃ M, ∀ p ∈ cylinder T, ‖?m.14‖ ≤ M
Poincare/Global/ParabolicHolderSpace.lean:146:30: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:152:39: error: expected token
Poincare/Global/ParabolicHolderSpace.lean:150:30: error: Invalid argument name `E` for function `holderSubmodule`

Hint: Perhaps you meant one of the following parameter names:
  • `α`: E̵α̲
  • `T`: E̵T̲
Poincare/Global/ParabolicHolderSpace.lean:150:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace (Ambient T E F)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ParabolicHolderSpace.lean:151:20: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:151:53: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/ParabolicHolderSpace.lean:151:55: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:151:57: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:152:31: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:152:36: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:150:78: error: unsolved goals
ev₁ : ∀ (p : ℝ × sorry), sorry
⊢ sorry
Poincare/Global/ParabolicHolderSpace.lean:162:46: error: Invalid argument name `E` for function
```

### Probe 2026-09-10T19:07:07.754715+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:66:40: error: don't know how to synthesize implicit argument `α`
  @lp (Pairs (cylinder T)) (fun x => F) (fun i => inst✝) ∞
context:
E✝ : Type u_1
F✝ : Type u_2
inst✝⁴ : NormedAddCommGroup E✝
inst✝³ : NormedAddCommGroup F✝
inst✝² : NormedSpace ℝ F✝
T : ℝ
E : Type u_3
F : Type u_4
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedAddCommGroup F
⊢ Type u_5
Poincare/Global/ParabolicHolderSpace.lean:66:52: error: don't know how to synthesize implicit argument `E`
  @Pairs (?m.17 T E F) (cylinder T)
context:
E✝ : Type u_1
F✝ : Type u_2
inst✝⁴ : NormedAddCommGroup E✝
inst✝³ : NormedAddCommGroup F✝
inst✝² : NormedSpace ℝ F✝
T : ℝ
E : Type u_3
F : Type u_4
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedAddCommGroup F
⊢ Type u_5
Poincare/Global/ParabolicHolderSpace.lean:66:59: error: don't know how to synthesize implicit argument `E`
  @cylinder (?m.17 T E F) T
context:
E✝ : Type u_1
F✝ : Type u_2
inst✝⁴ : NormedAddCommGroup E✝
inst✝³ : NormedAddCommGroup F✝
inst✝² : NormedSpace ℝ F✝
T : ℝ
E : Type u_3
F : Type u_4
inst✝¹ : NormedAddCommGroup E
inst✝ : NormedAddCommGroup F
⊢ Type u_5
Poincare/Global/ParabolicHolderSpace.lean:68:32: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  AddCommMonoid (Ambient T E F)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ParabolicHolderSpace.lean:100:20: error: Invalid argument name `E` for function `holderSubmodule`

Hint: Perhaps you meant one of the following parameter names:
  • `α`: E̵α̲
  • `T`: E̵T̲
Poincare/Global/ParabolicHolderSpace.lean:104:21: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:106:24: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:109:28: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:113:30: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:115:6: error(lean.unknownIdentifier): Unknown identifier `increment_eq`
Poincare/Global/ParabolicHolderSpace.lean:114:75: error: unsolved goals
α T : ℝ
x✝ : Sort u_3
Y : x✝
f : sorry
i : Pairs (cylinder T)
⊢ ‖sorry‖ = ‖sorry - sorry‖ / parabolicDist (↑i).1 (↑i).2 ^ α
Poincare/Global/ParabolicHolderSpace.lean:119:29: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:123:23: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:124:6: error(lean.unknownIdentifier): Unknown identifier `norm_eq_parts`
Poincare/Global/ParabolicHolderSpace.lean:123:68: error: unsolved goals
E : Type u_1
inst✝ : NormedAddCommGroup E
x✝ : Sort u_3
Y : x✝
f : sorry
p : ℝ × E
⊢ ‖sorry‖ ≤ ‖f‖
Poincare/Global/ParabolicHolderSpace.lean:128:25: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:144:23: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:145:61: error(lean.unknownIdentifier): Unknown identifier `norm_le`
Poincare/Global/ParabolicHolderSpace.lean:145:44: error: Type mismatch
  Exists.intro ‖?m.34‖ ?m.40
has type
  Exists ?m.31
but is expected to have type
  ∃ M, ∀ p ∈ cylinder T, ‖?m.14‖ ≤ M
Poincare/Global/ParabolicHolderSpace.lean:147:30: error: Invalid argument name `E` for function
Poincare/Global/ParabolicHolderSpace.lean:151:30: error: Invalid argument name `E` for function `holderSubmodule`

Hint: Perhaps you meant one of the following parameter names:
  • `α`: E̵α̲
  • `T`: E̵T̲
Poincare/Global/ParabolicHolderSpace.lean:151:4: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace (Ambient T E F)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ParabolicHolderSpace.lean:152:20: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:152:53: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/ParabolicHolderSpace.lean:152:55: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:152:57: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:153:31: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:153:36: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:154:32: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/ParabolicHolderSpace.lean:154:66: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/ParabolicHolderSpace.lean:154:68: error(lean.unknownIdentifier): Unknown identifier `E`
Poincare/Global/ParabolicHolderSpace.lean:154:70: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:155:43: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/ParabolicHolderSpace.lean:155:49: error(lean.unknownIdentifier): Unknown identifier `F`
Poincare/Global/ParabolicHolderSpace.lean:151:78: error: unsolved goals
ev₁ : ∀ (p : ℝ × sorry), sorry
⊢ sorry
Poincare/Global/ParabolicHolderSpace.lean:163:46: error: Invalid argument name `E` for function
```

### Probe 2026-09-10T19:07:12.599113+00:00

```sh
rg -n 'ParabolicHolder|holderSeminorm|parabolicDist|def.*Y ' Poincare/Global/HeatMildBUCPositiveHolder.lean Poincare/Global/CompactCoefficientEllipticity.lean; rg -n '^public import|^import' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean; sed -n '312,325p' .lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformEmbedding.lean
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:8:public import Mathlib.Analysis.MeanInequalities
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:9:public import Mathlib.Analysis.Normed.Lp.WithLp
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:8:public import Mathlib.Analysis.MeanInequalities
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:9:public import Mathlib.Analysis.MeanInequalitiesPow
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:10:public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:11:public import Mathlib.Data.Set.Image
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:12:public import Mathlib.Topology.Algebra.ContinuousMonoidHom
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:13:public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
  he.completeSpace_congr e.surjective

theorem completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplete s := by
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_subtype_val.isUniformInducing,
    Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete

instance IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} [hs : IsClosed s] :
    CompleteSpace s := hs.isComplete.completeSpace_coe

theorem completeSpace_ulift_iff : CompleteSpace (ULift α) ↔ CompleteSpace α :=
  IsUniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

```

### Probe 2026-09-10T19:07:23.269417+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:72:15: error: unsolved goals
case left
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
⊢ ∀ (a : ℝ) (b : E), (a, b) ∉ cylinder T → 0 (a, b) = 0

case right
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
⊢ ∀ (i : Pairs (cylinder T)), 0 i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (0 (↑i).1 - 0 (↑i).2)
Poincare/Global/ParabolicHolderSpace.lean:95:6: error: Type mismatch
  Eq.symm (smul_sub c ?m.301 ?m.302)
has type
  c • ?m.301 - c • ?m.302 = c • (?m.301 - ?m.302)
but is expected to have type
  c • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2) = ↑(WithLp.fst (c • v)) (↑i).1 - ↑(WithLp.fst (c • v)) (↑i).2
Poincare/Global/ParabolicHolderSpace.lean:153:60: error: Application type mismatch: The argument
  WithLp.continuous_fst
has type
  ∀ (p : ℝ≥0∞) (α : Type ?u.43882.3979) (β : Type ?u.43882.3978) [inst : TopologicalSpace α]
    [inst_1 : TopologicalSpace β], Continuous WithLp.fst
but is expected to have type
  Continuous WithLp.fst
in the application
  Continuous.comp (ContinuousLinearMap.continuous (lp.evalCLM ℝ (fun x => F) ∞ p)) WithLp.continuous_fst
Poincare/Global/ParabolicHolderSpace.lean:156:6: error: Application type mismatch: The argument
  WithLp.continuous_snd
has type
  ∀ (p : ℝ≥0∞) (α : Type ?u.43882.6512) (β : Type ?u.43882.6511) [inst : TopologicalSpace α]
    [inst_1 : TopologicalSpace β], Continuous WithLp.snd
but is expected to have type
  Continuous WithLp.snd
in the application
  Continuous.comp (ContinuousLinearMap.continuous (lp.evalCLM ℝ (fun x => F) ∞ i)) WithLp.continuous_snd
Poincare/Global/ParabolicHolderSpace.lean:159:4: error: Type mismatch
  isClosed_iInter fun p => isClosed_iInter fun x => isClosed_eq (ev₁ p) continuous_const
has type
  IsClosed (⋂ i, ⋂ i_1, {y | ↑(WithLp.fst y) i = ?m.153 i i_1})
but is expected to have type
  IsClosed fun v => ∀ p ∉ cylinder T, ↑(WithLp.fst v) p = 0
Poincare/Global/ParabolicHolderSpace.lean:160:4: error: Type mismatch
  isClosed_iInter fun i =>
    isClosed_eq (ev₂ i) (Continuous.const_smul (Continuous.sub (ev₁ (↑i).1) (ev₁ (↑i).2)) (?m.198 i))
has type
  IsClosed (⋂ i, {y | ↑(WithLp.snd y) i = ?m.198 i • (↑(WithLp.fst y) (↑i).1 - ↑(WithLp.fst y) (↑i).2)})
but is expected to have type
  IsClosed fun v =>
    ∀ (i : Pairs (cylinder T)),
      ↑(WithLp.snd v) i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2)
```

### Probe 2026-09-10T19:08:39.932185+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:72:15: error: unsolved goals
case left
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
⊢ ∀ (a : ℝ) (b : E), (a, b) ∉ cylinder T → 0 (a, b) = 0

case right
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
⊢ ∀ (i : Pairs (cylinder T)), 0 i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (0 (↑i).1 - 0 (↑i).2)
Poincare/Global/ParabolicHolderSpace.lean:95:6: error: Type mismatch
  Eq.symm (smul_sub c ?m.301 ?m.302)
has type
  c • ?m.301 - c • ?m.302 = c • (?m.301 - ?m.302)
but is expected to have type
  c • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2) = ↑(WithLp.fst (c • v)) (↑i).1 - ↑(WithLp.fst (c • v)) (↑i).2
Poincare/Global/ParabolicHolderSpace.lean:168:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  f p
in the target expression
  (fun i => ‖f i‖) p ≤ max M 0

case neg
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : ℝ × E → F
hoff : ∀ p ∉ cylinder T, f p = 0
hh : ∃ K, HasHolderBound α (cylinder T) f K
M : ℝ
hM : ∀ p ∈ cylinder T, ‖f p‖ ≤ M
p : ℝ × E
hp : p ∉ cylinder T
⊢ (fun i => ‖f i‖) p ≤ max M 0
Poincare/Global/ParabolicHolderSpace.lean:176:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖
in the target expression
  (fun i => ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖) i ≤ K

case hf
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : ℝ × E → F
hoff : ∀ p ∉ cylinder T, f p = 0
hb : ∃ M, ∀ p ∈ cylinder T, ‖f p‖ ≤ M
v : ↥(lp (fun x => F) ∞) := ⟨f, ⋯⟩
K : ℝ
hK : HasHolderBound α (cylinder T) f K
i : Pairs (cylinder T)
⊢ (fun i => ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖) i ≤ K
Poincare/Global/ParabolicHolderSpace.lean:193:8: error(lean.unknownIdentifier): Unknown constant `WithLp.ext`
Poincare/Global/ParabolicHolderSpace.lean:194:2: error: No goals to be solved
Poincare/Global/ParabolicHolderSpace.lean:207:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖↑(WithLp.fst ↑?f) (↑?i).1 - ↑(WithLp.fst ↑?f) (↑?i).2‖ / parabolicDist (↑?i).1 (↑?i).2 ^ ?m.103
in the target expression
  (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖

case inr
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : Y α T F
i : Pairs (cylinder T)
⊢ (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖
Poincare/Global/ParabolicHolderSpace.lean:216:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖↑(WithLp.fst ↑?f) (↑?i).1 - ↑(WithLp.fst ↑?f) (↑?i).2‖ / parabolicDist (↑?i).1 (↑?i).2 ^ ?m.77
in the target expression
  (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖

case a.inr
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : Y α T F
i : Pairs (cylinder T)
⊢ (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖
Poincare/Global/ParabolicHolderSpace.lean:274:60: error: Application type mismatch: The argument
  WithLp.continuous_fst
has type
  ∀ (p : ℝ≥0∞) (α : Type ?u.53724.3979) (β : Type ?u.53724.3978) [inst : TopologicalSpace α]
    [inst_1 : TopologicalSpace β], Continuous WithLp.fst
but is expected to have type
  Continuous WithLp.fst
in the application
  Continuous.comp (ContinuousLinearMap.continuous (lp.evalCLM ℝ (fun x => F) ∞ p)) WithLp.continuous_fst
Poincare/Global/ParabolicHolderSpace.lean:277:6: error: Application type mismatch: The argument
  WithLp.continuous_snd
has type
  ∀ (p : ℝ≥0∞) (α : Type ?u.53724.6512) (β : Type ?u.53724.6511) [inst : TopologicalSpace α]
    [inst_1 : TopologicalSpace β], Continuous WithLp.snd
but is expected to have type
  Continuous WithLp.snd
in the application
  Continuous.comp (ContinuousLinearMap.continuous (lp.evalCLM ℝ (fun x => F) ∞ i)) WithLp.continuous_snd
Poincare/Global/ParabolicHolderSpace.lean:280:4: error: Type mismatch
  isClosed_iInter fun p => isClosed_iInter fun x => isClosed_eq (ev₁ p) continuous_const
has type
  IsClosed (⋂ i, ⋂ i_1, {y | ↑(WithLp.fst y) i = ?m.153 i i_1})
but is expected to have type
  IsClosed fun v => ∀ p ∉ cylinder T, ↑(WithLp.fst v) p = 0
Poincare/Global/ParabolicHolderSpace.lean:281:4: error: Type mismatch
  isClosed_iInter fun i =>
    isClosed_eq (ev₂ i) (Continuous.const_smul (Continuous.sub (ev₁ (↑i).1) (ev₁ (↑i).2)) (?m.198 i))
has type
  IsClosed (⋂ i, {y | ↑(WithLp.snd y) i = ?m.198 i • (↑(WithLp.fst y) (↑i).1 - ↑(WithLp.fst y) (↑i).2)})
but is expected to have type
  IsClosed fun v =>
    ∀ (i : Pairs (cylinder T)),
      ↑(WithLp.snd v) i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2)
```

### Probe 2026-09-10T19:08:56.405226+00:00

```sh
rg -n 'setOf_forall|WithLp.ext|theorem ext|lemma ext' .lake/packages/mathlib/Mathlib/Data/Set/Lattice.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean | head -25
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Data/Set/Lattice.lean:139:theorem setOf_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
```

### Probe 2026-09-10T19:09:04.894175+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:174:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  f p
in the target expression
  (fun i => ‖f i‖) p ≤ max M 0

case neg
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : ℝ × E → F
hoff : ∀ p ∉ cylinder T, f p = 0
hh : ∃ K, HasHolderBound α (cylinder T) f K
M : ℝ
hM : ∀ p ∈ cylinder T, ‖f p‖ ≤ M
p : ℝ × E
hp : p ∉ cylinder T
⊢ (fun i => ‖f i‖) p ≤ max M 0
Poincare/Global/ParabolicHolderSpace.lean:182:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖
in the target expression
  (fun i => ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖) i ≤ K

case hf
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : ℝ × E → F
hoff : ∀ p ∉ cylinder T, f p = 0
hb : ∃ M, ∀ p ∈ cylinder T, ‖f p‖ ≤ M
v : ↥(lp (fun x => F) ∞) := ⟨f, ⋯⟩
K : ℝ
hK : HasHolderBound α (cylinder T) f K
i : Pairs (cylinder T)
⊢ (fun i => ‖(parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2)‖) i ≤ K
Poincare/Global/ParabolicHolderSpace.lean:199:8: error(lean.unknownIdentifier): Unknown constant `WithLp.ext`
Poincare/Global/ParabolicHolderSpace.lean:200:2: error: No goals to be solved
Poincare/Global/ParabolicHolderSpace.lean:213:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖↑(WithLp.fst ↑?f) (↑?i).1 - ↑(WithLp.fst ↑?f) (↑?i).2‖ / parabolicDist (↑?i).1 (↑?i).2 ^ ?m.103
in the target expression
  (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖

case inr
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : Y α T F
i : Pairs (cylinder T)
⊢ (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖
Poincare/Global/ParabolicHolderSpace.lean:222:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖↑(WithLp.fst ↑?f) (↑?i).1 - ↑(WithLp.fst ↑?f) (↑?i).2‖ / parabolicDist (↑?i).1 (↑?i).2 ^ ?m.77
in the target expression
  (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖

case a.inr
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f : Y α T F
i : Pairs (cylinder T)
⊢ (fun i => ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ / parabolicDist (↑i).1 (↑i).2 ^ α) i ≤ ‖WithLp.snd ↑f‖
Poincare/Global/ParabolicHolderSpace.lean:288:4: error: Type mismatch
  isClosed_iInter fun p => isClosed_iInter fun x => isClosed_eq (ev₁ p) continuous_const
has type
  IsClosed (⋂ i, ⋂ i_1, {y | ↑(WithLp.fst y) i = ?m.164 i i_1})
but is expected to have type
  IsClosed fun v => ∀ p ∉ cylinder T, ↑(WithLp.fst v) p = 0
Poincare/Global/ParabolicHolderSpace.lean:290:4: error: Type mismatch
  isClosed_iInter fun i =>
    isClosed_eq (ev₂ i) (Continuous.const_smul (Continuous.sub (ev₁ (↑i).1) (ev₁ (↑i).2)) (?m.210 i))
has type
  IsClosed (⋂ i, {y | ↑(WithLp.snd y) i = ?m.210 i • (↑(WithLp.fst y) (↑i).1 - ↑(WithLp.fst y) (↑i).2)})
but is expected to have type
  IsClosed fun v =>
    ∀ (i : Pairs (cylinder T)),
      ↑(WithLp.snd v) i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2)
Poincare/Global/ParabolicHolderSpace.lean:287:15: warning: This simp argument is unused:
  setOf_forall

Hint: Omit it from the simp argument list.
  simp only ̵[̵s̵e̵t̵O̵f̵_̵f̵o̵r̵a̵l̵l̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/ParabolicHolderSpace.lean:289:15: warning: This simp argument is unused:
  setOf_forall

Hint: Omit it from the simp argument list.
  simp only ̵[̵s̵e̵t̵O̵f̵_̵f̵o̵r̵a̵l̵l̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Probe 2026-09-10T19:09:13.443502+00:00

```sh
rg -n 'injective|inj|ext' .lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean | head -35; rg -n 'mem_insert |mem_insert_of_mem|mem_range_self' .lake/packages/mathlib/Mathlib/Data/Set/{Insert,Image}.lean | head -20
```

Exit: 0

```text
110:lemma ofLp_injective : Function.Injective (@ofLp p V) :=
111:  Function.LeftInverse.injective <| toLp_ofLp _
113:lemma toLp_injective : Function.Injective (@toLp p V) :=
114:  Function.LeftInverse.injective <| ofLp_toLp _
117:  ⟨ofLp_injective p, ofLp_surjective p⟩
120:  ⟨toLp_injective p, toLp_surjective p⟩
170:@[simp] lemma toLp_eq_zero {x : V} : toLp p x = 0 ↔ x = 0 := (toLp_injective p).eq_iff
171:@[simp] lemma ofLp_eq_zero {x : WithLp p V} : ofLp x = 0 ↔ x = 0 := (ofLp_injective p).eq_iff
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:54:theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:57:theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:60:theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:113:  ⟨a, mem_insert a s⟩
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:131:theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:134:theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:142:  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
.lake/packages/mathlib/Mathlib/Data/Set/Insert.lean:335:  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:573:    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ := by grind
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:578:    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ := by grind
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:639:  ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:755:    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:907:  eq_univ_of_forall mem_range_self
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:920:    range f = insert (f ⟨x, mem_insert x s⟩)
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:921:      (range fun y : s ↦ f ⟨y, mem_insert_of_mem _ y.2⟩) := by
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:960:    fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl <| mem_range_self _
```

### Probe 2026-09-10T19:09:16.237164+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:205:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑(WithLp.snd ↑?f) ?i
in the target expression
  ↑(↑f).ofLp.2 i = ↑(↑g).ofLp.2 i

case a.a.h.h
E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f g : Y α T F
h : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p
hval : WithLp.fst ↑f = WithLp.fst ↑g
i : Pairs (cylinder T)
⊢ ↑(↑f).ofLp.2 i = ↑(↑g).ofLp.2 i
Poincare/Global/ParabolicHolderSpace.lean:292:4: error: Type mismatch
  isClosed_iInter fun p => isClosed_iInter fun x => isClosed_eq (ev₁ p) continuous_const
has type
  IsClosed (⋂ i, ⋂ i_1, {y | ↑(WithLp.fst y) i = ?m.164 i i_1})
but is expected to have type
  IsClosed fun v => ∀ p ∉ cylinder T, ↑(WithLp.fst v) p = 0
Poincare/Global/ParabolicHolderSpace.lean:294:4: error: Type mismatch
  isClosed_iInter fun i =>
    isClosed_eq (ev₂ i) (Continuous.const_smul (Continuous.sub (ev₁ (↑i).1) (ev₁ (↑i).2)) (?m.210 i))
has type
  IsClosed (⋂ i, {y | ↑(WithLp.snd y) i = ?m.210 i • (↑(WithLp.fst y) (↑i).1 - ↑(WithLp.fst y) (↑i).2)})
but is expected to have type
  IsClosed fun v =>
    ∀ (i : Pairs (cylinder T)),
      ↑(WithLp.snd v) i = (parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (↑(WithLp.fst v) (↑i).1 - ↑(WithLp.fst v) (↑i).2)
Poincare/Global/ParabolicHolderSpace.lean:291:15: warning: This simp argument is unused:
  setOf_forall

Hint: Omit it from the simp argument list.
  simp only ̵[̵s̵e̵t̵O̵f̵_̵f̵o̵r̵a̵l̵l̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/ParabolicHolderSpace.lean:293:15: warning: This simp argument is unused:
  setOf_forall

Hint: Omit it from the simp argument list.
  simp only ̵[̵s̵e̵t̵O̵f̵_̵f̵o̵r̵a̵l̵l̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

### Probe 2026-09-10T19:09:22.830323+00:00

```sh
rg -n 'iInter_setOf|isClosed.*forall|isClosed.*[Aa]ll' .lake/packages/mathlib/Mathlib/{Data/Set/Lattice.lean,Topology} | head -28
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Data/Set/Lattice.lean:261:theorem iInter_setOf (P : ι → α → Prop) : ⋂ i, { x : α | P i x } = { x : α | ∀ i, P i x } := by
.lake/packages/mathlib/Mathlib/Topology/LocalAtTarget.lean:173:  simp_rw [isClosedEmbedding_iff, forall_and]
.lake/packages/mathlib/Mathlib/Topology/LocallyFinsupp.lean:232:  convert isClosed_sdiff_of_codiscreteWithin ((supportDiscreteWithin_iff_locallyFiniteWithin
.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean:47:  hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace
.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean:210:  hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/PiNat.lean:766:    refine nonempty_iInter_of_nonempty_biInter (fun n => isClosed_closedBall)
.lake/packages/mathlib/Mathlib/Topology/LocallyFinite.lean:127:theorem isClosed_iUnion (hf : LocallyFinite f) (hc : ∀ i, IsClosed (f i)) :
.lake/packages/mathlib/Mathlib/Topology/NoetherianSpace.lean:162:    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:583:  rw [isClosedMap_iff_closure_image, compl_surjective.forall]
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean:514:  refine isClosed_iff_forall_filter.2 fun f u _ hu huf ↦ ?_
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/UniformConvergenceTopology.lean:1103:  refine isClosed_iff_forall_filter.2 fun f u _ hu huf ↦ h.continuous_iff.2 fun s hs ↦ ?_
.lake/packages/mathlib/Mathlib/Topology/LocallyClosed.lean:184:      (by simpa using isClosed_closure.isLocallyClosed)
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:645:theorem Metric.isClosed_closedEBall {a : α} {r : ℝ≥0∞} : IsClosed (closedEBall a r) :=
.lake/packages/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean:649:alias EMetric.isClosed_closedBall := Metric.isClosed_closedEBall
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean:209:    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩
.lake/packages/mathlib/Mathlib/Topology/Compactness/CompactlyGeneratedSpace.lean:355:  rw [isClosed_iff_forall_filter]
.lake/packages/mathlib/Mathlib/Topology/Compactness/CompactlyGeneratedSpace.lean:358:  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
.lake/packages/mathlib/Mathlib/Topology/DiscreteSubset.lean:190:  rw [isDiscrete_iff_nhdsNE, isClosed_iff_clusterPt, ← forall_and]
.lake/packages/mathlib/Mathlib/Topology/Order/IntermediateValue.lean:418:  apply (IsClosed.inter hs isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin hx.2
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:281:theorem isClosed_ball (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x < r} := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:290:  ⟨isClosed_ball _, isOpen_ball _⟩
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:304:theorem isClosed_closedBall (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x ≤ r} := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:317:  ⟨isClosed_closedBall _, isOpen_closedBall hr⟩
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:339:  · convert v.isClosed_closedBall 0 using 3
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:355:  exact isClosed_closedBall _
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:387:@[deprecated (since := "2026-03-17")] alias isClosed_ball := Valuation.isClosed_ball
.lake/packages/mathlib/Mathlib/Topology/Algebra/ValuativeRel/ValuativeTopology.lean:390:@[deprecated (since := "2026-03-17")] alias isClosed_closedBall := Valuation.isClosed_closedBall
.lake/packages/mathlib/Mathlib/Topology/ClusterPt.lean:348:lemma isClosed_iff_forall_filter :
```

### Probe 2026-09-10T19:09:44.020241+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:09:54.375040+00:00

```sh
rg -n 'theorem (norm_smul|norm_mul|norm_sub_le)|lemma (norm_smul|norm_mul)|def equiv' .lake/packages/mathlib/Mathlib/Analysis/Normed/{Group/Basic,Lp/WithLp,Ring/Basic}.lean | head -35; rg -n 'indicator_of_mem|indicator_of_notMem' .lake/packages/mathlib/Mathlib/Algebra/Group/Indicator.lean | head -18
```

Exit: 0

```text
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean:72:protected def equiv : WithLp p V ≃ V where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:98:theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:103:theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:108:lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:112:lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:174:theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:216:lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:222:lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:284:lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:290:lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:803:theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:813:theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:206:theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:211:lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:217:lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:700:@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
```

### Probe 2026-09-10T19:10:15.541842+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/Axioms.lean
```

Exit: 0

```text
'Poincare.ParabolicHolder.parabolicDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.HasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instCoeFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.zero_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.hasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.scaledDifference_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.isClosed_holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instCompleteSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Probe 2026-09-10T19:10:19.847250+00:00

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
(empty)
```

### Probe 2026-09-10T19:10:19.882566+00:00

```sh
git diff --check
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:10:32.199329+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:10:52.175816+00:00

```sh
git add Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:10:52.208968+00:00

```sh
git diff --cached --check
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:10:52.251939+00:00

```sh
git commit -m "Prove completeness of the parabolic Holder sum-norm carrier"
```

Exit: 0

```text
[worker/parabolic-holder-carrier a3c0aed6] Prove completeness of the parabolic Holder sum-norm carrier
 1 file changed, 302 insertions(+)
 create mode 100644 Poincare/Global/ParabolicHolderSpace.lean
```

### Probe 2026-09-10T19:12:16.177613+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:354:24: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑(WithLp.fst ↑f) p
in the target expression
  (fun p => ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p) p = 0

E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T : ℝ
f g : Y α T ℝ
p : ℝ × E
hp : p ∉ cylinder T
⊢ (fun p => ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p) p = 0
Poincare/Global/ParabolicHolderSpace.lean:386:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicHolder.cylinder_mono`:
  [NormedAddCommGroup E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedAddCommGroup E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/ParabolicHolderSpace.lean:393:23: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (p ∈ cylinder T')

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/ParabolicHolderSpace.lean:401:66: error: Type mismatch
  if_pos hp
has type
  (if p ∈ cylinder T' then ?m.26 else ?m.27) = ?m.26
but is expected to have type
  ↑(WithLp.fst ↑(restrict hT f)) p = ↑(WithLp.fst ↑f) p
```

### Probe 2026-09-10T19:12:26.487631+00:00

```sh
sed -n '1,230p' harness/gate.sh; rg -n '^(@|theorem|lemma|def).*norm_mul|^.*lemma.*indicator_of' .lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Indicator.lean | head -20
```

Exit: 0

```text
#!/bin/bash
# Acceptance gate for worker output (the only judge).
# Usage: gate.sh <worktree> <module> [decl ...]
# Exit 0 = accepted. Checks: forbidden tokens in the module file, whitespace,
# `lake build <module>`, and a module-wide axiom scan (every declaration of the
# module must use only propext, Classical.choice, Quot.sound); extra decl names,
# if given, are additionally probed with #print axioms.
set -uo pipefail
WT="$1"; MODULE="$2"; shift 2
cd "$WT" || exit 2
FILE="$(echo "$MODULE" | tr . /).lean"
echo "=== GATE: forbidden tokens in $FILE ==="
if grep -nE '\b(sorry|admit)\b|^\s*axiom\b|native_decide|\bopaque\b|\bpostulate\b' "$FILE"; then echo "REJECT: forbidden token"; exit 3; fi
echo "=== GATE: git diff --check ==="; git diff --check HEAD -- . || { echo "REJECT: whitespace"; exit 3; }
echo "=== GATE: lake build $MODULE ==="
OUT=$(lake build "$MODULE" 2>&1); RC=$?; echo "$OUT" | tail -5
if [ $RC -ne 0 ] || echo "$OUT" | grep -qE '^error:|error: '; then echo "REJECT: build failed"; exit 4; fi
if echo "$OUT" | grep -q "$FILE.*warning: declaration uses 'sorry'"; then echo "REJECT: sorry warning"; exit 4; fi
echo "=== GATE: module-wide axiom scan ==="
SCAN=$(mktemp /tmp/gate_scan_XXXX.lean)
cat > "$SCAN" <<LEAN
import $MODULE
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? \`$MODULE | throwError "module not found"
  let mut bad : Array String := #[]
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      for a in axs do
        if a != \`\`propext && a != \`\`Classical.choice && a != \`\`Quot.sound then
          bad := bad.push s!"{n} uses {a}"
  logInfo m!"GATE_SCAN declarations={count} nonstandard={bad}"
LEAN
SCANOUT=$(LEAN_NUM_THREADS=1 lake env lean "$SCAN" 2>&1); echo "$SCANOUT" | grep -E "GATE_SCAN|error" ; rm -f "$SCAN"
if ! echo "$SCANOUT" | grep -q "GATE_SCAN declarations=[0-9]* nonstandard=\[\]"; then echo "REJECT: nonstandard axiom or scan failure"; exit 5; fi
if [ $# -gt 0 ]; then
  echo "=== GATE: #print axioms (named) ==="
  AX=$(mktemp /tmp/gate_axioms_XXXX.lean)
  { echo "import $MODULE"; for t in "$@"; do echo "#print axioms $t"; done; } > "$AX"
  AXOUT=$(LEAN_NUM_THREADS=1 lake env lean "$AX" 2>&1); echo "$AXOUT"; rm -f "$AX"
  if echo "$AXOUT" | grep -qE 'sorryAx|error'; then echo "REJECT: axiom probe"; exit 5; fi
fi
echo "=== GATE: PASS ==="
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:206:theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:209:theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := norm_mul_le a b
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:211:lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:214:lemma nnnorm_mul_le_of_le {r₁ r₂ : ℝ≥0} (h₁ : ‖a₁‖₊ ≤ r₁) (h₂ : ‖a₂‖₊ ≤ r₂) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:217:lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:219:lemma nnnorm_mul₃_le : ‖a * b * c‖₊ ≤ ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:700:@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:708:@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq <| norm_mul a b
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:710:@[simp] lemma enorm_mul : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by simp [enorm]
```

### Probe 2026-09-10T19:12:49.179656+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
Poincare/Global/ParabolicHolderSpace.lean:397:29: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  if p ∈ cylinder T' then ?m.59 else ?m.60
in the target expression
  ‖(fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) p‖ ≤ ‖f‖

E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T T' : ℝ
hT : T' ≤ T
f : Y α T F
p : ℝ × E
hp : p ∈ cylinder T'
⊢ ‖(fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) p‖ ≤ ‖f‖
Poincare/Global/ParabolicHolderSpace.lean:399:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  if p ∈ cylinder T' then ?m.64 else ?m.65
in the target expression
  ‖(fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) p -
        (fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) q‖ ≤
    ‖f‖ * parabolicDist p q ^ α

E : Type u_1
F : Type u_2
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedAddCommGroup F
inst✝ : NormedSpace ℝ F
α T T' : ℝ
hT : T' ≤ T
f : Y α T F
p : ℝ × E
hp : p ∈ cylinder T'
q : ℝ × E
hq : q ∈ cylinder T'
⊢ ‖(fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) p -
        (fun p => if p ∈ cylinder T' then ↑(WithLp.fst ↑f) p else 0) q‖ ≤
    ‖f‖ * parabolicDist p q ^ α
```

### Probe 2026-09-10T19:13:43.825213+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:14:06.973328+00:00

```sh
LEAN_NUM_THREADS=1 sh harness/gate.sh /private/tmp/poincare-workers/parabolic-holder-carrier Poincare.Global.ParabolicHolderSpace
```

Exit: 0

```text
=== GATE: forbidden tokens in Poincare/Global/ParabolicHolderSpace.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.ParabolicHolderSpace ===
✔ [2026/2026] Built Poincare.Global.ParabolicHolderSpace (2.9s)
Build completed successfully (2026 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=54 nonstandard=[]
=== GATE: PASS ===
```

### Probe 2026-09-10T19:14:24.747903+00:00

```sh
rg -n '^(abbrev|def|theorem|lemma|instance)|^@\[' Poincare/Global/ParabolicHolderSpace.lean; rg -n 'ClosedSmoothModel' Poincare/Global/RiemannianContext.lean Poincare/Global/CompactCoefficientEllipticity.lean | head -8; rg -n 'theorem fixedPoint|def fixedPoint|lemma fixedPoint|theorem norm_smul|theorem norm_pos_iff|theorem norm_sub_rev|theorem abs_sub_comm' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/{Defs,Basic}.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Basic.lean | head -25
```

Exit: 0

```text
29:def parabolicDist (p q : ℝ × E) : ℝ :=
32:theorem parabolicDist_nonneg (p q : ℝ × E) : 0 ≤ parabolicDist p q := by
35:theorem parabolicDist_symm (p q : ℝ × E) :
39:theorem parabolicDist_pos {p q : ℝ × E} (h : p ≠ q) : 0 < parabolicDist p q := by
47:def cylinder (T : ℝ) : Set (ℝ × E) := Icc 0 T ×ˢ univ
49:def HasHolderBound (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) (K : ℝ) : Prop :=
53:def Pairs (S : Set (ℝ × E)) :=
57:def holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
61:def supNorm (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
65:abbrev Ambient (T : ℝ) (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
68:def holderSubmodule (α T : ℝ) : Submodule ℝ (Ambient T E F) where
105:abbrev Y (α T : ℝ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
110:instance instCoeFun : CoeFun (Y (E := E) α T F) (fun _ => ℝ × E → F) := ⟨fun f => f.val.fst⟩
112:theorem zero_off (f : Y (E := E) α T F) {p : ℝ × E} (hp : p ∉ cylinder T) :
115:theorem increment_eq (f : Y (E := E) α T F) (i : Pairs (cylinder (E := E) T)) :
119:theorem increment_norm (f : Y (E := E) α T F) (i : Pairs (cylinder (E := E) T)) :
125:theorem norm_eq_parts (f : Y (E := E) α T F) :
129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
134:theorem holder_le (f : Y (E := E) α T F) {p q : ℝ × E}
150:theorem bounded (f : Y (E := E) α T F) :
153:theorem hasHolderBound (f : Y (E := E) α T F) :
156:theorem scaledDifference_norm (α : ℝ) (f : ℝ × E → F) {p q : ℝ × E} (h : p ≠ q) :
164:def ofFunction (f : ℝ × E → F) (hoff : ∀ p, p ∉ cylinder T → f p = 0)
189:@[simp] theorem ofFunction_apply (f : ℝ × E → F) (hoff hb hh) (p : ℝ × E) :
193:theorem exists_rep_iff (f : ℝ × E → F) :
206:@[simp] theorem zero_apply (p : ℝ × E) : (0 : Y (E := E) α T F) p = 0 := rfl
208:@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
211:@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
214:@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
235:theorem holderSeminorm_bddAbove (f : Y (E := E) α T F) :
245:theorem holderSeminorm_eq (f : Y (E := E) α T F) :
260:theorem supNorm_bddAbove (f : Y (E := E) α T F) :
267:theorem supNorm_eq (f : Y (E := E) α T F) :
286:theorem norm_eq (f : Y (E := E) α T F) :
290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
307:theorem isClosed_holderSubmodule :
324:instance instCompleteSpace [CompleteSpace F] : CompleteSpace (Y (E := E) α T F) :=
327:theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
331:theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
336:theorem le_supNorm (f : Y (E := E) α T F) (p : ℝ × E) :
341:theorem hasHolderBound_seminorm (f : Y (E := E) α T F) :
355:theorem product_holderBound (f g : Y (E := E) α T ℝ) :
377:def pointwiseMul (f g : Y (E := E) α T ℝ) : Y (E := E) α T ℝ :=
385:instance instMul : Mul (Y (E := E) α T ℝ) := ⟨pointwiseMul⟩
387:@[simp] theorem mul_apply (f g : Y (E := E) α T ℝ) (p : ℝ × E) :
390:theorem norm_mul_le (f g : Y (E := E) α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
407:theorem mul_mem (f g : Y (E := E) α T ℝ) :
412:theorem cylinder_mono {T' : ℝ} (hT : T' ≤ T) :
418:def restrict {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F) : Y (E := E) α T' F := by
428:@[simp] theorem restrict_apply {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F)
433:theorem restrict_le {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F) :
Poincare/Global/CompactCoefficientEllipticity.lean:7:abbrev E := ClosedSmoothModel 3
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
Poincare/Global/RiemannianContext.lean:35:    ModelWithCorners ℝ (ClosedSmoothModel n) (ClosedSmoothModel n) :=
Poincare/Global/RiemannianContext.lean:45:    [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
Poincare/Global/RiemannianContext.lean:47:  ContMDiffRiemannianMetric (closedSmoothModelWithCorners n) ∞ (ClosedSmoothModel n)
Poincare/Global/RiemannianContext.lean:54:variable [ChartedSpace (ClosedSmoothModel n) M]
Poincare/Global/RiemannianContext.lean:70:      (ClosedSmoothModel n) (tangentBundle (n := n) (M := M)) := by
Poincare/Global/RiemannianContext.lean:77:    IsContinuousRiemannianBundle (ClosedSmoothModel n)
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:256:theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:273:noncomputable def fixedPoint : α :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:277:theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:280:theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean:305:theorem fixedPoint_lipschitz_in_map {g : α → α} (hg : ContractingWith K g) {C}
```

### Probe 2026-09-10T19:14:46.230046+00:00

```sh
sed -n '240,282p' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean; sed -n '1,42p' Poincare/Global/RiemannianContext.lean; rg -n 'mkContinuous ' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean | head -8; rg -n '^\s*(theorem|lemma|def|abbrev).*\b(add_pos_of_nonneg_of_pos|add_pos_of_pos_of_nonneg|sqrt_nonneg|sqrt_pos|abs_pos|abs_sub_comm|norm_pos_iff|norm_sub_rev|norm_smul|smul_sub|smul_comm|div_le_iff₀|isClosed_eq)\b' .lake/packages/mathlib/Mathlib | head -45
```

Exit: 0

```text
variable (hf : ContractingWith K f)
include hf

theorem dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
  hf.toLipschitzWith.dist_le_mul x y

theorem dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
  suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ ≤ dist x (f x) + dist y (f y) + K * dist x y := by grw [hf.dist_le_mul]

theorem dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y ≤ dist x (f x) / (1 - K) := by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y

theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
theorem dist_fixedPoint_fixedPoint_of_dist_le' (g : α → α) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt g y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist x y ≤ C / (1 - K) :=
  calc
    dist x y = dist y x := dist_comm x y
    _ ≤ dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ ≤ C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

variable [Nonempty α] [CompleteSpace α]

variable (f) in
/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

/-- The point provided by `ContractingWith.fixedPoint` is actually a fixed point. -/
theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
  hf.efixedPoint_isFixedPt _

theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
  hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic

/-!
# Standard Riemannian context
This module packages the project-level tier M1 context for a closed smooth
Riemannian `n`-manifold.  The intended downstream variable section is:
```lean
open scoped Manifold ContDiff Bundle
variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]
variable (g : Poincare.ClosedSmoothRiemannianMetric n M)
```
From the single metric variable `g`, use the definitions below as local
instances when a downstream statement needs Mathlib's bundle or distance
typeclasses.
-/
noncomputable section
open Bundle Bornology
open scoped Manifold ContDiff Bundle Topology ENNReal
universe u
namespace Poincare

/-- The model vector space for a boundaryless smooth `n`-manifold. -/
abbrev ClosedSmoothModel (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n)

/-- The model-with-corners used for boundaryless smooth `n`-manifolds. -/
abbrev closedSmoothModelWithCorners (n : ℕ) :
    ModelWithCorners ℝ (ClosedSmoothModel n) (ClosedSmoothModel n) :=
  𝓡 n

/--
A smooth Riemannian metric on the tangent bundle of a smooth `n`-manifold.

This is the single non-typeclass metric variable used by the project context.
All Mathlib bundle and distance typeclasses below are derived from this data.
484:    ‖f.mkContinuous C h‖ ≤ C :=
490:    ‖f.mkContinuous C h‖ ≤ max C 0 :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Defs.lean:415:theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/MulAction.lean:98:lemma norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:994:lemma norm_pos_iff' : 0 < ‖a‖ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff']
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/FiniteExtension.lean:153:theorem norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {B : Basis ι K L} {i : ι}
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:47:theorem log_of_ne_zero (hx : x ≠ 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩ :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean:53:lemma abs_nonneg (a : A) : 0 ≤ abs a := sqrt_nonneg _
.lake/packages/mathlib/Mathlib/Data/Int/Sqrt.lean:36:theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:239:lemma sqrt_nonneg (a : A) : 0 ≤ sqrt a := cfcₙ_predicate _ a
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:439:theorem norm_smul (c : ℝ) (x : mixedSpace K) :
.lake/packages/mathlib/Mathlib/Data/Rat/Sqrt.lean:37:lemma sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q := mkRat_nonneg (Int.sqrt_nonneg _) _
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:158:lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:286:theorem sqrt_pos : 0 < √x ↔ 0 < x :=
.lake/packages/mathlib/Mathlib/Topology/Separation/Hausdorff.lean:487:theorem isClosed_eq [T2Space X] {f g : Y → X} (hf : Continuous f) (hg : Continuous g) :
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean:63:lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const
```

### Probe 2026-09-10T19:14:48.052623+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/Axioms.lean
```

Exit: 0

```text
'Poincare.ParabolicHolder.parabolicDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.HasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instCoeFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.zero_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.hasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.scaledDifference_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.exists_rep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.add_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.sub_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.smul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.isClosed_holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instCompleteSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.le_supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.hasHolderBound_seminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.product_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.mul_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.cylinder_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Probe 2026-09-10T19:15:13.480487+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/AllAxioms.lean
```

Exit: 1

```text
/tmp/parabolic-holder-evidence/AllAxioms.lean:7:19: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  OfNat MessageData 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  MessageData
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/parabolic-holder-evidence/AllAxioms.lean:13:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd MessageData ℕ MessageData

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

### Probe 2026-09-10T19:15:42.739639+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/Acceptance.lean
```

Exit: 1

```text
(holderSubmodule α T).addCommGroup
(holderSubmodule α T).module
(holderSubmodule α T).normedAddCommGroup
(holderSubmodule α T).normedSpace
instCompleteSpace
/tmp/parabolic-holder-evidence/Acceptance.lean:19:55: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  LE Type

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/parabolic-holder-evidence/Acceptance.lean:19:57: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  OfNat Type 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Type
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
(holderSubmodule α T).normedSpace
instCompleteSpace
instCompleteSpace
Poincare.ParabolicHolder.norm_eq.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) :
  ‖f‖ = supNorm (cylinder T) ↑(WithLp.fst ↑f) + holderSeminorm α (cylinder T) ↑(WithLp.fst ↑f)
Poincare.ParabolicHolder.norm_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) (p : ℝ × E) : ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖
Poincare.ParabolicHolder.holder_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) {p q : ℝ × E} (hp : p ∈ cylinder T)
  (hq : q ∈ cylinder T) : ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * parabolicDist p q ^ α
Poincare.ParabolicHolder.mul_mem.{u_1} {E : Type u_1} [NormedAddCommGroup E] {α T : ℝ} (f g : Y α T ℝ) :
  (∀ (p : ℝ × E), ↑(WithLp.fst ↑(f * g)) p = ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p) ∧ ‖f * g‖ ≤ ‖f‖ * ‖g‖
Poincare.ParabolicHolder.restrict_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T T' : ℝ} (hT : T' ≤ T) (f : Y α T F) : ‖restrict hT f‖ ≤ ‖f‖
Poincare.ParabolicHolder.exists_rep_iff.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ℝ × E → F) :
  (∃ y, ∀ (p : ℝ × E), ↑(WithLp.fst ↑y) p = f p) ↔
    (∀ p ∉ cylinder T, f p = 0) ∧ (∃ M, ∀ p ∈ cylinder T, ‖f p‖ ≤ M) ∧ ∃ K, HasHolderBound α (cylinder T) f K
```

### Probe 2026-09-10T19:15:48.172731+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/AllAxioms.lean
```

Exit: 0

```text
'Poincare.ParabolicHolder.instCoeFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.zero_off' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.scaledDifference_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.exists_rep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.HasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instCompleteSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.mul_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.hasHolderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSeminorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ext_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.le_supNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.increment_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._abel_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.hasHolderBound_seminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Y._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.norm_le_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.parabolicDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.add_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.restrict._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Ambient' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.cylinder_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.sub_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holder_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.smul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.supNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.holderSubmodule._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.instMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.isClosed_holderSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.pointwiseMul._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.ofFunction_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolder.product_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_ALL_DECLARATIONS=72 PASS
```

### Probe 2026-09-10T19:16:00.058062+00:00

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-holder-evidence/Acceptance.lean
```

Exit: 0

```text
(holderSubmodule α T).addCommGroup
(holderSubmodule α T).module
(holderSubmodule α T).normedAddCommGroup
(holderSubmodule α T).normedSpace
instCompleteSpace
(holderSubmodule α T).normedSpace
instCompleteSpace
instCompleteSpace
Poincare.ParabolicHolder.norm_eq.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) :
  ‖f‖ = supNorm (cylinder T) ↑(WithLp.fst ↑f) + holderSeminorm α (cylinder T) ↑(WithLp.fst ↑f)
Poincare.ParabolicHolder.norm_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) (p : ℝ × E) : ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖
Poincare.ParabolicHolder.holder_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : Y α T F) {p q : ℝ × E} (hp : p ∈ cylinder T)
  (hq : q ∈ cylinder T) : ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * parabolicDist p q ^ α
Poincare.ParabolicHolder.mul_mem.{u_1} {E : Type u_1} [NormedAddCommGroup E] {α T : ℝ} (f g : Y α T ℝ) :
  (∀ (p : ℝ × E), ↑(WithLp.fst ↑(f * g)) p = ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p) ∧ ‖f * g‖ ≤ ‖f‖ * ‖g‖
Poincare.ParabolicHolder.restrict_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T T' : ℝ} (hT : T' ≤ T) (f : Y α T F) : ‖restrict hT f‖ ≤ ‖f‖
Poincare.ParabolicHolder.exists_rep_iff.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ℝ × E → F) :
  (∃ y, ∀ (p : ℝ × E), ↑(WithLp.fst ↑y) p = f p) ↔
    (∀ p ∉ cylinder T, f p = 0) ∧ (∃ M, ∀ p ∈ cylinder T, ‖f p‖ ≤ M) ∧ ∃ K, HasHolderBound α (cylinder T) f K
```

### Probe 2026-09-10T19:16:11.981141+00:00

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 1

```text
(empty)
```

### Probe 2026-09-10T19:16:12.014655+00:00

```sh
git diff --check
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:16:12.046766+00:00

```sh
git add Poincare/Global/ParabolicHolderSpace.lean
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:16:12.078373+00:00

```sh
git diff --cached --check
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:16:12.119637+00:00

```sh
git commit -m "Prove sharp Holder multiplication and contractive cylinder restriction"
```

Exit: 0

```text
[worker/parabolic-holder-carrier 38a0cf0c] Prove sharp Holder multiplication and contractive cylinder restriction
 1 file changed, 142 insertions(+)
```

### Probe 2026-09-10T19:16:33.818575+00:00

```sh
git status --short --branch
```

Exit: 0

```text
## worker/parabolic-holder-carrier
```

### Probe 2026-09-10T19:16:33.850315+00:00

```sh
git log -3 --format="%H %s"
```

Exit: 0

```text
38a0cf0c2171d83b33054c0c2d7c186ca68df931 Prove sharp Holder multiplication and contractive cylinder restriction
a3c0aed6592453cdc0d123fc80a77f01967eb5ae Prove completeness of the parabolic Holder sum-norm carrier
c46220fb2dea444a71cfdca3764dcb0370a2afee Add the parabolic Hölder carrier and pinching-to-reaction survey tasks
```

### Probe 2026-09-10T19:16:33.881341+00:00

```sh
git diff --stat c46220fb2dea444a71cfdca3764dcb0370a2afee..HEAD
```

Exit: 0

```text
 Poincare/Global/ParabolicHolderSpace.lean | 444 ++++++++++++++++++++++++++++++
 1 file changed, 444 insertions(+)
```

### Probe 2026-09-10T19:16:33.911545+00:00

```sh
git diff --check c46220fb2dea444a71cfdca3764dcb0370a2afee..HEAD
```

Exit: 0

```text
(empty)
```

### Probe 2026-09-10T19:16:42.740412+00:00

```sh
rg --files harness | rg 'parabolic-holder-carrier|parabolic-holder'
```

Exit: 0

```text
harness/tasks/parabolic-holder-carrier.md
```

### Probe 2026-09-10T19:16:47.727821+00:00

```sh
cat harness/tasks/parabolic-holder-carrier.md
```

Exit: 0

```text
# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/parabolic-holder-carrier`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files, `Poincare.lean`, audit scripts, missions, or ledgers; you may add EXACTLY ONE new Lean module, `Poincare/Global/ParabolicHolderSpace.lean`. Commit each verified item on your branch; report actual command output to `harness/reports/parabolic-holder-carrier_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting statement and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only. Distinguish (a) proved in repo, (b) in Mathlib, (c) absent.

Context: read `HANDOFF.md` top section first.

# Task parabolic-holder-carrier

Read `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the norm choice `Y_T`, `X_T`) and section 3.2 first.

Objective: implement the parabolic Hölder carrier `Y_T` as a genuine complete normed space so that later tasks (K2, the frozen-coefficient correction, the nonlinear fixed point) can use Mathlib's Banach fixed point and bounded-operator theory on it.

Module: `Poincare/Global/ParabolicHolderSpace.lean`. Namespace: `Poincare.ParabolicHolder`. Imports: Mathlib only unless a landed definition is needed (`Poincare.Global.CompactCoefficientEllipticity` for `E`).

Required content, with `E := ClosedSmoothModel 3` (or general `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` and a target `{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]` if the generality costs nothing):

1. `parabolicDist (p q : ℝ × E) : ℝ := ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|` and its basic lemmas (nonneg, symm, zero iff equal on the cylinder is NOT needed).
2. The seminorm `holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ := ⨆ (p ∈ S) (q ∈ S) (_ : p ≠ q), ‖f p - f q‖ / parabolicDist p q ^ α` defined via `⨆` over a bounded family, or as `sSup` of the ratio set, with a predicate `HasHolderBound α S f K` meaning `∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * parabolicDist p q ^ α` (prefer building the space from the predicate: it avoids `⨆` pathologies).
3. The carrier: a structure `Y (α : ℝ) (T : ℝ) (F)` of functions `f : ℝ × E → F` that are bounded on the cylinder `S_T := Icc 0 T ×ˢ univ` and admit some Hölder bound there (store `∃ M, ∀ p ∈ S_T, ‖f p‖ ≤ M` and `∃ K, HasHolderBound α S_T f K`), with values outside `S_T` irrelevant: quotient by agreement on `S_T`, or simply require `f p = 0` for `p ∉ S_T` to make the norm definite (choose and justify; the second is simpler).
4. Instances: `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ` with norm `‖f‖ = sup_{S_T} ‖f‖ + [f]_{α;S_T}` (define both pieces as `sSup` of bounded nonempty sets or via `⨆` with `BddAbove` lemmas; prove the norm axioms), and `CompleteSpace` (a Cauchy sequence converges uniformly on `S_T` since the sup norm is dominated; the limit is bounded and Hölder with the limiting constant by passing to the limit in the pointwise inequality; convergence in the full norm follows from the same argument applied to differences). Use `BoundedContinuousFunction` completeness as a guide, not as a dependency (the elements are not required continuous; boundedness plus Hölder on `S_T` implies continuity on `S_T` anyway).
5. Bridging lemmas: `norm_le` (`‖f p‖ ≤ ‖f‖` on `S_T`), `holder_le` (`‖f p - f q‖ ≤ ‖f‖ * parabolicDist p q ^ α` on `S_T`), `mul_mem` for `F = ℝ` (product of two elements is an element with `‖f*g‖ ≤ 2‖f‖‖g‖` or the sharp constant), and `restrict_le` (the norm on `Y α T'` for `T' ≤ T` is bounded by the norm on `Y α T`).

Exact stop condition: the `CompleteSpace` instance and the five bridging lemmas compile and pass the gate. If `CompleteSpace` resists, land the normed space with the bridging lemmas and display the exact resisting limit-passing step.
```

### Probe 2026-09-10T19:16:47.758423+00:00

```sh
git show c46220fb:harness/tasks/parabolic-holder-carrier.md
```

Exit: 0

```text
# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/parabolic-holder-carrier`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files, `Poincare.lean`, audit scripts, missions, or ledgers; you may add EXACTLY ONE new Lean module, `Poincare/Global/ParabolicHolderSpace.lean`. Commit each verified item on your branch; report actual command output to `harness/reports/parabolic-holder-carrier_{done|blocked}.md`. Gate for any Lean module: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name by grep in the repo or `.lake/packages/mathlib`; record every probe with actual output. If blocked, display the exact resisting statement and the strongest compiled partial result; never weaken a target silently. Frozen contract files are read-only. Distinguish (a) proved in repo, (b) in Mathlib, (c) absent.

Context: read `HANDOFF.md` top section first.

# Task parabolic-holder-carrier

Read `harness/reports/parabolic-schauder-decomposition-survey_done.md` section 3.1 (the norm choice `Y_T`, `X_T`) and section 3.2 first.

Objective: implement the parabolic Hölder carrier `Y_T` as a genuine complete normed space so that later tasks (K2, the frozen-coefficient correction, the nonlinear fixed point) can use Mathlib's Banach fixed point and bounded-operator theory on it.

Module: `Poincare/Global/ParabolicHolderSpace.lean`. Namespace: `Poincare.ParabolicHolder`. Imports: Mathlib only unless a landed definition is needed (`Poincare.Global.CompactCoefficientEllipticity` for `E`).

Required content, with `E := ClosedSmoothModel 3` (or general `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]` and a target `{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]` if the generality costs nothing):

1. `parabolicDist (p q : ℝ × E) : ℝ := ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|` and its basic lemmas (nonneg, symm, zero iff equal on the cylinder is NOT needed).
2. The seminorm `holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ := ⨆ (p ∈ S) (q ∈ S) (_ : p ≠ q), ‖f p - f q‖ / parabolicDist p q ^ α` defined via `⨆` over a bounded family, or as `sSup` of the ratio set, with a predicate `HasHolderBound α S f K` meaning `∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * parabolicDist p q ^ α` (prefer building the space from the predicate: it avoids `⨆` pathologies).
3. The carrier: a structure `Y (α : ℝ) (T : ℝ) (F)` of functions `f : ℝ × E → F` that are bounded on the cylinder `S_T := Icc 0 T ×ˢ univ` and admit some Hölder bound there (store `∃ M, ∀ p ∈ S_T, ‖f p‖ ≤ M` and `∃ K, HasHolderBound α S_T f K`), with values outside `S_T` irrelevant: quotient by agreement on `S_T`, or simply require `f p = 0` for `p ∉ S_T` to make the norm definite (choose and justify; the second is simpler).
4. Instances: `AddCommGroup`, `Module ℝ`, `NormedAddCommGroup`, `NormedSpace ℝ` with norm `‖f‖ = sup_{S_T} ‖f‖ + [f]_{α;S_T}` (define both pieces as `sSup` of bounded nonempty sets or via `⨆` with `BddAbove` lemmas; prove the norm axioms), and `CompleteSpace` (a Cauchy sequence converges uniformly on `S_T` since the sup norm is dominated; the limit is bounded and Hölder with the limiting constant by passing to the limit in the pointwise inequality; convergence in the full norm follows from the same argument applied to differences). Use `BoundedContinuousFunction` completeness as a guide, not as a dependency (the elements are not required continuous; boundedness plus Hölder on `S_T` implies continuity on `S_T` anyway).
5. Bridging lemmas: `norm_le` (`‖f p‖ ≤ ‖f‖` on `S_T`), `holder_le` (`‖f p - f q‖ ≤ ‖f‖ * parabolicDist p q ^ α` on `S_T`), `mul_mem` for `F = ℝ` (product of two elements is an element with `‖f*g‖ ≤ 2‖f‖‖g‖` or the sharp constant), and `restrict_le` (the norm on `Y α T'` for `T' ≤ T` is bounded by the norm on `Y α T`).

Exact stop condition: the `CompleteSpace` instance and the five bridging lemmas compile and pass the gate. If `CompleteSpace` resists, land the normed space with the bridging lemmas and display the exact resisting limit-passing step.
```
