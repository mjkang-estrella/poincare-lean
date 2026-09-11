# Moving-limit Leibniz rule and frozen Duhamel equation: done

Date: 2026-09-11. Branch: `worker/moving-limit-leibniz-rule`.
Base: `bec9c44750f80151aabb63b859c283cfa944da3a`.
Verified proof head: `3e8cb854d9d0aa451d8a47577d35475542868792`.

Both requested parts are proved in the single new Lean module
`Poincare/Global/MovingLimitLeibniz.lean`. The file contains 12 theorems
and no new definitions or instances. Existing Lean files, the root import,
and frozen contracts are unchanged. The required dated handoff is updated.
This worker result is ready for independent review; it is not merged or accepted.

## Results

| Declaration | Verified result |
| --- | --- |
| `hasDerivWithinAt_integral_of_dominated_secants` | Differentiation under an integral within an arbitrary real set, using an integrable secant majorant. |
| `hasDerivWithinAt_integral_Icc` | Fundamental theorem of calculus for a continuous function on a closed interval, including both endpoints. |
| `hasDerivWithinAt_integral_moving_limit_of_secants` | Moving-limit Leibniz rule from dominated clipped secants. |
| `abs_sub_le_of_deriv_comparison` | Interior derivative comparison controls increments through continuous endpoints. |
| `abs_sub_le_rpow_of_deriv_bound` | Integrates the singular power derivative bound without requiring a diagonal derivative. |
| `abs_rpow_sub_le` | Fractional-power secant estimate at a positive base point. |
| `abs_clipped_rpow_sub_le` | Fractional-power secant estimate after clipping, with either sign of the base point. |
| `intervalIntegrable_abs_sub_rpow` | Integrability of the majorant on both sides of the observation time. |
| `clipped_secant_le_of_deriv_rpow_bound` | Derives a common secant majorant from the actual derivative bound. |
| `hasDerivWithinAt_integral_moving_limit` | Part A, with explicit diagonal power domination and the requested derivative conclusion. |
| `exists_heat_integrand_deriv_bound` | Derives that domination from the landed K2 Hessian estimate and the three-coordinate trace. |
| `duhamel_solves_heat_equation` | Part B, with the frozen statement copied verbatim. |

Each theorem is in its own proof commit. The final proof-only cleanup removes
redundant tactics. One intermediate singular-power attempt failed verification
and was corrected before its commit was amended; the final retained commit is
`1d81bf9b`. Its failed and successful compiler output is preserved below.

## Part A statement and compiled route

The conclusion is exactly the requested moving-limit derivative:
`HasDerivWithinAt (fun r => ∫ s in 0..r, F r s)
  (b + ∫ s in 0..t, D t s) (Icc 0 T) t`.

The allowed hypothesis adjustments are explicit:

- The continuous triangular integrand has `F t t = b`.
  The proposed `nhdsWithin t (Ico 0 t)` condition alone cannot determine
  `b` at `t = 0`, where that filter is empty. The landed continuous heat
  extension supplies the diagonal value.
- There are constants `0 < β ≤ 1` and `0 ≤ C` such that
  `|D r s| ≤ C * (r-s)^(β-1)` for `s ∈ Icc 0 T` and `r ∈ Ioc s T`.
  Pointwise parameter derivatives are required on the same region.
  This slab-wide power estimate is an explicit choice of domination which
  the application proves, with `β = α/2`.
- No separate derivative-integrability assumption is needed by this proof.
  The power and secant estimates supply the domination used by the integral
  limit argument. No differentiability in the second variable is assumed.

The direct fixed-interval parametric derivative theorem asks for derivative
control across the diagonal. The same obstruction affects differentiating
`G(ρ,r)` on a full rectangle. The successful route is:

1. Set `G r s = F (max r s) s - F s s`.
2. Prove
   `∫₀ʳ F(r,s) ds = ∫₀ᵀ G(r,s) ds + ∫₀ʳ F(s,s) ds`.
3. Derive the common estimate
   `|G r s - G t s| ≤ (C/β) * |t-s|^(β-1) * |r-t|`
   for `s ≠ t`. The majorant is integrable because `β > 0`.
   This handles both signs of the increment.
4. Use Mathlib's
   `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` with
   `hasDerivWithinAt_iff_tendsto_slope` to differentiate the fixed integral.
   The derivative of the clipped function is `D t s` for `s < t`
   and zero for `s > t`. The exceptional diagonal has measure zero.
5. Use `intervalIntegral.integral_hasDerivAt_right` on a continuous
   extension of the diagonal function, then restrict back to `Icc 0 T`.

The singular increment estimate uses
`monotoneOn_of_deriv_nonneg` on the comparison functions.
The underlying endpoint values are continuous; a derivative at the singular
initial endpoint is never assumed.

The explicit import of `Mathlib.Analysis.Calculus.ParametricIntervalIntegral`
initially lacked a cached object. A focused build succeeded. No full root
build or concurrent full build was run.

## Part B and frozen-contract check

The application uses the already proved continuous heat extension:
`F r s = if r-s = 0 then f(s,x) else heatSolution (r-s) (f(s,·)) x`.
The extended integrand equals the original integrand almost everywhere on
each time interval, so their integrals are equal. The original `u` is unchanged.

The scalar derivative bound follows from
`HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound`.
Each diagonal Hessian evaluation is bounded by its operator norm, using the
unit coordinate basis vectors. Summing gives `C = 3 * A * K`.
The landed `hasDerivAt_heat_integrand` supplies the actual time derivative.
The landed `duhamel_time_derivative_integral` identifies its integral with
the Duhamel Laplacian, and `laplacian_eq_hessian_trace` recovers the frozen
coordinate sum. `duhamel_zero` closes the initial value.

The final theorem has no added hypotheses. Its source statement matches
the task's Lean block verbatim. A separate Lean assignment of that exact
type to `duhamel_solves_heat_equation` also passes.

There is no remaining application goal. Both `t = 0` and `t = T` are
included by the within-set calculus argument.

## Final gates

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean
exit_code=0
output: empty

$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/MovingLimitLeibniz.lean
exit_code=1
output: empty

$ LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/FinalDependencies.lean
exit_code=0
12 declarations: each exactly [propext, Classical.choice, Quot.sound]
Exact frozen-type assignment: passed

$ git diff --check
exit_code=0
output: empty

$ git diff bec9c44750f80151aabb63b859c283cfa944da3a --check
exit_code=0
output: empty
```

The dependency probe copies the new module and appends `#print axioms`
for all 12 theorem declarations, followed by the exact frozen-type
assignment. Full output is retained below. Failed intermediate output
may contain Lean's automatically generated placeholder dependency; no such
dependency occurs in any final declaration.

First action for the reviewer:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean`.
Then independently check the exact statement and proof diff against
`bec9c44750f80151aabb63b859c283cfa944da3a`.

## Recorded probe output

Initial calls that yielded a running session are followed by their captured
completion output. Output lines are retained with trailing whitespace removed.

### Probe 001

```text
$ rg -n 'theorem tendsto_integral_filter_of_dominated_convergence|theorem integral_sub|theorem integral_const_mul|theorem slope_def|theorem slope_def_field|theorem norm_div|theorem integral_indicator|theorem integrableOn.*Icc|theorem hasDerivAt.*congr_of_eventuallyEq' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean .lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Slope.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean; rg -n 'theorem.*(mono.*deriv|antitone.*deriv)' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:267:theorem integral_sub {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:274:theorem integral_sub' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:298:theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1132:theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1139:theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α → G) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:69:theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenerated]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:212:nonrec theorem tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι}
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Slope.lean:41:theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Slope.lean:51:theorem slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
409:theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
417:theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
478:theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
486:theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :

exit_code=0
```

### Probe 002

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=69617
```

### Probe 003

```text
$ poll source probe
Poincare/Global/MovingLimitLeibniz.lean:1:0: error: object file '/private/tmp/poincare-workers/moving-limit-leibniz-rule/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.olean' of module Mathlib.Analysis.Calculus.ParametricIntervalIntegral does not exist

exit_code=1
```

### Probe 004

```text
$ LEAN_NUM_THREADS=1 lake build Mathlib.Analysis.Calculus.ParametricIntervalIntegral

running_session=43370
```

### Probe 005

```text
$ poll focused Mathlib build
✔ [2570/2570] Built Mathlib.Analysis.Calculus.ParametricIntervalIntegral (3.3s)
Build completed successfully (2570 jobs).

exit_code=0
```

### Probe 006

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=94467
```

### Probe 007

```text
$ poll source probe
Poincare/Global/MovingLimitLeibniz.lean:32:6: error: `dsimp` made no progress
Poincare/Global/MovingLimitLeibniz.lean:21:67: error: unsolved goals
case h
G : ℝ → ℝ → ℝ
D B : ℝ → ℝ
μ : Measure ℝ
S : Set ℝ
t : ℝ
hG : ∀ᶠ (r : ℝ) in 𝓝[S] t, Integrable (G r) μ
hGt : Integrable (G t) μ
hB : Integrable B μ
hbound : ∀ᶠ (r : ℝ) in 𝓝[S] t, ∀ᵐ (s : ℝ) ∂μ, ‖G r s - G t s‖ ≤ B s * ‖r - t‖
hD : ∀ᵐ (s : ℝ) ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t
hle : 𝓝[S \ {t}] t ≤ 𝓝[S] t
hi : Tendsto (fun n => ∫ (a : ℝ), (n - t)⁻¹ * (G n - G t) a ∂μ) (𝓝[S \ {t}] t) (𝓝 (∫ (a : ℝ), D a ∂μ))
r : ℝ
hr : Integrable (G r) μ
⊢ (r - t)⁻¹ * ∫ (a : ℝ), (G r - G t) a ∂μ = (r - t)⁻¹ * (∫ (s : ℝ), G r s ∂μ -ᵥ ∫ (s : ℝ), G t s ∂μ)
Poincare/Global/MovingLimitLeibniz.lean:44:53: warning: This simp argument is unused:
  integral_sub hr hGt

Hint: Omit it from the simp argument list.
  simp only [slope, smul_eq_mul, integral_const_mul,̵ ̵i̵n̵t̵e̵g̵r̵a̵l̵_̵s̵u̵b̵ ̵h̵r̵ ̵h̵G̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

exit_code=1
```

### Probe 008

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=50525
```

### Probe 009

```text
$ poll source probe

exit_code=0
```

### Probe 010

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/MovingLimitLeibniz.lean
git diff --check

running_session=92937
```

### Probe 011

```text
$ poll dependency gate 1
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```

### Probe 012

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=30602
```

### Probe 013

```text
$ poll FTC source gate
Poincare/Global/MovingLimitLeibniz.lean:65:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  c s
in the target expression
  g s = (fun x => g (c x)) s

case h
g : ℝ → ℝ
T t : ℝ
ht : t ∈ Icc 0 T
hg : ContinuousOn g (Icc 0 T)
c : ℝ → ℝ := fun r => max 0 (min T r)
hc : Continuous c
hcm : ∀ (r : ℝ), c r ∈ Icc 0 T
hce : ∀ r ∈ Icc 0 T, c r = r
hg' : Continuous fun r => g (c r)
hd : HasDerivAt (fun u => ∫ (x : ℝ) in 0..u, g (c x)) (g t) t
r : ℝ
hr : r ∈ Icc 0 T
s : ℝ
hs : s ∈ Icc 0 r
⊢ g s = (fun x => g (c x)) s

exit_code=1
```

### Probe 014

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=56263
```

### Probe 015

```text
$ poll FTC dependency gate
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 016

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=84329
```

### Probe 017

```text
$ poll clipped Leibniz source
Poincare/Global/MovingLimitLeibniz.lean:104:20: error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
Poincare/Global/MovingLimitLeibniz.lean:111:20: error: invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
Poincare/Global/MovingLimitLeibniz.lean:128:4: error: unsolved goals
case pos
F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
hdG : HasDerivWithinAt (fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) (∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
hdint : ∫ (s : ℝ) in Ioc 0 T, d s = ∫ (s : ℝ) in 0..t, D t s
hde :
  HasDerivWithinAt ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s)
    (b + ∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
r : ℝ
hr : r ∈ Icc 0 T
s : ℝ
hs : s ≤ r
⊢ F r s - F s s = (Iic r).indicator (fun s => F r s - F s s) s
Poincare/Global/MovingLimitLeibniz.lean:129:4: error: unsolved goals
case neg
F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
hdG : HasDerivWithinAt (fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) (∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
hdint : ∫ (s : ℝ) in Ioc 0 T, d s = ∫ (s : ℝ) in 0..t, D t s
hde :
  HasDerivWithinAt ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s)
    (b + ∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
r : ℝ
hr : r ∈ Icc 0 T
s : ℝ
hs : ¬s ≤ r
⊢ 0 = (Iic r).indicator (fun s => F r s - F s s) s
Poincare/Global/MovingLimitLeibniz.lean:130:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : ℝ) in Ioc 0 T, ?m.769 x ∂?m.770
in the target expression
  ∫ (s : ℝ) in 0..r, F r s = ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s) r

F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
hdG : HasDerivWithinAt (fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) (∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
hdint : ∫ (s : ℝ) in Ioc 0 T, d s = ∫ (s : ℝ) in 0..t, D t s
hde :
  HasDerivWithinAt ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s)
    (b + ∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
r : ℝ
hr : r ∈ Icc 0 T
he : G r = (Iic r).indicator fun s => F r s - F s s
⊢ ∫ (s : ℝ) in 0..r, F r s = ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s) r
Poincare/Global/MovingLimitLeibniz.lean:128:20: warning: This simp argument is unused:
  indicator_of_mem hs

Hint: Omit it from the simp argument list.
  simp only [G, i̵n̵d̵i̵c̵a̵t̵o̵r̵_̵o̵f̵_̵m̵e̵m̵ ̵h̵s̵,̵ ̵max_eq_left hs]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/MovingLimitLeibniz.lean:129:20: warning: This simp argument is unused:
  indicator_of_notMem hs

Hint: Omit it from the simp argument list.
  simp only [G, i̵n̵d̵i̵c̵a̵t̵o̵r̵_̵o̵f̵_̵n̵o̵t̵M̵e̵m̵ ̵h̵s̵,̵ ̵max_eq_right (le_of_not_ge hs), sub_self]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

exit_code=1
```

### Probe 018

```text
$ rg -n 'abs.*rpow|rpow.*abs|rpow_sub_one' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean | head -40; rg -n 'rpow_le_rpow_of_nonpos|rpow_le_rpow_of_exponent|rpow_sub_one|rpow_sub' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean | head -25; rg -n 'sub_sub_sub_cancel_right|integrableOn_Icc|Eventually.mono|Ioi_mem_nhds|Iio_mem_nhds' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean .lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean | head -20
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:353:  rw [rpow_sub_one hp.ne', ← rpow_def_of_pos hp, smul_add, smul_smul, mul_div_left_comm,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:367:  simp_rw [rpow_sub_one hp.ne, smul_add, ← add_assoc, smul_smul, ← add_smul, ← mul_assoc,
262:theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
265:theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
432:lemma rpow_sub_intCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y - n) = x ^ y / x ^ n := by
435:lemma rpow_sub_natCast {x : ℝ} (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
436:  simpa using rpow_sub_intCast hx y n
444:lemma rpow_sub_intCast' (hx : 0 ≤ x) {n : ℤ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
445:  rw [rpow_sub' hx h, rpow_intCast]
447:lemma rpow_sub_natCast' (hx : 0 ≤ x) (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n := by
448:  rw [rpow_sub' hx h, rpow_natCast]
453:theorem rpow_sub_one {x : ℝ} (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
454:  simpa using rpow_sub_natCast hx y 1
462:lemma rpow_sub_one' (hx : 0 ≤ x) (h : y - 1 ≠ 0) : x ^ (y - 1) = x ^ y / x := by
463:  rw [rpow_sub' hx h, rpow_one]
466:  rw [rpow_sub' hx h, rpow_one]
561:lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z := by
574:  ⟨lt_imp_lt_of_le_imp_le fun h ↦ rpow_le_rpow_of_nonpos hx h hz.le,
613:theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
624:@[deprecated (since := "2025-10-28")] alias rpow_le_rpow_of_exponent_nonpos :=
625:  rpow_le_rpow_of_nonpos
629:  fun _ ha _ _ hab => rpow_le_rpow_of_nonpos ha hab hr
645:theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
673:  convert rpow_le_rpow_of_exponent_le hx hz
691:  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
715:/-- This is a more general but less convenient version of `rpow_le_rpow_of_exponent_ge`.
717:theorem rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y)
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:748:theorem pi_Iio_mem_nhds (ha : ∀ i, x i < a i) : Iio a ∈ 𝓝 x := mem_of_superset
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:749:  (set_pi_mem_nhds finite_univ fun i _ ↦ Iio_mem_nhds (ha i)) (pi_univ_Iio_subset a)
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:752:theorem pi_Iio_mem_nhds' (ha : ∀ i, x' i < a' i) : Iio a' ∈ 𝓝 x' :=
.lake/packages/mathlib/Mathlib/Topology/Order/Basic.lean:753:  pi_Iio_mem_nhds ha
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:826:theorem integrableOn_Icc_iff_integrableOn_Ioc'
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:835:theorem integrableOn_Icc_iff_integrableOn_Ico'
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:859:theorem integrableOn_Icc_iff_integrableOn_Ioo' (ha : μ {a} ≠ ∞)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:862:  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha ha', integrableOn_Ioc_iff_integrableOn_Ioo' hb hb']
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:876:theorem integrableOn_Icc_iff_integrableOn_Ioc (ha : ‖f a‖ₑ ≠ ∞ := by finiteness) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:878:  integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:880:theorem integrableOn_Icc_iff_integrableOn_Ico (hb : ‖f b‖ₑ ≠ ∞ := by finiteness) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:882:  integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:892:theorem integrableOn_Icc_iff_integrableOn_Ioo
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean:895:  rw [integrableOn_Icc_iff_integrableOn_Ioc ha, integrableOn_Ioc_iff_integrableOn_Ioo hb]

exit_code=0
```

### Probe 019

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=23770
```

### Probe 020

```text
$ poll clipped Leibniz source
Poincare/Global/MovingLimitLeibniz.lean:106:36: error: Application type mismatch: The argument
  hr
has type
  r ∈ Ioi s
but is expected to have type
  ?m.613 < ?m.614
in the application
  LT.lt.le hr
Poincare/Global/MovingLimitLeibniz.lean:104:62: error: unsolved goals
case h
F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
s : ℝ
hs : s ∈ Ioc 0 T
hst : s ≠ t
hlt : s < t
hd : HasDerivAt (fun x => F x s - F s s) (D t s) t
r : ℝ
hr : r ∈ Ioi s
⊢ F (max r s) s - F s s = F r s - F s s
Poincare/Global/MovingLimitLeibniz.lean:113:37: error: Application type mismatch: The argument
  hr
has type
  r ∈ Iio s
but is expected to have type
  ?m.692 < ?m.693
in the application
  LT.lt.le hr
Poincare/Global/MovingLimitLeibniz.lean:111:56: error: unsolved goals
case h
F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
s : ℝ
hs : s ∈ Ioc 0 T
hst : s ≠ t
hlt : ¬s < t
hgt : t < s
r : ℝ
hr : r ∈ Iio s
⊢ F (max r s) s - F s s = 0
Poincare/Global/MovingLimitLeibniz.lean:132:48: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : ℝ) in 0..T, {x | x ≤ r}.indicator ?m.902 x ∂?m.903
in the target expression
  ∫ (s : ℝ) in 0..r, F r s =
    (∫ (x : ℝ) in 0..T, (Iic r).indicator (fun s => F r s - F s s) x) + ∫ (s : ℝ) in 0..r, F s s

F D : ℝ → ℝ → ℝ
b T t : ℝ
ht : t ∈ Icc 0 T
hcont : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hdiag : F t t = b
hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t
G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
d : ℝ → ℝ := (Iic t).indicator (D t)
hT : 0 ≤ T
hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T)
hcG : ∀ r ∈ Icc 0 T, ContinuousOn (G r) (Icc 0 T)
hiG : ∀ r ∈ Icc 0 T, IntegrableOn (G r) (Ioc 0 T) volume
B : ℝ → ℝ
hB : IntegrableOn B (Ioc 0 T) volume
hb : ∀ᶠ (r : ℝ) in 𝓝[Icc 0 T] t, ∀ᵐ (s : ℝ) ∂volume.restrict (Ioc 0 T), ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r - t‖
hdG : HasDerivWithinAt (fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) (∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
hdint : ∫ (s : ℝ) in Ioc 0 T, d s = ∫ (s : ℝ) in 0..t, D t s
hde :
  HasDerivWithinAt ((fun r => ∫ (s : ℝ) in Ioc 0 T, G r s) + fun r => ∫ (s : ℝ) in 0..r, F s s)
    (b + ∫ (s : ℝ) in 0..t, D t s) (Icc 0 T) t
r : ℝ
hr : r ∈ Icc 0 T
he : G r = (Iic r).indicator fun s => F r s - F s s
⊢ ∫ (s : ℝ) in 0..r, F r s =
    (∫ (x : ℝ) in 0..T, (Iic r).indicator (fun s => F r s - F s s) x) + ∫ (s : ℝ) in 0..r, F s s
Poincare/Global/MovingLimitLeibniz.lean:113:44: warning: This simp argument is unused:
  sub_self

Hint: Omit it from the simp argument list.
  simp only [G, max_eq_right hr.le,̵ ̵s̵u̵b̵_̵s̵e̵l̵f̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

exit_code=1
```

### Probe 021

```text
$ rg -n 'intervalIntegrable_rpow|integral_rpow' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean | head -22; rg -n 'abs_rpow|rpow_abs' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean | head -15; rg -n '^theorem HasDerivAt.rpow_const|^theorem.*hasDerivAt_rpow_const|Continuous.rpow_const|ContinuousOn.rpow_const' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean
146:theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
169:  exact mod_cast integral_rpow h
167:theorem abs_rpow_of_nonneg {x y : ℝ} (hx_nonneg : 0 ≤ x) : |x ^ y| = |x| ^ y := by
172:theorem abs_rpow_le_abs_rpow (x y : ℝ) : |x ^ y| ≤ |x| ^ y := by
174:  · rw [abs_rpow_of_nonneg hx]
179:theorem abs_rpow_le_exp_log_mul (x y : ℝ) : |x ^ y| ≤ exp (log x * y) := by
180:  refine (abs_rpow_le_abs_rpow x y).trans ?_
193:    _ ≤ |x| ^ (log x)⁻¹ := abs_rpow_le_abs_rpow ..
203:  exact abs_rpow_of_nonneg hx_nonneg
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:277:theorem ContinuousOn.rpow_const (hf : ContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0 ∨ 0 ≤ p) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:280:theorem Continuous.rpow_const (hf : Continuous f) (h : ∀ x, f x ≠ 0 ∨ 0 ≤ p) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:441:theorem hasDerivAt_rpow_const {x p : ℝ} (h : x ≠ 0 ∨ 1 ≤ p) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:685:theorem HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :

exit_code=0
```

### Probe 022

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=34295
```

### Probe 023

```text
$ poll clipped Leibniz source

exit_code=0
```

### Probe 024

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=87729
```

### Probe 025

```text
$ poll clipped Leibniz dependency gate
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```

### Probe 026

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=27684
```

### Probe 027

```text
$ poll derivative comparison source
Poincare/Global/MovingLimitLeibniz.lean:159:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  deriv (v - g) r
in the target expression
  0 ≤ deriv (fun x => v x - g x) r

case hf'_nonneg
g g' v v' : ℝ → ℝ
a z : ℝ
haz : a ≤ z
hg : ContinuousOn g (Icc a z)
hv : ContinuousOn v (Icc a z)
hdg : ∀ r ∈ Ioo a z, HasDerivAt g (g' r) r
hdv : ∀ r ∈ Ioo a z, HasDerivAt v (v' r) r
hb : ∀ r ∈ Ioo a z, |g' r| ≤ v' r
r : ℝ
hr : r ∈ Ioo a z
⊢ 0 ≤ deriv (fun x => v x - g x) r

exit_code=1
```

### Probe 028

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=28564
```

### Probe 029

```text
$ poll comparison dependency probe
/tmp/moving-limit-evidence/Dependencies.lean:159:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  deriv (v - g) r
in the target expression
  0 ≤ deriv (fun x => v x - g x) r

case hf'_nonneg
g g' v v' : ℝ → ℝ
a z : ℝ
haz : a ≤ z
hg : ContinuousOn g (Icc a z)
hv : ContinuousOn v (Icc a z)
hdg : ∀ r ∈ Ioo a z, HasDerivAt g (g' r) r
hdv : ∀ r ∈ Ioo a z, HasDerivAt v (v' r) r
hb : ∀ r ∈ Ioo a z, |g' r| ≤ v' r
r : ℝ
hr : r ∈ Ioo a z
⊢ 0 ≤ deriv (fun x => v x - g x) r
'Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 030

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=74520
```

### Probe 031

```text
$ poll comparison dependency gate
'Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 032

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=90803
```

### Probe 033

```text
$ poll singular derivative bound source
Poincare/Global/MovingLimitLeibniz.lean:187:15: error: don't know how to synthesize implicit argument `d'`
  @HasDerivAt.const_mul ℝ DenselyNormedField.toNontriviallyNormedField r ℝ Real.normedCommRing.toNormedRing
    Real.instRCLike.toNormedAlgebra (fun y => (id y - s) ^ ?m.161) (1 * ?m.161 * (id r - s) ^ (?m.161 - 1)) (C / β)
    (HasDerivAt.rpow_const (HasDerivAt.sub_const s (hasDerivAt_id r))
      (Or.inl (ne_of_gt (sub_pos.mpr (LE.le.trans_lt hsu hr.left)))))
context:
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
⊢ ℝ
Poincare/Global/MovingLimitLeibniz.lean:187:15: error: don't know how to synthesize implicit argument `d`
  @HasDerivAt.const_mul ℝ DenselyNormedField.toNontriviallyNormedField r ℝ Real.normedCommRing.toNormedRing
    Real.instRCLike.toNormedAlgebra (fun y => (id y - s) ^ ?m.161) (1 * ?m.161 * (id r - s) ^ (?m.161 - 1)) (C / β)
    (HasDerivAt.rpow_const (HasDerivAt.sub_const s (hasDerivAt_id r))
      (Or.inl (ne_of_gt (sub_pos.mpr (LE.le.trans_lt hsu hr.left)))))
context:
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
⊢ ℝ → ℝ
Poincare/Global/MovingLimitLeibniz.lean:187:16: error: don't know how to synthesize implicit argument `p`
  @HasDerivAt.rpow_const (fun x => id x - s) 1 r ?m.161 (HasDerivAt.sub_const s (hasDerivAt_id r))
    (Or.inl (ne_of_gt (sub_pos.mpr (LE.le.trans_lt hsu hr.left))))
context:
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
⊢ ℝ
Poincare/Global/MovingLimitLeibniz.lean:188:7: error: don't know how to synthesize implicit argument `b`
  @Or.inl (id r - s ≠ 0) (1 ≤ ?m.161) (ne_of_gt (sub_pos.mpr (LE.le.trans_lt hsu hr.left)))
context:
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
⊢ Prop
Poincare/Global/MovingLimitLeibniz.lean:187:9: error: failed to infer `have` declaration type
Poincare/Global/MovingLimitLeibniz.lean:196:2: error: `dsimp` made no progress

exit_code=1
```

### Probe 034

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=68978
```

### Probe 035

```text
$ poll singular derivative bound dependencies
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
/tmp/moving-limit-evidence/Dependencies.lean:186:73: error: unsolved goals
case h.e'_9
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
hp : HasDerivAt (fun y => C / β * (id y - s) ^ β) (C / β * (1 * β * (id r - s) ^ (β - 1))) r
⊢ C * (r - s) ^ (-1 + β) = C * (-s + id r) ^ (-1 + β)
/tmp/moving-limit-evidence/Dependencies.lean:196:2: error: linarith failed to find a contradiction
case h
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
hdv : ∀ r ∈ Ioo u v, HasDerivAt (fun r => C / β * (r - s) ^ β) (C * (r - s) ^ (β - 1)) r
hi : |g v - g u| ≤ ((fun x => C / β) * fun x => (id x - s) ^ β) v - ((fun x => C / β) * fun x => (id x - s) ^ β) u
a✝ : C / β * ((v - s) ^ β - (u - s) ^ β) < |g v - g u|
⊢ False
failed
'Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 036

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=28466
```

### Probe 037

```text
$ poll power secant source
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/MovingLimitLeibniz.lean:186:73: error: unsolved goals
case h.e'_9
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
r : ℝ
hr : r ∈ Ioo u v
hp : HasDerivAt (fun y => C / β * (id y - s) ^ β) (C / β * (1 * β * (id r - s) ^ (β - 1))) r
⊢ C * (r - s) ^ (-1 + β) = C * (-s + id r) ^ (-1 + β)
Poincare/Global/MovingLimitLeibniz.lean:196:2: error: linarith failed to find a contradiction
case h
g g' : ℝ → ℝ
s T u v C β : ℝ
hβ : 0 < β
hc : ContinuousOn g (Icc s T)
hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r
hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r - s) ^ (β - 1)
hsu : s ≤ u
huv : u ≤ v
hvT : v ≤ T
hdv : ∀ r ∈ Ioo u v, HasDerivAt (fun r => C / β * (r - s) ^ β) (C * (r - s) ^ (β - 1)) r
hi : |g v - g u| ≤ ((fun x => C / β) * fun x => (id x - s) ^ β) v - ((fun x => C / β) * fun x => (id x - s) ^ β) u
a✝ : C / β * ((v - s) ^ β - (u - s) ^ β) < |g v - g u|
⊢ False
failed

exit_code=1
```

### Probe 038

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=59344
```

### Probe 039

```text
$ poll corrected singular derivative dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 040

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.abs_rpow_sub_le\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=41278
```

### Probe 041

```text
$ poll fractional-power secant dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.abs_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 042

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean

running_session=45757
```

### Probe 043

```text
$ poll clipped power source
Poincare/Global/MovingLimitLeibniz.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Poincare/Global/MovingLimitLeibniz.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
Poincare/Global/MovingLimitLeibniz.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/MovingLimitLeibniz.lean:239:6: error: failed to prove positivity/nonnegativity/nonzeroness

exit_code=1
```

### Probe 044

```text
$ rg -n 'max_sub_sub|sub_max_sub|abs_sub_comm|norm_eq_abs|theorem IntervalIntegrable.congr_ae' .lake/packages/mathlib/Mathlib/Algebra/Order/Group/Unbundled/MinMax.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Order/Group/Abs.lean | head -25
rg: .lake/packages/mathlib/Mathlib/Algebra/Order/Group/Unbundled/MinMax.lean: No such file or directory (os error 2)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:97:theorem IntervalIntegrable.congr_ae {g : ℝ → ε} (hf : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:734:  simp only [← Real.norm_eq_abs, norm_integral_eq_norm_integral_uIoc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1354:  simpa only [← Real.norm_eq_abs] using norm_integral_le_integral_norm hab

exit_code=0
```

### Probe 045

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=74022
```

### Probe 046

```text
$ rg -n 'max_sub_sub|sub_max_sub|theorem max_sub' .lake/packages/mathlib/Mathlib/Algebra/Order; sed -n '92,106p' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/Pointwise/Interval.lean:478:  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean:62:@[to_additive max_sub_sub_right]
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean:70:@[to_additive max_sub_sub_left]
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean:80:theorem max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) := by
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:796:    rw [← max_sub_sub_right]

theorem intervalIntegrable_congr_ae {g : ℝ → ε} (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b := by
  rw [intervalIntegrable_iff, integrableOn_congr_fun_ae h, intervalIntegrable_iff]

theorem IntervalIntegrable.congr_ae {g : ℝ → ε} (hf : IntervalIntegrable f μ a b)
    (h : f =ᵐ[μ.restrict (Ι a b)] g) :
    IntervalIntegrable g μ a b := by
  rwa [← intervalIntegrable_congr_ae h]

theorem intervalIntegrable_congr {g : ℝ → ε} (h : EqOn f g (Ι a b)) :
    IntervalIntegrable f μ a b ↔ IntervalIntegrable g μ a b :=
  intervalIntegrable_congr_ae <| (ae_restrict_mem measurableSet_uIoc).mono h

alias ⟨IntervalIntegrable.congr, _⟩ := intervalIntegrable_congr

exit_code=0
```

### Probe 047

```text
$ poll clipped power dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 048

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=71945
```

### Probe 049

```text
$ poll two-sided power integrability
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/moving-limit-evidence/Dependencies.lean:286:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  |t - s|
in the target expression
  (fun s => (t - s) ^ (β - 1)) s = (fun s => |t - s| ^ (β - 1)) s

β T t : ℝ
hβ : 0 < β
ht : t ∈ Icc 0 T
hl : IntervalIntegrable (fun s => (t - s) ^ (β - 1)) volume 0 t
hr : IntervalIntegrable (fun s => (s - t) ^ (β - 1)) volume t T
s : ℝ
hs : s ∈ Ioc 0 t
⊢ (fun s => (t - s) ^ (β - 1)) s = (fun s => |t - s| ^ (β - 1)) s
/tmp/moving-limit-evidence/Dependencies.lean:291:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  |t - s|
in the target expression
  (fun s => (s - t) ^ (β - 1)) s = (fun s => |t - s| ^ (β - 1)) s

β T t : ℝ
hβ : 0 < β
ht : t ∈ Icc 0 T
hl : IntervalIntegrable (fun s => (t - s) ^ (β - 1)) volume 0 t
hr : IntervalIntegrable (fun s => (s - t) ^ (β - 1)) volume t T
hl' : IntervalIntegrable (fun s => |t - s| ^ (β - 1)) volume 0 t
s : ℝ
hs : s ∈ Ioc t T
⊢ (fun s => (s - t) ^ (β - 1)) s = (fun s => |t - s| ^ (β - 1)) s
'Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 050

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=30365
```

### Probe 051

```text
$ poll power integrability dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 052

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=10073
```

### Probe 053

```text
$ poll derivative-to-secant dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```

### Probe 054

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=17594
```

### Probe 055

```text
$ poll main Leibniz dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/moving-limit-evidence/Dependencies.lean:337:56: error: Invalid `⟨...⟩` notation: The expected type `Quot ⇑CauSeq.equiv` is not an inductive type

Note: This notation can only be used when the expected type is an inductive type with a single constructor
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 056

```text
$ rg -n 'norm_laplacian|laplacian.*norm|norm_eq_one|norm_basisFun' .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean | head -25; rg -n 'theorem le_opNorm|theorem norm_sum_le' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator .lake/packages/mathlib/Mathlib/Analysis/Normed/Group | head -16; sed -n '168,202p' Poincare/Global/HeatDuhamelSpatialHolderHessian.lean
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:454:lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:455:    ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:458:lemma nnnorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:459:    ‖b i‖₊ = 1 := b.orthonormal.nnnorm_eq_one i
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:462:lemma enorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:463:    ‖b i‖ₑ = 1 := b.orthonormal.enorm_eq_one i
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:164:theorem laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis {ι : Type*} [Fintype ι] {e : E}
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:174:theorem laplacian_eq_iteratedFDeriv_orthonormalBasis {ι : Type*} [Fintype ι]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:185:theorem laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis {e : E} (hs : UniqueDiffOn ℝ s)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:189:  apply laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he (stdOrthonormalBasis ℝ E)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:196:theorem laplacian_eq_iteratedFDeriv_stdOrthonormalBasis :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:199:  laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:205:  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:227:  simp [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:237:  simp [laplacian_eq_iteratedFDeriv_orthonormalBasis f Complex.orthonormalBasisOneI]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:244:  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_const_of_ne two_ne_zero,
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:258:  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs h₂x, h₁x]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:266:  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, hx]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:276:  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:282:  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:304:  simp only [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:311:  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_neg]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:318:  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:324:  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Laplacian.lean:347:  simp [laplacianWithin_eq_iteratedFDerivWithin_stdOrthonormalBasis _ hs hx,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:207:theorem le_opNorm (x : V₁) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:217:theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:829:theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:239:theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:248:theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
    (∫ s in (0 : ℝ)..t, A * (t - s) ^ (α / 2 - 1)) =
      A * (2 / α) * t ^ (α / 2) := by
  rw [intervalIntegral.integral_const_mul]
  have he : α / 2 - 1 = -(1 - α / 2) := by ring
  simp_rw [he]
  rw [integral_sub_rpow_neg (by linarith : 1 - α / 2 < 1)]
  rw [show 1 - (1 - α / 2) = α / 2 by ring]
  field_simp

/-- Dilation gives joint continuity of the full Hessian at positive times. -/
theorem continuous_hessian_pos :
    Continuous (fun p : Ioi (0 : ℝ) × E => Hess p.1 p.2) := by
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
  have hunit : ContDiff ℝ 0 (Hess 1) :=
    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
    Real.sqrt_pos.2 p.1.property
  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 2)⁻¹) •
        Hess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
      ((ha.pow 2).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
      (hunit.continuous.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
  apply hc.congr
  intro p
  have h := hessian_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm

/-- The cancelled spatial integral is integrable over the Duhamel time interval. -/
theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}

exit_code=0
```

### Probe 057

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=12645
```

### Probe 058

```text
$ poll main Leibniz final dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```

### Probe 059

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/FrozenProbe.lean

running_session=83951
```

### Probe 060

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=68922
```

### Probe 061

```text
$ poll exact frozen-statement probe
/tmp/moving-limit-evidence/FrozenProbe.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/FrozenProbe.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/FrozenProbe.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/moving-limit-evidence/FrozenProbe.lean:370:21: error: unsolved goals
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
⊢ HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, heatSolution (r - s) (fun y => f (s, y)) x)
    (f (t, x) + ∫ (s : ℝ) in 0..t, deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) (Icc 0 T) t
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
⊢ HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, heatSolution (r - s) (fun y => f (s, y)) x)
    (f (t, x) + ∫ (s : ℝ) in 0..t, deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) (Icc 0 T) t

exit_code=1
```

### Probe 062

```text
$ poll heat derivative majorant dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/moving-limit-evidence/Dependencies.lean:379:6: error: Type mismatch
  norm_sum_le ?m.404 ?m.405
has type
  ‖∑ i ∈ ?m.404, ?m.405 i‖ ≤ ∑ i ∈ ?m.404, ‖?m.405 i‖
but is expected to have type
  |∑ i,
        ((fderiv ℝ (fderiv ℝ (heatSolution (r - s) fun y => f (s, y))) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) i)| ≤
    ∑ i,
      ‖((fderiv ℝ (fderiv ℝ (heatSolution (r - s) fun y => f (s, y))) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          ((EuclideanSpace.basisFun (Fin 3) ℝ) i)‖
'Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 063

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=34961
```

### Probe 064

```text
$ poll heat majorant corrected dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit_code=0
```

### Probe 065

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=27951
```

### Probe 066

```text
$ poll frozen theorem dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/moving-limit-evidence/Dependencies.lean:434:55: error: unsolved goals
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
F : ℝ → ℝ → ℝ := fun r s => if r - s = 0 then f (s, x) else heatSolution (r - s) (fun y => f (s, y)) x
hc : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hd :
  ∀ s ∈ Icc 0 T,
    ∀ r ∈ Ioc s T, HasDerivAt (fun ρ => F ρ s) (deriv (fun ρ => heatSolution (ρ - s) (fun y => f (s, y)) x) r) r
C : ℝ
hC : 0 ≤ C
hCb :
  ∀ s ∈ Icc 0 T,
    ∀ r ∈ Ioc s T, |deriv (fun ρ => heatSolution (ρ - s) (fun y => f (s, y)) x) r| ≤ C * (r - s) ^ (α / 2 - 1)
⊢ f (t, x) = ?m.536
/tmp/moving-limit-evidence/Dependencies.lean:409:21: error: unsolved goals
α : ℝ
hα : 0 < α
hα1 : α < 1
T : ℝ
hT : 0 < T
hT1 : T ≤ 1
f : ℝ × E → ℝ
M K : ℝ
hM0 : 0 ≤ M
hK0 : 0 ≤ K
hf : ContinuousOn f (Icc 0 T ×ˢ univ)
hM : ∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M
hK : ∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α
t : ℝ
ht : t ∈ Icc 0 T
x : E
F : ℝ → ℝ → ℝ := fun r s => if r - s = 0 then f (s, x) else heatSolution (r - s) (fun y => f (s, y)) x
hc : ContinuousOn (fun p => F p.1 p.2) {p | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1}
hd :
  ∀ s ∈ Icc 0 T,
    ∀ r ∈ Ioc s T, HasDerivAt (fun ρ => F ρ s) (deriv (fun ρ => heatSolution (ρ - s) (fun y => f (s, y)) x) r) r
C : ℝ
hC : 0 ≤ C
hCb :
  ∀ s ∈ Icc 0 T,
    ∀ r ∈ Ioc s T, |deriv (fun ρ => heatSolution (ρ - s) (fun y => f (s, y)) x) r| ≤ C * (r - s) ^ (α / 2 - 1)
⊢ HasDerivWithinAt (fun r => ∫ (s : ℝ) in 0..r, heatSolution (r - s) (fun y => f (s, y)) x)
    (f (t, x) + ∫ (s : ℝ) in 0..t, deriv (fun r => heatSolution (r - s) (fun y => f (s, y)) x) t) (Icc 0 T) t
'Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit_code=1
```

### Probe 067

```text
$ cp Poincare/Global/MovingLimitLeibniz.lean /tmp/moving-limit-evidence/Dependencies.lean
printf '\n#print axioms Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation\n' >> /tmp/moving-limit-evidence/Dependencies.lean
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/Dependencies.lean

running_session=70809
```

### Probe 068

```text
$ poll exact frozen theorem final dependencies
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:51: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
/tmp/moving-limit-evidence/Dependencies.lean:190:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 069

```text
$ Final focused Lean gate

running_session=9023
```

### Probe 070

```text
$ Final forbidden-token gate

exit_code=1
```

### Probe 071

```text
$ Final whitespace gates

exit_code=0
```

### Probe 072

```text
$ poll final focused Lean gate

exit_code=0
```

### Probe 073

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/moving-limit-evidence/FinalDependencies.lean

running_session=92139
```

### Probe 074

```text
$ poll final declaration dependencies and exact frozen-type assignment
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_of_dominated_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit_of_secants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.abs_sub_le_of_deriv_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_sub_le_rpow_of_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.abs_clipped_rpow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.intervalIntegrable_abs_sub_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.MovingLimitLeibniz.clipped_secant_le_of_deriv_rpow_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.hasDerivWithinAt_integral_moving_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.exists_heat_integrand_deriv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation' depends on axioms: [propext, Classical.choice, Quot.sound]

exit_code=0
```

### Probe 075

```text
$ rg -n '(theorem|lemma|def).*hasDerivAt_(id|const)|theorem hasDerivWithinAt_iff_tendsto_slope|theorem hasDerivAt_iff_tendsto_slope|theorem intervalIntegrable_rpow|le_opNorm₂|inv_mul_cancel₀' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean .lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:336:  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:369:      · exact left_inv_eq_right_inv (inv_mul_cancel₀ <| inv_ne_zero h) (inv_mul_cancel₀ h)
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:422:  · rw [inv_mul_cancel₀ h, one_mul]
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:472:  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel₀ h]⟩
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:492:      inv_mul_cancel₀ ha, mul_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:37:theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:44:theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:148:    ‖f‖ fun y x => (f.le_opNorm₂ x y).trans_eq <| by simp only [mul_right_comm]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:153:    exact (flip f).le_opNorm₂ y x
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean:64:theorem hasDerivWithinAt_iff_tendsto_slope :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean:69:theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean:73:theorem hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean:78:theorem hasDerivAt_iff_tendsto_slope_left_right [LinearOrder 𝕜] : HasDerivAt f f' x ↔
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean:82:theorem hasDerivAt_iff_tendsto_slope_zero :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:670:theorem hasDerivAt_id : HasDerivAt id 1 x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:673:theorem hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:763:theorem hasDerivAt_const : HasDerivAt (fun _ => c) 0 x :=

exit_code=0
```

### Probe 076

```text
$ git diff --stat bec9c44750f80151aabb63b859c283cfa944da3a
 Poincare/Global/MovingLimitLeibniz.lean | 444 ++++++++++++++++++++++++++++++++
 1 file changed, 444 insertions(+)

exit_code=0
```

## Batched Mathlib source-name search

```text
$ rg -n --glob *.lean <batched source identifiers> .lake/packages/mathlib/Mathlib
rg_exit_code=0
First matching source line for each resolved identifier:
Analysis: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:9:import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
Calculus: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:12:public import Mathlib.Analysis.Calculus.Deriv.Basic
Continuous: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:492:lemma continuous_sumCoeffsExp : Continuous (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
ContinuousLinearMap: .lake/packages/mathlib/Mathlib/Algebra/Category/ContinuousCohomology/Basic.lean:78:  { hom := TopModuleCat.ofHom (ContinuousLinearMap.compLeftContinuous _ _ φ.hom.hom)
ContinuousOn: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:296:  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc fun x hx ↦
EuclideanSpace: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:174:  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
Eventually: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:447:  · exact Eventually.of_forall fun h => R.T_nonneg _
Filter: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:120:    Filter.Tendsto (of v).convs Filter.atTop <| 𝓝 v := by
Finset: .lake/packages/mathlib/Mathlib/Algebra/WithConv.lean:8:public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
Global: .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:268:Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
HasDerivAt: .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:233:    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
HasDerivWithinAt: .lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/TsumUniformlyOn.lean:77:  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
Icc_subset_Icc: .lake/packages/mathlib/Mathlib/NumberTheory/AbelSummation.lean:70:    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
Icc_subset_Icc_right: .lake/packages/mathlib/Mathlib/NumberTheory/AbelSummation.lean:163:    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
Iio_mem_nhds: .lake/packages/mathlib/Mathlib/NumberTheory/SumPrimeReciprocals.lean:71:  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
Integrable: .lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:56:`Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)` is equivalent to
IntegrableOn: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:294:    IntegrableOn (fun t ↦ θ t / (t * log t ^ 2)) (Set.Icc 2 x) volume := by
Interval: .lake/packages/mathlib/Mathlib/Algebra/CharP/Basic.lean:15:public import Mathlib.Order.Interval.Set.Defs
IntervalIntegrable: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:364:    IntervalIntegrable (fun x ↦ 1 / log x ^ 2) MeasureTheory.volume a b := by
Ioc_subset_Icc_self: .lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:268:      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
Ioi_mem_nhds: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:242:    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
Mathlib: .lake/packages/mathlib/Mathlib/Deprecated/Aliases.lean:8:public import Mathlib.Init
Measure: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:10:public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
MeasureTheory: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:10:public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
MonotoneOn: .lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:288:    Monotone f ↔ MonotoneOn f (Icc l (l + a)) :=
OrthonormalBasis: .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:833:def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (euclidean.mixedSpace K) :=
Poincare: .lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Conservative.lean:37:conservative dynamical system, Poincare recurrence theorem
Real: .lake/packages/mathlib/Mathlib/Algebra/Tropical/BigOperators.lean:29:`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).
Topology: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:12:public import Mathlib.Topology.Order.LeftRightNhds
abs_le: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Summable.lean:131:        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
abs_neg: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:64:protected theorem abs_neg : ∀ x : EReal, (-x).abs = x.abs
abs_nonneg: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:75:  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
abs_of_neg: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:253:        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
abs_of_nonneg: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:241:      rw [abs_of_nonneg hx]
abs_of_nonpos: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:247:      simp only [Pi.neg_apply, abs_of_nonpos hx]
abs_of_pos: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:446:      rw [abs_of_pos this]
abs_sub_comm: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:121:  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v
add_comm: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:128:  | add_comm {a b : Pre R X} : Rel (a + b) (b + a)
ae_ne: .lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean:66:lemma Measure.ae_ne (μ : Measure α) [NoAtoms μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=
ae_restrict_mem: .lake/packages/mathlib/Mathlib/Probability/ConditionalProbability.lean:198:  ae_smul_measure (ae_restrict_mem hs) _
aestronglyMeasurable: .lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Function.lean:92:  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
basisFun: .lake/packages/mathlib/Mathlib/RepresentationTheory/Tannaka.lean:204:  refine ⟨s, (basisFun k G).ext fun u ↦ ?_⟩
calc: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:106:    calc 1 < ε * (N' : K) := (div_lt_iff₀' ε_pos).mp one_div_ε_lt_N'
comp: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:270:      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A →+* FreeAlgebra A X).comp
comp_continuous: .lake/packages/mathlib/Mathlib/Topology/Homotopy/Lifting.lean:133:    (cont_g'.comp_continuous (.prodMk_left a) fun _ ↦ ⟨⟨⟩, ha⟩) ?_ 0 (g'_0 a).symm) t
comp_sub_left: .lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:371:  convert h.comp_sub_left x
comp_sub_right: .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean:101:  exact Integrable.comp_sub_right hg μ
congr: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:250:    congr 1
congr': .lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:104:theorem Integrable.congr'_enorm {f : α → ε} {g : α → ε'} (hf : Integrable f μ)
congr_of_eventuallyEq: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:185:    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
congr_of_mem: .lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean:469:    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy ↦ ?_) ?_
const_mul: .lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:75:lemma _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl
continuousAt: .lake/packages/mathlib/Mathlib/Dynamics/TopologicalEntropy/DynamicalEntourage.lean:84:  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)
continuousOn: .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Group/Abelian.lean:115:          α.left.continuous.continuousOn).isPreirreducible
continuousOn_const: .lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:223:  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
continuous_const: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:494:  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))
continuous_fst: .lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:164:  cont' := ϕ.continuous (continuous_subtype_val.comp continuous_fst) continuous_snd
continuous_id: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:494:  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))
continuous_snd: .lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:103:  cont' := continuous_snd
convex_Icc: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:240:    (convex_Icc _ _) ?mem_Icc <| ⟨h_bi_le_r i, by exact_mod_cast (le_of_lt (R.r_lt_n i n h_ge_n₀))⟩
deriv: .lake/packages/mathlib/Mathlib/Computability/RegularExpressions.lean:143:/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
diff_subset: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:587:        · exact zsmul_mem (subset_span (Set.diff_subset hv)) _
differentiableAt: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:242:    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
differentiableWithinAt: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:348:  fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt
div_nonneg: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:461:lemma div_nonneg (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
dsimp: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:248:    dsimp +instances only [HSMul.hSMul, instSMul, Quot.map]
eq_or_lt_of_le: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:479:  · rcases eq_or_lt_of_le ha with rfl | ha
fderiv: .lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/InteriorBoundary.lean:228:    (hfx : Function.Surjective (fderiv ℝ f x)) : f x ∈ interior s := by
filter_mono: .lake/packages/mathlib/Mathlib/Dynamics/Ergodic/Extreme.lean:78:    _ = ∫⁻ _ in s, c ∂μ := lintegral_congr_ae <| hc.filter_mono <| ae_mono restrict_le_self
filter_upwards: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:87:    filter_upwards [eventually_gt_atTop 1] with x hx
id_eq: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:566:  simp only [AlgHom.ext_iff, AlgHom.coe_id, id_eq, AlgHom.coe_comp, Subalgebra.coe_val,
if_neg: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:507:        have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans <| if_neg hxy
if_true: .lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:267:    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
indicator: .lake/packages/mathlib/Mathlib/Algebra/NoZeroSMulDivisors/Defs.lean:25:assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀
indicator_of_mem: .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Pi.lean:87:    exact Set.indicator_of_mem (hj _ hi) _
indicator_of_notMem: .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Pi.lean:89:    exact Finset.prod_eq_zero hi <| Set.indicator_of_notMem hj _
integrableOn_Icc: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:296:  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc fun x hx ↦
integral_congr: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:322:      intervalIntegral.integral_congr fun u _ ↦ by simp [deriv_inv_log, field]
integral_congr_ae_restrict: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:384:  apply intervalIntegral.integral_congr_ae_restrict
integral_const_mul: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:436:        rw [intervalIntegral.integral_const_mul, abs_of_nonneg]
integral_hasDerivAt_right: .lake/packages/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean:217:  simpa using intervalIntegral.integral_hasDerivAt_right int1 int2 int3 |>.isLittleO
integral_indicator: .lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/IntegralCompProd.lean:244:    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
integral_of_le: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:317:    ← intervalIntegral.integral_of_le hx]
integral_sub: .lake/packages/mathlib/Mathlib/NumberTheory/ZetaValues.lean:174:      rw [intervalIntegral.integral_sub, intervalIntegral.integral_comp_mul_left _ m0', mul_zero,
interior_Icc: .lake/packages/mathlib/Mathlib/NumberTheory/Modular.lean:928:  · rw [abs_lt, ← Set.mem_Ioo, ← interior_Icc]
intervalIntegrable: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:365:  refine ContinuousOn.intervalIntegrable fun x hx ↦ ContinuousAt.continuousWithinAt ?_
intervalIntegrable_of_Icc: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean:137:    · exact (h_df.continuousOn.mono (Icc_subset_Icc le_rfl hy.2)).intervalIntegrable_of_Icc hy.1
intervalIntegral: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:317:    ← intervalIntegral.integral_of_le hx]
inv_mul_cancel: .lake/packages/mathlib/Mathlib/Algebra/Tropical/Basic.lean:412:    inv_mul_cancel := fun _ => untrop_injective <| neg_add_cancel _
inv_nonneg: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:267:        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
le_abs_self: .lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean:114:  sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))
le_max_left: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:111:      (N' : K) ≤ (N : K) := by exact_mod_cast le_max_left _ _
le_max_right: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:113:      _ ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
le_of_eq: .lake/packages/mathlib/Mathlib/Computability/TuringMachine/StackTuringMachine.lean:677:    stk_nth_val _ (hT k), List.getElem?_eq_none (le_of_eq List.length_reverse),
le_of_lt: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:153:  have : ∀ x : K, 0 ≤ a * (x * x) + b * x + c := fun x => le_of_lt (h x)
le_of_not_ge: .lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:67:  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩
le_of_not_gt: .lake/packages/mathlib/Mathlib/Data/Sign/Defs.lean:315:  exact (le_of_not_gt h_1).eq_of_not_lt h_2
le_opNorm: .lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:182:    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
le_rfl: .lake/packages/mathlib/Mathlib/Algebra/Tropical/Basic.lean:299:  untrop_injective (min_eq_right le_rfl)
le_total: .lake/packages/mathlib/Mathlib/Algebra/Tropical/Basic.lean:251:    le_total := fun a b => le_total (untrop a) (untrop b)
le_trans: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:240:            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
left_mem_Icc: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:117:        rw [Set.left_mem_Icc]
lt_of_le_of_ne: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:444:          inv_pos.2 (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm)
lt_of_not_ge: .lake/packages/mathlib/Mathlib/Data/PSigma/Order.lean:82:        · exact Lex.right _ (hab.lt_of_not_ge fun h => hba <| Lex.right _ h) }
lt_or_gt_of_ne: .lake/packages/mathlib/Mathlib/Computability/TuringMachine/StackTuringMachine.lean:564:      rcases lt_or_gt_of_ne h with h | h
max_eq_left: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:253:        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
max_eq_right: .lake/packages/mathlib/Mathlib/Computability/Ackermann.lean:314:        rw [max_eq_right h₁]
max_le: .lake/packages/mathlib/Mathlib/Data/Multiset/UnionInter.lean:371:      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩
max_sub_sub_right: .lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:796:    rw [← max_sub_sub_right]
measurableSet_Ioc: .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean:262:    refine setIntegral_nonneg_ae measurableSet_Ioc (univ_mem' fun t ht ↦ ?_)
measurableSet_Ioo: .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:278:    exact ⟨s, hs, hs'.indicator measurableSet_Ioo⟩
mem_univ: .lake/packages/mathlib/Mathlib/Data/W/Basic.lean:121:  Nat.lt_succ_of_le (Finset.le_sup (f := (depth <| f ·)) (Finset.mem_univ i))
min_eq_right: .lake/packages/mathlib/Mathlib/Algebra/Tropical/Basic.lean:299:  untrop_injective (min_eq_right le_rfl)
min_le_left: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:355:              · exact min_le_left _ _
mono: .lake/packages/mathlib/Mathlib/Algebra/Homology/HomologySequenceLemmas.lean:23:of these three morphisms to induce a mono/epi/iso in a given degree
mono_set: .lake/packages/mathlib/Mathlib/NumberTheory/AbelSummation.lean:77:  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
monotoneOn_of_deriv_nonneg: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:341:    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
mul_assoc: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:131:  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
mul_comm: .lake/packages/mathlib/Mathlib/Algebra/RingQuot.lean:323:  mul_comm := by
mul_le_mul_of_nonneg_left: .lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean:181:  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd
mul_left_comm: .lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Associated.lean:316:        rw [← hv, mul_assoc c (v : M) d, mul_left_comm c, ← hu]
mul_nonneg: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:141:  · have ha' : 0 ≤ 4 * a := mul_nonneg zero_le_four ha.le
mul_one: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:133:  | mul_one {a : Pre R X} : Rel (a * 1) a
ne_of_gt: .lake/packages/mathlib/Mathlib/Data/EReal/Inv.lean:521:  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
neg_ne_zero: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:162:  discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) <| by
neg_nonneg: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:146:  discrim_neg a b c ▸ discrim_le_zero <| by simpa only [neg_mul, ← neg_add, neg_nonneg]
neg_pos: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:163:    simpa only [neg_mul, ← neg_add, neg_pos]
neg_sub: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Basic.lean:303:  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)
nhdsWithin_mono: .lake/packages/mathlib/Mathlib/Topology/LocallyFinite.lean:80:  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ ↦ nhdsWithin_mono _)
norm_eq_abs: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:252:  simp only [norm_eq_abs]
norm_eq_one: .lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Basic.lean:253:alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary
norm_inv: .lake/packages/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean:138:    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
norm_mul: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:237:  rw [norm_mul, ← mul_assoc]
norm_ne_zero_iff: .lake/packages/mathlib/Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean:145:  let xu : Lˣ := (Algebra.norm_ne_zero_iff.1 <| hx ▸ zero_ne_one.symm).isUnit.unit
norm_nonneg: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:223:    convert mul_le_mul_of_nonneg_right this (norm_nonneg _ : 0 ≤ ‖b i‖)
norm_sum_le: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:219:    _ ≤ ∑ i, ‖Int.fract (b.repr m i) • b i‖ := norm_sum_le _ _
not_le: .lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:140:  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge
prodMk: .lake/packages/mathlib/Mathlib/Algebra/FiniteSupport/Basic.lean:56:lemma HasFiniteMulSupport.prodMk {M' : Type*} [One M'] {f : α → M} {g : α → M'}
restrict: .lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Support.lean:130:  use Finset.restrict f.support f.coeff
restrict_Ioo_eq_restrict_Ioc: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean:287:    rw [← restrict_Ioo_eq_restrict_Ioc]
right_mem_Icc: .lake/packages/mathlib/Mathlib/Algebra/Order/Interval/Set/Instances.lean:63:instance instOne : One (Icc (0 : R) 1) where one := ⟨1, right_mem_Icc.2 zero_le_one⟩
rpow_const: .lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Bounds.lean:52:    exact continuous_im.rpow_const fun τ ↦ .inl τ.im_ne_zero
rpow_le_rpow: .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Monotone.lean:75:    convert rpow_le_rpow _ hz (le_of_lt ha) using 1
rpow_le_rpow_of_nonpos: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:573:          _ ≤ _ := rpow_le_rpow_of_nonpos (hf_pos₂ u hu.1) (hf₁ u hu).2 (le_of_lt hp)
rpow_nonneg: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:585:        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)
rpow_sub_one: .lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:229:          rw [rpow_sub_one, ← div_mul, div_one, mul_comm, one_div, inv_rpow, ← div_eq_mul_inv]
self_mem_nhdsWithin: .lake/packages/mathlib/Mathlib/NumberTheory/Modular.lean:895:    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
slope: .lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean:232:    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
smul_eq_mul: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:289:    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
stronglyMeasurableAtFilter: .lake/packages/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean:214:    f_contOn.stronglyMeasurableAtFilter isOpen_Ioo _ zRe_mem_s
sub_add_cancel: .lake/packages/mathlib/Mathlib/Algebra/RingQuot.lean:440:          fun _ w ↦ w ⟨x, y, h, sub_add_cancel x y⟩⟩
sub_apply: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Pi.lean:80:    Pi.isUnit_iff, sub_apply, algebraMap_apply]
sub_const: .lake/packages/mathlib/Mathlib/Algebra/Ring/Periodic.lean:124:theorem Periodic.sub_const [SubtractionCommMonoid α] (h : Periodic f c) (a : α) :
sub_le_sub_right: .lake/packages/mathlib/Mathlib/Data/Multiset/UnionInter.lean:58:  Multiset.add_le_add_right <| Multiset.sub_le_sub_right h
sub_ne_zero: .lake/packages/mathlib/Mathlib/Algebra/CharP/Defs.lean:196:  rw [ne_comm, ← sub_ne_zero, sub_neg_eq_add, one_add_one_eq_two, ← Nat.cast_two, Ne,
sub_neg: .lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:383:lemma sub_neg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
sub_nonneg: .lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:373:lemma sub_nonneg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
sub_nonpos: .lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:377:lemma sub_nonpos {x y : EReal} : x - y ≤ 0 ↔ x ≤ y := by
sub_pos: .lake/packages/mathlib/Mathlib/Data/EReal/Operations.lean:380:lemma sub_pos {x y : EReal} : 0 < x - y ↔ y < x := by
sub_self: .lake/packages/mathlib/Mathlib/Algebra/RingQuot.lean:456:        rw [← su, map_sub, mkRingHom_rel h, sub_self]
sub_sub_sub_cancel_right: .lake/packages/mathlib/Mathlib/Algebra/Field/GeomSum.lean:54:  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]
sub_zero: .lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:102:  rw [quadratic_eq_zero_iff ha this, add_zero, sub_zero, or_self_iff]
sum_le_sum: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:221:    _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => ?_
symm: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:409:theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R := by
tendsto_integral_filter_of_dominated_convergence: .lake/packages/mathlib/Mathlib/Probability/StrongLaw.lean:193:  refine tendsto_integral_filter_of_dominated_convergence (fun x => abs (f x)) ?_ ?_ ?_ ?_
trans: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:505:        have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans <| if_pos rfl
trans_lt: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:101:    have zero_lt_B : 0 < B := B_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
uIcc_of_le: .lake/packages/mathlib/Mathlib/Algebra/Field/Periodic.lean:120:  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]
uIoc_of_le: .lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:440:    rw [Set.uIoc_of_le (by linarith), ← integrableOn_Icc_iff_integrableOn_Ioc]
univ: .lake/packages/mathlib/Mathlib/Algebra/Tropical/Lattice.lean:68:      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
vsub_eq_sub: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Basic.lean:412:    simp_rw [vsub_eq_sub, zero_sub, neg_mem_iff]
zero_add: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:129:  | zero_add {a : Pre R X} : Rel (0 + a) a
zero_rpow: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:559:      simp only [hx, zero_rpow (ne_of_lt hp), mul_zero,
zero_sub: .lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean:299:        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]

```

## Verified proof diff

```diff
diff --git a/Poincare/Global/MovingLimitLeibniz.lean b/Poincare/Global/MovingLimitLeibniz.lean
new file mode 100644
index 00000000..ce082dd6
--- /dev/null
+++ b/Poincare/Global/MovingLimitLeibniz.lean
@@ -0,0 +1,444 @@
+import Poincare.Global.HeatDuhamelHeatEquation
+import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
+
+set_option autoImplicit false
+
+noncomputable section
+
+open Set MeasureTheory Filter
+open scoped Topology Interval
+
+namespace Poincare.MovingLimitLeibniz
+
+/-- Integrable bounds on secants permit differentiation within an arbitrary real set. -/
+theorem hasDerivWithinAt_integral_of_dominated_secants
+    {G : ℝ → ℝ → ℝ} {D B : ℝ → ℝ} {μ : Measure ℝ} {S : Set ℝ} {t : ℝ}
+    (hG : ∀ᶠ r in 𝓝[S] t, Integrable (G r) μ)
+    (hGt : Integrable (G t) μ) (hB : Integrable B μ)
+    (hbound : ∀ᶠ r in 𝓝[S] t, ∀ᵐ s ∂μ,
+      ‖G r s - G t s‖ ≤ B s * ‖r - t‖)
+    (hD : ∀ᵐ s ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t) :
+    HasDerivWithinAt (fun r => ∫ s, G r s ∂μ) (∫ s, D s ∂μ) S t := by
+  rw [hasDerivWithinAt_iff_tendsto_slope]
+  have hle : 𝓝[S \ {t}] t ≤ 𝓝[S] t := nhdsWithin_mono _ diff_subset
+  have hi := tendsto_integral_filter_of_dominated_convergence B
+    (by
+      filter_upwards [hG.filter_mono hle] with r hr
+      exact (hr.aestronglyMeasurable.sub hGt.aestronglyMeasurable).const_mul (r-t)⁻¹)
+    (by
+      filter_upwards [hbound.filter_mono hle, self_mem_nhdsWithin] with r hr hrt
+      have hn : r - t ≠ 0 := sub_ne_zero.mpr (by simpa using hrt.2)
+      filter_upwards [hr] with s hs
+      rw [norm_mul, norm_inv]
+      calc
+        ‖r - t‖⁻¹ * ‖G r s - G t s‖ ≤ ‖r - t‖⁻¹ * (B s * ‖r - t‖) :=
+          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (norm_nonneg _))
+        _ = B s := by rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn), mul_one])
+    hB (by
+      filter_upwards [hD] with s hs
+      simpa only [slope, smul_eq_mul] using
+        (hasDerivWithinAt_iff_tendsto_slope.mp hs))
+  apply hi.congr'
+  filter_upwards [hG.filter_mono hle] with r hr
+  simp only [slope, smul_eq_mul, Pi.sub_apply, vsub_eq_sub,
+    integral_const_mul, integral_sub hr hGt]
+
+/-- The primitive of a continuous function has the expected derivative at both endpoints. -/
+theorem hasDerivWithinAt_integral_Icc {g : ℝ → ℝ} {T t : ℝ}
+    (ht : t ∈ Icc 0 T) (hg : ContinuousOn g (Icc 0 T)) :
+    HasDerivWithinAt (fun r => ∫ s in (0 : ℝ)..r, g s) (g t) (Icc 0 T) t := by
+  let c : ℝ → ℝ := fun r => max 0 (min T r)
+  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
+  have hcm (r : ℝ) : c r ∈ Icc 0 T :=
+    ⟨le_max_left _ _, max_le (ht.1.trans ht.2) (min_le_left _ _)⟩
+  have hce (r : ℝ) (hr : r ∈ Icc 0 T) : c r = r := by
+    simp only [c, min_eq_right hr.2, max_eq_right hr.1]
+  have hg' : Continuous (fun r => g (c r)) := hg.comp_continuous hc hcm
+  have hd := intervalIntegral.integral_hasDerivAt_right (hg'.intervalIntegrable 0 t)
+    hg'.aestronglyMeasurable.stronglyMeasurableAtFilter hg'.continuousAt
+  rw [hce t ht] at hd
+  apply hd.hasDerivWithinAt.congr_of_mem _ ht
+  intro r hr
+  apply intervalIntegral.integral_congr
+  intro s hs
+  rw [uIcc_of_le hr.1] at hs
+  change g s = g (c s)
+  rw [hce s ⟨hs.1, hs.2.trans hr.2⟩]
+
+/-- Clipping below the diagonal reduces the moving limit to dominated secants on a fixed interval. -/
+theorem hasDerivWithinAt_integral_moving_limit_of_secants
+    {F D : ℝ → ℝ → ℝ} {b T t : ℝ} (ht : t ∈ Icc 0 T)
+    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
+      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
+    (hdiag : F t t = b)
+    (hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => F r s) (D t s) t)
+    (hbound : ∃ B : ℝ → ℝ, IntegrableOn B (Ioc 0 T) ∧
+      ∀ᶠ r in 𝓝[Icc 0 T] t, ∀ᵐ s ∂volume.restrict (Ioc 0 T),
+        ‖F (max r s) s - F (max t s) s‖ ≤ B s * ‖r-t‖) :
+    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
+      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
+  let G : ℝ → ℝ → ℝ := fun r s => F (max r s) s - F s s
+  let d : ℝ → ℝ := (Iic t).indicator (D t)
+  have hT : 0 ≤ T := ht.1.trans ht.2
+  have hcdiag : ContinuousOn (fun s => F s s) (Icc 0 T) :=
+    hcont.comp (continuous_id.prodMk continuous_id).continuousOn
+      (fun s hs => ⟨hs, hs, le_rfl⟩)
+  have hcG (r : ℝ) (hr : r ∈ Icc 0 T) : ContinuousOn (G r) (Icc 0 T) :=
+    (hcont.comp ((continuous_const.max continuous_id).prodMk continuous_id).continuousOn
+      (fun s hs => ⟨hs, ⟨hr.1.trans (le_max_left _ _), max_le hr.2 hs.2⟩,
+        le_max_right _ _⟩)).sub hcdiag
+  have hiG (r : ℝ) (hr : r ∈ Icc 0 T) : IntegrableOn (G r) (Ioc 0 T) :=
+    (hcG r hr).integrableOn_Icc.mono_set Ioc_subset_Icc_self
+  obtain ⟨B, hB, hb⟩ := hbound
+  have hdG : HasDerivWithinAt (fun r => ∫ s in Ioc 0 T, G r s)
+      (∫ s in Ioc 0 T, d s) (Icc 0 T) t := by
+    apply hasDerivWithinAt_integral_of_dominated_secants
+      (B := B) (Eventually.mono self_mem_nhdsWithin hiG) (hiG t ht) hB
+    · filter_upwards [hb] with r hr
+      filter_upwards [hr] with s hs
+      simpa only [G, sub_sub_sub_cancel_right] using hs
+    · filter_upwards [ae_restrict_mem measurableSet_Ioc,
+        (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
+      by_cases hlt : s < t
+      · have hd := (hderiv s ⟨hs.1, hlt⟩).sub_const (F s s)
+        have he : (G · s) =ᶠ[𝓝 t] (fun r => F r s - F s s) := by
+          filter_upwards [Ioi_mem_nhds hlt] with r hr
+          simp only [G, max_eq_left (le_of_lt (show s < r from hr))]
+        have hd' := hd.congr_of_eventuallyEq he
+        simpa only [d, indicator_of_mem (show s ∈ Iic t from hlt.le)] using
+          hd'.hasDerivWithinAt (s := Icc 0 T)
+      · have hgt : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
+        have he : (G · s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
+          filter_upwards [Iio_mem_nhds hgt] with r hr
+          simp only [G, max_eq_right (le_of_lt (show r < s from hr)), sub_self]
+        have hd' := (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
+        simpa only [d, indicator_of_notMem (show s ∉ Iic t from not_le.mpr hgt)] using
+          hd'.hasDerivWithinAt (s := Icc 0 T)
+  have hdint : (∫ s in Ioc 0 T, d s) = ∫ s in (0 : ℝ)..t, D t s := by
+    rw [← intervalIntegral.integral_of_le hT]
+    exact intervalIntegral.integral_indicator (f := D t) ht
+  rw [hdint] at hdG
+  have hde := hdG.add (hasDerivWithinAt_integral_Icc ht hcdiag)
+  rw [hdiag, add_comm (∫ s in (0 : ℝ)..t, D t s) b] at hde
+  apply hde.congr_of_mem _ ht
+  intro r hr
+  have he : G r = (Iic r).indicator (fun s => F r s - F s s) := by
+    funext s
+    by_cases hs : s ≤ r
+    · simp only [G, indicator_of_mem (show s ∈ Iic r from hs), max_eq_left hs]
+    · simp only [G, indicator_of_notMem (show s ∉ Iic r from hs), max_eq_right (le_of_not_ge hs), sub_self]
+  change (∫ s in (0 : ℝ)..r, F r s) =
+    (∫ s in Ioc 0 T, G r s) + ∫ s in (0 : ℝ)..r, F s s
+  rw [← intervalIntegral.integral_of_le hT, he]
+  have hcut : (∫ s in (0 : ℝ)..T, (Iic r).indicator (fun s => F r s - F s s) s) =
+      ∫ s in (0 : ℝ)..r, F r s - F s s :=
+    intervalIntegral.integral_indicator hr
+  rw [hcut]
+  have hcF : ContinuousOn (F r) (Icc 0 r) :=
+    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
+      (fun s hs => ⟨⟨hs.1, hs.2.trans hr.2⟩, hr, hs.2⟩)
+  rw [intervalIntegral.integral_sub (hcF.intervalIntegrable_of_Icc hr.1)
+    ((hcdiag.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1)]
+  ring
+
+/-- An interior derivative comparison controls increments even at singular endpoints. -/
+theorem abs_sub_le_of_deriv_comparison
+    {g g' v v' : ℝ → ℝ} {a z : ℝ} (haz : a ≤ z)
+    (hg : ContinuousOn g (Icc a z)) (hv : ContinuousOn v (Icc a z))
+    (hdg : ∀ r ∈ Ioo a z, HasDerivAt g (g' r) r)
+    (hdv : ∀ r ∈ Ioo a z, HasDerivAt v (v' r) r)
+    (hb : ∀ r ∈ Ioo a z, |g' r| ≤ v' r) :
+    |g z - g a| ≤ v z - v a := by
+  have hm : MonotoneOn (fun r => v r - g r) (Icc a z) := by
+    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.sub hg)
+    · intro r hr
+      rw [interior_Icc] at hr
+      exact ((hdv r hr).sub (hdg r hr)).differentiableAt.differentiableWithinAt
+    · intro r hr
+      rw [interior_Icc] at hr
+      change 0 ≤ deriv (v - g) r
+      rw [((hdv r hr).sub (hdg r hr)).deriv]
+      exact sub_nonneg.mpr ((le_abs_self _).trans (hb r hr))
+  have hp : MonotoneOn (fun r => v r + g r) (Icc a z) := by
+    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hv.add hg)
+    · intro r hr
+      rw [interior_Icc] at hr
+      exact ((hdv r hr).add (hdg r hr)).differentiableAt.differentiableWithinAt
+    · intro r hr
+      rw [interior_Icc] at hr
+      change 0 ≤ deriv (v + g) r
+      rw [((hdv r hr).add (hdg r hr)).deriv]
+      have := (abs_le.mp (hb r hr)).1
+      linarith
+  have h1 := hm (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
+  have h2 := hp (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz) haz
+  exact abs_le.mpr ⟨by dsimp at h2; linarith, by dsimp at h1; linarith⟩
+
+/-- Integrating a singular power bound requires no derivative at the initial endpoint. -/
+theorem abs_sub_le_rpow_of_deriv_bound
+    {g g' : ℝ → ℝ} {s T u v C β : ℝ} (hβ : 0 < β)
+    (hc : ContinuousOn g (Icc s T))
+    (hd : ∀ r ∈ Ioc s T, HasDerivAt g (g' r) r)
+    (hb : ∀ r ∈ Ioc s T, |g' r| ≤ C * (r-s) ^ (β-1))
+    (hsu : s ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
+    |g v - g u| ≤ (C / β) * ((v-s)^β - (u-s)^β) := by
+  have hdv (r : ℝ) (hr : r ∈ Ioo u v) :
+      HasDerivAt (fun r : ℝ => (C / β) * (r-s)^β) (C * (r-s)^(β-1)) r := by
+    have hp := (((hasDerivAt_id r).sub_const s).rpow_const (p := β)
+      (Or.inl (ne_of_gt (sub_pos.mpr (hsu.trans_lt hr.1))))).const_mul (C / β)
+    simp only [id_eq] at hp
+    convert hp using 1
+    field_simp [hβ.ne']
+  have hi := abs_sub_le_of_deriv_comparison huv
+    (hc.mono (Icc_subset_Icc hsu hvT))
+    (continuousOn_const.mul ((continuous_id.sub continuous_const).continuousOn.rpow_const
+      (fun _ _ => Or.inr hβ.le)))
+    (fun r hr => hd r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
+    hdv (fun r hr => hb r ⟨hsu.trans_lt hr.1, hr.2.le.trans hvT⟩)
+  change |g v - g u| ≤ (C / β) * (v-s)^β - (C / β) * (u-s)^β at hi
+  nlinarith [hi]
+
+/-- A fractional power has an integrable secant bound measured from a positive base point. -/
+theorem abs_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
+    (hx : 0 ≤ x) (hy : 0 < y) :
+    |x^β - y^β| ≤ y^(β-1) * |x-y| := by
+  have hyid : y^β = y * y^(β-1) := by
+    rw [Real.rpow_sub_one hy.ne']
+    field_simp
+  rcases eq_or_lt_of_le hx with hx0 | hx0
+  · subst x
+    rw [Real.zero_rpow hβ.ne', zero_sub, abs_neg,
+      abs_of_nonneg (Real.rpow_nonneg hy.le _), zero_sub, abs_neg, abs_of_pos hy, hyid]
+    exact le_of_eq (mul_comm _ _)
+  have hxid : x^β = x * x^(β-1) := by
+    rw [Real.rpow_sub_one hx0.ne']
+    field_simp
+  rcases le_total x y with hxy | hyx
+  · have hp := Real.rpow_le_rpow hx hxy hβ.le
+    have hq := Real.rpow_le_rpow_of_nonpos hx0 hxy (sub_nonpos.mpr hβ1)
+    rw [abs_of_nonpos (sub_nonpos.mpr hp), abs_of_nonpos (sub_nonpos.mpr hxy)]
+    have hm := mul_le_mul_of_nonneg_left hq hx
+    rw [hxid, hyid]
+    nlinarith [hm]
+  · have hp := Real.rpow_le_rpow hy.le hyx hβ.le
+    have hq := Real.rpow_le_rpow_of_nonpos hy hyx (sub_nonpos.mpr hβ1)
+    rw [abs_of_nonneg (sub_nonneg.mpr hp), abs_of_nonneg (sub_nonneg.mpr hyx)]
+    have hm := mul_le_mul_of_nonneg_left hq hx
+    rw [hxid, hyid]
+    nlinarith [hm]
+
+/-- The same bound survives clipping at zero, from either side of the base point. -/
+theorem abs_clipped_rpow_sub_le {β x y : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
+    (hy : y ≠ 0) :
+    |(max x 0)^β - (max y 0)^β| ≤ |y|^(β-1) * |x-y| := by
+  have hb : 0 ≤ |y|^(β-1) := Real.rpow_nonneg (abs_nonneg _) _
+  rcases lt_or_gt_of_ne hy with hyneg | hypos
+  · rw [max_eq_right hyneg.le, Real.zero_rpow hβ.ne', sub_zero,
+      abs_of_nonneg (Real.rpow_nonneg (le_max_right x 0) _), abs_of_neg hyneg]
+    by_cases hx : x ≤ 0
+    · simp only [max_eq_right hx, Real.zero_rpow hβ.ne']
+      exact mul_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) _) (abs_nonneg _)
+    have hxpos : 0 < x := lt_of_not_ge hx
+    rw [max_eq_left hxpos.le, abs_of_pos (sub_pos.mpr (hyneg.trans hxpos))]
+    rcases le_total x (-y) with hxy | hyx
+    · have hp := Real.rpow_le_rpow hxpos.le hxy hβ.le
+      have he : (-y)^β = (-y) * (-y)^(β-1) := by
+        rw [Real.rpow_sub_one (neg_ne_zero.mpr hy)]
+        field_simp
+      rw [he] at hp
+      have hq := mul_nonneg hxpos.le (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
+      nlinarith
+    · have hp := Real.rpow_le_rpow_of_nonpos (neg_pos.mpr hyneg) hyx (sub_nonpos.mpr hβ1)
+      have he : x^β = x * x^(β-1) := by
+        rw [Real.rpow_sub_one hxpos.ne']
+        field_simp
+      rw [he]
+      have hq := mul_le_mul_of_nonneg_left hp hxpos.le
+      have hz := mul_nonneg (neg_nonneg.mpr hyneg.le)
+        (Real.rpow_nonneg (neg_nonneg.mpr hyneg.le) (β-1))
+      nlinarith
+  · rw [max_eq_left hypos.le, abs_of_pos hypos]
+    have hh := abs_rpow_sub_le hβ hβ1 (le_max_right x 0) hypos
+    apply hh.trans
+    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hypos.le _)
+    by_cases hx : 0 ≤ x
+    · rw [max_eq_left hx]
+    · have hx' : x < 0 := lt_of_not_ge hx
+      rw [max_eq_right hx'.le, zero_sub, abs_neg, abs_of_pos hypos,
+        abs_of_neg (sub_neg.mpr (hx'.trans hypos))]
+      linarith
+
+/-- The singularity of the secant majorant is integrable on either side of its base point. -/
+theorem intervalIntegrable_abs_sub_rpow {β T t : ℝ}
+    (hβ : 0 < β) (ht : t ∈ Icc 0 T) :
+    IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 T := by
+  have hl : IntervalIntegrable (fun s : ℝ => (t-s)^(β-1)) volume 0 t := by
+    simpa only [sub_zero, sub_self] using
+      ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
+        (r := β-1) (by linarith)).comp_sub_left t).symm
+  have hr : IntervalIntegrable (fun s : ℝ => (s-t)^(β-1)) volume t T := by
+    simpa only [zero_add, sub_add_cancel] using
+      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := T-t)
+        (r := β-1) (by linarith)).comp_sub_right t
+  have hl' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume 0 t := by
+    apply hl.congr
+    intro s hs
+    rw [uIoc_of_le ht.1] at hs
+    simp only [abs_of_nonneg (sub_nonneg.mpr hs.2)]
+  have hr' : IntervalIntegrable (fun s : ℝ => |t-s|^(β-1)) volume t T := by
+    apply hr.congr
+    intro s hs
+    rw [uIoc_of_le ht.2] at hs
+    simp only [abs_of_nonpos (sub_nonpos.mpr hs.1.le), neg_sub]
+  exact hl'.trans hr'
+
+/-- A power bound for the derivative supplies a common majorant for clipped secants. -/
+theorem clipped_secant_le_of_deriv_rpow_bound
+    {g g' : ℝ → ℝ} {s T r t C β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
+    (hC : 0 ≤ C) (hs : s ≤ T) (hr : r ≤ T) (ht : t ≤ T) (hst : t ≠ s)
+    (hc : ContinuousOn g (Icc s T))
+    (hd : ∀ z ∈ Ioc s T, HasDerivAt g (g' z) z)
+    (hb : ∀ z ∈ Ioc s T, |g' z| ≤ C * (z-s)^(β-1)) :
+    |g (max r s) - g (max t s)| ≤ (C / β) * |t-s|^(β-1) * |r-t| := by
+  have hCβ : 0 ≤ C / β := div_nonneg hC hβ.le
+  have hinc (a b : ℝ) (ha : a ∈ Icc s T) (hb' : b ∈ Icc s T) :
+      |g a - g b| ≤ (C / β) * |(a-s)^β - (b-s)^β| := by
+    rcases le_total a b with hab | hba
+    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr ha.1) (sub_le_sub_right hab s) hβ.le
+      rw [abs_sub_comm (g a) (g b), abs_sub_comm ((a-s)^β) ((b-s)^β),
+        abs_of_nonneg (sub_nonneg.mpr hp)]
+      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb ha.1 hab hb'.2
+    · have hp := Real.rpow_le_rpow (sub_nonneg.mpr hb'.1) (sub_le_sub_right hba s) hβ.le
+      rw [abs_of_nonneg (sub_nonneg.mpr hp)]
+      exact abs_sub_le_rpow_of_deriv_bound hβ hc hd hb hb'.1 hba ha.2
+  have hi := hinc (max r s) (max t s)
+    ⟨le_max_right _ _, max_le hr hs⟩ ⟨le_max_right _ _, max_le ht hs⟩
+  have hp := abs_clipped_rpow_sub_le (x := r-s) (y := t-s) hβ hβ1
+    (sub_ne_zero.mpr hst)
+  have he (z : ℝ) : max z s - s = max (z-s) 0 := by
+    rw [← max_sub_sub_right, sub_self]
+  rw [he r, he t] at hi
+  have he' : r-s-(t-s) = r-t := by ring
+  rw [he'] at hp
+  exact hi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hCβ)
+
+/-- The Leibniz rule on a closed time interval under an integrable diagonal power singularity. -/
+theorem hasDerivWithinAt_integral_moving_limit
+    {F D : ℝ → ℝ → ℝ} {b T t C β : ℝ} (ht : t ∈ Icc 0 T)
+    (hβ : 0 < β) (hβ1 : β ≤ 1) (hC : 0 ≤ C)
+    (hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
+      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1})
+    (hdiag : F t t = b)
+    (hderiv : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
+      HasDerivAt (fun ρ => F ρ s) (D r s) r)
+    (hbound : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T, |D r s| ≤ C * (r-s)^(β-1)) :
+    HasDerivWithinAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, F r s)
+      (b + ∫ s in (0 : ℝ)..t, D t s) (Icc 0 T) t := by
+  apply hasDerivWithinAt_integral_moving_limit_of_secants ht hcont hdiag
+    (fun s hs => hderiv s ⟨hs.1.le, hs.2.le.trans ht.2⟩ t ⟨hs.2, ht.2⟩)
+  refine ⟨fun s => (C / β) * |t-s|^(β-1), ?_, ?_⟩
+  · exact ((intervalIntegrable_abs_sub_rpow hβ ht).const_mul (C / β)).1
+  · filter_upwards [self_mem_nhdsWithin] with r hr
+    filter_upwards [ae_restrict_mem measurableSet_Ioc,
+      (volume.restrict (Ioc 0 T)).ae_ne t] with s hs hst
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
+    have hc : ContinuousOn (fun r => F r s) (Icc s T) :=
+      hcont.comp (continuous_id.prodMk continuous_const).continuousOn
+        (fun z hz => ⟨hsT, ⟨hs.1.le.trans hz.1, hz.2⟩, hz.1⟩)
+    simpa only [Real.norm_eq_abs] using
+      clipped_secant_le_of_deriv_rpow_bound hβ hβ1 hC hs.2 hr.2 ht.2 hst.symm
+        hc (hderiv s hsT) (hbound s hsT)
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+open HeatDuhamelHeatEquation
+
+/-- The existing Hessian estimate supplies the scalar time-derivative majorant. -/
+theorem exists_heat_integrand_deriv_bound {α T M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E, |f (s, x) - f (s, y)| ≤ K * ‖x-y‖^α)
+    (x : E) :
+    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
+      |deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r| ≤
+        C * (r-s)^(α/2-1) := by
+  obtain ⟨A, hA, hAb⟩ :=
+    HeatDuhamelSpatialHolderHessian.exists_heat_hessian_holder_bound hα hα1
+  refine ⟨3 * A * K, by positivity, ?_⟩
+  intro s hs r hr
+  have hc : Continuous (fun y : E => f (s,y)) :=
+    hf.comp_continuous (continuous_const.prodMk continuous_id)
+      (fun y => ⟨hs, mem_univ y⟩)
+  have hH := hAb (sub_pos.mpr hr.1) hK0 hc.aestronglyMeasurable
+    (by simpa only [Real.norm_eq_abs] using hM s hs) (hK s hs) x
+  rw [(hasDerivAt_heat_integrand hs hr.1 hf hM x).deriv, laplacian_eq_hessian_trace]
+  calc
+    |∑ i : Fin 3, fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
+      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)| ≤
+      ∑ i : Fin 3, ‖fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
+        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ :=
+      by
+        simpa only [Real.norm_eq_abs] using
+          (norm_sum_le Finset.univ (fun i : Fin 3 =>
+            fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x
+              (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)))
+    _ ≤ ∑ _i : Fin 3, A * K * (r-s)^(α/2-1) := by
+      apply Finset.sum_le_sum
+      intro i _
+      apply le_trans _ hH
+      simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
+        ContinuousLinearMap.le_opNorm₂
+          (fderiv ℝ (fderiv ℝ (heatSolution (r-s) (fun y => f (s,y)))) x)
+          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i)
+    _ = (3 * A * K) * (r-s)^(α/2-1) := by simp; ring
+
+/-- The Duhamel solution satisfies the frozen inhomogeneous heat equation. -/
+theorem duhamel_solves_heat_equation :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  (∀ x : E, u 0 x = 0) ∧
+  ∀ t ∈ Icc 0 T, ∀ x : E,
+    HasDerivWithinAt (fun r : ℝ => u r x)
+      (f (t, x) + ∑ i : Fin 3, fderiv ℝ (fderiv ℝ (u t)) x
+        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i))
+      (Icc 0 T) t := by
+  intro α hα hα1 T hT hT1 f M K hM0 hK0 hf hM hK
+  dsimp only
+  refine ⟨fun x => duhamel_zero f x, ?_⟩
+  intro t ht x
+  rw [← laplacian_eq_hessian_trace]
+  rw [← (duhamel_time_derivative_integral hα hα1 ht hf hM hK x).2]
+  let F : ℝ → ℝ → ℝ := fun r s => if r-s = 0 then f (s,x)
+    else heatSolution (r-s) (fun y => f (s,y)) x
+  have hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
+      {p : ℝ × ℝ | p.2 ∈ Icc 0 T ∧ p.1 ∈ Icc 0 T ∧ p.2 ≤ p.1} :=
+    (continuousOn_heat_integrand_extension hf hM x).comp
+      ((continuous_fst.sub continuous_snd).prodMk continuous_snd).continuousOn
+      (fun p hp => ⟨sub_nonneg.mpr hp.2.2, hp.1⟩)
+  have hd : ∀ s ∈ Icc 0 T, ∀ r ∈ Ioc s T,
+      HasDerivAt (fun ρ => F ρ s)
+        (deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r) r := by
+    intro s hs r hr
+    have hd0 := (hasDerivAt_heat_integrand hs hr.1 hf hM x).differentiableAt.hasDerivAt
+    apply hd0.congr_of_eventuallyEq
+    filter_upwards [Ioi_mem_nhds hr.1] with ρ hρ
+    simp only [F, if_neg (ne_of_gt (sub_pos.mpr (show s < ρ from hρ)))]
+  obtain ⟨C, hC, hCb⟩ := exists_heat_integrand_deriv_bound hα hα1 hK0 hf hM hK x
+  have hsolve := hasDerivWithinAt_integral_moving_limit
+    (F := F) (b := f (t,x))
+    (D := fun r s => deriv (fun ρ => heatSolution (ρ-s) (fun y => f (s,y)) x) r)
+    ht (β := α / 2) (by linarith) (by linarith) hC hc (by simp only [F, sub_self, if_true]) hd hCb
+  apply hsolve.congr_of_mem _ ht
+  intro r hr
+  apply intervalIntegral.integral_congr_ae_restrict
+  rw [uIoc_of_le hr.1, ← restrict_Ioo_eq_restrict_Ioc]
+  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+  simp only [F, if_neg (ne_of_gt (sub_pos.mpr hs.2))]
+
+end Poincare.MovingLimitLeibniz

```
