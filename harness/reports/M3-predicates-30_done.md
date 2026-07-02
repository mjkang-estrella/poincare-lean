# M3-predicates-30 done report

## Result

The trace block `T3` is now proved in
`Poincare/Global/ScalarVariation.lean`.

New proof-bearing theorems:

- `covTensor2SecondDerivAt_timeDeriv_Hslot_trace_eq_hessianAt`
- `deltaGammaDivergenceTraceSecondDerivTraceBlockAt_eq_sum_hessianAt`
- `deltaGammaDivergenceTraceHessianAssemblyAt_of_positiveBlock`

The fixed-pair lemma packages
`K_y(p,q) = covTensor2DerivAt g H y (extend E w y) p q`, applies the already
proved first-order trace commute to `K`, applies the same first-order trace
commute to `H` for the derivative-direction correction, and then converts the
outer derivative of `d(tr h)` to `g.hessianAt (traceMetricVariationAt g H)` via
`extDerivFun_extDerivFun_extend_eq_hessianAt_add`.

The trace-block theorem sums the fixed-pair lemma after swapping the finite
sum order, proving the frozen RHS shape:

```lean
deltaGammaDivergenceTraceSecondDerivTraceBlockAt
  (gt t₀) (timeDerivAt gt t₀) x
=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun j ↦ metricDualVectorAt g x (b.coord j)
  ∑ j, g.hessianAt f x (b j) (sharp j)
```

The new assembly wrapper consumes this trace-block theorem, so the divergence
Hessian assembly now waits only on the positive `(T1 + T2)` block, plus the
explicit regularity hypotheses used by the trace-block proof.

## Sanity check

The flat two-torus pattern from `M3-predicates-29_blocked.md` remains
consistent.  For `h₁₁ = cos y` at `y = 0`, the trace block is the Hessian trace
of `tr h = cos y`, hence evaluates to `-1`; the split contributes
`-1/2 * T3 = 1/2`, matching the repaired summed keystone sanity check.

## Verification

Commands run:

```bash
rg -n '\b(sorry|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean
lake env lean Poincare/Global/ScalarVariation.lean
lake build Poincare.Global.ScalarVariation
```

Results:

- no `sorry`, `axiom`, or `native_decide` matches in the edited file;
- focused Lean check succeeds;
- `lake build Poincare.Global.ScalarVariation` succeeds (`Built ...`, 82s),
  with only existing linter warnings.
