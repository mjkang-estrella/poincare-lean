# M3-predicates-21 blocked report

## Verified progress

This worker added the first proof-bearing part of the requested anchored Gram
route in `Poincare/Global/ScalarVariation.lean`.

New closed first-slot trace infrastructure:

- `deltaGammaFirstSlotEndomorphismAt`
- `deltaGammaFirstSlotTraceFieldAt_eq_linearMap_trace`
- `deltaGammaFirstSlotTraceFieldAt_eq_trace_in_basis`
- `deltaGammaFirstSlotTrace_leviCivita_slot_cancel`
- `deltaGammaFirstSlotTraceFieldAt_eq_sum_gram_inv`

The last theorem is the field-level anchored Gram identity requested in the
task.  For every invertible anchored Gram matrix it rewrites

```lean
deltaGammaFirstSlotTraceFieldAt gt t₀ y w
```

as the `x`-anchored sum

```lean
∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
  g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i) w)
    (gramFrame x y j)
```

using basis invariance of the ordinary trace of the linear endomorphism
`v ↦ deltaGammaAt gt t₀ y v w`.  The trace-cyclicity lemma separately proves
the base-fiber cancellation between the output Levi-Civita action and the
traced input action by reducing both sides to
`LinearMap.trace ℝ (TM x) (Γ ∘ Δ) = LinearMap.trace ℝ (TM x) (Δ ∘ Γ)`.

## Remaining exact obligation

The target

```lean
DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x
```

is still blocked by the analytic derivative bridge for the anchored scalar
entries.  After the new anchored identity, differentiating the field at `x`
requires a closed lemma of the following shape:

```lean
extDerivFun
  (fun y : M =>
    (gt t₀).inner y
      (deltaGammaAt gt t₀ y (extend E p y) (extend E w y))
      (extend E q y)) x u
=
  (gt t₀).inner x (covDeltaGammaDerivAt gt t₀ x u p w) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x ((gt t₀).leviCivita (extend E p) x u) w) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x p ((gt t₀).leviCivita (extend E w) x u)) q
  + (gt t₀).inner x
      (deltaGammaAt gt t₀ x p w)
      ((gt t₀).leviCivita (extend E q) x u)
```

That lemma is the closed analogue of the model `fderiv`-of-bundled-`δΓ` trace
step.  It is not currently available in the closed file: `MetricFlowRegularAt`
defines `covDeltaGammaDerivAt` and gives time-differentiability of the
connection values, but it does not provide an `MDifferentiableAt`/metric
compatibility bridge for the spatial field

```lean
fun y =>
  deltaGammaAt gt t₀ y (extend E p y) (extend E w y)
```

needed to differentiate the scalar pairing above.

Once that scalar-entry derivative bridge exists, the rest of the planned route
is now set up:

1. rewrite the moving field by
   `deltaGammaFirstSlotTraceFieldAt_eq_sum_gram_inv`,
2. differentiate products and inverse Gram entries using the existing
   `gramMatrix_inv_extDerivFun_eq_neg_sum`,
3. cancel the Levi-Civita input/output corrections using
   `deltaGammaFirstSlotTrace_leviCivita_slot_cancel` plus the existing Gram
   cancellation machinery,
4. identify the remaining fixed-base sum with
   `deltaGammaContractionDerivAt gt t₀ x u w`.

## Verification

Focused check:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with pre-existing linter warnings.

Forbidden placeholders:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/ScalarVariation.lean \
  Poincare/Global/ScalarEvolution.lean
```

Result: no matches.

Diff hygiene:

```bash
git diff --check
```

Result: success.

Exact requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, with pre-existing linter warnings.
