# M3-predicates-28 blocked report

## Status

I did not change the frozen statement
`DeltaGammaInnerTraceFieldCovariantDerivativeAt`, and I did not try to prove
it.  The requested sanity check shows that this frozen pointwise statement is
also false for the same flat-torus pattern that killed the cyclic identity in
`M3-predicates-27`.

The valid corrected route is still the direct divergence-trace route through
`covDeltaGamma_koszul`, but it must target the summed trace assembly directly,
not the pointwise inner-trace field derivative predicate.

## Frozen statement checked

The frozen predicate says, for all `u w : TM x`,

```lean
deltaGammaDivergenceAt gt t₀ x w u =
  (extDerivFun
      (fun y : M ↦ tensorDivergenceOneFormAt g H y (extend E w y))
      x u
    - tensorDivergenceOneFormAt g H x
      (g.leviCivita (extend E w) x u))
  - (1 / 2 : ℝ) * g.hessianAt f x w u
```

where `g = gt t₀`, `H = timeDerivAt gt t₀`, and
`f y = traceMetricVariationAt g H y`.

In a flat parallel frame this is the claim

```text
Σ_i ∂_i δΓ^i_{wu}
  =
∂_u((div h)_w) - 1/2 ∂_w∂_u tr(h).
```

The left side is the divergence-order trace.  The right side is the derivative
of the lower-slot inner trace formula `div h - 1/2 d tr(h)`.

## Static flat check

If the variation is static, `H = 0`.  Then `δΓ = 0`,
`covDeltaGammaDerivAt = 0`, `tensorDivergenceOneFormAt H = 0`, and
`traceMetricVariationAt g H = 0`.  Both sides of the frozen statement are zero.

This check passes, but it is only the zero-variation sanity case.

## Flat torus counterexample

Work on a flat 2-torus with coordinates `(x, y)` and the standard parallel
orthonormal frame.  Let the metric variation have only

```text
h_11 = cos y
```

nonzero, and evaluate at `y = 0` with `u = w = e_1`.

The linearized Christoffel tensor is

```text
δΓ^k_ij = 1/2 (∂_i h_jk + ∂_j h_ik - ∂_k h_ij).
```

Thus

```text
δΓ^1_11 = 1/2 ∂_1 h_11 = 0,
δΓ^2_11 = -1/2 ∂_2 h_11 = 1/2 sin y.
```

So the frozen left side is

```text
Σ_i ∂_i δΓ^i_11
  = ∂_1 δΓ^1_11 + ∂_2 δΓ^2_11
  = 0 + 1/2 cos y
  = 1/2
```

at `y = 0`.

The frozen right side is

```text
∂_1((div h)_1) - 1/2 ∂_1∂_1 tr(h).
```

Here `(div h)_1 = ∂_1 h_11 + ∂_2 h_21 = 0` and
`tr(h) = h_11 = cos y`, hence

```text
∂_1((div h)_1) - 1/2 ∂_1∂_1 tr(h) = 0.
```

The frozen statement therefore gives `1/2 = 0` in this model.

The connection-correction terms in `covDeltaGamma_koszul` vanish in this flat
parallel frame, so they cannot repair the mismatch.

## What `covDeltaGamma_koszul` shows

Substituting `covDeltaGamma_koszul` into the divergence-order trace with slots

```text
u = e_i, v = w, w = u, z = e_i
```

gives, in the same flat notation,

```text
2 Σ_i g((∂_i δΓ)(w,u), e_i)
  =
Σ_i ∂_i∂_w h_ui
  + Σ_i ∂_i∂_u h_wi
  - Σ_i ∂_i∂_i h_wu.
```

So

```text
Σ_i g((∂_i δΓ)(w,u), e_i)
  =
1/2 ∂_w((div h)_u)
  + 1/2 ∂_u((div h)_w)
  - 1/2 Δ h_wu.
```

This is not the frozen pointwise inner-trace derivative

```text
∂_u((div h)_w) - 1/2 ∂_w∂_u tr(h).
```

After taking the raised metric trace over `w = e_j`, `u = e_j`, however, the
correct expression becomes

```text
Σ_j Σ_i g((∂_i δΓ)(e_j,e_j), e_i)
  =
div div h - 1/2 Δ tr(h).
```

This is exactly the intended divergence assembly shape.

## Corrected adapter chain

Do not use
`deltaGammaDivergenceAt_eq_innerTraceFieldDerivative_of_entryBridge` and do not
try to discharge `DeltaGammaInnerTraceFieldCovariantDerivativeAt`.

The corrected chain should prove the summed divergence statement directly:

1. Expand
   `Σ_j deltaGammaDivergenceAt gt t₀ x (b j) (sharp j)` using
   `deltaGammaDivergenceAt_eq_inner_sum`.
2. Apply `covDeltaGamma_koszul` with slots
   `u = b i`, `v = b j`, `w = sharp j`, `z = sharp i`, then sum in `i,j`.
3. Identify the two positive second-derivative groups as the double-divergence
   trace, giving `tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x`.
4. Identify the negative second-derivative group as the raised Hessian trace of
   `traceMetricVariationAt`, using the once-differentiated trace-commute
   analogue of the already discharged `TraceMetricVariationDerivAt`.
5. Cancel or absorb the first-order `δΓ · Γ` correction terms with the existing
   slot-cancellation machinery.

The best existing target for this route is
`DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x`, followed by
`deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly`.  The existing
`DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x` is a summed
identity and still has the right flat-model value, but its current advertised
derivation through the false pointwise inner-trace predicate should be bypassed.

## Verified remaining predicate list

With the false pointwise predicate retired from the route, the remaining honest
non-regularity frontier is:

- direct `DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x` from
  `covDeltaGamma_koszul`, or equivalently a direct proof of the summed
  `DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x`
- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x`
- `TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x`
- `ClosedContractedBianchiAt (gt t₀) x`

The contraction-side predicate
`DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x` already has the
`..._of_deltaGammaFieldMDifferentiableAt_entries_contMDiffAt` adapter in
`Poincare.Global.ScalarVariation`.

## Verification

Forbidden-token check:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean
```

Result: no matches.

Requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success.  The build completed with existing warnings and ended with:

```text
Build completed successfully (2806 jobs).
```
