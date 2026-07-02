# M3-predicates-29 progress report

## Summed flat-torus sanity check

The two previous pointwise intermediates fail on the flat two-torus with
standard parallel frame and metric variation

```text
h_11 = cos y,   all other h_ij = 0.
```

At `y = 0`, the divergence-order pointwise trace for `u = w = e_1` is

```text
Σ_i ∂_i δΓ^i_11 = 1/2,
```

while the false pointwise inner-trace derivative is `0`.  The fully summed
target instead takes the raised trace over the lower slots:

```text
Σ_j Σ_i ∂_i δΓ^i_jj.
```

The only nonzero contribution is still the `j = 1, i = 2` term:

```text
Σ_j Σ_i ∂_i δΓ^i_jj = ∂_2 δΓ^2_11 = 1/2.
```

The right side of the intended keystone is

```text
div div h - 1/2 Δ(tr h).
```

For this variation,

```text
div div h = ∂_1∂_1 h_11 = 0,
tr h = cos y,
Δ(tr h) = ∂_2∂_2 cos y = -1 at y = 0,
```

so

```text
div div h - 1/2 Δ(tr h) = 0 - 1/2(-1) = 1/2.
```

Thus the double trace repairs the false pointwise identity and matches the
model keystone shape.

## Current proof status

The pointwise false route was bypassed.  In
`Poincare/Global/ScalarVariation.lean`, the following verified proof-bearing
pieces were added:

- `covDeltaGamma_koszul_secondDerivAt`: one summand of
  `covDeltaGamma_koszul` collapses to the pure three-term
  `covTensor2SecondDerivAt` expression after substituting first-order
  `deltaGamma_koszul` into the three connection-correction terms.
- `deltaGammaDivergenceTrace_sndDerivAt`: the full double trace of
  `deltaGammaDivergenceAt` is now expressed as the closed analogue of the
  model's `deltaGammaDivergenceTrace_sndDeriv`.
- `deltaGammaDivergenceTraceSecondDerivPositiveBlockAt` and
  `deltaGammaDivergenceTraceSecondDerivTraceBlockAt`: named numeric blocks for
  the `(T1 + T2)` and `T3` double traces.
- `deltaGammaDivergenceTrace_sndDerivAt_blocks`: the summed trace is split as
  positive block minus `1/2` times the trace block.
- `deltaGammaDivergenceTraceHessianAssemblyAt_of_sndDeriv_groups`: the frozen
  `DeltaGammaDivergenceTraceHessianAssemblyAt` follows from the two exact group
  evaluations.

The remaining unproved analytic content is exactly the two model sub-identities
in closed form:

```lean
deltaGammaDivergenceTraceSecondDerivPositiveBlockAt
  (gt t₀) (timeDerivAt gt t₀) x
= tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
```

and

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

I stopped here rather than introducing a fake closed proof of those two
second-order trace-commute/group-evaluation identities.
