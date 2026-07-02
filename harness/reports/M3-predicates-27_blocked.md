# M3-predicates-27 blocked report

## Status

I did not change the frozen cyclic target statement or assert it as a theorem.
After expanding the identity against the closed `covDeltaGamma_koszul` formula,
the requested pointwise cyclic trace identity is not valid for a general metric
variation.

## Frozen cyclic obligation

The remaining obligation from the M3-predicates-24/25 reports is:

```lean
∀ u w : TM x,
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
   let g : ClosedSmoothRiemannianMetric n M := gt t₀
   let b := Module.finBasis ℝ (TM x)
   let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
     fun i ↦ metricDualVectorAt g x (b.coord i)
   ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
  =
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
   let g : ClosedSmoothRiemannianMetric n M := gt t₀
   let b := Module.finBasis ℝ (TM x)
   let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
     fun i ↦ metricDualVectorAt g x (b.coord i)
   ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i))
```

## Counterexample check

At a flat background with a parallel orthonormal frame, the connection
correction terms vanish at the point and `covDeltaGammaDerivAt` is the ordinary
derivative of the linearized Christoffel tensor

```text
δΓ_{kij} = 1/2 (∂ᵢ h_{jk} + ∂ⱼ h_{ik} - ∂ₖ h_{ij}).
```

Take a flat 2-torus with coordinates `(x, y)`, base point `y = 0`, and a smooth
metric variation with only `h₁₁ = cos y` nonzero.  Use `u = w = e₁` and the
standard parallel frame.

Left side:

```text
Σᵢ ∂₁ δΓ_{1ii} = 0,
```

because the variation depends only on `y`.

Right side:

```text
Σᵢ ∂ᵢ δΓ_{i11}
  = ∂₂ δΓ_{211}
  = ∂₂ (-1/2 ∂₂ h₁₁)
  = 1/2
```

at `y = 0`.  Thus the proposed identity gives `0 = 1/2`.

This is not a boundary or noncompactness issue: the example is periodic on the
flat torus, and it is realized by a smooth metric family `g_t = g + t h` for
small `t`.

## Koszul-expansion obstruction

Substituting `covDeltaGamma_koszul` into both sides exposes the same mismatch.
The right side contains the traced second-derivative contribution

```text
-1/2 Σᵢ ∇ᵢ∇ᵢ h(u,w)
```

from the `- covTensor2SecondDerivExpansionAt ...` Koszul slot.  The left side
contains instead the derivative of the inner trace

```text
∇ᵤ(div h)(w) - 1/2 ∇ᵤ∇ᵥ tr(h),
```

after the symmetric trace contraction.  Schwarz swaps commute mixed derivatives,
but they do not turn the Laplacian trace term into the derivative of the inner
trace for arbitrary `h`.

The correction terms are first-order `δΓ · Γ` terms and vanish in the flat
parallel-frame counterexample, so they cannot repair the second-derivative
mismatch.

## Consequence

The cascade requested in this task cannot be closed from this frozen identity:

- `DeltaGammaInnerTraceFieldCovariantDerivativeAt gt t₀ x` cannot honestly be
  derived from the stated cyclic identity.
- Consequently `DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x` and
  the divergence Hessian assembly remain open.

The valid route appears to require a corrected identity with the missing
second-derivative/Laplacian contribution retained, or an additional specialized
hypothesis on the metric variation.  I stopped here per the worker contract
instead of changing the frozen target or adding an unsound theorem.

