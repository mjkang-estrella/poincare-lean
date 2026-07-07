# M5-glob-12 blocked report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/KoszulNaturality.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.quadratic_euclidean_transition_sign_pin
```

## Pin outcome

The sign is pinned by a local one-dimensional Euclidean coordinate-change
calculation:

```text
sigma z = z + z^2,   v = 1,   source Gamma(v,v) = 0.
```

At `0`, Lean proves:

```text
D sigma_0 = 1
B = d/ds (D sigma(s) v)|_0 = 2
target Gamma(D sigma v, D sigma v) = -2
```

Therefore the compatible transition identity under this repo's convention
`geodesicFlowField Gamma p = (p.2, -Gamma p.1 p.2 p.2)` is:

```text
target Gamma(D sigma v, D sigma v)
  = D sigma_0 (source Gamma(v,v)) - B
```

The theorem also proves the plus-sign variant is false in this pin:

```text
target Gamma(D sigma v, D sigma v)
  != D sigma_0 (source Gamma(v,v)) + B
```

So the M5-glob-11 sign analysis is confirmed: the ordinary second-derivative
chain-rule correction must enter the Christoffel transition with a minus sign.

## Remaining blockers

The full producer chain is still blocked by missing exported transition inputs.

1. The proved metric transport theorem currently exports
   `chartMetric_chartTransitionMFDeriv`, using `chartTransitionMFDeriv`.
   The geodesic state and M5-glob-11 bridge use
   `chartTransitionDeriv = fderiv chartTransition`. I did not find an exported
   theorem identifying these derivatives on chart overlaps.

2. `LeviCivitaUniqueness.lean` gives pointwise/value uniqueness of
   metric-compatible torsion-free connections. The repo also has local
   transported-value agreement in `LeviCivitaTransport.lean`, but I did not
   find an exported theorem packaging the sigma-transported source Christoffel
   field as metric-compatible and torsion-free for the target chart metric, nor
   the resulting abstract Christoffel transition identity.

3. The second-order chain-rule input for
   `d/ds (chartTransitionDeriv x0 y0 (gamma s).1 (gamma s).2)` with the
   ordinary `D^2 sigma(v,v)` correction is not exported in the shape consumed by
   `ChristoffelTransition.lean`.

Because the worker contract forbids `sorry` and vacuous wrappers, I stopped at
the verified sign pin rather than adding assumed producer hypotheses.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/KoszulNaturality.lean
git diff --check -- Poincare/Global/KoszulNaturality.lean
lake build Poincare.Global.KoszulNaturality
```

Actual result:

```text
rg: no matches
git diff --check: no output
lake build Poincare.Global.KoszulNaturality
✔ [2832/2832] Built Poincare.Global.KoszulNaturality (1.0s)
Build completed successfully (2832 jobs).
```

The build replayed pre-existing imported-module warnings; the new module
itself built successfully and introduced no reported warning.
