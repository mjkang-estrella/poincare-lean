# M5-glob-26 blocked report

## Status

Blocked on the fully instantiated Cartan-map geodesic-preservation theorem, with
verified strict-partial progress in the required new Lean file:

- `Poincare/Global/LCNaturality.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport
  .christoffelAt_map_eq_signed_transport_of_differentiated_pullback
```

It proves the map-generic Levi-Civita uniqueness algebra needed for the Cartan
chart map. Given:

- an invertible differential `D z`,
- symmetry of the second differential correction `(fderiv R D z)`,
- the differentiated metric-pullback identity `hdiff`,
- the pointwise metric pullback identity `hpull`,
- target metric symmetry, and
- nondegenerate bilinear representatives for the source and target metrics,

the target Christoffel corrector is the signed transport of the source
Christoffel corrector:

```lean
CovariantDerivative.christoffelAt G1 (F z) b1 hb1 (D z v) (D z u) =
  D z (CovariantDerivative.christoffelAt G0 z b0 hb0 v u) -
    (fderiv R D z u) v
```

The orientation matches `chartChristoffelField`, whose first slot is the
section-value slot and whose second slot is the direction slot.

## Blocking boundary

The current exported Cartan API is still pointwise at the nonzero normal
coordinate:

```lean
IsometryConsumers.exists_cartanChartMap_ift_partialHomeomorph_on_punctured_ball
```

returns, for each `v`, a single equivalence-valued derivative `D` and a
pointwise pullback identity. The full geodesic-preservation argument needs a
neighborhood-level differential field for `cartanChartMap` together with its
`fderiv` symmetry and a germ pullback identity that can be fed to
`PullbackDifferentiate.differentiated_pullback_hdiff_of_eventuallyEq`.

Without that exported Cartan `D : E -> E ->L[R] E` field and the corresponding
eventual pullback germ around the point, the new generic LC transport theorem
cannot yet be instantiated to a non-hypothetical Cartan transition law, and the
subsequent geodesic ODE transport/PL uniqueness step remains out of reach.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/LCNaturality.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/LCNaturality.lean
git diff --check -- Poincare/Global/LCNaturality.lean
lake build Poincare.Global.LCNaturality
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
28:theorem christoffelAt_map_eq_signed_transport_of_differentiated_pullback

git diff --check -- Poincare/Global/LCNaturality.lean
exit status 0

lake build Poincare.Global.LCNaturality
Built Poincare.Global.LCNaturality
Build completed successfully (2742 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
