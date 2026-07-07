# M5-glob-41 blocked: Cartan C² assembly isolated

## Status

Blocked on the fully non-hypothetical `ContDiffAt ℝ 2 F (eM v)` producer from
the augmented smooth-dependence chain.

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/ContDiffTwo.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.ContDiffTwo
  .cartanChartMap_contDiffAt_two_of_expChart_contDiffAt_two
```

For

```lean
let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
  (g := roundSphereMetric3) p₀
let F := CartanDifferential.cartanChartMap g x₀ p₀ L
```

the theorem proves the chart-composition assembly

```lean
ContDiffAt ℝ 2 F (eM v)
```

from the two chart-side inputs

```lean
ContDiffAt ℝ 2 eM.symm (eM v)
ContDiffAt ℝ 2 eS (L v)
```

and `v ∈ eM.source`.  The proof is the direct non-circular composition
`eS ∘ L ∘ eM.symm`, using `ContDiffAt.comp` and the `C∞` linearity of `L`.

## Blocking boundary

This closes only the final `ContDiffAt 2` assembly step.  The repository still
does not export the required non-hypothetical chart-side regularity facts

```lean
ContDiffAt ℝ 2
  (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀).symm
  (eM v)

ContDiffAt ℝ 2
  (GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) p₀)
  (L v)
```

from the augmented second-variation / smooth-dependence machinery on the
punctured ball.  In particular, the previously exported augmented fixed-time
derivatives remain directional/data-parametric; there is still no
neighborhood-level theorem identifying the resulting second-variation endpoint
CLM as the derivative of the canonical field `q ↦ fderiv ℝ F q`, nor the
corresponding `C¹` derivative-field package needed to derive the two chart C²
facts above without additional hypotheses.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ContDiffTwo.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ContDiffTwo.lean
git diff --check -- Poincare/Global/ContDiffTwo.lean
lake build Poincare.Global.ContDiffTwo
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
42:theorem cartanChartMap_contDiffAt_two_of_expChart_contDiffAt_two

git diff --check -- Poincare/Global/ContDiffTwo.lean
exit status 0

lake build Poincare.Global.ContDiffTwo
✔ [3145/3145] Built Poincare.Global.ContDiffTwo (2.5s)
Build completed successfully (3145 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
