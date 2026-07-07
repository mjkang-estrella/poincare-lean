# M5-glob-29 blocked: germ discharged, smooth derivative-field regularity remains

## Status

Blocked on the fully unconditional F-transition law.

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/GermAndField.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.GermAndField
  .exists_cartanChartMap_fderiv_eventual_pullback_germ_on_punctured_ball
```

It consumes
`DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball`.
For every nonzero `v` in the returned radius and every source endpoint
membership proof `v ∈ eM.source`, it proves:

- near `eM v`, the selected pointwise field evaluated at the inverse coordinate
  `eM.symm q` is a genuine derivative of the Cartan chart map:
  `∀ᶠ q in 𝓝 (eM v), HasFDerivAt F (DF (eM.symm q)) q`;
- the pointwise metric pullback identity becomes the required neighborhood
  germ for the actual derivative:
  `(fun q => G₁ (F q) ((fderiv ℝ F q) a) ((fderiv ℝ F q) b)) =ᶠ[𝓝 (eM v)]
    (fun q => G₀ q a b)`.

The proof uses openness of the punctured radius set, openness of the
`OpenPartialHomeomorph` target, continuity of `eM.symm` on the target, the
local right inverse law `eM (eM.symm q) = q`, and strict-derivative uniqueness
to rewrite `fderiv ℝ F q` to the selected `DF (eM.symm q)` eventually.

## Remaining blocking boundary

`FTransition.exists_cartanChartMap_christoffelAt_F_transition_law_on_punctured_ball`
still needs a differentiable derivative field and symmetric second derivative:

```lean
HasFDerivAt D (fderiv ℝ D (eM v)) (eM v)
∀ a b, (fderiv ℝ D (eM v) a) b = (fderiv ℝ D (eM v) b) a
```

The natural candidate is `D q = fderiv ℝ F q`, and the new theorem proves the
right eventual pullback germ for that candidate.  The repository still does not
export the needed `C²`/second-derivative regularity for the Cartan chart map or
the derivative-field differentiability and symmetry theorem required to feed
`LCNaturality` unconditionally.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/GermAndField.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/GermAndField.lean
git diff --check -- Poincare/Global/GermAndField.lean
lake build Poincare.Global.GermAndField
```

Actual result:

```text
placeholder scan: no matches
top-level declaration scan:
36:theorem exists_cartanChartMap_fderiv_eventual_pullback_germ_on_punctured_ball

git diff --check -- Poincare/Global/GermAndField.lean
exit status 0

lake build Poincare.Global.GermAndField
Built Poincare.Global.GermAndField
Build completed successfully (3219 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
