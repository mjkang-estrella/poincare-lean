# M5-glob-37 blocked: fderiv residual export calculus landed

## Status

Blocked on the fully non-hypothetical augmented-endpoint-to-`fderiv` comparison,
with verified strict-partial progress in the required new Lean file:

- `Poincare/Global/ResidualExport.lean`

No existing Lean file was edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.ResidualExport
  .fderiv_directional_residual_and_symm_of_hasFDerivAt_fderiv
```

For a map `F : E -> G`, a point `q : E`, and a candidate second derivative

```lean
CLM : E ->L[Real] E ->L[Real] G
```

the theorem consumes a genuine Frechet derivative of the canonical derivative
field

```lean
HasFDerivAt (fun q' : E => fderiv Real F q') CLM q
```

plus `ContDiffAt Real 2 F q`, and exports both pieces demanded downstream:

```lean
forall c > 0, eventually in nhds 0, forall w,
  norm ((fderiv Real F (q + delta) - fderiv Real F q - CLM delta) w) <=
    (c * norm delta) * norm w
```

and

```lean
forall a b, (CLM a) b = (CLM b) a
```

The residual proof unfolds the `HasFDerivAt` remainder with
`hasFDerivAt_iff_isLittleO_nhds_zero` and `isLittleO_iff`, then evaluates the
operator residual using `ContinuousLinearMap.le_opNorm`.  The symmetry proof
rewrites `ContDiffAt.isSymmSndFDerivAt` through `hfderiv.fderiv`.

## Blocking boundary

This closes the final calculus export once

```lean
HasFDerivAt (fun q' : E => fderiv Real F q') CLM q
```

has actually been produced.

The repository still lacks the non-hypothetical bridge identifying the
augmented endpoint derivatives from `SecondDischarge.lean` /
`SecondFlowDerivative.lean` and the endpoint CLM from `SecondFrechet.lean` with
the Frechet derivative of the concrete canonical derivative field
`q |-> fderiv Real F q` for the Cartan chart map.  In particular, the current
APIs still do not export a neighborhood-level comparison turning the
second-variation endpoint family into the exact residual for

```lean
fderiv Real F (q + delta) - fderiv Real F q - CLM delta
```

uniformly in `delta` and the direction `w`.

Therefore the unconditional `FTransition` law cannot yet be closed honestly in
this worktree.  The remaining proof obligation is specifically the
augmented-endpoint-to-canonical-`fderiv` identification, not the residual
calculus or second-derivative symmetry export.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/ResidualExport.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/ResidualExport.lean
git diff --check -- Poincare/Global/ResidualExport.lean
lake build Poincare.Global.ResidualExport
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
31:theorem fderiv_directional_residual_and_symm_of_hasFDerivAt_fderiv

git diff --check -- Poincare/Global/ResidualExport.lean
exit status 0

lake build Poincare.Global.ResidualExport
✔ [3227/3227] Built Poincare.Global.ResidualExport (12s)
Build completed successfully (3227 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
