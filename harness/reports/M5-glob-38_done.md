# M5-glob-38 done: open-neighborhood congruence for endpoint derivatives

## Status

Strict-partial progress landed in the required new Lean file:

- `Poincare/Global/CongruenceStep.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.CongruenceStep
  .fderiv_directional_residual_and_symm_of_endpoint_hasFDerivAt_on_open
```

For a map `F : E -> G`, an endpoint derivative family

```lean
endpoint : E -> E ->L[Real] G
```

and a candidate second derivative

```lean
CLM : E ->L[Real] E ->L[Real] G
```

the theorem consumes:

```lean
IsOpen U
q ∈ U
Set.EqOn (fun q' => fderiv Real F q') endpoint U
HasFDerivAt endpoint CLM q
ContDiffAt Real 2 F q
```

It turns open-set equality into

```lean
(fun q' => fderiv Real F q') =ᶠ[𝓝 q] endpoint
```

via `Filter.eventuallyEq_of_mem`, transfers the derivative with
`Filter.EventuallyEq.hasFDerivAt_iff`, and feeds the result to
`ResidualExport.fderiv_directional_residual_and_symm_of_hasFDerivAt_fderiv`.

The conclusion is the exact residual and symmetry package:

```lean
forall c > 0, eventually in nhds 0, forall w,
  norm ((fderiv Real F (q + delta) - fderiv Real F q - CLM delta) w) <=
    (c * norm delta) * norm w
```

and

```lean
forall a b, (CLM a) b = (CLM b) a
```

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/CongruenceStep.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/CongruenceStep.lean
git diff --check -- Poincare/Global/CongruenceStep.lean
lake build Poincare.Global.CongruenceStep
```

Actual result:

```text
placeholder/forbidden scan: no matches
top-level declaration scan:
25:theorem fderiv_directional_residual_and_symm_of_endpoint_hasFDerivAt_on_open

git diff --check -- Poincare/Global/CongruenceStep.lean
exit status 0

lake build Poincare.Global.CongruenceStep
✔ [3228/3228] Built Poincare.Global.CongruenceStep (12s)
Build completed successfully (3228 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module built
successfully and introduced no reported warning.
