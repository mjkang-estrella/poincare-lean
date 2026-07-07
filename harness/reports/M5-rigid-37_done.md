# M5-rigid-37 done: linearized endpoint map as a CLM

## Status

Done.  Added `Poincare/Global/LinearizedCLM.lean` only; no existing Lean files
or `Poincare.lean` were modified.

## Implemented payload

- `linearizedGeodesicFlow_solution_add_uniqueOn_Icc`: standalone additivity of
  linearized solutions on a PL interval, proved by applying
  `linearODE_solution_uniqueOn_Icc` to `Ψadd` and `fun s => Ψw s + Ψw' s`.
- `linearizedGeodesicFlow_solution_smul_uniqueOn_Icc`: standalone scalar
  homogeneity on a PL interval, proved by the same uniqueness route applied to
  `Ψsmul` and `fun s => c • Ψw s`.
- Endpoint corollaries
  `linearizedGeodesicFlow_endpoint_add_of_uniqueOn_Icc` and
  `linearizedGeodesicFlow_endpoint_smul_of_uniqueOn_Icc`.
- `linearizedEndpointLinearMap` and `linearizedEndpointCLM`, with
  `[FiniteDimensional ℝ E]` continuity supplied by
  `LinearMap.toContinuousLinearMap`.
- Defining lemma:
  `linearizedEndpointCLM_apply`, stating
  `linearizedEndpointCLM Ψ T hadd hsmul w = (Ψ w T).1`.

## Verification

Safety scan:

```bash
rg -n "sorry|axiom|native_decide" Poincare/Global/LinearizedCLM.lean
```

Actual result: no matches.

Build command:

```bash
lake build Poincare.Global.LinearizedCLM
```

Actual result: succeeded.

Final build line:

```text
✔ [2836/2836] Built Poincare.Global.LinearizedCLM (12s)
Build completed successfully (2836 jobs).
```
