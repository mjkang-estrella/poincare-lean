# M5-glob-52 blocked: selected-field C1 transfer isolated

## Status

Verified strict-partial progress was added in the required new Lean file:

- `Poincare/Global/LevelThreeFeed.lean`

No existing Lean files were edited, and `Poincare.lean` was not changed.

## Verified Lean payload

The new module adds one isolated theorem:

```lean
theorem Poincare.LevelThreeFeed
  .selected_expChart_derivative_fields_contDiffAt_one_of_fderiv_contDiffAt_one
```

It proves the noncomputable-selection bridge for the `FieldProducer` fields:
if the selected derivative fields are genuine `HasFDerivAt` witnesses on
neighborhoods of the base points, then uniqueness of Frechet derivatives makes
them locally equal to the canonical fields

```lean
fun q => fderiv ℝ eM q
fun q => fderiv ℝ eS q
```

Therefore `ContDiffAt ℝ 1` for those canonical derivative fields transfers to
the selected `sourceD` and `targetD` fields.

## Blocking boundary

This does not prove the unconditional F-transition law.  The current repository
still does not export the level-three residual/smooth-dependence theorem that
would prove the canonical endpoint derivative fields are `C1`:

```lean
ContDiffAt ℝ 1 (fun q => fderiv ℝ eM q) v
ContDiffAt ℝ 1 (fun q => fderiv ℝ eS q) (L v)
```

The available level-three files provide:

- `ThirdVariation.lean`: the PL opener for the doubly augmented linear ODE;
- `FieldC1.lean`: compact-tube Taylor remainders for the doubly augmented field;
- `FlowSmoothness.lean`: `C2`/Lipschitz data for the augmented field.

What remains missing is the theorem that instantiates those ingredients for a
genuine doubly augmented endpoint family, proves differentiability of the
second-variation endpoint field in the base point, and identifies that field
with the canonical `fderiv` fields near the produced source and target points.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide|\?_' Poincare/Global/LevelThreeFeed.lean
rg -n '^(theorem|lemma|def|structure|class|axiom|noncomputable def)\b' Poincare/Global/LevelThreeFeed.lean
git diff --check -- Poincare/Global/LevelThreeFeed.lean harness/reports/M5-glob-52_blocked.md
lake build Poincare.Global.LevelThreeFeed
```

Actual result:

```text
forbidden-token scan: no matches
top-level declaration scan:
32:theorem selected_expChart_derivative_fields_contDiffAt_one_of_fderiv_contDiffAt_one

git diff --check -- Poincare/Global/LevelThreeFeed.lean harness/reports/M5-glob-52_blocked.md
exit status 0

lake build Poincare.Global.LevelThreeFeed
✔ [3236/3236] Built Poincare.Global.LevelThreeFeed (10s)
Build completed successfully (3236 jobs).
```
