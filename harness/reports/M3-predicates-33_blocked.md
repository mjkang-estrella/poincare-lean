# M3-predicates-33 blocked report

## Summary

The frozen target `ClosedContractedBianchiAt (gt t0) x` was not closed
unconditionally in this session.

Verified progress landed in `Poincare/Global/ScalarVariation.lean`:

- `ClosedContractedBianchiAt.of_tensorDivergenceOneForm_eq_half_extDerivFun_near`

This lemma proves the exact second-divergence target from the neighborhood
directional Ricci-divergence identity:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

plus scalar C2 regularity and differentiability of the scalar exterior
derivative fields needed to differentiate the one-form identity.

## Route decision

Route A remains the preferred route, but the useful decomposition is now sharper
than replaying the full model computation at once.  The model proof factors as:

1. prove the directional identity `div Ric = 1/2 dR`,
2. differentiate that one-form identity,
3. trace the result to get `div div Ric = 1/2 ΔR`.

The new closed lemma verifies steps 2 and 3 for the closed definitions.  The
remaining hard part is step 1 in closed form.

## Exact remaining goal

For a closed smooth metric `g`, at least locally near `x`, prove:

```lean
∀ᶠ y in nhds x, ∀ w : TM y,
  tensorDivergenceOneFormAt g (ricciVariationField g) y w =
    (1 / 2 : ℝ) * extDerivFun (fun z : M ↦ g.scalarAt z) y w
```

This is the closed analogue of the model theorem family
`fderiv_coordScalar_eq_two_ricciDivergenceForm_of_contDiff`,
`einstein_tensor_divergence_free_of_contDiff`, and
`tensorDivCLM_coordRicciForm_eq_half_grad_field`.

Once that one-form identity is proved from the existing closed curvature and
Bianchi assets, the frozen predicate follows by the committed theorem.

## Sanity check

- Flat/static torus: `Ric = 0` and scalar curvature is constant, so both sides
  of the one-form identity and the final double-divergence identity are zero.
- Round sphere: Ricci is parallel and scalar curvature is constant, so the
  divergence and scalar-gradient sides both vanish.
- The bookkeeping matches the model route: differentiating `div Ric = 1/2 dR`
  and tracing gives `div div Ric = 1/2 ΔR`.

## Verification

Forbidden-placeholder scan on the edited Lean files: no matches.

Requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success.  The build completed with existing linter warnings and ended
with:

```text
Build completed successfully (2806 jobs).
```
