# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-source-map`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-source-map_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/chain-parametrization-inventory.md` (the whole plan; your task is one of its
"First five bounded tasks" and is reproduced below verbatim), then the cited definitions.

# Task supplied-source-map

### 1. `Poincare/Global/CartanSuppliedSourceMap.lean`

Define in namespace `CartanSuppliedSourceMap`:

```lean
def germ (S : CartanSourceExponential.Family g)
    (F : CartanTargetExponential.Family) (x : M) (p : RoundSphere3)
    (K : E ≃L[ℝ] E) : OpenPartialHomeomorph M RoundSphere3 :=
  (S.normal x).trans
    (K.toHomeomorph.toOpenPartialHomeomorph.trans
      ((F.chart p).trans (chartAt E p).symm))
```

Exact theorem targets, with the displayed arguments universally quantified:

```lean
x ∈ (germ S F x p K).source
germ S F x p K x = p
(germ S F x p K : M → RoundSphere3) =
  fun z => (chartAt E p).symm (F.chart p (K (S.normal x z)))
(germ (CartanSourceExponential.genericFamily g)
  CartanTargetExponential.genericFamily x p
  L.toContinuousLinearEquiv : M → RoundSphere3) =
    CartanMap.cartanMap g x p L
```

Name them `anchor_mem_source`, `germ_anchor`, `germ_apply`, `generic_map_eq`. The last target intentionally asks equality of forward maps, not definitional equality of differently parenthesized `OpenPartialHomeomorph.trans` packages. Gate: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceMap.lean`, followed by exact `#check` probes of those four names. Evidence: `CartanMap.openPartialHomeomorph`, `CartanSourceExponential.genericFamily`, and `CartanTargetExponential.cartanMap_anchor` cited above. Stop if the supplied source's anchor laws do not suffice to prove membership; record the exact extra target-side condition instead of adding it silently.

