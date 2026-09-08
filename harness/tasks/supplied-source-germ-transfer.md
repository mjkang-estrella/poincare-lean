# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-source-germ-transfer`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-source-germ-transfer_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/chain-parametrization-inventory.md` (the whole plan; your task is one of its
"First five bounded tasks" and is reproduced below verbatim), then the cited definitions. Task 1 has landed on
`main` as `Poincare/Global/CartanSuppliedSourceMap.lean` (namespace `Poincare.CartanSuppliedSourceMap`, names
`germ`, `anchor_mem_source`, `germ_anchor`, `germ_apply`, `generic_map_eq`); import and use it.

# Task supplied-source-germ-transfer

### 2. `Poincare/Global/CartanSuppliedSourceGermTransfer.lean`

Build on task 1. Exact main target `germ_eventuallyEq_of_normal_eventuallyEq`:

```lean
(S.normal x : M → E) =ᶠ[𝓝 x] (S'.normal x : M → E) →
  (CartanSuppliedSourceMap.germ S F x p K : M → RoundSphere3)
    =ᶠ[𝓝 x]
  (CartanSuppliedSourceMap.germ S' F x p K : M → RoundSphere3)
```

Also prove `normal_symm_eventuallyEq_of_normal_eventuallyEq` with conclusion
`((S.normal x).symm : E → M) =ᶠ[𝓝 (0 : E)] ((S'.normal x).symm : E → M)` under the same hypothesis. Prove `exists_open_common_source_agreement` with conclusion
`∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ (germ S F x p K).source ∩ (germ S' F x p K).source ∧ EqOn (germ S F x p K) (germ S' F x p K) V`.

These are neighborhood/inverse transport lemmas, not a pointwise equality wrapper. Use the two partial-homeomorphism inverse laws and openness; do not identify total inverses. Gate: compile the new file and `#check` all three names. Evidence and proof model: `CartanCanonicalFamilyGermComparison.cartanMap_canonical_eventuallyEq_generic`; `LocalFamily.GenericEndpointAgreement.normal_eq_generic` uses the exact inverse/source argument but currently requires stronger legacy endpoint membership. Stop on a missing neighborhood hypothesis, not by strengthening the conclusion to a false global equality.

