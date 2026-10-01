# Chart successor proof scope, a01

Read-only analysis at `ff3ca4b6dce6499f44ab09a0d3ef8dd80a9417dc`, branch `codex/chart-identification-433-a01`. The checkout retains the authorized 17 applied derivative substitutions, three unfolding substitutions and the inverse-chart h2 repair. Current source SHA-256 is `2e9280becdc909776f0fc3e216d74118b10b4f8ce155565e47210a9838539ac1`. The prior failed `gate-direct-a01.stdout.log` remains SHA-256 `8ccbcf9c8f401653d6e566a08de0bcac67ffb0b4ad1ef816fea6f2e042e5f042` and recorded exit 1. No source file was edited and no build was run.

This supports retained full-root compatibility for proved smoothability S and the separately verified smooth-Poincare consumer. It does not close independent original Hamilton inputs or convergence, accept the current chart patch, or establish final completion.

## Smallest additional scopes

Fresh direct diagnostics name six additional existing theorem bodies. Nine local proof regions suffice for the verified repair route. Line ranges below refer to the current dirty normalized+h2 source; add three for their positions in the original frozen clean source. `proposed-regions-a01.json` records both coordinate systems and exact owner names.

| Existing theorem | Current local proof region | Repair route |
| --- | --- | --- |
| `extDerivFun_apply_chart` | h1 body, 90 | `exact hf.mfderiv` |
| `extDerivFun_apply_chart` | h2 body, 93-94 | `rfl` |
| `isLocallyConstant_of_extDerivFun_eq_zero` | hInv body, 198-201 | Keep its explicit lemma term; use `simpa only [L] using!` |
| `isLocallyConstant_of_extDerivFun_eq_zero` | hzro' body, 211 | `simpa only [F, L] using! hzro` |
| `extDerivFun_apply_mlieBracket_chart` | heq body, 269-270 | `rfl` |
| `extDerivFun_apply_mlieBracket_chart` | final model reduction, 306-308 | Explicit pointwise universal-bracket equality, then the existing calculus/center rewrites |
| `extDerivFun_section_eventually_chart` | heq body, 349-350 | `rfl` |
| `extDerivFun_extDerivFun_chart` | heq body, 403-404 | `rfl` |
| `extDerivFun_apply_mlieBracket` | heq body, 480-481 | `rfl` |

The scalar chart identity holds by definitional equality for generic nontrivially normed field K, so includes the real specialization. The original `simp` leaves `chartAt K (f x) q = q` because `chartAt_self_eq` is not tagged simp. Current Mathlib `ChartedSpace.lean:355`, `IsManifold/ExtChartAt.lean:850,859,862` provide the explicit same identity. No chart, model, scalar field, tangent or norm data is substituted.

`MDifferentiableAt.mfderiv` provides h1 without unfolding a type whose tangent/model instance dictionaries only agree definitionally. The two `using!` calls check the original inverse-chart or zero-derivative conclusion with full expected-type elaboration, while `simp only` retains the chart and lets. No replacement instance is installed. `backward.isDefEq.respectTransparency false` is unnecessary for all tested routes. This is normal Lean elaboration and ordinary kernel-checked proof construction.

The final bracket reduction can use:

```lean
  simp only [I'.range_eq_univ, mpullbackWithin_univ]
  have hbr := congrFun (lieBracketWithin_univ (𝕜 := ℝ)
    (V := (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm X : E' → E'))
    (W := (mpullback 𝓘(ℝ, E') I' (extChartAt I' x).symm Y : E' → E')))
    (extChartAt I' x x)
  rw [hbr, fderiv_apply_lieBracket_of_isSymmSndFDerivAt hFc hsymm
    (hpull Y hY) (hpull X hX), hc X, hc Y]
```

Both original field directions and the X(Yf)-Y(Xf) sign stay fixed. This adds a local proof of an actual Mathlib identity, with no new assumption, public declaration, stronger regularity or alternate model. The accepted normalization manifest and h2 proof remain separate already-authorized edits; freeze the successor additive scope before applying any of these source repairs.

## Probe evidence

All invocations use cached direct `env LEAN_NUM_THREADS=1 lake env lean <ignored-probe>`, same base HEAD/toolchain/manifest and source hash receipts. No Lake build or compiler-output cache publication occurred.

- `LocalIdentities-a01.lean`: exit 1, preserved. The h1, scalar chart identity, hInv and hzro' proofs elaborated; the last pointwise bracket attempt omitted function-equality application and enough typed implicit arguments.
- `LocalIdentities-a02.lean`: exit 0. The six local identities elaborate without a transparency setting.
- `LocalIdentities-a03.lean`: exit 0, 2.63 seconds. Simplifies scalar h2 further to rfl; generic scalar heq also rfl.
- `BracketReplay-a01.lean`: exit 1, preserved. A plain `simpa only [lieBracketWithin_univ, hc] using!` still cannot simplify the nominal dependent-field goal. No acceptance inferred.
- `BracketReplay-a02.lean`: exit 0, 2.79 seconds. Copies the original generic chart/fixed-chart prerequisites and complete chart bracket proof under a scratch namespace, retaining the original headers and assumptions, with only the routes above. Explicit typed hbr resolves the resisting target.
- `BracketReplay-a03.lean`: exit 0, 2.85 seconds. Same successful fragment plus axiom prints. `extDerivFun_apply_chart`, unchanged `extDerivFun_apply_fixed_chart` and `extDerivFun_apply_mlieBracket_chart` copies each depend on exactly `propext`, `Classical.choice`, `Quot.sound`.

The successful fragments contain no option changes. Retained unused-simp warnings are harmless and were left intact. Failed probes were not overwritten.

## Freeze and acceptance boundary

Retain the original 20 exact kernel/formula type and universe contracts, actual generic/model assumptions, imports, chart domains, computational definitions, field directions and every unrelated byte. A successor source guard can allow just the nine listed local regions on top of the existing reviewed API+h2 transformation. In particular do not widen `extDerivFun_apply_fixed_chart`, `mpullback_extChartAt_symm_apply`, `mlieBracket_apply_chart` or any public/private headers.

The parent must still freeze/review the successor, apply the scope under its lease, then run a fresh direct module check, focused module build, both 20-declaration rigid type/axiom/unsafe/partial checks, additive source guard, token scan and `git diff --check`. Scratch fragment success does not substitute for these gates or independently accept the full module.

Exact first action: freeze the additional nine-region source contract against this retained dirty-candidate identity, reusing the existing exact public contracts, before dispatching proof edits. Then rerun the fresh chart Task gates. Preserve all original root imports and final completion requirements.
