Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation-2: variation roadmap subtasks 1-3 (δRic from δΓ)

Read `harness/reports/M3-scalar-variation_notes.md` — this task is its subtasks 1, 2, 3, extending `Poincare/Global/ScalarVariation.lean`. On main: `RicciEndoHasDerivAt`, `deriv_scalarAt_eq_trace_of_ricciEndoHasDerivAt`, `deltaGammaAt` (+ left-linearity, static-zero), `timeDerivAt` vocabulary (Global/MetricVariation.lean), smooth canonical connection. Model templates in ModelLaplacian.lean: `hasDerivAt_coordRicci`, `ricciDeriv_*`, `christoffelDeriv_*` (grep for exact names).

In order (each its own commit):

1. **Ricci-to-endomorphism lift** (subtask 1): from pointwise `HasDerivAt (fun t => (gt t).ricciAt x u w)` hypotheses (all u w) + time-differentiability of the metric/its inverse (honest hypotheses — mirror how `timeDerivAt`/`TimeDifferentiableAt` are phrased), produce `RicciEndoHasDerivAt gt t₀ x A'` with A' expressed via the raised derivative (product rule: d(G⁻¹·Ric) = dG⁻¹·Ric + G⁻¹·dRic; the repo's `hasDerivAt_clm_inverse`-style tools + `fderiv_inverse_raise_apply` patterns in ModelLaplacian are templates; Mathlib `HasDerivAt.clm_apply`/`.comp` for the fiberwise composition).
2. **δΓ right-slot additivity** (subtask 2): `deltaGammaAt_add_right` / `deltaGammaAt_smul_right`. The report notes this needs linearity of the canonical `extend` section in its seed vector OR a tensorial local-frame redefinition — if redefinition is cleaner, you may ADD a new tensorial def (e.g. `deltaGammaTensorAt`) and prove it agrees with `deltaGammaAt` where both are defined (do NOT silently change deltaGammaAt's existing definition — statement freeze; an agreement lemma keeps the history honest).
3. **δRic from δΓ contractions** (subtask 3): `ricciVariation_eq_deltaGamma_contractions` — the closed-manifold analogue of the model's Ricci-variation formula: `HasDerivAt (fun t => (gt t).ricciAt x u w) (deltaRicciAt ...) t₀` where `deltaRicciAt` is defined from `deltaGammaAt` contractions (define it; mirror `ricciDeriv` shape). This is the hardest piece — commit partial trace/contraction lemmas as you go; if the full formula stalls, land the pieces + refined report.

No sorry/axiom; blocked → greens + update the notes file. `lake build Poincare.Global.ScalarVariation`, report names.
