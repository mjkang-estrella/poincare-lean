Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-variation-9: subtask 6 — the Hamilton scalar evolution theorem (Ricci-flow substitution)

Strategy note from the orchestrator: rather than first discharging the remaining analytic predicates (TraceMetricVariationDerivAt, the two divergence assemblies), do the SUBSTITUTION step now — it is independent, and it converts the goal into its final form so the predicate-discharge tasks have their true target visible.

On main (Global/ScalarVariation.lean + RicciFlow.lean + ScalarEvolution.lean): `scalarVariation_lichnerowicz` (dR/dt = div div h − Δ(tr h) − ⟨h,Ric⟩ under named predicates), `isClosedRicciFlowSolutionAt_timeDerivAt` (under the flow, timeDerivAt paired with sections = −2·ricciTraceAt), `SatisfiesHamiltonScalarEvolutionAt`, `HamiltonScalarEvolutionProgram`.

Deliverables (each its own commit):

1. **h = −2Ric identification**: from `IsClosedRicciFlowSolutionAt gt t₀ x` (+ honest hypotheses), prove `timeDerivAt gt t₀ x v w = −2 * (gt t₀).ricciAt x v w` for tangent vectors v w — bridging the section-level flow field to the pointwise bilinear form (the existing rewiring theorem is section-tested; you need the version at arbitrary tangent vectors — extend via the canonical `extend` sections as `deltaGammaAt` did, or add the honest hypothesis if extension regularity stalls).
2. **Substitution algebra**: with h = −2Ric: `traceMetricVariationAt = −2R`, `metricVariationRicciPairingAt = −2|Ric|²` (wire to `ricciNormSqAt` — check shapes; `scalarAt = tr Ric` lemmas exist in RicciNorm.lean), `tensorDoubleDivergenceAt (−2Ric) = −2·div div Ric`. Each as its own lemma.
3. **Contracted Bianchi obligation**: div div Ric = ½ΔR is what kills the divergence term (div div(−2Ric) = −ΔR; −Δ(tr h) = +2ΔR; net +ΔR... verify the bookkeeping against the model: `hamilton_scalar_evolution_of_bianchi`). State it as a named honest predicate `ClosedContractedBianchiAt` (the closed-manifold twice-contracted Bianchi — its native proof is future work; model analogue `coord_twice_contracted_bianchi` proven).
4. **THE THEOREM**: `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation`: IsClosedRicciFlowSolutionAt + [named predicates] → `SatisfiesHamiltonScalarEvolutionAt gt t₀ x` — i.e. dR/dt = ΔR + 2|Ric|². Then `hamiltonScalarEvolutionProgram_of_predicates` connecting to the program Prop as far as the honest hypotheses allow (do NOT claim the unconditional program — the predicates are open).

No sorry/axiom; blocked → greens + notes. `lake build Poincare.Global.ScalarVariation` (and ScalarEvolution if touched), report names.
