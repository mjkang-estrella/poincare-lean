Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-6: pinching roadmap step 3 — the |Ric|² evolution expansion

On main: `ricciEvolution3ReactionAt` (the 3D reaction form, proven), the Ricci evolution equation (`satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`), the |Ric|² time-derivative vocabulary from M4-pinch-1 (in ScalarVariation.lean — read its exact defs), and the formalized moving-metric trace machinery.

Deliverable (roadmap step 3): under the flow in 3D, the evolution of `|Ric|²`:
`d/dt ricciNormSqAt = [rough-Laplacian-of-|Ric|² − 2|∇Ric|²]-shape + reaction-trace + metric-motion terms`
— concretely, the honest decomposition: differentiate `ricciNormSqAt = tr((♯Ric)²)` in t; the Ric-derivative terms substitute the PROVEN evolution (reaction form via `ricciEvolution3ReactionAt`); the g⁻¹-motion terms are the `metricRaiseDerivAt`/pairing machinery (h = −2Ric gives +4·tr(Ric³)-shape contributions — PIN the coefficient on the diagonal test pattern). Land whichever of these shapes is achievable in one session:
(a) minimal: `d/dt |Ric|² = 2⟨∂ₜRic, Ric⟩ + motion-terms` (the abstract product rule + the motion-term identification, each piece its own lemma), with the reaction substituted;
(b) full: including the Bochner-type `⟨ΔRic, Ric⟩ = ½Δ|Ric|² − |∇Ric|²` step (needs the ∇Ric-norm vocabulary — define honestly if missing; the second-order trace machinery supports the Δ-commute half; |∇Ric|² ≥ 0 is what the pinching argument actually uses, so the INEQUALITY form `⟨ΔRic,Ric⟩ ≤ ½Δ|Ric|²` may suffice and be easier — prefer it if the equality stalls).

Test-pattern pin everything. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
