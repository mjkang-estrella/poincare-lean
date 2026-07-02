Read harness/worker_contract.md first and obey it strictly.

# Task M3-scalar-evolution-statement: closed-manifold Hamilton scalar evolution — statement layer + flat instance

Context on main: for `g : ClosedSmoothRiemannianMetric n M` we now have `g.laplacianAt` (Global/Laplacian.lean), `g.ricciNormSqAt` (Global/RicciNorm.lean), `g.scalarAt` (Global/Curvature.lean), and `IsClosedRicciFlowSolutionAt` (Global/RicciFlow.lean). The single-chart model proves Hamilton's `∂R/∂t = ΔR + 2|Ric|²` (`hamilton_scalar_evolution_*` in ModelLaplacian.lean); the audit (harness/reports/manifold_assets.md, frontier lemma 5) marks the closed-manifold version as the frontier target needing exactly this vocabulary.

Deliverable: NEW file `Poincare/Global/ScalarEvolution.lean` (+ root import). This is a STATEMENT + SANITY task, not the full proof (that's a later multi-session port):

1. `def SatisfiesHamiltonScalarEvolutionAt (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop` — `HasDerivAt (fun t => (gt t).scalarAt x) ((gt t₀).laplacianAt (fun y => (gt t₀).scalarAt y) x + 2 * (gt t₀).ricciNormSqAt x) t₀`, with whatever regularity data the involved definitions genuinely require carried as documented hypotheses/arguments (follow the Curvature.lean pattern). Provide the unfolding lemma (non-opacity).
2. `theorem hamilton_scalar_evolution_static_flat`-style sanity: for a time-constant metric with vanishing Ricci curvature (hypotheses as in `isClosedRicciFlowSolutionAt_const_of_ricciFlat`), BOTH sides vanish: scalarAt is time-constant (deriv of const = 0) and, GIVEN Ricci-flatness hypotheses strong enough to make scalarAt ≡ 0 as a function of y (state honestly what you need), laplacianAt of it = 0 (use `laplacianAt_const`-machinery) and ricciNormSqAt = 0 (from ricciNormSqAt via the trace of the zero endomorphism — prove `ricciNormSqAt_eq_zero` of a suitable ricci-vanishing hypothesis). So the static flat metric satisfies the evolution equation. Every hypothesis genuine; no certificate structures.
3. `def HamiltonScalarEvolutionProgram : Prop` — the honest frontier statement: every closed Ricci-flow solution family satisfies scalar evolution (∀ gt t₀ x, IsClosedRicciFlowSolutionAt gt t₀ x → [regularity hyps] → SatisfiesHamiltonScalarEvolutionAt gt t₀ x). This is a DEFINITION of the target (like PoincareConjecture), NOT to be proven — it documents the port target. Comment must say explicitly it is unproven and cite the single-chart analogue theorem names.
4. Blocked pieces → commit greens + report.

No sorry/axiom. `lake build Poincare.Global.ScalarEvolution`, commit, report declaration names.
