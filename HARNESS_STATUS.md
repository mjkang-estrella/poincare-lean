# Orchestration Harness Status

Maintained by the orchestrator (Claude Fable 5); workers are codex gpt-5.5
xhigh in isolated worktrees. Every entry below passed `harness/gate.sh`
(green targeted build, no `sorry`/new `axiom`, `#print axioms` closure exactly
`{propext, Classical.choice, Quot.sound}`) before merging to `main`.
See `harness/ledger.json` for the task DAG and `harness/reports/` for audits
and blocked-decompositions.

## Verified progress (2026-07-01)

### Tier M0 — global statement layer (complete)
- `Poincare.PoincareConjecture` (`Poincare/Global/Statement.lean`): the smooth
  3-dimensional Poincaré conjecture over Mathlib manifolds; sphere instances
  verified inhabited.
- `Poincare.MathlibPoincareStatement → PoincareConjecture`
  (`Poincare/Global/Alignment.lean`): pinned to Mathlib's `proof_wanted`
  spelling; the converse honestly requires smoothing theory (Moise), recorded
  in `harness/reports/M0-align_notes.md`.
- Mathlib gap survey: `harness/reports/mathlib_gaps.md`.

### Tier M1 — Riemannian geometry on closed manifolds
- `Poincare.ClosedSmoothRiemannianMetric` + derived instance chain to
  `MetricSpace` (`Global/RiemannianContext.lean`), incl. finite-distance
  lemma on compact connected manifolds.
- Fundamental Theorem of Riemannian Geometry at the manifold layer:
  `levi_civita_unique` (`Global/LeviCivita.lean`) and `levi_civita_exists`
  (`Global/LeviCivitaExistence.lean`, specializing the repo's manifold-level
  Koszul construction in `KoszulExistence.lean`).
- Canonical curvature: `g.leviCivita`, `g.ricciAt` (symmetric bilinear),
  `g.scalarAt`, Einstein ⇒ `scalarAt = n·λ` (`Global/Curvature.lean`) —
  carries a documented `ContMDiffCovariantDerivative g.leviCivita 1`
  hypothesis pending the regularity chain (below).
- Ricci endomorphism, `|Ric|²`, pinching `R² ≤ n·|Ric|²` with
  equality-iff-Einstein (`Global/RicciNorm.lean`).
- Gradient / covariant Hessian / scalar Laplacian (`Global/Laplacian.lean`);
  Hessian symmetry deferred to the regularity chain (report filed).
- Ricci flow statement: `IsClosedRicciFlowSolutionAt` + `of_metric`
  constructor + Ricci-flat static instance (`Global/RicciFlow.lean`).

### Levi-Civita regularity chain (GOAL ACHIEVED 2026-07-01)
`closedLeviCivitaConnection_contMDiff` proven and registered as the instance
`leviCivita_contMDiff` (`Global/Curvature.lean`), so the curvature layer is
hypothesis-free (`ricciAt_symm'` demonstration). Full chain, every link gate
PASS: model-space regularity at any order (`ModelChristoffel.lean`);
chart-transport API + uniqueness bridges; transported torsion-freeness and
metric compatibility; local identification on cutoff-one neighborhoods;
chart-side hom smoothness; hom-bundle `EventuallyEq` lift; bump-localization +
germ locality + `inCoordinates` gluing (`Global/LeviCivitaRegularity.lean`,
`Global/LeviCivitaTransport.lean`).

### Tier M3 — evolution equations (opened)
- Hamilton scalar evolution stated on closed manifolds:
  `SatisfiesHamiltonScalarEvolutionAt` + unfolding iff; proven static-flat
  sanity instance (`hamilton_scalar_evolution_static_flat`); documented
  unproven port target `HamiltonScalarEvolutionProgram`
  (`Global/ScalarEvolution.lean`).

### Tier L — single-chart model
- Schur lemma completed: `schur_fderiv_coordScalar_eq_zero_of_einstein_field`
  (Einstein field, n > 2 ⇒ dR = 0), closing the last bounded local thread.

## Honest ceiling
Nothing here is close to the Poincaré conjecture itself. No nontrivial
closed-manifold Ricci-flow solution exists yet; short-time existence,
integration on manifolds, entropy functionals, surgery, and 3-manifold
topology remain absent from both this repo and Mathlib (see
`harness/reports/manifold_assets.md` and `mathlib_gaps.md`). The legacy
package/certificate layers (`RicciFlowInterface.lean` etc.) remain quarantined
as vacuous/legacy per `INTEGRITY_ASSESSMENT.md` and are not counted as
progress.
