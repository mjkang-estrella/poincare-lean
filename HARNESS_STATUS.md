# Orchestration Harness Status

Maintained by the orchestrator (Claude Fable 5); workers are codex gpt-5.5
xhigh in isolated worktrees. Every entry below passed `harness/gate.sh`
(green targeted build, no `sorry`/new `axiom`, `#print axioms` closure exactly
`{propext, Classical.choice, Quot.sound}`) before merging to `main`.
See `harness/ledger.json` for the task DAG and `harness/reports/` for audits
and blocked-decompositions.

## Verified progress (2026-07-01 — 2026-07-05)

### Goal 9 (2026-07-05, fleet returned): interface shrinkage + geodesic campaign opened
Eight gated merges (5 codex-worker, 3 orchestrator-direct), all axiom-closure
clean:
- **Hamilton interface shrunk**: `scalarAt_mdifferentiableAt` proven
  UNCONDITIONALLY at general `n` (`Global/ScalarRegularity.lean`, composing the
  M3 Gram-frame trace route), so `HamiltonConvergencePinchedLimit3Core`
  (`Global/PinchedLimitInterface.lean`) drops the differentiability payload;
  `iff` + core minimal-interface Poincaré composition proven; the
  differentiability-free `sphere_of_pinched_limit_core`
  (`Global/PinchedLimitCore.lean`).
- **Einstein formulation of the analytic wall**: `PositiveEinsteinMetric3`
  (`Global/EinsteinInterface.lean`) with
  `hamiltonConvergencePinchedLimit3_of_positiveEinsteinMetric3` (constant-scalar
  trick) and `poincareConjecture_of_positiveEinstein_of_unitRecognition`; the
  normalization bridge `exists_unitConstantCurvature_of_positiveEinsteinMetric3`
  (Einstein `lam > 0` ⇒ sec ≡ `lam/2` by the Schur route ⇒ `constSMul` to unit
  curvature, `Global/EinsteinNormalization.lean`) connects it DIRECTLY to unit
  recognition.
- **Geodesic campaign opened** (road to unit Killing–Hopf):
  `Global/GeodesicChart.lean` — chart geodesic flow field, Picard–Lindelöf
  local existence, Grönwall local uniqueness, second-order readings; Mathlib
  inventory confirms NO geodesic/exp-map/Hopf–Rinow layer exists upstream
  (`harness/reports/M5-geo-1_assets.md` + 5-step roadmap).
  `Global/MetricCompleteness.lean` — closed ⇒ complete for the induced
  distance (Hopf–Rinow prerequisite).
- **Round S³ model metric**: pullback tensor + `symm`/`pos`/`isVonNBounded`
  proven (`Global/RoundSphereMetric.lean`, via `mfderiv_coe_sphere_injective`
  + antilipschitz); only the `contMDiff` section field remains (exact statement
  + plan in `harness/reports/M5-model-1_blocked.md`).
- **Rescaling functional calculus**: `constSMul` transport —
  `ricciAt` invariant, `ricciEndoAt`/`scalarAt` scale by `c⁻¹`,
  `ricciNormSqAt`/`tracelessRicciNormSqAt` by `c⁻²`, plus the
  constant-independent pinched-payload preservation
  (`Global/MetricRescaleCurvature.lean`).
- **Wave 2 (2026-07-05/06), all gate PASS — 11 gated merges total for goal 9**:
  `roundSphereMetric3` COMPLETE (`contMDiff` section smoothness via
  `inTangentCoordinates`/`mfderiv_const` + hom-bundle trivialization congr) —
  the repo's first concrete closed Riemannian metric; chart Christoffel field
  for `g.leviCivita` (`Global/GeodesicTransport.lean`, christoffelOneForm of
  the blended chart metric with the PROVEN eventual-agreement bridge
  `chartLeviCivita_eventuallyEq_closed`) with `C¹` regularity and local
  geodesics through every point in every chart direction
  (`exists_local_geodesic_chart_solution`); `RicciFlowShortTimeExistence3`
  honest interface + static Ricci-flat shape checks + the flow-half transfer
  into the Hamilton evolution input (`Global/ShortTimeInterface.lean`), with
  the parabolic inventory verdict (Sobolev/Hölder partial; heat kernel,
  Schauder, linear parabolic theory ABSENT from pinned Mathlib) and a 5-step
  DeTurck statement-layer roadmap (`harness/reports/M2-scope-1_assets.md`).
- **Waves 3-4 (2026-07-06), all gate PASS — 26 gated merges total for goal 9**:
  - *Geodesic/exponential track*: `geodesicGermAt` (spec-based germ, zero,
    source, initial-velocity at germ level) → zero-velocity + HOMOGENEITY law
    (`expRayAt`) → uniform Picard–Lindelöf existence on velocity balls →
    endpoint-controlled PL flow + interval uniqueness (the ball invariant the
    exported Mathlib wrapper drops) → target-shrunk flow + flow-germ
    identification → **`expAt` DEFINED** (`ExponentialFixedTime.lean`: flow
    homogeneity on `Icc`, `expAt_zero`, eventual ray law, source membership).
    Chart-overlap scaffold landed; general-overlap naturality re-scoped by the
    orchestrator to the RE-ANCHORING law (blended fields represent `g` only on
    cutoff-1 zones) — in flight as M5-geo-10.
  - *Round-sphere track*: stereographic conformal factor `16/(‖z‖²+4)²`
    proven → chart coefficients of `roundSphereMetric3` = conformal ×
    Euclidean (`RoundSphereChartMetric.lean`) → conformal chart Christoffel
    formula → **chart-level sphere constant κ = 1 in the `-(κ/2)·KN` form**
    (`ConformalCurvature.lean`). The manifold transport
    (`HasConstantSectionalCurvature3 roundSphereMetric3 1` — the sphere
    witness) is in flight as M5-model-7.
  - *DeTurck track*: Lie-derivative vocabulary + Ricci–DeTurck pointwise
    predicate + zero-field reduction iff + short-time/pullback interfaces +
    composition; the DeTurck vector field as the invariant `g`-trace of the
    connection difference + gauged-flow predicate + static sanity; regularity
    reduced to one summand lemma, whose raw-basis conjunct the orchestrator
    flagged SUSPECT-FALSE (predicates-11 pattern) — thread PARKED with the
    extend-frame reroute recorded (not on the M2 critical path).
- **GOAL 9 CROWN (2026-07-06, merges #38-40)**: the six-iteration
  chart↔manifold CURVATURE BRIDGE completed
  (`ChartCurvatureBridge6.lean` — chart Christoffel computations now certify
  manifold `curvatureOp` facts at anchors, for any closed metric); the
  SPHERE WITNESS assembled:
  `roundSphereMetric3_hasConstantSectionalCurvature_one :
  HasConstantSectionalCurvature3 roundSphereMetric3 1`
  (`RoundSphereWitness.lean`) — the repo's first concrete-geometry theorem;
  and the KN contraction `isEinsteinAt_of_hasConstantSectionalCurvature3`
  (κ ⇒ Einstein `2κ`, trace constant confirmed) yielding
  `roundSphereMetric3_isEinsteinAt_two` and
  **`positiveEinsteinMetric3_roundSphere`**
  (`ConstantCurvatureEinstein.lean`): the `PositiveEinsteinMetric3`
  interface — hence `HamiltonConvergencePinchedLimit3` via the proven
  reduction — is INHABITED at the model space. The two-interface conditional
  Poincaré path is certified non-vacuous end-to-end.
- Goal 9 totals: 40 gated merges (zero rejections, zero fabrications); three
  suspect routes intercepted by orchestrator review; three threads parked
  with recorded plans (DeTurck raw-basis regularity, reanchor ODE law,
  full-interval ray law).

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

### Tier M3 — Hamilton scalar evolution (THEOREM PROVEN 2026-07-02)
- `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`
  (`Global/ScalarEvolution.lean`): for a closed Ricci-flow solution family,
  `∂R/∂t = ΔR + 2|Ric|²` — with the closed twice-contracted Bianchi identity
  discharged internally (`closedContractedBianchiAt_canonical`, from the
  proven cyclic second Bianchi `eventually_closed_cyclic_second_bianchi` and
  the curvature-divergence trace identification). Hypotheses: the flow
  equation near the point + honest regularity classes (each with
  satisfiability witnesses) + the two δΓ assembly predicates (whose
  Hessian-trace discharge forms are proven; the `_hessian_variation` variant
  consumes them).
- Supporting campaign (~55 gated worker tasks over 2026-07-01/02, all
  axiom-closure-clean): metric variation vocabulary, Lichnerowicz formula,
  Gram-matrix trace-derivative machinery, Levi-Civita C² regularity,
  curvature Koszul expansion, extend-bracket vanishing, cyclic second
  Bianchi. Two proposed intermediate identities were REFUTED by flat-torus
  counterexamples and rerouted — no false statement survived.

### Tier M5 — the sphere endgame: interface shrinkage (orchestrator-direct, 2026-07-05)
- While the codex fleet was rate-limited, the orchestrator executed six gated
  merges directly: the Killing–Hopf interface factored into normalization +
  unit recognition; the constant rescaling `c•g` constructed; Levi-Civita
  invariance and curvature transport under rescaling proven; and
  **`ConstantCurvatureNormalization3` DISCHARGED** (`constSMul` + Kulkarni–
  Nomizu κ² algebra). The minimal conditional Poincaré path is now
  `poincareConjecture_of_hamiltonConvergence_of_unitRecognition`: exactly two
  named hypotheses — Hamilton convergence and UNIT-curvature recognition.

### Tier M5 — the sphere endgame (CONDITIONAL POINCARÉ PATH, 2026-07-04)
- `poincareConjecture_of_hamiltonConvergencePinchedLimit3`
  (`Global/SphereTheorem.lean`): the first end-to-end conditional path from
  Ricci-flow estimates to `PoincareConjecture`, conditional on exactly two
  named interfaces (hypotheses, never axioms):
  `HamiltonConvergencePinchedLimit3` (analytic convergence wall) and
  `PositiveConstantCurvatureSpaceForm3` (Killing–Hopf recognition).
  Proven links: vanishing traceless Ricci → Einstein → Schur (via the goal-2
  contracted Bianchi) → connected constancy → constant sectional curvature →
  `sphere_of_pinched_limit`.

### Tier M4 — pinching (HAMILTON 1982 ESTIMATES PROVEN, 2026-07-04)
- `hamilton_pinching_preserved`: max of |Ric|²/R² nonincreasing (R > 0, 3D).
- `hamilton_pinching_improvement`: max of |Ric°|²/R^(2−δ) nonincreasing for
  the sharp admissible δ(ε) = 6ε²/(1−2ε+3ε²) under eigenvalue pinching, with
  `hamilton_eigenvalue_pinching_floor_preserved`.
- Foundations: tensor Bochner identity, parabolic |Ric|² inequality, corrected
  quotient evolution, spectral reaction sign, closed parabolic max principle.
- Consolidation audit (M4-audit-1..5): axiom sets clean; bump-function
  globalization closed the extension-regularity gap; static witnesses
  (Ricci-flat / space-form) certify non-vacuity of the scalar chain.

### Tier M4 — tensor evolution (RICCI EVOLUTION EQUATION PROVEN 2026-07-03)
- `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`
  (`Global/ScalarVariation.lean`): under Ricci flow,
  `∂ₜRic = ΔRic + 2·Rm(Ric,·) − 2·Ric²` (classical Hamilton form), with the
  moving-metric trace reconciliation formalized against the proven scalar
  equation. Foundation: the closed tensor Ricci identity (antisymmetrized
  ∇² = curvature action), the differentiated contracted-Bianchi bridge, and
  the corrected Lichnerowicz vocabulary. Three definition/target errors were
  caught pre-proof by test-metric coefficient pinning (space form +
  non-Einstein diagonal) and sanctioned-corrected with full history.

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
