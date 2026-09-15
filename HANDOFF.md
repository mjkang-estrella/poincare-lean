# Handoff Snapshot

## 2026-09-15 Worker Hamilton auxiliary quotient evolution: verified partial

Branch `worker/hamilton-auxiliary-quantity-evolution`, base `330ec679`, proof
head `56b75aeb`. The new `Global/HamiltonScalarGradientEstimate.lean` proves
the intrinsic heat-operator quotient rules and normalized scalar-gradient
quotient evolution from joint C⁵ metric entries. The quotient normalization
term is `−(4/3)rQ`. The factor-three scalar trace estimate gives only `c₂=0`;
the exact numerical damping obstruction and the `20/7` to `2/21` calibration
are also proved. No positive cancellation constant or full Hamilton auxiliary
inequality is claimed.

All nine emitted declarations have exactly the three required foundational
dependencies. Focused compilation, module build, worker gate, token scan,
and whitespace checks pass. Three proof items are committed separately.
The blocked report and actual compiler evidence are in
`harness/reports/hamilton-auxiliary-quantity-evolution_blocked.md`.
This worker result awaits independent review and is not accepted or integrated.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonScalarGradientEstimate.lean`.
Then derive the sharper geometric trace-gradient bound from contracted Bianchi
and append it to this chain. The quotient Hessian/mixed-gradient estimate
also remains open. The existing maximum-comparison engine can be reused.
## 2026-09-15 Worker buffered frozen nested cutoffs proved

Branch `worker/buffered-frozen-nested-cutoff`, base `330ec679`, verified proof
head `de7bbe43`. The existing `Global/BufferedFrozenParabolicSolver.lean` now
contains the nested cutoff construction, exact principal-error cancellation,
time-uniform commutator carriers and cutoff graph bounds, and the uniform
single-chart estimate. All 506 original lines are unchanged.

`Poincare.BufferedFrozenParabolicSolver.single_chart_error` identifies the
Hölder residual with the genuine chart operator and proves both requested
norm bounds. `Poincare.BufferedFrozenParabolicSolver.exists_single_chart_parametrix`
constructs the near-frozen inverse and a positive time interval from the actual
coefficient-extension smallness conditions. Oscillation is only an existence
condition; the single-chart error contains the two commutator time powers.
The finite-atlas assembly estimates remain separate work.

Focused compilation, the module build, empty token scan, and whitespace checks
pass. All 101 emitted declarations, including the 37 new ones, have exactly
the three required foundational dependencies. Actual diagnostics, final gate
outputs, the complete module audit program, and the appended proof diff are in
`harness/reports/buffered-frozen-nested-cutoff_done.md`.
This worker result awaits independent review and has not been merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean`.

## 2026-09-15 Worker intrinsic Bochner and scalar-gradient evolution proved

Branch `worker/intrinsic-bochner-scalar-gradient`, task base `cdcf6956`,
verified proof head `abf4efa5`. The single new
`Global/IntrinsicBochnerScalarGradient.lean` proves intrinsic Bochner for C³
scalars by chart localization, higher-order joint scalar regularity, and the
normalized scalar-gradient evolution equation. Joint C⁴ metric entries give
joint C² scalar curvature. The final producer uses the authorized C⁵ entries
to supply spatial C³ scalar curvature and all extra scalar hypotheses.
The Ricci terms cancel, leaving the normalization term `-2 r S`.

Focused compilation, an expanded literal-target assignment, the empty token
scan, and whitespace checks pass. All 68 emitted declarations have exactly
the three required foundational dependencies. Actual failed and final probe
outputs, audit programs, and the proof diff are in
`harness/reports/intrinsic-bochner-scalar-gradient_done.md`.
This worker result awaits independent review and has not been merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/IntrinsicBochnerScalarGradient.lean`.
## 2026-09-15 Worker buffered frozen parabolic solver: extension and chart solver proved

Branch `worker/buffered-frozen-parabolic-solver`, base `555d8724`, verified proof
head `118bd164`. The new `Global/BufferedFrozenParabolicSolver.lean` proves
compactly supported oscillation extensions with time-uniform Hölder bounds,
small-radius control for genuine inverse metric entries, compact atlas cutoffs,
and bounded frozen and near-frozen chart solvers with the genuine equation on
the cutoff one-locus. Items 1 and 2 are committed as `4cde61a0` and `890859f6`.

Item 3 remains blocked. With b=ψ(a−A₀), the required cancellation on supp ψ is
false: a−A₀−b=(1−ψ)(a−A₀). Commit `118bd164` proves the actual cutoff-product
identity including this transition error. The requested norm estimate remains
unproved; the frozen contract was not changed. The survey's separate coefficient
cutoff ξ=1 on supp ψ is the proposed next contract correction.

Focused compilation, module build, literal survey target adapters, empty token
scan, and whitespace checks pass. All 64 emitted declarations have exactly the
three required foundational dependencies. Actual outputs, failed probes, and the
proof diff are in `harness/reports/buffered-frozen-parabolic-solver_blocked.md`.
This worker result awaits independent review and has not been merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/BufferedFrozenParabolicSolver.lean`.
Then review the two-cutoff contract before attempting the single-chart norm bound.

## 2026-09-15 Worker finite-atlas parabolic tensor carriers proved

Branch `worker/finite-atlas-parabolic-tensor-space`, base `e65eaa7b`,
verified proof head `143cb944`. The single new
`Global/FiniteAtlasParabolicTensorSpace.lean` proves the survey's exact
closedness, completeness, and record-equivalence targets for the weighted
compatible tensor carriers. It also proves support/symmetry/overlap membership,
bounded entry evaluation, and compact coordinate supports. Both carriers
inherit their finite-product submodule norms and real vector-space instances.

Focused compilation, imported target and instance checks, the empty token scan,
and whitespace checks pass. All 120 emitted declarations have exactly the
three required foundational dependencies. Probe sources, failures, final outputs,
and proof diff are in `harness/reports/finite-atlas-parabolic-tensor-space_done.md`.
This worker result awaits independent review and has not been merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean`.
## 2026-09-15 Worker scalar-gradient evolution: partial calculus proved

Branch `worker/scalar-gradient-evolution-identity`, base `9f0374b6`, verified
proof head `d72764f9`. The single new `Global/ScalarGradientEvolution.lean`
proves seven named results: moving covector/gradient norm differentiation,
manifold mixed-partial differentiation, the normalized scalar-gradient time
derivative under explicit extra scalar regularity, the coordinate/intrinsic
Ricci bridge, anchor-coordinate Bochner, and the intrinsic Laplacian expansion
for a chart-supported scalar. The complete emitted module has 45 declarations,
each with exactly the three required foundational dependencies. Focused
compilation, token search, and whitespace checks pass.

The full intrinsic scalar-gradient Bochner identity and the assembled evolution
predicate remain unproved. Joint C⁴ metric entries have not yet been shown to
supply the additional joint C² scalar and differentiable scalar-Laplacian
hypotheses of the time theorem. The exact resisting identity, all probe outputs,
source snapshots, and final diff are in
`harness/reports/scalar-gradient-evolution-identity_blocked.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ScalarGradientEvolution.lean`.
Then reproduce report probe 27 and prove the coordinate/intrinsic Laplacian
germ equality needed for localized Bochner assembly.


## 2026-09-15 Worker near-frozen parabolic right inverse proved

Branch `worker/near-frozen-parabolic-right-inverse`, base `57144244`,
verified proof head `5c1f77a4`. The single new
`Global/NearFrozenParabolicRightInverse.lean` proves the exact
`exists_nearFrozen_solution` and a uniform bounded linear operator form.
The proof packages the symmetric-factor change of variables as a frozen
linear inverse and corrects it using the original-coefficient multiplier.
Its choices are `C = 2 D`, `ε₀ = 1 / (36 D)`, and `τ₀ = 1`, where `D`
depends only on the exponent and ellipticity bounds.

Focused source compilation, imported literal-target assignment, empty token
scan, and whitespace checks pass. The full emitted-module audit checks all
26 declarations, including generated declarations outside the task namespace;
each has exactly the three required foundational dependencies. Actual outputs,
failed probes, probe sources, and the proof diff are preserved in
`harness/reports/near-frozen-parabolic-right-inverse_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `DEVELOPER_DIR=/Library/Developer/CommandLineTools LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearFrozenParabolicRightInverse.lean`.

## 2026-09-15 Worker near-identity parabolic right inverse proved

Branch `worker/near-identity-parabolic-right-inverse`, base `a77fdab5`,
verified proof head `4fbea6a4`. The single new
`Global/NearIdentityParabolicRightInverse.lean` proves multiplier linearity and
boundedness, the one-half error estimate, the Neumann-corrected inverse, its
closed-cylinder variable-coefficient equation and uniform `2 C_S` norm bound,
and existence of a zero-trace solution for every forcing under the quarter bounds.

All 29 declarations, including generated proofs, have exactly the three required
foundational dependencies. Focused source compilation, expanded-coefficient
existence type assignment, forbidden-token scan, and whitespace checks pass.
Full outputs, failed diagnostics, probe sources, and the final proof diff are in
`harness/reports/near-identity-parabolic-right-inverse_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean`.
## 2026-09-15 Worker Hamilton Eta-only core reduction proved

Branch `worker/hamilton-eta-core-reduction`, base `8721fff7`, proof head
`7890e2d2`. The one new `Global/HamiltonEtaCoreReduction.lean` supplies the
mean floor `(3/4) eta` from the uniform normalization gap and reconstructs the
final reaction core with rate `eta`. The new core removes scalar comparison,
its coefficient gap, and variance-energy domination from the pinned NS core.
All six declarations compile with exactly the required foundational dependencies;
token and whitespace gates pass. Actual outputs and the proof diff are in
`harness/reports/hamilton-eta-core-reduction_done.md`.
The Eta producer remains open. This worker result awaits independent review
and has not been merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonEtaCoreReduction.lean`.

## 2026-09-15 Worker Duhamel continuous linear operator proved

Branch `worker/duhamel-solution-operator-clm`, base `2ca30baa`, proof head
`baa43865`. The single new `Global/DuhamelSolutionOperatorCLM.lean` proves
graph uniqueness from values on positive time intervals and constructs the
continuous linear Duhamel operator with its integral formula, uniform short-time
norm bound, and heat equation on the closed interval. All 12 declarations have
exactly the required foundational dependencies. The focused module, explicit
four-target type assignments, forbidden-token scan, and whitespace checks pass.
Actual outputs and the proof diff are in
`harness/reports/duhamel-solution-operator-clm_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean`.

Snapshot date: 2026-09-08 (UTC)


## 2026-09-15 Worker parabolic Hölder multiplier estimate proved

Branch `worker/parabolic-holder-multiplier-estimate`, base `2ca30baa`, proof
head `430f5bfb`. The single new `Global/ParabolicHolderMultiplier.lean`
proves all four task items in separate commits: zero-trace Hessian
interpolation, bounded coordinate entries and the split product norm bound,
the nine-entry multiplier estimate, and elementwise one-half error smallness
after a supplied bounded solution map. The forcing is built with `ofFunction`
and agrees with the requested coefficient-Hessian sum.

Focused compilation, the empty forbidden-token scan, and whitespace checks
pass. All 46 explicit and generated declarations have exactly
`[propext, Classical.choice, Quot.sound]`. Full probe output, failed
diagnostics, statement checks, and the proof diff are preserved in
`harness/reports/parabolic-holder-multiplier-estimate_done.md`.
This worker result awaits independent review and is not merged or accepted.
The continuous-linear-map packaging of the error remains separately scoped.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean`.

## 2026-09-11 Worker Duhamel parabolic Hölder bound proved

Branch `worker/duhamel-parabolic-holder-seminorm`, base `ae66c744`, proof head
`610b2e15`. The single new `Global/DuhamelParabolicHolderSeminorm.lean`
proves the exact `duhamel_hessian_parabolic_holder` and its landed
`hasHolderBound_duhamel_hessian` predicate form, with constant `C₁ + C₂`.
Both theorems were compiled and committed separately. The exact task-statement
assignment, forbidden-token scan, dependency checks for both declarations,
and whitespace gate pass. Full probe output, the initial parser diagnostic,
and proof diff are in `harness/reports/duhamel-parabolic-holder-seminorm_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelParabolicHolderSeminorm.lean`.

## 2026-09-11 Worker moving-limit Leibniz: both parts proved

Branch `worker/moving-limit-leibniz-rule`, base `bec9c447`, verified proof
head `3e8cb854`. The single new `Global/MovingLimitLeibniz.lean` contains
12 theorems. The general Leibniz rule uses a diagonal power bound on the
parameter derivative. Clipping below the diagonal gives integrable secants
from both sides, so the proof includes the initial and terminal endpoints.
The final theorem copies the frozen `duhamel_solves_heat_equation` statement
verbatim and supplies all hypotheses from the landed heat results.

The focused Lean check, token scan, whitespace check, exact frozen-type
assignment and all 12 dependency checks pass. Every theorem has exactly
`[propext, Classical.choice, Quot.sound]`. Complete probe output and the
proof diff are in `harness/reports/moving-limit-leibniz-rule_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/MovingLimitLeibniz.lean`.

## 2026-09-11 Worker Duhamel heat equation: boundary and interior integral proved

Branch `worker/heat-duhamel-heat-equation`, base `c165951b`, proof head
`28e88eb4`. The single new `Global/HeatDuhamelHeatEquation.lean` contains
11 separately committed theorems: the exact Hessian-trace identity, actual
Hessian/Laplacian time integrability, the Duhamel Laplacian interchange,
the positive-time integrand derivative, Gaussian rescaling and joint
zero-time continuity, the diagonal boundary limit, identification of the
integrated time derivative, and zero initial value.

The focused source check, empty token scan, whitespace check, and exact
foundational-dependency checks for all 12 declarations pass. The frozen
`duhamel_solves_heat_equation` remains unproved and undeclared. Its exact
remaining goal is the moving-limit time derivative on `Icc 0 T`, including
the terminal left derivative. The blocked report records the full frozen
probe, the resisting domination shape, failed compiler output and proof
diff in `harness/reports/heat-duhamel-heat-equation_blocked.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHeatEquation.lean`.
Then reproduce the remaining-goal snippet from the report before adding the
right-sided Leibniz argument.



## 2026-09-10 Worker Duhamel Hessian differentiation: exact K2 proved

Branch `worker/heat-duhamel-hessian-differentiation`, base `0642d40e`,
proof head `2807e763`. The new
`Global/HeatDuhamelHessianDifferentiation.lean` proves the frozen
`duhamel_hessian_bound`: zero initial trace, spatial C² regularity, genuine
cancelled Hessian time integrability, equality with the actual Hessian and
the `C K t^(α/2)` bound. The gradient moment scales exactly as `t^(-1/2)`;
its time integrability closes both branches of the earlier worker probe.

All 20 theorems were compiled and committed individually. The focused gate,
exact frozen-statement assignment, token scan and whitespace check pass.
All 21 declarations, including the local instance, have exactly the required
foundational dependencies. Full probe output and proof diff are in
`harness/reports/heat-duhamel-hessian-differentiation_done.md`.
This worker result awaits independent review and is not merged or accepted.

First action: `git diff 0642d40e..2807e763 -- Poincare/Global/HeatDuhamelHessianDifferentiation.lean`.


## 2026-09-10 Worker Duhamel spatial Hessian: steps 1 and 2 proved

Branch `worker/heat-duhamel-spatial-holder-hessian`, base `4c991f21`, proof
head `eac76c3a`. The new `Global/HeatDuhamelSpatialHolderHessian.lean`
proves the full bounded-data heat Hessian convolution identity and its
cancelled form, the sharp spatial Hölder bound, time integrability of the
cancelled integral, and its `t^(α/2)` norm estimate. Fourteen theorems were
compiled and committed individually. All 15 declarations, including the
local instance, have exactly the required foundational dependencies. The
source, token, and whitespace gates pass.

The frozen `duhamel_hessian_bound` is not proved or declared. The step-3
differentiation probe closes its Hessian hypotheses but leaves time
measurability and time integrability of the first spatial heat derivative
unproved. First differentiation of the Duhamel value and C² continuity
also remain. The class-B blocked report preserves exact goals, probe
source/output, checks, and the final diff in
`harness/reports/heat-duhamel-spatial-holder-hessian_blocked.md`. This
worker result is not merged or accepted.

First action: `rg -n 'hasFDerivAt_heatKernel_spatial|integrable_smul_fderiv_heatKernel_sub' Poincare/Global/HeatCauchyTheorem.lean Poincare/Global/HeatCauchyNext2.lean`.

## 2026-09-08 Worker normalization exact contract proved

Branch `worker/closed-ricci-flow-normalization`, base `8345b27c`, verified
proof head `e468a20b`. The new `Global/ClosedRicciFlowNormalization.lean`
proves the survey's exact `normalization` theorem. The Ricci equation supplies
a log-density derivative and an integrable density bound on compact time
slabs; dominated convergence gives mean scalar continuity. The exponential
scale and local inverse time map include ordinary derivatives at zero and
reached-time containment. The original Appendix D definitions are unchanged.

The focused Lean check, forbidden-token scan, whitespace check, exact target
assignment, and exact dependency checks pass for all 21 noninternal
declarations. This worker result is not merged or accepted. The frozen output
predicate does not include joint C³ regularity of the normalized family; no
proof of that stronger output clause is claimed. Full evidence and failed
diagnostics are in `harness/reports/closed-ricci-flow-normalization_done.md`.

First action: `git diff 8345b27c..e468a20b -- Poincare/Global/ClosedRicciFlowNormalization.lean`.


## 2026-09-08 Supplied Cartan route complete: unit recognition is a theorem

Plan `harness/reports/parametrization-plan-3.md` tasks 11 to 19 all landed
on `main`, each gated by `harness/gate.sh` (focused build, forbidden-token
scan, module-wide axiom scan exactly `{propext, Classical.choice,
Quot.sound}`). Modules, in dependency order:
`CartanSuppliedFinitePatchCover`, `CartanSuppliedUniformPatchSwitch`,
`CartanSuppliedBufferedPairAgreement`, `CartanSuppliedPatchPolicy`,
`CartanSuppliedWholeCellRealization`, `CartanSuppliedSubdivisionTransport`,
`CartanSuppliedHomotopyEndpoints`, `CartanSuppliedTerminalTransport`,
`CartanSuppliedRestrictedDevelopment`, `CartanSuppliedUnitRecognition`.

Consequences now checked on `main`:

- `CartanSuppliedUnitRecognition.unitRecognition :
  UnitConstantCurvatureSphereRecognition3 M` for every closed simply
  connected second countable smooth 3-manifold, on its original chart
  instance (transfer through
  `ConnectionInstanceNaturality.exists_controlled_recognition_reduction'`).
- `Poincare.universal_unit_constant_curvature_sphere_recognition`
  (`Global/UniversalUnitRecognition.lean`) discharges the `unit-recognition`
  mission endpoint. `python3 scripts/theorem_registry.py graph --mission
  harness/v2/missions/unit-recognition.json --require-closed` exits 0 with
  `all_obligations_discharged: true`. The mission was rewritten: the refuted
  H1/H2 obligation nodes are replaced by checked nodes for the supplied route.
- `poincareConjecture_of_universalHamiltonConvergence :
  UniversalHamiltonConvergenceStatement → PoincareConjecture` and
  `poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence :
  ExistsSmoothabilitySmoothManifoldStatement → UniversalHamiltonConvergenceStatement →
  PoincareConjectureStatement` (`Global/HamiltonPoincareReduction.lean`).

Remaining boundary to the reserved theorem `Poincare.poincare_conjecture`
(still intentionally absent):

1. Universal Hamilton convergence (`hamilton-front` mission, two open
   obligations: the five analytic inputs and the endpoint). No Cartan, patch,
   mesh, homotopy, or recognition premise remains in front of it.
2. Existence-shaped smoothability of compact simply connected topological
   3-manifolds (`ExistsSmoothabilitySmoothManifoldStatement`, the Moise-type
   bridge from the smooth `PoincareConjecture` to the frozen topological
   statement). Not yet registered as a mission obligation.

The alternative `grounded-topology` route (surgery sources and covering
construction) is unchanged and still has two open obligations.

The exact remaining boundary is now machine-checked as the mission
`harness/v2/missions/hamilton-poincare.json` (endpoint
`Poincare.poincare_conjecture`): obligations `hamilton-convergence`
(`Poincare.universal_hamilton_convergence`) and `exists-smoothability`
(`Poincare.universal_exists_smoothability`, pinned type
`ExistsSmoothabilitySmoothManifoldStatement`), checked nodes
`unit-recognition` (unconditional) and `hamilton-reduction`. `graph` exits
0 with three open obligations; `--require-closed` exits 2.

Survey results (2026-09-08, codex `gpt-6-astra` high, reports trimmed on
main, full evidence on the retained `worker/*` branches):

- `harness/reports/hamilton-front-decomposition_done.md`: the `reaction`
  record alone produces the Hamilton endpoint, and a smaller finite-energy
  normalized-flow interface suffices; universal Hamilton convergence is
  equivalent to universal positive Einstein existence. Implemented as
  `Global/HamiltonReactionEndpoint.lean`, `Global/HamiltonEndpointEquivalences.lean`
  (also `poincareConjecture_of_universalPositiveEinstein`), and
  `Global/HamiltonFiniteEnergyFlowInterface.lean`, all gated; registered in
  `hamilton-front.json` as obligations `hamilton-reaction-existence` and
  `finite-energy-flow-existence` with checked reductions. Every existence
  statement stays open: a normalized Ricci flow on an arbitrary closed simply
  connected 3-manifold needs parabolic existence, Shi-type estimates, and
  pinching theory absent from the pinned Mathlib, and the universal statement
  assumes no positive-Ricci initial metric (this is the Perelman-level core).
- `harness/reports/smoothability-bridge-survey_done.md`: no A-sized core
  step exists for Moise-type smoothability; estimated multi-year library
  development (PL manifolds, triangulation, smoothing theory all absent from
  Mathlib). The repository's finite-atlas assembly is real: its proposal 1
  is implemented as `Global/SelectedFiniteNerveSmoothingStatements.lean`
  (statement plus the checked edge to `ExistsSmoothabilitySmoothManifoldStatement`)
  and pinned in `hamilton-poincare.json` as `selected-finite-nerve-smoothing`.
  No alternative from currently reachable hypotheses was found.

Next campaign (dispatched 2026-09-08): `reaction-record-decomposition`
(prove which reaction-record and finite-energy-interface fields follow from
a smaller core; one new module allowed) and
`ricci-flow-existence-interface-survey` (lemma-level plan for DeTurck
short-time existence on closed 3-manifolds; report only). Also landed:
`Global/FiniteTriangulationStatements.lean` (finite complex compactness and
the open finite-triangulation interface, survey items 5.1 and 5.3).

`reaction-record-decomposition` landed (`Global/HamiltonReactionCoreReduction.lean`,
gate PASS, 9 declarations): density integrability, density-derivative
measurability, the area formula, and time differentiability of the chart-frame
record are proved from joint C³ entries plus a local integrable domination
clause; the residual core `HamiltonReactionCore3` (normalized flow, compact
realization with three continuity clauses, positive mean floor, reaction
domination, joint C³ entries, local domination) reconstructs the reaction
record and yields the endpoint. Pinned as `hamilton-reaction-core` in
`hamilton-front.json`. All existence content remains open.

`ricci-flow-existence-interface-survey` landed (trimmed report; full
appendices on the retained worker branch): the landed interfaces
(`RicciFlowShortTimeExistence3`, DeTurck and pullback interfaces, BUC
Euclidean existence, pointwise inverse-gauge existence) reduce short-time
existence to a variable-coefficient quasilinear parabolic existence and
regularity theorem with compatible global construction, class B (tasks 3-6
of its section 3; Schauder solvability, finite-atlas linear inverse,
nonlinear residual estimate, smooth regularity). The boundary cannot be split
into one chartwise linear assumption plus proved bookkeeping. Route ranking:
finite-atlas parabolic Hölder contraction first. Its only class-A item, the
compact ellipticity constant, landed as `Global/CompactCoefficientEllipticity.lean`
(`exists_uniform_coercivity`, gate PASS).

`hamilton-compact-family-invariant-continuity` landed as a verified partial
result (`Global/HamiltonCompactFamilyInvariantContinuity.lean`, gate PASS):
joint continuity of scalar curvature and squared traceless Ricci along any
metric family with jointly continuous scalar third-jet profiles, in every
dimension. The weak continuity of the finite volume measure along such a
family is the open remainder; the follow-up
`hamilton-family-volume-measure-continuity` targets it plus the jet-form core.

`hamilton-chart-density-local-domination` landed
(`Global/HamiltonChartDensityLocalDomination.lean`, gate PASS, 10
declarations): the local integrable domination clause of the reaction core is
derived from joint C³ metric entries (continuous intrinsic time-variation
trace, logarithmic density derivative, exponential density comparison), so
`HamiltonReactionCore3'` drops it; pinned as `hamilton-reaction-core-reduced`
in `hamilton-front.json` with its checked endpoint reduction.

`hamilton-family-volume-measure-continuity` landed
(`Global/HamiltonFamilyVolumeMeasureContinuity.lean`, gate PASS, 14
declarations): weak continuity of the finite volume measure along a metric
family with jointly continuous scalar third-jet profiles, through the
cutoff-one chart cover, parametrized Gram density continuity, and the
constant-measure moving-integral theorem; with the landed curvature clauses
this gives the jet-form core. The orchestrator combined both clause removals
into `Global/HamiltonReactionCoreFinal.lean`: `HamiltonReactionCore3Final`
(forward-time normalized flow, joint C³ entries, compact realization with
continuous jet profiles, positive mean floor, uniform reaction domination)
reconstructs the full reaction record and yields the endpoint; pinned as
`hamilton-reaction-core-final` in `hamilton-front.json`. Everything that
remains in that core is Ricci-flow analysis proper.

Ricci-flow route, first step (2026-09-08): `deturck-principal-second-jet`
landed as a verified partial (`Global/DeTurckPrincipalSecondJet.lean`, gate
PASS, 18 declarations): the constant-family DeTurck chart rate expands to the
coordinate Ricci trace, advection and two derivative slots; the formal Ricci
and Lie second-jet expressions cancel to exactly `spatialPrincipal` for the
genuine chart metric; the Christoffel derivative is expressed in chart-metric
jets. `principalIdentity` (the rate equals the inverse-metric contraction of
the metric's second derivative plus a first-jet remainder chosen before the
metric) was then proved by the follow-up `deturck-principal-identity`
(`Global/DeTurckPrincipalIdentity.lean`, gate PASS, 50 declarations): the
witness is `lowerTerm (B z) (fderiv ℝ B z)` with `B` the background
Christoffel field, an explicit finite algebraic expression in the metric
value, its first jet, and the fixed background jets. This closes the Ricci
survey's task 2; the route's next steps are the class-B parabolic Schauder
items (tasks 3 to 6) and the class-C gauge/normalization tasks 7 and 8.

`closed-ricci-flow-normalization` landed
(`Global/ClosedRicciFlowNormalization.lean`, gate PASS, 21 declarations):
the survey's task 8. Universal regular short-time Ricci flows with joint C³
entries yield universal normalized short-time flows with the same initial
metric, through the exponential scale of the mean-scalar integral, the
strictly increasing normalized clock with its local inverse, the log chart
density derivative `-R` along the flow, a finite-slab density bound, moving
integral continuity by dominated convergence, and hence mean-scalar
continuity. The output family's own C³ regularity is not part of the
contract and is not claimed.

Ricci route status after today: tasks 1, 2, 8 of the existence survey are
landed; tasks 3 to 6 (linear parabolic Schauder solvability, finite-atlas
linear inverse, nonlinear residual estimate, smooth regularity) are the
class-B analytic core, and task 7 depends on 6. No worker is in flight.

2026-09-10: `hamilton-mean-floor-reduction` landed as a verified partial
(`Global/HamiltonMeanFloorReduction.lean`, gate PASS, 8 declarations):
normalized mean-scalar continuity on the whole forward ray (through the
pointwise normalized equation and the continuous time-variation trace, no
moving-integral differentiation), a continuous normalization primitive with
its derivative at zero, the lower profile `(ρ/2)·exp(-P t) ≤ meanScalar`
from positive initial scalar, and a positive floor on every compact
interval. It also refutes the intended residual: a bounded normalization
primitive is inconsistent with a positive mean floor on the ray (the
primitive grows at least linearly). So the floor clause of
`HamiltonReactionCore3Final` cannot be discharged by the scalar exponential
comparison alone; the S9 integrated-energy-domination route (nonnegative
mean derivative) is the remaining class-B candidate. The reaction domination
clause converts algebraically (landed
`normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination`)
from a uniform cubic pinching bound, which is itself class B.

`parabolic-schauder-decomposition-survey` landed (trimmed report; full
inventories on the retained worker branch): the linear parabolic step should
be run in a parabolic Hölder norm (`Y_T`, `X_T` with actual derivative
graphs), by constant-coefficient localization plus correction of a bounded
parametrix (Neumann series; a generic version is proved in scratch). The
repository already has the Gaussian kernel, bounded heat semigroup, BUC
semilinear existence, spatial second-derivative formulas and temporal Dini
cancellation, but no variable-coefficient estimate. First gated tasks: K1
(scaled Hessian kernel moments and cancellation, class A, dispatched as
`heat-kernel-hessian-moments`) and K2 (Duhamel Hessian sup estimate from
spatial Hölder forcing, class B, needs K1).

K1 landed (`Global/HeatKernelHessianMoments.lean`, gate PASS, 11
declarations): for `0 < α < 1` and `0 < t ≤ 1`, the Hessian of the landed
Gaussian kernel has integrable `‖x‖^α`-weighted norm with integral at most
`C t^{α/2 - 1}`, is integrable, and integrates to zero (dilation of the
bilinear Hessian formula, a Gaussian-times-power envelope, Haar scaling,
second moments). K2 (`heat-duhamel-spatial-holder-hessian`, class B) is
dispatched on top of it.

`parabolic-holder-carrier` landed (`Global/ParabolicHolderSpace.lean`,
gate PASS, 54 declarations): the parabolic Hölder space `Y α T F` on the
cylinder `Icc 0 T ×ˢ univ`, represented as a closed submodule of the
complete sum-norm product of two `lp ∞` factors (values and scaled
differences), hence `NormedAddCommGroup`, `NormedSpace ℝ`, and
`CompleteSpace` for complete `F`, with the exact norm formula
`supNorm + holderSeminorm`, the constructor `ofFunction`, pointwise and
Hölder bounds, the sharp product bound `‖f * g‖ ≤ ‖f‖ * ‖g‖` on real-valued
elements, and contractive restriction to shorter cylinders. This is the
Banach carrier for the frozen-coefficient correction and the nonlinear
fixed point of the parabolic route.

`hamilton-pinching-to-reaction-survey` landed (trimmed; full appendices on
the retained worker branch). Findings: the negative pinching reaction belongs
to the scalar-normalized quotient, not the raw cubic reaction; the landed
eigenvalue preservation degrades `ε` to `2ε − 1/3`; normalized scalar,
lower-Ricci and traceless-energy evolutions are automatic from the flow plus
joint C³ entries, but the normalized quotient predicates have no public
producer yet; S9 needs moving-integral derivatives (volume automatic, total
scalar needs closed Laplacian Stokes on the slices) and `V ≤ 6E`. A-plan:
item 1 normalized quotient evolution, item 2 forward preservation from
initial data, item 3 S9 mean floor with explicit Stokes premise (proof
compiles in scratch), item 4 a sufficient core adapter. B residuals: the
strict uniform normalization gap (for P1), `V ≤ 6E` (for P2), and a Stokes
producer. Items 1 and 3 are dispatched.

Item 3 landed (`Global/HamiltonMeanFloorFromEnergyDomination.lean`, gate
PASS, 9 declarations): the moving total-scalar and volume derivative
identities from joint C³ entries with the closed Laplacian Stokes premise
explicit, the S9 mean floor from positive initial mean and forward energy
domination `V ≤ 6E`, and the energy core `HamiltonReactionCore3Energy`
(existential floor replaced by initial mean positivity, `V ≤ 6E`, and
scalar Stokes) with its endpoint reduction; pinned as
`hamilton-reaction-core-energy` in `hamilton-front.json`.

Item 1 landed (`Global/NormalizedFlowPinchingEvolutionAutomatic.lean`,
gate PASS): the ordinary pinching quotient evolution predicate and, for
`0 < δ ≤ 1`, the traceless improvement evolution predicate are constructed
from all-time joint C³ entries, the normalized equation on the slice, and
positive scalar on the slice, at exactly the types the landed maximum
principle theorems consume; the normalization terms cancel in the ordinary
quotient and contribute a nonpositive term in the improved one. Item 2
(`normalized-flow-initial-pinching-preservation`) is dispatched.

K2 landed as a verified partial (`Global/HeatDuhamelSpatialHolderHessian.lean`,
gate PASS, 14 theorems): the Hessian of the heat convolution equals the
cancelled kernel integral `∫ (f(x−y) − f(x)) • Hess_t(y) dy` for bounded
data, the weighted majorant `K·Jα·t^{α/2−1}` with its exact time integral
`(2/α) t^{α/2}`, joint positive-time Hessian continuity, time integrability
of the cancelled integrand under cylinder continuity and spatial Hölder
control, and the double-integral bound. The remaining step is
differentiation of the Duhamel time integral in space (two measurability and
integrability branches of the dominated-derivative theorem are displayed);
the follow-up `heat-duhamel-hessian-differentiation` targets it.

Item 2 landed (`Global/NormalizedFlowInitialPinchingPreservation.lean`,
gate PASS, 5 declarations): pointwise positive scalar on every forward
slice from positive initial scalar; spatial C² of the pinching quotient from
joint C³ entries; and, from an initial eigenvalue floor `ε₀ ≤ 1/3`, the
degraded floor `2ε₀ − 1/3` and the quotient bound `1 − 4ε₀ + 6ε₀²` on every
forward slice by the landed maximum principle, plus the improved-quotient
variant for `1/6 < ε₀`. Item 4 (`hamilton-initial-pinching-reaction-core`,
the sufficient core adapter) is dispatched.

Item 4 landed (`Global/HamiltonInitialPinchingReactionCoreReduction.lean`,
gate PASS, 7 declarations): `HamiltonReactionCore3InitialPinching` replaces
the final core's mean-floor and reaction clauses by initial data (pointwise
positive scalar, an eigenvalue floor `ε ∈ (1/6, 1/3]`, an admissible `δ`)
plus three explicit residual estimates: scalar-to-mean comparison with
coefficient gap `4/3 − 2(2−δ)(1−4ε+6ε²)C > 0`, `V ≤ 6E`, and scalar Stokes
on forward slices; the `Eta` variant swaps the comparison/gap pair for a
positive normalization gap. Both reconstruct the final core with
`rate = γ · meanScalar(g₀)`; pinned as
`hamilton-reaction-core-initial-pinching` in `hamilton-front.json`.

Hamilton front after the pinching plan (2026-09-10): the analytic inputs
that remain are (a) existence of the forward normalized flow with joint C³
entries and a compact jet-continuous realization (the Ricci route), (b) the
three residual estimates above, which are Hamilton 1982 sections 10 to 17
content (scalar comparison, variance-energy domination) plus a
closed-manifold Stokes producer.

K2 completed (`Global/HeatDuhamelHessianDifferentiation.lean`, gate PASS,
21 declarations): the gradient kernel moments and convolution gradient
bound, joint continuity of the Duhamel gradient integrand, differentiation
of the Duhamel time integral in space at first and second order by the
dominated-derivative theorem, continuity of the resulting Hessian, and the
frozen `duhamel_hessian_bound`: for bounded, cylinder-continuous forcing
with spatial Hölder constant `K`, the Duhamel solution is `C²` in space, its
Hessian equals the cancelled kernel double integral, and it is bounded by
`C · K · t^{α/2}` with `C` independent of the forcing. The parabolic route's
first analytic estimate is therefore landed.

Step L0 completed (`Global/ParabolicSolutionGraph.lean`, gate PASS, 45
declarations): the solution-graph carrier `Graph α T`, whose elements are
genuine derivative graphs (value, time derivative, spatial differential and
Hessian) with zero initial trace and all four components in the landed
Hölder carrier, realized as a closed submodule of the product, hence a
complete normed space with the exact sum-norm formula, component bounds,
the mean-value time bound `‖u(t,x)‖ ≤ t‖uₜ‖`, and the `ofDerivatives`
constructor. Together with `ParametrixNeumannCorrection` (step L7, proved
directly) the algebraic scaffolding of the linear step is in place; what
remains there is quantitative (L3 to L6).

`closed-laplacian-stokes-producer` landed as a verified partial
(`Global/ClosedLaplacianStokesProducer.lean`, gate PASS, 13 declarations):
the open-chart Hausdorff measure formula and density integrability from
finite Riemannian volume, a smooth partition subordinate to the genuine
source cover, the coordinate scalar with compact support and global `C²`
regularity, continuity of the localized Laplacian, target-wise smoothness of
the density weight and inverse Gram entries, and a constructor for the
subordinate-geometry record with five explicit arguments. `ClosedLaplacianStokes g f`
unfolds to integrability of the Laplacian plus vanishing integral. The
residual is narrower than expected: globally `C¹` extensions of the
coefficient fields (they are smooth only on chart targets), the classical
divergence identity `∑ₖ ∂ₖ(w aᵏʲ) = −w aᵏˡ Γʲₖₗ`, and the identification of
the intrinsic Laplacian with its coordinate Christoffel form. The follow-up
`closed-laplacian-stokes-global-coefficients` targets exactly those three.

The spatial half of L3 landed (`Global/HeatDuhamelHessianSpatialHolder.lean`,
gate PASS, 26 declarations): the third derivative of the Gaussian kernel with
its cubic envelope, dilation and exact moment scaling; the near estimate on
the terminal interval of length `ρ²`; the far estimate by translating one
cancelled integral, integrating the third derivative along the segment and
applying Fubini; and the assembled
`duhamel_hessian_spatial_holder`, a bound `C·K·‖x−z‖^α` on the difference of
the Duhamel Hessians with `C` fixed before the time horizon and the forcing.

`closed-laplacian-stokes-global-coefficients` landed as a verified partial
(`Global/ClosedLaplacianStokesGlobalCoefficients.lean`, gate PASS, 11
theorems): a finite shrinking of the chart cover with compact coordinate
closures and a subordinate partition, simultaneous globally smooth
extensions of the density weight and inverse Gram entries agreeing with the
genuine fields near every point of those closures, the derivative formulas
for both genuine fields, and the classical divergence identity
`∑ₖ ∂ₖ(w aᵏʲ) = −w aᵏˡ Γʲₖₗ` in dimension three together with its transfer
to locally agreeing extensions. Two things remain: the identification of the
intrinsic Laplacian with its coordinate Christoffel form (the exact residual
goal is printed in the report; the bridge is
`LeviCivitaTransport.chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one`),
and a restricted-domain variant of the record constructor, since the landed
one fixes each coordinate domain to an entire chart target. The follow-up
`intrinsic-laplacian-coordinate-form` targets both.

`heat-duhamel-heat-equation` landed as a verified partial
(`Global/HeatDuhamelHeatEquation.lean`, gate PASS, 11 theorems): Mathlib's
Euclidean Laplacian equals the coordinate Hessian trace, the heat
convolution Hessian and Laplacian are integrable in forcing time, the
Laplacian of the Duhamel value is the time integral of the convolution
Laplacian, the interior time derivative is the spatial Laplacian, the
boundary limit along the diagonal is `f(t,x)`, and the value at time zero
vanishes. Exactly one general calculus lemma remains, the Leibniz rule for
an integral with a moving upper limit and a parameter-dependent integrand;
the follow-up `moving-limit-leibniz-rule` isolates it and then applies it.

The time half of L3 landed (`Global/HeatDuhamelHessianTimeHolder.lean`,
gate PASS, 25 declarations): the time derivative of the Gaussian Hessian
with its quartic envelope, weighted integrability and exact moment scaling
`t^{α/2−2}`; the tail, near and far estimates; and
`duhamel_hessian_time_holder`, a bound `C·K·|t₁−t₂|^{α/2}` on the Duhamel
Hessian difference at a fixed point. With the spatial half this gives the
full parabolic Hölder control of `D²u`, and the combination landed as
`Global/DuhamelParabolicHolderSeminorm.lean` (gate PASS):
`duhamel_hessian_parabolic_holder` bounds the Hessian difference between any
two cylinder points by `C·K·parabolicDist^α`, and
`hasHolderBound_duhamel_hessian` states it in the landed carrier's predicate.
So the Hessian half of the constant-coefficient estimate `‖u‖_X ≤ C‖f‖_Y` is
complete; what is left of L3 is the heat equation itself (blocked only on the
moving-limit Leibniz rule) and the corresponding bounds for `uₜ`, which follow
from the equation.

`moving-limit-leibniz-rule` landed both parts
(`Global/MovingLimitLeibniz.lean`, gate PASS, 12 theorems): a general
Leibniz rule for an integral whose upper limit and integrand both move,
proved from dominated clipped secants together with the fundamental theorem
of calculus on a closed interval and a family of fractional-power secant
estimates, and then the frozen `duhamel_solves_heat_equation` itself, so the
Duhamel integral provably satisfies `∂ₜu = f + Δu` within the cylinder with
zero initial value. The constant-coefficient solution is therefore fully
characterized; `duhamel-solution-operator-bound` assembles the remaining
component estimates into the bounded operator of step L3.

`intrinsic-laplacian-coordinate-form` landed both parts
(`Global/IntrinsicLaplacianCoordinateForm.lean`, gate PASS, 20 declarations):
the intrinsic gradient's chart pullback is the coordinate metric gradient,
the covariant Hessian equals `∂ᵢ∂ⱼφ̂ − Γᵏᵢⱼ ∂ₖφ̂` after removing the auxiliary
cutoff, the metric trace is the inverse-Gram contraction in the chart frame,
hence the coordinate form of the intrinsic Laplacian; then the
restricted-domain record constructor and, unconditionally,
`closedLaplacianStokes_of_contMDiff_two`: on a closed smooth three-manifold
the Laplacian of any `C²` scalar is integrable with zero integral, plus the
forward-flow corollary for scalar curvature.

Consequently the orchestrator landed `Global/HamiltonStokesFreeReactionCore.lean`
(gate PASS): the Stokes clause is deleted from the initial-pinching core,
since it follows from the flow and joint `C³` clauses already present.
Pinned as `hamilton-reaction-core-stokes-free`. **Two residual estimates now
remain in front of the Hamilton endpoint**: the scalar-to-mean comparison
with its coefficient gap, and the variance-energy domination `V ≤ 6E`.

Step L3 completed (`Global/DuhamelSolutionOperatorBound.lean`, gate PASS,
15 theorems): sup and parabolic Hölder bounds for the time derivative
(through the equation and the Hessian bounds), the gradient (sup bound
`2MC₁√t`, spatial Hölder by bounded-Lipschitz interpolation, time Hölder by
reversing the Duhamel time integral), and the value; then
`exists_solution_graph_bound`: for `0 < α < 1` there is `C` such that for
every `0 < T ≤ 1` and every forcing `f` in the Hölder carrier, the Duhamel
solution is a solution graph `G` with `‖G‖ ≤ C‖f‖`. The constant-coefficient
inverse of the parabolic route is therefore bounded from `Y α T` into
`Graph α T` with a constant uniform in `T ≤ 1`.

2026-09-15 design review (GPT Astra, conversational; full record in
`harness/reports/astra-design-review-2026-09-15.md`): (1) build the
parametrix on the finite atlas of `M` as finite products of the landed
scalar carriers, dropping the whole-space step L6; (2) the nonlinear step
needs the reference family `g₀ + t Q(g₀)` with a quantitative bound on the
residual's time derivative, and the zero-trace interpolation controls only
the product term; (3) **correction**: the clause `V ≤ 6E` carried by the
energy and initial-pinching cores is not implied by pinching (the
almost-Schur constant is 24 in dimension three, and near-round metrics reach
ratio about 15), so the S9 mean-floor route is a dead end as parametrized;
the mean floor must come from Hamilton's scalar oscillation control, whose
first lemma is the normalized `|∇R|²` evolution identity. The mission node
`hamilton-reaction-core-energy` remains a valid conditional reduction but
should not be treated as a discharge target; the residual survey in flight
decides the restructuring.

`duhamel-solution-operator-clm` landed (`Global/DuhamelSolutionOperatorCLM.lean`,
gate PASS, 12 declarations): graphs are determined by their value component
(`Graph.ext_of_u`, by uniqueness of the Fréchet and interval derivatives),
the Duhamel construction is linear, and `duhamelOperator : Y α T ℝ →L[ℝ] Graph α T`
carries the uniform norm bound and satisfies the heat equation on the
cylinder. This is the exact shape `ParametrixNeumannCorrection` consumes.

The L5 multiplier estimate landed (`Global/ParabolicHolderMultiplier.lean`,
gate PASS, 20 declarations): a solution graph has vanishing gradient and
Hessian at time zero, hence the zero-trace interpolation
`supNorm ddu ≤ T^{α/2}‖G‖`; coordinate entries of a `Bilin`-valued carrier
element are carrier elements with the split product bound
`‖b·h‖ ≤ sup b·‖h‖ + [b]_α·sup h`; the nine-entry forcing
`Σᵢⱼ bᵢⱼ·∂ᵢ∂ⱼu` is a carrier element with
`‖F‖ ≤ 9(ε + Λ T^{α/2})‖G‖` when the coefficients have sup at most `ε` and
Hölder seminorm at most `Λ`; and the error smallness `‖R f‖ ≤ ½‖f‖` under
`9C_Sε ≤ 1/4`, `9C_SΛT^{α/2} ≤ 1/4`. This is the smallness mechanism for
the frozen-coefficient correction.

`hamilton-residual-estimates-survey` landed (trimmed; full appendices on
the retained worker branch), and it agrees with the design review on the
key point: `V ≤ 6E` is precisely the nonnegative-mean-derivative condition
in dimension three, not the almost-Schur inequality (whose sharp constant
under `Ric ≥ 0` is 24), so no producer from pinching should be attempted.
The scalar comparison R1 on the historical route needs three class-B
inputs: the scale-effective Bernstein scalar-gradient estimate on the
unnormalized pinched flow, the blow-up/rescaling transfer, and
gradient-to-global-oscillation under positive pinching; a tail comparison
also does not give the all-ray coefficient gap, and the preserved quotient
constant can leave zero gap at feasible parameters. The strongest reduction
found: the single uniform normalization gap
`2(2−δ)N/R + η ≤ (4/3)r` (the `Eta` residual) supplies the mean floor
`3η/4` by itself and the reaction rate `η` through the landed direct-gap
theorem, so it closes the unchanged final core alone (compiled in scratch,
Appendix C6). Dispatched as `hamilton-eta-core-reduction`. Thirteen
candidate child obligations with exact elaborated expressions are listed in
its section 4.9 for future registration.

`near-identity-parabolic-right-inverse` landed
(`Global/NearIdentityParabolicRightInverse.lean`, gate PASS, 21
declarations): the nine-entry forcing is linear in the graph, giving the
multiplier `Graph →L Y` with bound `9(ε + ΛT^{α/2})`; the error operator
`R = multiplier ∘ duhamelOperator` has `‖R‖ ≤ 1/2` under the quarter-size
conditions; and `nearIdentityInverse = duhamelOperator ∘ (1 − R)⁻¹` solves
`∂ₜu = f + Σᵢⱼ (δᵢⱼ + bᵢⱼ) ∂ᵢ∂ⱼu` on the closed cylinder with
`‖G‖ ≤ 2C_S‖f‖`. This is the first variable-coefficient parabolic
solvability theorem in the repository: Hölder coefficients close to the
identity on a short cylinder. With L4 (in flight) the same holds near any
fixed positive-definite matrix; the finite-atlas parametrix is the
remaining linear step.

Step L4 landed (`Global/FrozenEllipticHeatOperator.lean`, gate PASS, 28
declarations): transport of Hölder elements and solution graphs through a
linear change of variables with explicit norm factors, the trace identity
under the change, recovery of the heat equation from the Duhamel value
formula, the symmetric positive square root of a positive-definite
coefficient form (Mathlib's `CFC.sqrt` on `Matrix (Fin 3) (Fin 3) ℝ`,
transported to a continuous linear equivalence) with `‖S‖ ≤ √Λ`,
`‖S⁻¹‖ ≤ 1/√λ`, and `exists_frozen_solution_graph_bound`: for any symmetric
`A` with `λ‖v‖² ≤ A v v ≤ Λ‖v‖²`, every forcing has a solution graph of
`∂ₜu = f + Σᵢⱼ A(eᵢ,eⱼ)∂ᵢ∂ⱼu` with `‖G‖ ≤ C(α,λ,Λ)‖f‖`, uniformly in
`T ≤ 1`. Combined with the near-identity correction this gives solvability
near any fixed elliptic coefficient matrix.

`hamilton-eta-core-reduction` landed (`Global/HamiltonEtaCoreReduction.lean`,
gate PASS, 6 declarations): `meanFloorFromEta` (the Eta gap at one point of
a positive-scalar slice gives `r ≥ 3η/4`), the core `HamiltonReactionCore3Eta`
(the pinned Stokes-free core with the scalar-to-mean comparison, its
coefficient gap, and the variance-energy clause all deleted and the single
existential Eta gap added), and its reductions to the final core (witnesses
`c = 3η/4`, `rate = η`), the endpoint, and universal Hamilton convergence.
Pinned as `hamilton-reaction-core-eta`; the energy and Stokes-free nodes are
annotated as superseded discharge targets. **The Hamilton boundary is now:
existence of the forward normalized flow with joint C³ entries and a
compact jet-continuous realization, initial pinching data, and one uniform
analytic estimate, the normalization gap `2(2−δ)N/R + η ≤ (4/3)r`.**

`near-frozen-parabolic-right-inverse` landed
(`Global/NearFrozenParabolicRightInverse.lean`, gate PASS, 13 declarations):
the frozen elliptic inverse as a continuous linear operator with a bound by
ellipticity, its Neumann correction for small Hölder perturbations, and
`exists_nearFrozen_solution` / `exists_nearFrozen_operator`: with constants
`C, ε₀, τ₀` chosen before the coefficient form, the time horizon, the
perturbation, and the forcing, every `∂ₜu = f + Σ(A₀ + b)ᵢⱼ∂ᵢ∂ⱼu` with
`sup|b| ≤ ε₀` and `[b]_α T^{α/2} ≤ ε₀` on `T ≤ τ₀` has a solution graph with
`‖G‖ ≤ C‖f‖`. This is the chart-level local solver of the finite-atlas
parametrix.

`finite-atlas-parametrix-survey` landed (trimmed): the finite-atlas route
closes in the landed unweighted graph norm PROVIDED one new analytic lemma,
full lower-derivative Hölder interpolation
`‖u‖_Y ≤ C_I T^{1−α/2}‖G‖`, `‖Du‖_Y ≤ C_I T^{(1−α)/2}‖G‖`, with an
elementary route through a finite-difference derivative estimate; the
commutator terms then carry the factor `T^{(1−α)/2}`, the error estimate is
`‖R‖ ≤ C₀C_Sω(ρ) + C_ρC_S(Λ_ρT^{α/2} + T^{(1−α)/2})`, and a geometric gate
remains (controlled refinement with bounded neighbour count so `C₀` stays
controlled while `ρ → 0`). Its three gated tasks: the compatible tensor
carriers on the finite atlas, the interpolation plus cutoff commutator, and
the buffered frozen solver with the oscillation extension. The first two are
dispatched.

Finite-atlas task 1 landed (`Global/FiniteAtlasParabolicTensorSpace.lean`,
gate PASS, 84 declarations): the compatible forcing and zero-trace solution
carriers `Y_M`, `X_M` for symmetric 2-tensor fields on the finite shrunk
atlas, as closed submodules (support, symmetry and the weighted overlap law
are intersections of continuous linear kernels) of finite products of the
landed scalar carriers, hence complete normed spaces with the inherited
norm; the record/submodule equivalence, entry bounds, the expanded
transition equation, and compactness of the coordinate supports.

`scalar-gradient-evolution-identity` landed as a verified partial
(`Global/ScalarGradientEvolution.lean`, gate PASS, 7 theorems): the moving
covector and gradient norm variation with the inverse metric, the manifold
mixed-partial interchange, and the time derivative of `S = |∇R|²` along the
normalized flow with explicit extra scalar regularity,
`∂ₜS = 2⟨∇R,∇ΔR⟩ + 4⟨∇R,∇N⟩ + 2Ric(∇R,∇R) − 2rS` (the design review's
displayed form omitted the Ricci term; this is the verified one), plus the
Bochner identity for the blended chart metric with intrinsic Ricci at the
anchor and the intrinsic Laplacian expansion for chart-supported `C²`
scalars. Two residuals remain: transporting Bochner from the blended chart
metric to the intrinsic one (to turn `2⟨∇R,∇ΔR⟩ + 2Ric(∇R,∇R)` into
`ΔS − 2|∇²R|²`), and a joint `C⁴` regularity producer for the third
spatial derivative of `R` along the flow.

Finite-atlas task 2 landed (`Global/ParabolicCutoffCommutator.lean`, gate
PASS, 52 declarations): the quadratic remainder and finite-difference
derivative estimate `|Dh·v| ≤ 2A/η + (η/2)B`; the full lower-derivative
interpolation for solution graphs, `‖u‖_Y ≤ 12·T^{1−α/2}‖G‖` and
`‖Du‖_Y ≤ 12·T^{(1−α)/2}‖G‖` (the key new analytic lemma of the finite-atlas
route); the cutoff product graph and its bounded linear operator; and the
commutator identity with the first-order forcing bound
`‖[L,ψ]G‖ ≤ 24·(Σ‖bᵢ‖·T^{(1−α)/2} + ‖c‖·T^{1−α/2})‖G‖`. The commutator
terms of the parametrix now carry positive time powers as required.

Contract change (2026-09-15, user-approved; `harness/worker_contract.md`
section "Contract update"): one module per chain (follow-ups append, never
alter existing declarations), fully qualified names only, catalog search
before surveying (`harness/v2/catalog/campaign-2026-09-15.json`), the
dispatch script exports `DEVELOPER_DIR` for the Xcode git shim, and
consolidation tasks are allowed once a chain completes. Queued: consolidate
the constant-coefficient Duhamel chain at the next window with no parabolic
worker in flight.

`intrinsic-bochner-scalar-gradient` landed (`Global/IntrinsicBochnerScalarGradient.lean`,
gate PASS, 38 declarations; the first attempt died on a provider capacity
error after committing the Bochner identity, the second finished): the
intrinsic Bochner formula `Δ|∇f|² = 2|∇²f|² + 2⟨∇f,∇Δf⟩ + 2Ric(∇f,∇f)`
for `C³` scalars by chart localization; the joint regularity ladder (joint
`C^{k+1}` entries give `C^k` Christoffel fields, `C^{k+2}` entries give
`C^k` curvature and scalar curvature); and
`SatisfiesScalarGradientEvolutionAt` proved along the normalized flow from
joint `C⁵` metric entries. Step one of Hamilton's gradient route is
complete; the next is the evolution inequality for Hamilton's auxiliary
quantity `F = |∇R|²/R − ηR² + 168(N − R²/3)`.

`buffered-frozen-parabolic-solver` landed as a verified partial
(`Global/BufferedFrozenParabolicSolver.lean`, gate PASS, 43 declarations):
the coefficient extension by a smooth cutoff with sup bound `ω(ρ)` and a
single Hölder constant for all short times, `ω(ρ) → 0`, ellipticity of the
inverse metric, and the chart frozen operator. Item 3 is blocked by a genuine
finding: with ONE cutoff serving both the coefficient extension and the
solution product, the required cancellation is false on the annulus where
the cutoff is strictly between 0 and 1. The fix is the survey's buffered
design with nested cutoffs (outer `ξ = 1` on the support of the inner `ψ`),
dispatched as a follow-up that appends to the same module.

Catalog: the registry `snapshot` export is unusable at this scale (one
batch timed out on heartbeats, another produced a 4.9 GB file); replaced by
the grep index `harness/v2/catalog/declarations-global.tsv`, regenerated at
each landing, and the contract's search rule now points there.

`hamilton-auxiliary-quantity-evolution` landed as a verified partial
(`Global/HamiltonScalarGradientEstimate.lean`, gate PASS, 9 declarations,
the new Hamilton gradient-estimate chain module): the intrinsic quotient
rules for the heat operator `D = ∂ₜ − Δ`, the normalized evolution of the
quotient `Q = |∇R|²/R`
(`DQ = −2|∇²R|²/R + 4⟨∇R,∇N⟩/R − 2SN/R² − (4/3)rQ + 2⟨∇R,∇S⟩/R² − 2S²/R³`),
and the traceless-energy evolution bounded by its cubic reaction. Blocked
on strict derivative-energy damping: the landed `|∇R|² ≤ 3|∇Ric|²` yields
no strictly negative `|∇Ric|²` coefficient in the `U` evolution, so the
`|∇Ric|²` terms of Hamilton's combination cannot yet be cancelled; the
sharper contracted-Bianchi bound behind Hamilton's `2/21` is the exact
missing estimate (see the report's section 2).

`buffered-frozen-nested-cutoff` landed, the first task under the
append-to-chain contract (`Global/BufferedFrozenParabolicSolver.lean` grew
from 506 to 1039 lines with the original lines unchanged; gate PASS, 66
declarations): nested cutoffs (inner `ψ = 1` near the coordinate support,
outer `ξ = 1` on the inner support), exact coefficient agreement
`A₀ + b = a` on the inner support, the residual identity
`L_chart(ψ·Sf) − f = [L_chart, ψ](Sf)`, the genuine commutator carriers with
a uniform cutoff bound, and the single-chart estimate
`‖L_chart(ψ·Sf) − f‖_Y ≤ C_ψ·(T^{(1−α)/2} + T^{1−α/2})·‖f‖_Y` plus solver
existence. With nested cutoffs the oscillation `ω(ρ)` no longer appears in
the error; it only enters the existence condition of the near-frozen solver.
The single-chart local solver of the finite-atlas parametrix is complete.

Worker policy used for tasks 13 to 19: codex `gpt-6-astra`, reasoning effort
chosen by difficulty (all seven ran at `high`), `harness/dispatch_codex.sh
<task> <taskfile> <effort>`; tasks 16 and 17 ran in parallel because 17
imports only task 15. Liveness from the Bash tool must use `/bin/ps` (the rtk
hook filters bare `ps`).


## 2026-09-08 Mapped geodesic assembly worker result

Branch `worker/mapped-geodesic-assembly`, base `cead6503`, verified proof
head `2023d14b`. The one new `FixedChartMappedGeodesicAssembly.lean` proves
all four frozen targets. The mapped-geodesic and endpoint-reanchoring
producers are in `FixedChartUniformEndpointReanchoring`; `exists_onCompact`
and the exact task-9 `exists_radii` are in `FixedChartLocalSuccessorEquality`.

C2 regularity transfers from the retained endpoints through the actual
supplied inverse. It discharges the uniform Christoffel transition law.
The actual datum determines the mapped initial velocity, and compactness
gives full-time trajectory displacement control. The normalized geodesic
solves the target initial-value problem on all of `[0,1]`. Both radii precede
all moving parameters; the final H2 includes full-ball source containment
and equality for every datum, together with H1 at the same predecessor radius.

All ten public theorems passed direct Lean and were committed separately.
The focused build passed with 3616 jobs; four signature probes passed.
All twelve theorem closures, including private helpers, are exactly
`[propext, Classical.choice, Quot.sound]`. Token and diff checks pass.
No existing Lean file or root import changed. Commands, actual output,
compiler retries, and the proof commits are recorded in
`harness/reports/mapped-geodesic-assembly_done.md`.

This result awaits independent orchestrator review and import integration.
Global recognition and the Poincare endpoint are not asserted here.
Exact first independent review action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartMappedGeodesicAssembly.lean`.


## 2026-09-08 Augmented system full-time regularity worker result

Branch `worker/augmented-system-regularity`, base `2992f59d`, verified proof
head `3347f3e5`. The new `FixedChartAugmentedSystemRegularity.lean` proves
`augmentedSystemRegularity` with the unchanged imported definition and
`patch_endpoint_contDiffOn_two` on the original retained ball at `C.T`.
The full-interval fundamental-solution continuation, Gronwall derivative
identification, and operator-norm continuity give a general full-time C1
flow theorem. Compact neighborhoods inside the open augmented initial-state
domain cover the entire retained ball, without shortening its time interval.

All five theorems compiled and were committed separately. The focused build
passed with 3615 jobs. The module scan reports five declarations with no
nonstandard dependencies; every named closure is exactly
`[propext, Classical.choice, Quot.sound]`. Both exact target probes and token
and diff checks pass. No existing Lean file or root import changed.
The report `harness/reports/augmented-system-regularity_done.md` records the
commands, actual outputs, failed compiler attempt, and proof commits.
This result awaits independent orchestrator review. The mapped-geodesic
equation, H1/H2, and recognition remain separate work.

Exact first independent review action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartAugmentedSystemRegularity.lean`.


## 2026-09-08 Patch second variation worker partial

Branch `worker/patch-second-variation`, base `d1a10d37`, verified proof head
`f13ece96`. The new `FixedChartPatchSecondVariation.lean` proves C2 regularity
of the operator-valued augmented field and genuine C2 initial-state
dependence of the retained patch flow on the ball of radius `C.r / 2` for
all times in one common `[-τ,τ]`, with `0 < τ ≤ C.T`.

The retained endpoint time `C.T` is not reached by that theorem. One exact
remainder, `AugmentedSystemRegularity C`, asks for the actual augmented
solution and C1 endpoint dependence on the original time interval and open
state ball. Its checked `target_of_augmentedSystemRegularity` theorem gives
the step-1 C2 endpoint assertion. It does not give the frozen mapped-geodesic
target; that theorem and its three unconditional consequences remain absent.

Six theorems passed direct Lean and were committed individually. The focused
3614-job build passed. All six theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; the module scan found no nonstandard
dependencies. Token and diff checks passed. No existing Lean file or root
import changed. Commands, actual output, failed compiler logs, and the exact
remainder are in `harness/reports/patch-second-variation_blocked.md`.
This worker result awaits independent review.

Exact first independent review action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartPatchSecondVariation.lean`.


## 2026-09-08 Uniform endpoint reanchoring worker partial

Branch `worker/uniform-endpoint-reanchoring`, base `5baf6aa8`, verified
proof head `ff760da6`. The new `FixedChartUniformEndpointReanchoring.lean`
proves uniform host-coordinate metric-pullback germs and a signed diagonal
Christoffel law conditional on differentiability of the actual derivative.
It also proves the corresponding chain rule, retained-flow time normalization,
full-interval uniqueness, and compactly uniform endpoint displacement.

One concrete remainder, `UniformMappedGeodesicEquation`, suffices for the
exact endpoint target and the conditional H2 and H1+H2 consequences. Its
producer remains open. Supplied-map derivative regularity, uniform trajectory
retention in the transition neighborhood, and the actual successor initial
velocity identity have not been discharged. No unconditional target name
was introduced.

All 11 public theorems passed direct Lean and were committed separately.
The focused build passed with 3613 jobs; the scan reports 12 public declarations
with no nonstandard dependencies. All named closures are exactly
`[propext, Classical.choice, Quot.sound]`. Token and diff checks pass.
No existing Lean file or root import changed. Commands, outputs, retries,
proof commits, and the exact remainder are recorded in
`harness/reports/uniform-endpoint-reanchoring_blocked.md`.
This worker result awaits independent review.

Exact first independent review action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformEndpointReanchoring.lean`.


## 2026-09-08 Supplied source germ transfer worker result

Branch `worker/supplied-source-germ-transfer`, base `ae6ce9f4`, verified proof
head `7a8ba3ae`. The new `CartanSuppliedSourceGermTransfer.lean` proves all
three frozen targets: normal agreement transfers to Cartan germ agreement,
inverse normal agreement near zero, and agreement on an open common source.
The inverse proof uses continuity and both partial inverse laws on their
domains, without an extra neighborhood premise.

Direct Lean, the focused 3359-job build, all three exact name probes, and the
module-wide scan pass. Each theorem closure is exactly
`[propext, Classical.choice, Quot.sound]`. Token and diff checks pass.
No existing Lean file or root import changed. The report
`harness/reports/supplied-source-germ-transfer_done.md` records commands,
outputs, three proof commits, the compiler retry, and the verified proof diff.
This worker result awaits independent review. H1/H2 and recognition remain
separate work.

Exact first review action:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceGermTransfer.lean`.

## 2026-09-08 Fixed-chart uniform source normal worker result

Branch `worker/fixed-chart-uniform-source-normal`, base `0218a202`, proof head
`26efa2d4`. The new `FixedChartUniformSourceNormal.lean` constructs the exact
retained flow `Patch`, including the unchanged compact `K,R,ρ` clause, from
the uniform normal-neighborhood theorem. Task 3's product slices, time
rescaling, and the inverse fixed manifold chart give normal partial
homeomorphisms with both anchor laws. The joint inverse source is open and
its evaluator is continuous; `rawLocalFamily` has exactly those anchors,
sources, and normal vectors. Position control is retained on endpoint sources.

Direct elaboration, the focused 3548-job build, and the exact-field probes
pass. All 16 theorem closures are exactly `[propext, Classical.choice, Quot.sound]`;
the module-wide scan checks 64 declarations with only permitted dependencies.
Token and diff checks pass. No existing Lean file or root import changed.
The worker result awaits independent orchestrator acceptance. Commands,
outputs, failed compiler evidence, and the proof diff are recorded in
`harness/reports/fixed-chart-uniform-source-normal_done.md`.

Exact first review action:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformSourceNormal`.
The next mathematical task is inventory task 5's fixed-anchor frame/germ
comparison. H1/H2 and recognition remain separate work.


## 2026-09-08 Fixed-chart endpoint slices worker result

Branch `worker/fixed-chart-endpoint-slices`, base `5f57f9b6`, proof head
`853f4b50`. The new `FixedChartEndpointSlices.lean` constructs exact vertical
partial homeomorphism slices, deriving inverse anchor preservation from the
source hypothesis and right inverse law. Both zero laws and all four joint
openness/continuity laws compile. The focused build passes with 915 jobs;
the exact-field probes pass and all 16 scanned declarations have only permitted
dependencies. Every named closure is exactly `[propext, Classical.choice, Quot.sound]`.

No existing Lean file or root import changed. The result awaits orchestrator
review. Commands, output, failed compiler evidence, and the proof diff are in
`harness/reports/fixed-chart-endpoint-slices_done.md`. Geodesic patch construction,
H1/H2, and recognition remain separate work.

Exact first review action:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartEndpointSlices`.
## 2026-09-08 Supplied source map worker result

Branch `worker/supplied-source-map`, base
`5f57f9b6085a0037461b703f79778e69fe638aad`, proof head `1d1480cd`.
The new `CartanSuppliedSourceMap.lean` defines the supplied source/target germ
and proves `anchor_mem_source`, `germ_anchor`, `germ_apply`, and
`generic_map_eq`. The source and target anchor laws suffice without extra
hypotheses. The generic comparison is equality of forward maps.

Direct Lean, the focused 3358-job build, all four exact name probes, the
module-wide scan, and token/diff checks pass. All four theorem closures are
exactly `[propext, Classical.choice, Quot.sound]`. A bare-reflexivity attempt
hit a kernel timeout; rewriting through the existing map formulas passed.
The report `harness/reports/supplied-source-map_done.md` preserves the output
and four proof commits. No existing Lean file or root import changed.
This result awaits orchestrator review and does not prove H1/H2 or recognition.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedSourceMap.lean`.



## 2026-09-08 Fixed-chart uniform normal radius worker result

Branch `worker/uniform-normal-radius`, base `41cfdfd2`, verified proof head
`2cb7348e`. The new `FixedChartUniformNormalRadius.lean` proves the
zero-velocity flow and full fundamental solution, the triangular joint
anchor/endpoint derivative, strict differentiability, joint inverse
neighborhoods, and compactly uniform injectivity and coverage radii.
The final existence theorem instantiates the repository's exact uniform
fixed-chart PL selector and retains the prescribed position neighborhood.

For every compact anchor set inside that flow's open initial-position ball
and every prescribed velocity bound `R > 0`, one `ρ > 0` gives injectivity
on `ball 0 ρ` and coverage of `ball z ρ` by velocities in `ball 0 R` at every
anchor. The inverse neighborhoods stay inside the original state ball.

Direct Lean and the focused 3259-job build pass. All 11 theorem closures are
exactly `[propext, Classical.choice, Quot.sound]`; the module-wide scan checks
19 declarations with no nonstandard dependencies. Token and diff checks pass.
No existing Lean file or root import changed. Commands, proof commits, and
failed compiler evidence are in `harness/reports/uniform-normal-radius_done.md`.
This worker result awaits orchestrator review.

The construction makes no identification with the old `expAt`. The exponential
family, H1/H2, and sphere recognition remain separate work.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformNormalRadius`.


## 2026-09-08 Joint geodesic initial-state derivative worker result

Branch `worker/geodesic-position-derivative`, base
`1e8df02f77da1b7e8879839991ad75c259f82301`, verified proof head `de042d58`.
The new `GeodesicFlowJointDerivative.lean` proves the frozen joint
initial-position/initial-velocity `HasFDerivAt` theorem under local C2
Christoffel regularity in finite-dimensional charts. It constructs the full
operator-valued fundamental solution on one common interval, proves joint
operator-norm continuity and C1 endpoints, and instantiates the exact
variable-initial-state continuous PL package while retaining its prescribed
position neighborhood.

Direct Lean and the focused 3258-job build pass. All 14 theorem closures are
exactly `[propext, Classical.choice, Quot.sound]`; the module-wide scan checks
15 declarations with no nonstandard dependencies. Token and diff checks pass.
No existing Lean file or root import changed. The report and failed compiler
evidence are recorded in `harness/reports/geodesic-position-derivative_done.md`.
This worker result awaits orchestrator review.

The optional explicit differential of the position endpoint at zero velocity
is not proved. The joint inverse-function construction, a new exponential
family, H1/H2, and sphere recognition remain separate work.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.GeodesicFlowJointDerivative`.
The next mathematical action is the differential of
`(z,v) ↦ (z, (α (z,v) T).1)` at `(z,0)`.


## 2026-09-08 Connection naturality worker result

Branch `worker/connection-naturality`, base `0af3ddc6008aa53120b04d91a1caea455e89b4ae`,
verified proof head `487a4158`. The new
`ConnectionInstanceNaturality.lean` discharges both clauses of
`CurvatureInstanceTransport.ConnectionCurvatureNaturality` without `hN`.
Scalar derivatives and Lie brackets transform by the geometric identification;
Leibniz, metric compatibility, zero torsion, and Levi-Civita uniqueness give
connection naturality. Local regularity, germ locality, and curvature
tensoriality give curvature values on the canonical extensions.

The controlled-instance sphere-recognition reduction and its compatible-metric
existential form now have no naturality premise. Recognition on the controlled
instance remains an input. This result does not prove sphere recognition or
the Poincare conjecture.

Direct Lean, the focused 3072-job build, the three exact-signature probes,
and diff/token checks pass. All 20 declaration closures are exactly
`[propext, Classical.choice, Quot.sound]`. No existing Lean file or root
import changed. Commands, outputs, proof commits, and evidence paths are in
`harness/reports/connection-naturality_done.md`. This worker result awaits
orchestrator review.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.ConnectionInstanceNaturality`.

## 2026-09-08 Curvature transport worker partial

Branch `worker/curvature-transport`, base `99419b12559e2f220d868c56983a26cc10716603`,
proof head `330e7f07`. `CurvatureInstanceTransport.lean` proves inverse-J
transport of tangent-section Cn regularity in both directions for every
`n ≤ ∞`, pointwise differentiability transport, and additivity of the raw
conjugated Levi-Civita operator. These results have no naturality premise.

Connection bundling, compatibility, torsion, curvature transport, and the
controlled-instance sphere-recognition reductions retain the explicit
`ConnectionCurvatureNaturality` premise. Its pointwise connection and
curvature-tensor identities are both unproved. The result does not supply
unconditional curvature transport or sphere recognition.

Direct elaboration and the focused 3071-job build pass. All 23 declaration
closures are exactly `[propext, Classical.choice, Quot.sound]`; token and diff
checks pass. No existing Lean file or root import changed. This worker result
awaits orchestrator review. Commands, failed attempts, and commits are in
`harness/reports/curvature-transport_blocked.md`.

Exact first action for independent review:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.CurvatureInstanceTransport`.
The next mathematical action is the cross-instance scalar exterior-derivative
chain rule stated in the report, needed for the raw conjugated Leibniz law.

## 2026-09-08 Cached audit payload wiring

Worker branch `worker/audit-payload-wiring`, base `7acd90a8`, now builds the
fixed payloads in `audit/PoincareAudit` from the four Lean-heavy audit scripts.
The generated parser checks and reserved-theorem probe remain live. Token
coverage reads each audit's own modules, including two preserved comment-only
semantic markers. The legacy-revision equivalence check passes.

Same-tree old/new comparison preserved all 112 axiom, 979 root-import, 124
semantic, and 13,397 completion result/header lines and every exit code.
Status generation fell from 448.222 s to 296.975 s in single warm-cache runs.
Both snapshots record `reserved theorem absent only`; `CURRENT_STATUS.md`
was restored and is not part of this change. All 55 script tests and 66 runtime
tests passed. Renaming one checked theorem in a scratch copy made the cached
root-import audit fail; restoring it made the target build pass again.

No proof source changed and no merge or acceptance was performed. Full
commands, timings, retained live checks, and fault evidence are in
`harness/reports/audit-payload-wiring_done.md` and its evidence archive.

Exact first action: review the worker diff from `7acd90a8`, then independently
run `python3 scripts/audit_payload_equivalence.py --check` before integration.


## 2026-09-07 Geometric metric transport worker result

Branch `worker/metric-transport-2`, base
`80fcfacea10aa364aa7bd9d3e7670b136a4f57fb`, verified proof head `51df193e`.
The new `RiemannianMetricInstanceTransportGeometric.lean` constructs `J` as
an invertible new-to-old chart derivative, proves the tangent and hom-bundle
coefficient bridges, transfers smoothness across compatible chart instances,
and constructs `transport` with the frozen geometric `transport_inner`
formula. The smoothness field is proved, not assumed. This supersedes the
previous metric worker's open geometric transport action below.

Direct elaboration and the focused 2704-job build pass. All 28 new declaration
closures are exactly `[propext, Classical.choice, Quot.sound]`; forbidden-token
and diff checks pass. No existing Lean file or root import was edited.
The result awaits orchestrator review. Actual output and proof commits are in
`harness/reports/metric-transport-2_done.md`.

The optional induced-distance equality is not proved; its exact remaining
shape is `RiemannianMetricInstanceTransportGeometric.InducedDistanceAgreement`.
A separately bundled fiber `LinearIsometryEquiv` is also not supplied.

Exact first action for independent review against the recorded base:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.RiemannianMetricInstanceTransportGeometric`.


## 2026-09-07 Metric transport worker obstruction

Branch `worker/metric-transport`, base
`7e955466b24a22af0873a73f20a3b00d7e8f05b9`, proof commit `c9eb952c`.
The new `RiemannianMetricInstanceTransport.inner_trivialization_apply`
theorem computes metric coefficients using the derivative from the fixed
anchor chart to the moving preferred chart, in both arguments. Direct
elaboration, the focused 2702-job build, forbidden-token scan, and diff
check pass. Its axiom closure is `[propext, Classical.choice, Quot.sound]`.
No existing Lean file or root import was changed.

The frozen transport preserving raw `inner` values is mathematically false.
Choosing the identity chart at zero and the global doubling chart elsewhere
on `ClosedSmoothModel 3` preserves the maximal atlas, but an unchanged
Euclidean bilinear form has coefficients `g` at zero and `4g` elsewhere in
the fixed identity-chart trivialization. The coordinate formula is verified
in Lean; the concrete counterexample has not been fully instantiated in
Lean. The worker stops under the invalid-statement rule and awaits review.
See `harness/reports/metric-transport_blocked.md` for actual command output.

Exact first action: revise the frozen `transport_inner` target to pull back
both metric arguments by the derivative from the new preferred chart to
the old preferred chart. Then prove the tangent-trivialization intertwining
law for that geometric identification.

## 2026-09-07 Controlled preferred-chart worker result

Branch `worker/controlled-chart-instance`, recorded base `c7338a642d2cf5bf3044f1ed5ca1a90bb86cf075`,
proof head `df7b3ed3`. This worker result awaits orchestrator review.
`Poincare/Global/ControlledChartInstance.lean` proves existence of a finite
atlas of original smooth charts whose preferred sources contain one positive
uniform metric ball. It proves equality of the old and new maximal atlases,
the fixed-endpoint source-neighborhood property, and scalar `ContMDiff`
equivalence for every `n ≤ ∞`. The compatible-metric theorem explicitly uses
`d.toUniformSpace.toTopologicalSpace = t` and `d.replaceTopology hd.symm` to
preserve the original topology.

The focused build completed successfully with 2702 jobs. Direct elaboration,
the frozen-target and scalar-equivalence probes, and `git diff --check`
passed. All nine theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; the forbidden-token scan is empty.
No existing Lean file or root import was edited. Details and actual compiler
output are in `harness/reports/controlled-chart-instance_done.md`.
This does not prove generic exponential joint regularity, H1/H2, or metric
and curvature transport. Those remain separate mathematical tasks.

Exact first action for independent review, after applying the worker commits
against the recorded base:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.ControlledChartInstance`.
The next mathematical task is `ClosedSmoothRiemannianMetric` transport across
the compatible instances, using the new scalar smoothness transport lemma.

## 2026-09-07 M5-glob-69 worker obstruction

Worker branch `worker/M5-glob-69`, base `d08f4a52`, proof commits `df566640`
and `8d1b76a7`. This is a worker result awaiting orchestrator review.
The frozen curvature-only successor-equality persistence theorem was not
proved or changed. The new module `SuccessorEqualityRadiusPersistence.lean`
proves that even a positive admissible radius at fixed `(x,p)` forces every
nearby total preferred chart to be injective on one common neighborhood.
It also proves that constant total extensions outside chart balls shrinking
toward a nonisolated anchor produce collisions, and that such collisions
exclude the frozen persistence conclusion under constant curvature.

The concern is equality of total partial-homeomorphism coercions outside
their sources. The allowed chart choices do not impose a common neighborhood
of injectivity there. A recharted round-sphere counterexample is described
in `harness/reports/M5-glob-69_blocked.md`, but its metric and curvature have
not been instantiated in Lean. The verified result is a conditional
obstruction, not a complete Lean refutation or a proof of H2.

The new module passed direct Lean elaboration and the focused `lake build`
with 3579 jobs. All six new theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; forbidden-token scans are empty.
No existing Lean file, root import, mission, task, or ledger was changed.

Exact first action: instantiate the report's shrinking preferred charts on
the round sphere, then apply
`SuccessorEqualityRadiusPersistence.preferredChartCollisionAccumulation_of_shrinking_constant_extensions`
and
`SuccessorEqualityRadiusPersistence.not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation`.
Review the frozen statement before resuming source/target flow-uniformity work.

## 2026-09-07 Validation refactor

Branch `worker/audit-loops`, merged to `main` after the checks below. The
scaffold audits were the validation bottleneck: `root_import_audit.sh` and
`axiom_audit.sh` rescanned all 23,309 harvested theorem names once per
route check and spawned one `rg` process per lookup, `write_status_summary.sh`
ran every audit twice through `completion_audit.sh`, and every script
required an `rg` binary that this Mac does not expose to non-interactive
shells (the audits aborted with `rg: command not found`).

Changes, each preserving the printed PASS/FAIL/MISSING lines and exit
semantics:

- The route-naming checks are single `awk` passes over the harvested name
  list (`route_awk_lib` in the axiom and root-import audits; the semantic
  family loops likewise). Same-tree comparison: old and new stdout are
  byte-identical for the axiom (112 result lines), root-import (979), and
  semantic (124) audits; renaming a route theorem makes old and new fail with
  the same single FAIL line and exit 1.
- `scripts/bin/rg` is a stdlib-only Python subset of ripgrep, prepended to
  `PATH` by every audit script only when no `rg` binary exists. With no `rg`
  on `PATH`, the interface, shape, mathlib-gap, semantic, root-import, axiom,
  and formalization audits print the same result lines as with ripgrep.
- `write_status_summary.sh` records each gate's exit status and passes the
  directory to `completion_audit.sh` as `COMPLETION_AUDIT_GATE_RESULTS_DIR`;
  the completion audit prints `REUSE:` under each gate header and aborts on a
  recorded nonzero status. Standalone `sh scripts/completion_audit.sh` is
  unchanged.
- The axiom audit prints `FAIL: axiom footprint Lean check did not elaborate`
  with the first Lean lines instead of exiting silently.
- The completion and formalization audits' placeholder scan is
  `scripts/lean_placeholder_scan.py`, which strips `--` and nested `/- -/`
  comments before matching. The previous `rg` scan flagged docstring prose
  (`admit`, `postulate`, `constant`) in four modules written after June, which
  made the completion boundary read as "unexpected completion audit
  failures" although the only real failures are the absent reserved theorem.
  On this tree the scan reports zero hits.
- `scripts/theorem_contract_audit.sh` prints its `== Theorem contract audit ==`
  header again; the 2026-09-05 rewrite to `frozen_contract_audit.py` had
  dropped it while `completion_audit.sh` still requires that sentinel in
  `CURRENT_STATUS.md`, so the snapshot sentinel check failed on the first
  regeneration.
- Tests: `scripts/tests/test_rg_fallback.py`,
  `scripts/tests/test_completion_gate_reuse.py`,
  `scripts/tests/test_lean_placeholder_scan.py`; the harness runtime, deploy,
  and worker suites are unchanged and green.

Warm-cache timings on the same tree, sequential runs:

| Audit | Before | After (ripgrep) | After (fallback) |
| --- | ---: | ---: | ---: |
| axiom footprint | 522 s | 55 s | 74 s |
| root import | 524 s | 64 s | 93 s |
| semantic surface | 178 s | 81 s | 93 s |
| interface | 14 s | 13 s | 22 s |

Integration checkpoint on `main` at `b807cd42`: `sh scripts/write_status_summary.sh`
(build plus every audit once, then the completion audit reusing the recorded
gate statuses) completed in 518 s and regenerated `CURRENT_STATUS.md` with
every scaffold audit at status 0, completion audit status 1, and completion
boundary status `reserved theorem absent only`.

Not merged: branch `worker/audit-refactor` (commit `9c2c7584`) holds an
interrupted agent's extraction of the Lean check payloads into a non-default
`lean_lib PoincareAudit` (`audit/PoincareAudit/*.lean`,
`scripts/audit_payload_equivalence.py`). It would let Lake cache the Lean half
of the audits. On 2026-09-07, after adding the missing root module
`audit/PoincareAudit.lean` and moving the module docstrings below the
`import` lines (two follow-up commits on that branch), its own `--check`
reports every module as a lossless extraction of the legacy heredocs (83,887
checks), `lake build PoincareAudit` succeeds in 35 s on a warm cache with all
seven payload modules elaborating under `#guard_msgs` and `#std_axioms`, and a
no-op rebuild takes 2 s. No audit script consumes the library yet: wiring it
in means replacing the heredoc elaborations and reworking the
self-referential token-coverage checks that read the script text, so it stays
a separate reviewed change.

## 2026-09-07 Boundary correction

Checked in `/Users/mjkang/Develop/poincare` on branch `main`, base `b2b96fc2`.
Two prose ledgers were behind Lean; both are corrected here with theorem-level
evidence (`harness/reports/M5-glob-68_closure.md`).

1. The 2026-09-04 "exact next analytic action" below was already done by
   commit `723b4132`: `CompactReferenceMetricTensorFamilyData.exists_uniformMetricLowerComparison`
   (`Poincare/Global/CompactReferenceMetricTensorFamilyLowerComparison.lean`)
   removes the `UniformClosedRiemannianMetricLowerComparison` input, and
   `NormalizedFlowFormalProfilePositiveEinstein.lean` exposes the
   `...OfCompactTensorControl` constructors. Its axiom footprint is
   `[propext, Classical.choice, Quot.sound]`. The remaining open inputs of
   `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfilesOfCompactTensorControl`
   are, by exact name: `compactTensorReferenceControl :
   CompactReferenceMetricTensorFamilyData reaction.K reaction.metric`,
   `hequicontinuous`, `hpointwiseCompact`, and `scalarSubordinateGeometry`,
   plus the `reaction` record itself, whose only producer needs
   `HamiltonPinchingCoreData3` (normalized-flow existence with Hamilton's
   eigenvalue floor). These are the Hamilton-1982 analytic wall; no producer
   of any of them exists in the repository.

2. The Cartan "F-transition law" that `harness/ledger.json` and reports
   M5-glob-21..67 call blocked was closed curvature-only by commit `d8f2e43c`
   (2026-07-17), never recorded:
   `UniformAnchoredFTransition.exists_cartanChartMap_christoffelAt_F_transition_law_curvature_only`,
   `UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law`,
   `DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`.
   The M5-glob-49..67 third-variation/selector tower is not on the closing
   path. Reports through M5-glob-67 are historical.

3. The live Cartan boundary is now recorded in Lean:
   `Poincare/Global/CartanTwoNeighborhoodDevelopment.lean` defines H1
   (`UnitCurvatureSuccessorDataNeighborhood3`) and H2
   (`UnitCurvatureSuccessorEqualityNeighborhood3`) and proves
   `globalLocalDevelopment_of_two_neighborhoods`,
   `unitConstantCurvatureSphereRecognition3_of_two_neighborhoods`,
   `universalUnitRecognition_of_two_neighborhood_statements`, and
   `Poincare.poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods`,
   each with axiom footprint `[propext, Classical.choice, Quot.sound]`.
   Constant curvature proves only the fixed-anchor slices of H1 and H2
   (`universalSuccessorDataLocus_vertical_mem_nhds_of_curvature`,
   `fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature`);
   the joint neighborhoods as anchors and alignments move are open.
   The reviewed obligations are machine-readable in
   `harness/v2/missions/unit-recognition.json`; on this tree

   ```sh
   python3 scripts/theorem_registry.py graph \
     --mission harness/v2/missions/unit-recognition.json --require-closed
   ```

   exits `2` with `successor-data-neighborhood`,
   `successor-equality-neighborhood`, and `unit-recognition` open and the
   reduction `checked_with_hypotheses`.

The module is wired into `Poincare.lean`; `LEAN_NUM_THREADS=1 lake env lean
Poincare.lean` succeeded on this tree. The independent root probe still reports
`Unknown identifier Poincare.poincare_conjecture`; the repository is not
complete.

Exact first action for the next agent: attack H2 through its equivalent
`DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence g`
(persistence of the radius of
`DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`
under motion of the anchors), or H1 through
`CartanGenericSuccessorDataLocalCover.FixedChartLocalGenericDataPersistence g`
(persistence of the successor datum's open conditions and strict derivative
as the anchors move, using `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`).
Freeze the chosen statement with a schema-2.1 contract before dispatch.

## 2026-09-08 Repair track and audit payload caching

Integrated on `main` after the orchestrator's gate and review (codex workers,
`harness/dispatch_codex.sh`):

- `Poincare/Global/ControlledChartInstance.lean` (task
  `controlled-chart-instance`): a compact manifold admits a finite
  `ChartedSpace` instance with the same smooth maximal atlas whose preferred
  chart sources contain a uniform ball around their anchors
  (`exists_controlled_chartedSpace_source_persistence`,
  `exists_controlled_chartedSpace_of_compatibleMetric`), and scalar
  smoothness agrees between such instances
  (`scalarContMDiff_iff_of_atlas_subset`).
- `Poincare/Global/RiemannianMetricInstanceTransport.lean` (task
  `metric-transport`, stopped as statement-invalid): the hom-bundle
  trivialization formula `inner_trivialization_apply`; the raw-fiber transport
  contract was refuted because the identification `TangentSpace I x = E` is
  chart-dependent.
- `Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean` (task
  `metric-transport-2`): the geometric transport `transport inst' h g` with
  `transport_inner` (pullback by the chart-change derivative `J x` in both
  slots), including the smoothness of the transported section. The induced
  distance comparison is the exact remaining `def InducedDistanceAgreement`.
- `Poincare/Global/CurvatureInstanceTransport.lean` (task
  `curvature-transport`, stopped with a verified partial): unconditional
  vector-field transport with regularity equivalence in both directions, the
  conjugated derivative and its additivity; the bundled connection, metric
  compatibility, zero torsion, Levi-Civita agreement, constant-curvature
  transport, and the recognition reduction
  (`exists_controlled_recognition_reduction`: any compatible metric gives a
  finite controlled instance to which unit recognition reduces) are all
  conditional on the single explicit boundary
  `ConnectionCurvatureNaturality` (the conjugated derivative equals the new
  Levi-Civita connection on differentiable fields, and curvature values
  conjugate by `J`). Sixteen theorems, standard axiom footprint.
- `Poincare/Global/ConnectionInstanceNaturality.lean` (task
  `connection-naturality`): the boundary is discharged
  (`connectionCurvatureNaturality`), so the reduction is unconditional:
  `exists_controlled_recognition_reduction'` gives, for any compatible metric,
  a finite controlled charted-space instance with uniform-ball chart sources
  such that unit-curvature sphere recognition for that instance implies
  recognition for the original instance. Twenty-two declarations, standard
  axiom footprint, wired into the root import.

The next obstruction is one level down. The exponential chart
`expAt g x` is built from three per-anchor `Classical.choose` selections
(`GeodesicTransport.cutoff x` with no radius control,
the Picard–Lindelöf flow package, and the inverse-function neighborhood), so
joint statements in the anchor such as H1 and H2 cannot be proved even on the
controlled instance without re-founding the exponential layer with explicit
uniform constructions: the unblended fixed-chart geodesic flow on compact
chart regions, joint `C¹` dependence on initial position and velocity, and a
joint inverse-function argument on `(x, v) ↦ (x, exp_x v)` giving a uniform
normal radius; then a chart family (`CartanSourceExponential.Family`) built
from it, and the chain run over that family. The first bounded step landed:
`Poincare/Global/GeodesicFlowJointDerivative.lean` (task
`geodesic-position-derivative`, fourteen theorems, standard axiom footprint)
proves joint `C¹` dependence of the fixed-chart geodesic flow on the initial
state with a fundamental solution of the full variational equation, and
instantiates it on the repository's uniform Picard–Lindelöf chart flow
(`exists_uniform_local_geodesic_chart_flow_initialState_C1`). The second
step landed too: `Poincare/Global/FixedChartUniformNormalRadius.lean` (task
`uniform-normal-radius`, nineteen declarations, standard axiom footprint):
stationarity of zero-velocity flows, the joint endpoint derivative
`(u, w) ↦ (u, u + T • w)`, strict differentiability, the joint
inverse-function neighborhood, and
`exists_uniform_local_geodesic_chart_flow_normal_neighborhoods`: one
positive normal radius for every anchor in a compact region of the chart's
initial-position ball, with injectivity and ball coverage. Both are wired
into the root import.

Design conclusion for the next campaign. A globally jointly regular
`CartanSourceExponential.Family` cannot in general be continuous across the
chart switches of a finite atlas, so the usable notion is local: near every
anchor one fixed chart and one uniform exponential. The Cartan chain
(`CartanMap.openPartialHomeomorph`, `DifferentialInducedSuccessor.Data`, and
their consumers) is hardwired to the per-anchor `expAt` selector, so the
chain has to be parametrized over an exponential-chart family with the
uniform family as an instance; germ-level theorems transfer by per-anchor
agreement (ODE uniqueness on the cutoff-one zone), joint-in-anchor theorems
must be re-proved for the uniform family. The inventory
`harness/reports/chain-parametrization-inventory.md` (task
`chain-parametrization-inventory`, analysis only, every citation grep- and
probe-verified) measures the corridor at 112 modules and 1,442 declarations,
identifies the exact hardwired definitions (`CartanMap.openPartialHomeomorph`,
`DifferentialInducedSuccessor.Data` and its ten exponential-bound fields,
`RestrictedCompatibleCartanAtlasData3`, the two `UnitCurvature*Cartan*`
adapters), proposes parametrizing the interpretation of a Cartan state and its
differential successor over supplied source and target exponential families
(about fourteen new files), and specifies the first five bounded tasks with
exact Lean targets. Tasks 1 to 4 of that
plan are landed on `main`, each gate PASS with the module-wide axiom scan and
wired into the root import: `CartanSuppliedSourceMap.lean` (the germ of a
supplied source family and target family, agreeing with `CartanMap.cartanMap`
on the generic families), `CartanSuppliedSourceGermTransfer.lean` (germ
agreement transfers along agreement of normal coordinates, with an open
common source), `FixedChartEndpointSlices.lean` (per-anchor slices of a
joint product inverse with exact loci and the four joint regularity laws),
and `FixedChartUniformSourceNormal.lean` (the retained `Patch` built from the
uniform fixed-chart exponential, its `normal` charts, anchor laws, open joint
source locus, continuous evaluator, and `rawLocalFamily`). Task 5 landed as
`FixedChartUniformPreferredGermAgreement.lean` (invertible anchor frame,
`normalized_endpoint_eventuallyEq_expAt`,
`normal_eventuallyEq_generic_in_anchor_frame`): the patch's normal
coordinates agree with the generic exponential's as germs at every anchor of
the patch, which is the bridge that lets the chain's germ-level theorems
transfer to the uniform family. The next five files are
specified with type-checked targets in
`harness/reports/parametrization-plan-2.md` (tasks 6 to 10: the supplied
differential successor data, its transfer from coordinate data, the local
successor existence and equality statements on the patch, which are the
well-posed replacements of H1 and H2, and the supplied reachable chain).
Task 6 landed as
`CartanSuppliedDifferentialSuccessor.lean` (the `Interpretation` of a chain
state by supplied source and target exponentials with the generic and patch
instances, `CoordinateData`, `Data`, `Data.successor`, and the five frozen
laws, 84 scanned declarations). Task 7 landed as
`CartanSuppliedDifferentialTransfer.lean` (ten theorems: data from
coordinate data, successor equality laws, generic-to-supplied and
supplied-to-generic transfers, the patch germ agreement, the generic interval
equality, the local equality transfer, and the patch successor at the
anchor). Task 8 (`fixed-chart-local-successor-existence`, the well-posed
replacement of H1 on the patch) stopped with a verified partial that is
itself a milestone: `FixedChartLocalSuccessorExistence.exists_uniform_domain_radius`
gives ONE radius, chosen before the source anchor, target anchor, alignment,
and point, for the domain conjuncts of the supplied successor data on
compact anchor sets, together with the moving-anchor operator bound and host
metric comparison (fifteen declarations, standard axioms, merged). The exact
remainder is `UniformDifferentialPullback`: uniform strict differentiability
of the patch exponentials at the moving vector and the metric pullback
identity, i.e. the local-isometry content of the Cartan map uniform in the
anchor; `exists_onCompact_of_uniformDifferentialPullback` reduces the frozen
task-8 target to it. Task `uniform-differential-pullback` (curvature-only)
is dispatched for that remainder. Task 9
(`fixed-chart-local-successor-equality`, the H2 replacement) stopped with
its own milestone partial, merged: `FixedChartLocalSuccessorEquality.exists_uniform_common_source_radii`
gives two radii, chosen before every moving anchor, alignment, point, and
datum, such that the ball about the successor anchor lies in both germ
sources (seven declarations, standard axioms). Its exact remainder is
`UniformEndpointReanchoring`: the predecessor map applied to the supplied
endpoint centered at the successor anchor equals the supplied target endpoint
at the image, with uniform radii; this is the exponential naturality of the
Cartan map uniform in the anchor (the per-anchor version is
`DifferentialSuccessorNaturality.exists_map_expAt_ray_naturality_radius`).
`exists_onCompact_of_uniformEndpointReanchoring` and
`exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring`
reduce the frozen task-9 target to the two remainders. So the H1/H2
replacements on the patch now stand on exactly two curvature-only analytic
statements, both uniform versions of theorems already proved per anchor: the
local isometry of the Cartan map (`UniformDifferentialPullback`) and its
exponential naturality (`UniformEndpointReanchoring`). The pullback task
(`uniform-differential-pullback`) landed its partial, merged
(`FixedChartUniformDifferentialPullback.lean`, eleven declarations): uniform
strict differentiability of both patch exponentials at the moving supplied
vector (`exists_uniform_differential_radius`, no curvature needed) and the
metric identity at zero velocity (`metric_pullback_zero`). Its exact
remainder, `UniformNonzeroMetricPullback`, is the metric pullback along
nonzero vectors with one radius before all moving parameters, and
`target_of_uniformNonzeroMetricPullback` derives the frozen task-8 target
from it. This single curvature-only statement, the uniform Jacobi-field
comparison on a fixed-chart patch, is now the analytic core of the
unit-recognition route; everything from it to the smooth Poincaré statement
(given Hamilton convergence) is either proved or reduced to it plus
`UniformEndpointReanchoring`. Task `uniform-nonzero-metric-pullback` landed
its partial, merged (`FixedChartUniformJacobiComparison.lean`, thirteen
declarations): full-interval fundamental solutions for the retained patch
flows (no smallness hypothesis, both endpoints, joint continuity), the
identification of the canonical derivative of the supplied coordinate
exponential with the position component of the fundamental solution, and the
normalized Jacobi initial data. Its exact remainder is
`MovingInitialPositionJacobiComparison`: a pointwise statement with no radius
quantifier at all, saying that along a source patch geodesic and the aligned
sphere geodesic the chart-metric pairings of the Jacobi fields at the retained
times agree; `target_of_movingInitialPositionJacobiComparison` and the two
conditional consequences reduce the uniform pullback and the frozen task-8
target to it. The report names the lower-level lemmas that already allow
arbitrary initial position (the transverse Gauss lemma, the curvature
contraction, the Jacobi norm system). Task
`moving-position-jacobi-comparison` PROVED it: `FixedChartMovingPositionJacobi.lean`
(eighteen declarations, standard axioms, merged) contains
`movingInitialPositionJacobiComparison`, `uniformNonzeroMetricPullback`,
`uniformDifferentialPullback_of_constantCurvature`, and `exists_radius`, whose
statement is byte-for-byte the frozen task-8 target: on a fixed-chart patch,
for compact anchor sets, one radius chosen before the source anchor, target
anchor, alignment, and point yields supplied successor data with actual source
membership. This is the well-posed replacement of H1, proved. The remaining
analytic statement for the H2 replacement was `UniformEndpointReanchoring`;
task `uniform-endpoint-reanchoring` landed a partial, merged
(`FixedChartUniformEndpointReanchoring.lean`, twelve declarations): the
uniform metric pullback germ from the landed H1 data, the chart-level Koszul
transition law uniformly, conditional only on differentiability of the chart
map's derivative, the mapped-state chain rule needing only that, full
unit-interval geodesic uniqueness, the uniform displacement radius, and the
reduction `target_of_uniformMappedGeodesicEquation` of the frozen H2
remainder to one concrete mapped-geodesic initial-value problem
(`UniformMappedGeodesicEquation`). The unclosed step is second-order
regularity of the patch endpoint map, which the landed joint-`C¹` theorem
should give by applying it to the augmented flow-plus-fundamental-solution
system; task `patch-second-variation` landed a partial, merged
(`FixedChartPatchSecondVariation.lean`, nine declarations): the operator
augmented field and its `C²` regularity for the fixed-chart geodesic field,
the augmented ODE for the flow paired with its fundamental solution, the
full-interval derivative identification for the patch flow, and short-time
`C²` of the patch flow on the half-radius ball
(`exists_patch_flow_contDiffOn_two_short_time`). The single remainder is
`AugmentedSystemRegularity C`: `C¹` dependence at the retained time `C.T` of
the augmented flow on the full retained ball, which
`target_of_augmentedSystemRegularity` turns into `C²` of the endpoint map.
The flow theorems return a shorter time; the missing piece is continuation
over the full retained interval, the same full-interval Grönwall argument
already done for the base flow. Task `augmented-system-regularity` PROVED
it (`FixedChartAugmentedSystemRegularity.lean`, merged): `augmentedSystemRegularity`
and `patch_endpoint_contDiffOn_two`, so every patch endpoint map is `C²` on
its full retained ball. Task `mapped-geodesic-assembly` PROVED the
assembly (`FixedChartMappedGeodesicAssembly.lean`, merged): chart-map `C²`,
the uniform transition law, the mapped geodesic initial-value problem,
`uniformEndpointReanchoring_of_constantCurvature`, `exists_onCompact`, and
`FixedChartLocalSuccessorEquality.exists_radii`, byte-for-byte the frozen
task-9 target. So on a fixed-chart patch of a controlled instance, for
compact anchor sets and a unit-curvature metric, one step radius and one
evaluation radius chosen before every moving parameter give supplied
successor data (H1) and germ equality on the evaluation ball for every
datum (H2). These are the well-posed replacements of the two obligations
refuted on 2026-09-08, now proved. Task 10 (`supplied-reachable-chain`) landed
(`CartanSuppliedReachableChain.lean`, twenty-two scanned declarations):
reachable chains under a per-step interpretation policy, existence from
`StepAvailable`, anchor and source laws, and endpoint equality under open
agreement. The remaining program is specified in
`harness/reports/parametrization-plan-3.md` (task `parametrization-plan-3`,
analysis only): nine serial tasks 11 to 19, each with type-checked targets:
finite patch cover with cores and buffers, uniform patch switch, patch
policy with an external label schedule, whole-cell realization, subdivision
transport, homotopy endpoints, terminal transport, restricted development,
and the final unit-recognition adapters to the controlled instance and the
universal statement. Two qualifications are recorded there: the cover is a
finite refinement of patches (not one patch per chart), and the policy keeps
a label while both anchors stay in compact operating cores inside the open
patch anchor sets, since the H1/H2 theorem is uniform only on compact sets.
Task 11 (`supplied-finite-patch-cover`) landed
(`CartanSuppliedFinitePatchCover.lean`: patch cover with cores, buffers, and
Lebesgue number; `QuantitativeCover` with uniform step and evaluation radii
from the patch H1/H2 theorem). Task 12 (`supplied-uniform-patch-switch`)
landed a partial (`CartanSuppliedUniformPatchSwitch.lean`, forty scanned
declarations: `buffered_eventuallyEq`, `mesh_pos`, `transition_eqOn`, the
uniform common source, and a fixed-anchor switch radius uniform over labels
and alignments); its exact remainder is `UniformBufferedPairAgreement`, the
agreement of two patch interpretations on a ball of radius uniform over
compact buffer overlaps, i.e. uniform chart-transition naturality of the
patch normals; task `uniform-buffered-pair-agreement` PROVED it
(`CartanSuppliedBufferedPairAgreement.lean`), so task 12's frozen
`exists_switchControl` is unconditional under curvature 1. Task 13
(`supplied-patch-policy`) landed (`CartanSuppliedPatchPolicy.lean`: the
policy with external label schedule and covering fallback, `StepAvailable`
for every node-anchored state, sticky chains, and chain equality under
equal schedules). Task 14 (`supplied-whole-cell-realization`) landed
(`CartanSuppliedWholeCellRealization.lean`: strict whole-cell subdivisions
of any path at any positive radius, supplied sticky realizations at the
system mesh, endpoint anchoring, and a rooted realization of the common
skeleton). Task 15 (`supplied-subdivision-transport`) landed
(`CartanSuppliedSubdivisionTransport.lean`: supplied states transport across
arbitrary monotone refinement factors and repeated nodes, so every two
realizations of one path have equal endpoint states). Task 16
(`supplied-homotopy-endpoints`) landed (`CartanSuppliedHomotopyEndpoints.lean`:
small homotopy grids, the supplied ladder invariant with actual patch
switches, endpoint equality for arbitrary realizations of homotopic paths, and
path independence under `SimplyConnectedSpace M`). Task 17
(`supplied-terminal-transport`) landed (`CartanSuppliedTerminalTransport.lean`:
short paths inside a mesh ball, every short-path terminal datum equals the
full reached state, and concatenation transport from the exact reached
middle state). Task 18 (`supplied-restricted-development`) landed
(`CartanSuppliedRestrictedDevelopment.lean`: the total rooted-endpoint
developing map equals the terminal fallback germ on an open neighborhood of
every point, hence forms a restricted atlas and is a local homeomorphism to
the round sphere under `SimplyConnectedSpace M`). Task 19
(`supplied-unit-recognition`, the final adapter) is dispatched.

`harness/gate.sh` now performs a module-wide axiom scan (every declaration
of the module) instead of relying on hand-listed names.

Validation: the audit payload wiring (task `audit-payload-wiring`) is merged.
The Lean check payloads of the axiom, root-import, semantic, and completion
audits live in the non-default Lake library `PoincareAudit` (`audit/`), built
and cached by Lake; `scripts/audit_payload_equivalence.py --check` proves the
modules are a lossless extraction of the legacy heredocs at
`b2b96fc2` (83,887 checks and 10,210 axiom probes). The four scripts shrank
from 129,000 to 25,000 lines. Same-tree comparison on `main` after the merge:
sorted result lines identical for all four audits (112, 985, 124, and 13,390
lines); warm timings axiom 56 s to 48 s, root import 68 s to 57 s, semantic
82 s to 46 s, standalone completion 488 s to 415 s. The worker's evidence
archive is kept outside git in `harness/logs/`.

## 2026-09-08 H1 and H2 are atlas-dependent as stated

Three codex workers (tasks M5-glob-69, 70, 71; `harness/dispatch_codex.sh`)
attacked H2, H1, and the joint regularity of the exponential chart in its
anchor. All three stopped under the contract's invalid-statement rule with
Lean-checked obstructions, consolidated in
`harness/reports/M5-glob-72_statement_refutation.md`: the statements are
formulated for the arbitrary preferred charts `chartAt E x`, and a
`ChartedSpace` instance may exclude a fixed point from every other chart, so
`GenericJointRegularity` is false for every metric on the punctured model
(`Poincare/Global/GenericJointRegularityCounterexample.lean`), H1 forces
`PreferredChartSourcePersistence` (`FixedChartSuccessorDataPersistence.lean`),
and H2 forces chart injectivity on common neighborhoods
(`SuccessorEqualityRadiusPersistence.lean`). All new modules pass the gate with
the standard axiom footprint and are wired into the root import.

The mission `harness/v2/missions/unit-recognition.json` therefore records
obligations that cannot be discharged in their current form; its description
says so. The checked reduction from H1 and H2 remains valid but is now known to
start from unprovable premises for pathological atlases. The Hamilton-front
registration (`harness/v2/missions/hamilton-front.json`, worker
`hamilton-front-mission`, gated and merged) is unaffected.

Exact first action: task `harness/tasks/controlled-chart-instance.md`
(dispatched to a codex worker at high effort): prove that a compact manifold
admits a `ChartedSpace` instance with the same smooth structure whose
preferred-chart sources contain a uniform ball around their anchors, from a
finite subatlas and a Lebesgue number. The subsequent steps are metric and
curvature transport across such instances and re-running the Cartan chain over
a controlled `CartanSourceExponential.Family`.

## 2026-09-07 Hamilton front registration

Worker branch `worker/hamilton-front-mission`, based on
`aa82826aec916ad9339e2da1049f80009cdf2c7a`, adds
`Poincare/Global/HamiltonFrontStatements.lean` and the mission
`harness/v2/missions/hamilton-front.json`. The structure preserves exactly the
five inputs of the compact-tensor formal-profile constructor, including its
independent compact-parameter universe. Checked reductions reach universal
positive-Einstein existence, Hamilton convergence, and the conditional smooth
`PoincareConjecture` composition with Cartan H1/H2. Neither universal Hamilton
inputs nor the unconditional Hamilton endpoint is proved. The worker report
`harness/reports/hamilton-front-mission_done.md` records compiler, registry, and
test evidence, including an existing ripgrep output-order test flake and a
passing unchanged rerun. Exact first action for the orchestrator: independently
run `python3 scripts/theorem_registry.py graph --mission
harness/v2/missions/hamilton-front.json --require-closed` and review the five
input types before accepting or decomposing this mission.

## 2026-09-05 Main integration

The integration checkout is now `/Users/mjkang/Develop/poincare`, branch `main`.
The merge retains the old local-main history and incorporates
`codex/proof-workflow-improvements` at `5d408763`, the repeated-interruption
handling at `81cde044`, and the focused-review implementation at `a87c80a6`.
The earlier proof-worker branches are included through their reviewed
cherry-picked changes. Existing worktrees and their evidence are preserved.

The focused reviewer now uses the same schema-2.1 declaration-probe generator
as the runtime gate. A regression test checks both strict deliverables and
legacy probe compatibility. Integration preserves both the execution-backlog
target and the independent integration-batch setting.

The combined runtime suite passed 66 tests, deployment suite 49, worker suite
33, and Pi suite 94 with 11 skips. The Lean sources, root imports, toolchain,
and dependency manifest are byte-for-byte identical to the verified
`5d408763` tree; no Lean theorem was changed during these merges. No live
model or persistent harness service was changed by this Git integration.

The next action remains the reviewed mission check, run from `main`:

```sh
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
```

The source-existence, covering-construction, and final Poincare obligations
remain open. The historical verification limitations below still apply.

## 2026-09-05 Reviewed topology and proof-workflow checkpoint

The active integration worktree is
`/Users/mjkang/.codex/worktrees/proof-workflow-improvements/poincare`, branch
`codex/proof-workflow-improvements`, based on the previously pushed
`64c9f999c9c699cb52e87ea36fad294d43b774d4`. The implementation commits are
`d73eb030` for the topology source, `500ecdd3` for the theorem registry, and
`84ca80dd` for strict statement contracts. This section supersedes older
descriptions of the active branch and theorem-selection workflow below.

The new `GroundedTopologySource` retains one decomposition and trace, their
owning surgery package, and a Perelman production source on the matching flow.
`GroundedTopologyPresentation` selects a compatible atlas on the same topology.
The independent read-back rejected an earlier draft which required the original
arbitrary topological atlas to be differentiable; the accepted types remove
that requirement. The new conditional assembly passes the presentation's full
source into the covering premise.

`GroundedTopologySource.active_components_cover` proves coverage of the original
space at every recorded stage by backwards induction through the actual parent
maps. Disjointness gives unique component membership. The high-Ricci membership
lemma transfers a point using the actual trace-flow equality and locates its
spatial point in that partition. It does not locate the point at the stage's
event time or in the event region.

These are sets in the original manifold, not physical time-slice manifolds.
Their carriers still lack the topology and embedding requirements needed for
geometric reconstruction. The source also does not identify event regions with
high-curvature regions. Both universal chosen-atlas source existence and
`GroundedTopologyThreeSphereCoveringStatement` remain open, as does treatment
of a zero-event history. No final Poincare theorem is supplied by this work.

The registry reads exact types and dependencies from Lean after focused builds.
Its reviewed mission is `harness/v2/missions/grounded-topology.json`. Planned
edges stay separate from checked proof dependencies; a conditional theorem
cannot discharge an unconditional obligation. Expected statements include
transitive semantic fingerprints. Catalogs bind to source identity, and stale
or edited evidence is rejected.

New mathematical Tasks use opt-in schema `2.1`, as required by the updated
orchestrator prompt. Every deliverable has a frozen type and universe list,
with definition hashes and an independent read-back tied to the snapshot.
Pinned source files are streamed through hash checks without being copied into
worker prompts. Existing context limits and broker scope remain unchanged.
Version `2.0` remains available for historical tasks. The curated theorem audit
now checks exact types and axiom footprints; it no longer demands reflexive
`theorem_eq` companions. The full completion audit also rejects a failed or
nonstandard final axiom check instead of printing it and continuing.

The full completion run passed build, interface, mathlib-gap, semantic-surface,
root-import, and axiom checks, then exposed four older shape-parser false
positives. That parser treated qualified methods such as `Type.ofSource` as
definitions of `Type`. It now limits the legacy name convention to unqualified
definitions, always records filenames, and preserves the existing checks on
those definitions. Four regression tests and the live shape audit pass after
the repair. The five curated contracts were then rerun and passed. The initial
completion log is preserved; the entire completion script was not repeated
after this parser-only repair. No successful full completion audit is claimed.
An independent final root probe still reports
`Unknown identifier Poincare.poincare_conjecture`.

Independent verification passed the focused Lean checks and axiom probes for
all eight new proof declarations, the five curated contracts, and a serialized
4,105-target full build. The runtime suite passed 63 tests, worker suite 33,
registry suite 16, and curated-audit suite 10. The Pi suite completed 94 tests
with 14 environment-dependent skips. These suites include changed secondary
types, forged or stale review evidence, unsafe proof-typed definitions, changed
dependent definitions, false graph closure, and omitted multi-megabyte pinned
sources. The warm-cache pilot medians were 2.60 seconds for statements and
2.52 seconds for assembly, measured while the completion audit also ran; no
before/after speedup is claimed.

Local implementation task snapshots and their corrected directory-scope
revisions are under `harness/v2/tasks`; the invalid initial spellings are
preserved under `tasks/history`. These records were not dispatched to the
persistent Harness database. All local worker leases are released in
`proof-workflow-improvements-leases.closed.json`. The live model services and
persistent deployment were not modified.

The exact first action is:

```sh
python3 scripts/theorem_registry.py graph \
  --mission harness/v2/missions/grounded-topology.json --require-closed
```

Exit `2` denotes valid evidence with open obligations. Before dispatching the
next proof, split the `covering-construction` obligation at a geometric carrier
or gluing interface and review its exact statement. Do not infer carrier
embeddings, spherical pieces, or a covering from the existing partition fields.
See `docs/PROOF_WORKFLOW.md` for commands and the precise scope of the pilot.

## Project Truth

- Mac integration repository: `/Users/mjkang/Develop/poincare`, branch `main`.
- Harness v2 pivot base: `7ce913d87be973256517ea862fb4d3dbfae7cb82`,
  equal to `origin/main` before the implementation. The Mac control-plane
  commit is `8114cfe2a592d22ea1973441c0fb086c72e8826d`; the bounded proof Job
  commit is `f266c2fd4a8c23ca55bad0a09f35cc638e6842c0`. Inspect the current
  commit and working tree before acting; preserve any later changes.
- An exact stdin probe at the pivot base and again at the deployed release
  candidate failed with `Unknown identifier Poincare.poincare_conjecture`.
- The repository is still incomplete. Completion means Lean checks exactly
  `Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`, its
  axiom footprint is allowed, and the full completion audit passes in a clean,
  stable integration checkout.

`CURRENT_STATUS.md` was generated on 2026-06-30 and `harness/ledger.json` ends
with the 2026-07-07 legacy selector-assembly work. Both are historical until
regenerated or revalidated against the current commit. Lean and the current
diff remain authoritative.

## 2026-09-04 Formal Profile and Grounded-Interface Checkpoint

The active integration worktree is
`/Users/mjkang/.codex/worktrees/formalization-until-6/poincare` on branch
`codex/formalization-until-6`. Its clean checkpoint is
`77fb1a54ba95f099ffe891d54190aec7a2f80d60`, 82 commits ahead of unchanged
`origin/main` at `bc076f1e893c6ba834729f8bcb359a1f400a3e72`.

The scalar `C0,3` compactness route no longer requires every profile limit to
be realized by a smooth Riemannian metric. The new verified chain is:

```text
compact componentwise scalar third-jet profiles
  -> formal metric and inverse on the nondegenerate locus
  -> formal Christoffel jets through order two
  -> formal curvature, Ricci, covariant Ricci, and norm contraction
  -> exact agreement with genuine chart quantities
  -> finite fixed-anchor cutoff-one cover
  -> global UniformCovariantRicciDerivativeNormBound
  -> reaction-decay positive-Einstein analytic data
```

The principal endpoint is
`NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayPositiveEinsteinAnalyticData3.ofComponentwiseAscoliFormalMetricThirdJetProfiles`.
Its remaining nondegeneration input is the explicit
`UniformClosedRiemannianMetricLowerComparison`; the former
`hForwardProfileLimitsRealized` premise is absent. The bounded-component
variant is also proved. All formal curvature expressions agree exactly with
the repository's genuine `anchorChartCurvatureFamily`, Ricci,
covariant-Ricci, inverse-metric, and sixfold norm formulas.

The grounded surgery interface was also repaired. The constructorless
`HasSingularityModelBlowupClassification` marker is now a proof-bearing
classification source together with surjectivity onto every pointed
rescaling index. The five component classification maps compose to this
coverage theorem in `SingularityModelBlowupCoverage.lean`. No existing
payload proves any of those five surjectivity claims, so that remains genuine
Perelman work rather than an artificial inconsistency.

On the topology side,
`ExtinctionThreeSphereCoveringProjectionStatement` records the non-circular
post-extinction target `exists p : ThreeSphere -> M, IsCoveringMap p`.
Simply connected covering-space rigidity turns it into the sphere
homeomorphism. The older full topology package still stores the final
homeomorphism and is not an honest proof plan; its decomposition and surgery
trace realization predicates also remain empty inductives.

At this checkpoint, a serialized 4,095-target `lake build`, root elaboration,
interface audit, semantic-surface audit, 6,008-declaration theorem-contract
audit, root-import audit, and axiom audit all pass. The exact probe still
fails with `Unknown identifier Poincare.poincare_conjecture`; the repository
is not complete.

The exact next analytic action is to derive a pointwise inverse-chart volume
density lower bound from
`CompactReferenceMetricTensorFamilyData.volume_le`, using the proved
`inverseChart_hausdorffChartDensityEquality`. Combined with its uniform metric
upper bound and the three-dimensional determinant inequality, this should
produce `UniformClosedRiemannianMetricLowerComparison` and remove the last new
nondegeneration input. In parallel mathematical terms, the independent hard
frontiers remain classified-model coverage of all pointed rescalings and
Cartan successor-equality persistence needed for a total developing map.

## Completed Bounded Deployment Exercise

The first Harness v2 exercise was
`automatic-scalar-derivative-constructor` revision 4, accepted from Job
`automatic-scalar-derivative-constructor-r4-a03`, frozen at
`7ce913d87be973256517ea862fb4d3dbfae7cb82`. Attempts `r4-a01` and `r4-a02`
were terminalized and preserved; neither immutable Job was relaunched after a
supervisor record existed.

Its single allowed source file is:

```text
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean
```

The accepted edit adds the frozen `ofReactionFields` constructor and derives
`scalarTimeDerivativeJointContinuous` from `reaction.jointMetricEntries` via
the existing theorem
`scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three`.
The constructor may not add `ScalarTimeDerivativeJointContinuous` or scalar
domination as a replacement argument. Leanstral made the one-file edit through
Pi's scoped patch tool, its worker `lean_check` passed, and Codex independently
reran all six frozen acceptance commands plus the canonical exact-type
declaration probe before committing and accepting it. The accepted Job gate is
`harness/v2/state/jobs/automatic-scalar-derivative-constructor-r4-a03/gate.json`
on `mj-zima`.

The previous broad positive-time-overlap and compact-history surfaces remain
important context, but this narrower constructor is the selected first
dependency reduction. Do not redispatch the last legacy ledger entry.

## 2026-07-20 Bochner Continuity Checkpoint

The integration checkout advanced from
`ee4a8e5382f2b664a9843fc6b8ec237c535a9460` to the accepted proof commit
`bec8bc4a5a514a6ba502e2a945f96317be397a5c`. Harness Task
`cov-ricci-bochner-continuity-inline` revision 2 was accepted from Job
`cov-ricci-bochner-continuity-inline-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-continuity-inline-r2-a01/gate.json`
on `mj-zima`. The worker lease is released and no Job remains active.

The accepted theorem is
`Poincare.continuous_joint_covRicciNormSqAt_of_bochner_fields`. It uses the
Ricci Bochner identity to derive joint continuity of `covRicciNormSqAt` from
joint continuity of the Ricci-norm Laplacian and rough-Ricci pairing, together
with the existing pointwise smoothness hypotheses. Its focused Lean gate,
canonical frozen-type `import Poincare` probe, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit retained only its known direct-import ledger failures; this checkpoint
also wires the previously accepted automatic scalar-time-derivative module
directly into `Poincare.lean`, reducing that ledger by one.

## 2026-07-20 Bochner-Fields Constructor Checkpoint

The integration checkout advanced from
`12b700a27f31e7fb521eb1bec1845fbf4e842e61` to accepted proof commit
`c5a80d17b236b82d5daac96982e9edf87fdb89b4`. Harness Task
`cov-ricci-bochner-fields-constructor` revision 2 was accepted from Job
`cov-ricci-bochner-fields-constructor-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-fields-constructor-r2-a01/gate.json`
on `mj-zima`. No Job or file lease remains active.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerFields`.
It installs `reaction.topologicalSpaceK`, derives joint covariant-Ricci norm
continuity with `continuous_joint_covRicciNormSqAt_of_bochner_fields`, and
calls `ofReactionFields`, so neither joint covariant-Ricci norm continuity nor
scalar-time-derivative continuity is an explicit constructor argument. The
canonical frozen-type probe passed and `#print axioms` reported only
`propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `cov-ricci-bochner-fields-constructor-r1-a01` is preserved as
interrupted evidence: its draft omitted the local topology instance, then
exhausted its 12,000-token budget on stale correction hunks. Revision 2
recorded that exact failure and passed in a fresh supervised Pi session. Its
focused gate, targeted module build, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit has exactly the same four known direct-import ledger failures as before
this checkpoint, with no new failure.

The exact completion probe at the integrated commit still reports
`EXACT_DECLARATION_PROBE=absent`; `Poincare.poincare_conjecture` is not
declared. The next theorem-shaped action is to probe and freeze a fixed-target
lifting constructor that packages `ofBochnerFields` for the `analytic` field
of the automatic-finite-nerve ODE-primitive compact-history boundary, rather
than adding another alias or assuming the already assembled analytic record.
Before claiming any Job at the new base, publish and verify the immutable Lake
cache for the final clean HEAD. Do not redispatch the obsolete broad
`cov-ricci-bochner-constructor` Task; it retains only an interrupted Job and
could not be marked superseded because the accepted replacement Task did not
name that older Task in its immutable `supersedes` field.

## 2026-07-21 Bochner Pairing-Regularity Reduction Checkpoint

The integration checkout advanced from
`682560dcd37dd510b51b5a789fe8efc71ed8d97c` through the accepted proof
integration recorded by this commit. Harness Task
`bochner-pairing-from-ricci-norm` revision 3 was accepted from Job
`bochner-pairing-from-ricci-norm-r3-a01`; its reviewed worker commit is
`e216ed5bfc0e6dd098ea445eafc06d7048d3e669` and its strict gate is
`harness/v2/state/jobs/bochner-pairing-from-ricci-norm-r3-a01/gate.json` on
`mj-zima`. All Jobs and leases for the Task are terminal and released.

The accepted theorem is
`Poincare.continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`. It derives
the pairing differentiability input to the existing Bochner continuity theorem
from C2 regularity of `ricciNormSqAt`, using
`covRicciRicciPairingAt_mdifferentiableAt_of_ricciNormSqAt_contMDiffAt_two`.
Consequently the new theorem requires the Ricci-norm regularity field plus the
Ricci second-derivative, Laplacian, and rough-pairing continuity fields, but no
independent `hPairDiff` hypothesis. The canonical frozen-type probe passed and
`#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `bochner-pairing-from-ricci-norm-r1-a01` is preserved as
interrupted evidence after it exhausted its bounded Pi context without a patch.
Revision-2 Job `bochner-pairing-from-ricci-norm-r2-a01` found the correct proof
but was rejected because its first scoped patch request was broker-rejected and
the immutable Task allowed exactly one patch call. Revision 3 froze the valid
patch bytes and completed exactly one scoped patch, one Lean check, and one diff
request in a fresh supervised Pi session.

Focused elaboration, the frozen acceptance array, root elaboration, interface,
semantic-surface, theorem-contract, and axiom audits passed. The root-import
audit retains exactly its four known missing direct imports: the two Cartan
tail-overlap reductions, the scalar-variation joint-continuity reduction, and
the automatic finite-nerve compact-history boundary module. The exact
completion probe still reports `EXACT_DECLARATION_PROBE=absent`.

The next theorem-shaped action is to freeze an
`NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3`
constructor that takes the norm-field inputs above and installs the analytic
record through `continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`,
removing `hPairDiff` at the constructor boundary. Before claiming a Job at the
new integration base, complete the required root build and publish and verify a
new immutable Lake cache for that exact clean HEAD.

## 2026-07-21 Bochner Norm-Fields Constructor Checkpoint

The integration checkout advanced from
`7b216e8c246a309f2ec43ef59507799ec0e8d980` to accepted proof commit
`c39ad01f334e372d169428f8fd874b070f7d644d`. Harness Task
`cov-ricci-bochner-norm-fields-constructor` revision 2 was accepted from Job
`cov-ricci-bochner-norm-fields-constructor-r2-a01`; its strict gate is
`harness/v2/state/jobs/cov-ricci-bochner-norm-fields-constructor-r2-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no Harness Job or
file lease remains active.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerNormFields`.
It installs the reaction parameter topology, derives joint covariant-Ricci
norm continuity through
`continuous_joint_covRicciNormSqAt_of_bochner_norm_fields`, and calls
`ofReactionFields`. Its frozen constructor type therefore retains the Ricci
norm C2, Ricci second-derivative, Laplacian-continuity, rough-pairing
continuity, and subordinate-geometry inputs but has no independent
`hPairDiff`, joint covariant-Ricci continuity, or scalar-time-derivative
continuity argument. The canonical exact-type probe passed and `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `cov-ricci-bochner-norm-fields-constructor-r1-a01` is preserved
as interrupted evidence. It eventually produced the same valid one-file patch
and passed its brokered focused Lean check, but its final report hit
`stopReason=length`, so the Harness correctly refused to route it to review.
Revision 2 froze those exact patch bytes and completed exactly one scoped
patch, one Lean check, and one diff request in a fresh supervised Pi session.

The frozen acceptance array, targeted module build, canonical declaration
probe, root elaboration, interface, semantic-surface, theorem-contract, and
axiom audits passed. The root-import audit retains exactly its four known
baseline direct-import gaps—
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`, and the
automatic-finite-nerve joint-covariant-Ricci tail-overlap compact-history
boundary—and this proof commit changes neither `Poincare.lean` nor that audit.
The exact completion probe still fails with unknown identifier
`Poincare.poincare_conjecture`.

The next theorem-shaped action is to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFields`
in the existing automatic-finite-nerve boundary module. Freeze its type as the
current `ofBochnerFields` type with `hPairDiff` removed, and construct its
`analytic` field through the newly accepted analytic-data constructor. The
exact first action in the next cycle is to create and schema-validate that
single-file Task at the final clean HEAD; before claiming its first Job, run
the Task-bound root-build provenance recorder and publish and verify the new
immutable Lake cache for that exact base.

## 2026-07-21 Automatic Finite-Nerve Norm-Fields Boundary Checkpoint

The integration checkout advanced from
`0d89b5a67f9577e16f75601e8ac7cad20dee0901` to accepted proof commit
`c778276a36de0bacda0462a95f002d50f7d52129`. Harness Task
`automatic-finite-nerve-bochner-norm-boundary-constructor` revision 2 was
accepted from Job
`automatic-finite-nerve-bochner-norm-boundary-constructor-r2-a01`; its strict
gate is
`harness/v2/state/jobs/automatic-finite-nerve-bochner-norm-boundary-constructor-r2-a01/gate.json`
on `mj-zima`. All Jobs for the Task are terminal and no file lease remains
active.

The accepted declaration is
`Poincare.AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFields`.
It constructs the boundary's analytic field through the accepted analytic-data
`ofBochnerNormFields` constructor. Its frozen type retains the tetrahedral-star,
reaction, compact tensor, Ricci-norm C2, Ricci second-derivative,
Laplacian-continuity, rough-pairing-continuity, subordinate-geometry, ODE
primitive, and compact-history inputs, while removing the independent
`hPairDiff` premise. It also takes neither joint covariant-Ricci continuity nor
scalar-time-derivative continuity as a replacement argument. The canonical
exact-type probe passed and `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound`.

Revision-1 Job
`automatic-finite-nerve-bochner-norm-boundary-constructor-r1-a01` is preserved
as interrupted evidence. Its broad prompt produced two broker-rejected patch
requests, then terminated fail-closed with an empty worker patch after a
partial Pi stream and tool-crosscheck disagreement. Revision 2 froze a
7,409-byte patch that Codex had independently checked with `git apply --check`
and full stdin elaboration; its fresh Pi session then completed exactly one
scoped patch, one focused Lean check, and one patch-form diff request.

The frozen Task gate, a private incremental 4,065-job root build, root
elaboration, interface, semantic-surface, theorem-contract, and axiom audits
passed. The root-import audit retains exactly its four known direct-import
ledger failures: the two Cartan tail-overlap reductions, the scalar-variation
joint-continuity reduction, and the automatic finite-nerve joint-covariant-
Ricci tail-overlap compact-history boundary. The exact completion probe still
reports unknown identifier `Poincare.poincare_conjecture`.

The next theorem-shaped action is to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`
in the existing positive-time-overlap boundary module. Freeze its type as the
new ODE-primitive constructor type with the primitive moving input replaced by
`FixedTargetMovingGenericSuccessorGenericInverseEndpointODEPositiveTimeOverlapInputs3`
and compact-history feedback indexed by its existing conversion. Construct the
analytic field through the accepted analytic-data norm-fields constructor and
do not reintroduce `hPairDiff`. Before claiming the first Job at the final clean
HEAD, record, publish, and verify a new immutable Lake cache for that exact
base.

## 2026-07-21 Positive-Time and Tail-Overlap Boundary Checkpoint

The integration checkout advanced from
`3d8dc9f20a5b943d1fc55019ad968713947ca137` through accepted proof commits
`4b1f19736735a536ab2e5c6023da4fcfdf441bbb`,
`6bc720d764a74893e04ec27cc32e04272c0677f9`, and finally
`079292fae8a23cbb88082f2270a5e1c3f95cddf9`.

Harness Task
`automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor`
revision 2 was accepted from Job
`automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor-r2-a01`.
It adds
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`.
Revision-1 evidence is preserved as interrupted after Pi's stream and broker
events could not be reconciled, even though its later broker-applied patch was
mathematically valid. Revision 2 froze those exact patch bytes and passed a
fresh three-call session. Its strict gate is
`harness/v2/state/jobs/automatic-finite-nerve-positive-time-bochner-norm-boundary-constructor-r2-a01/gate.json`.

Task `automatic-positive-time-tail-bochner-norm-boundary-constructor`
revision 1 was then accepted from Job
`automatic-positive-time-tail-bochner-norm-boundary-constructor-r1-a01`.
Its declaration
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsAndTailOverlap`
replaces the positive-time moving input by the exact tail-only input, using the
verified tail-to-positive-time adapter while preserving the compact-history
index definitionally. Its strict gate is
`harness/v2/state/jobs/automatic-positive-time-tail-bochner-norm-boundary-constructor-r1-a01/gate.json`.

Finally, Task `automatic-scalar-tail-boundary-sphere-conclusion` revision 2
was accepted from Job
`automatic-scalar-tail-boundary-sphere-conclusion-r2-a01`. It defines the
named scalar-derivative/tail-overlap compact-history boundary, converts it to
the verified positive-time boundary, and proves
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.sphereConclusion`.
It also adds the single direct `Poincare.lean` import required to expose this
declaration canonically. Revision-1 Job
`automatic-scalar-tail-boundary-sphere-conclusion-r1-a01` is preserved as
rejected evidence: all focused commands passed, but its frozen scope forbade
the root import, so the mandatory `import Poincare` declaration probe returned
unknown identifiers. Revision 2 records that exact failure and its strict gate
is
`harness/v2/state/jobs/automatic-scalar-tail-boundary-sphere-conclusion-r2-a01/gate.json`.

Every accepted Job used exactly one scoped patch, one focused Lean check, and
one patch diff. Codex independently checked the exact frozen types and observed
only `propext`, `Classical.choice`, and `Quot.sound`. Post-integration root
elaboration and the interface, semantic-surface, theorem-contract, and axiom
audits passed. The root-import ledger shrank from four failures to exactly
three: the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe still reports unknown identifier
`Poincare.poincare_conjecture`; no unconditional final theorem exists.

No Harness Job or file lease remains active. The next theorem-shaped action is
to add
`AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`
in the now root-visible tail-boundary module. Freeze its arguments as the
accepted positive-time `ofBochnerNormFieldsAndTailOverlap` type, but return the
new scalar-tail structure and store the original tail input directly. The
exact first action in the next cycle is to create and schema-validate that
single-file Task at the final clean HEAD; before claiming its Job, record,
publish, and independently verify a new immutable Lake cache for that exact
base.

## 2026-07-21 Scalar-Tail Bochner Norm-Fields Constructor Checkpoint

The integration checkout advanced from
`b2d4ac3cafd3a64848877bcd950864371a7b2e73` through accepted proof commit
`cea0abe49a28290d6c37dcb365caa6440688c4b7`. Harness Task
`automatic-scalar-tail-bochner-norm-boundary-constructor` revision 2 was
accepted from Job
`automatic-scalar-tail-bochner-norm-boundary-constructor-r2-a01`; its strict
gate is
`harness/v2/state/jobs/automatic-scalar-tail-bochner-norm-boundary-constructor-r2-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no Harness Job or
file lease remains active.

The accepted declaration is
`Poincare.AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFields`.
It calls the verified positive-time `ofBochnerNormFieldsAndTailOverlap`
constructor, explicitly projects its analytic field at the ambient charted
space, and stores the original tail input and definitionally indexed
compact-history feedback in the scalar-tail record. Its frozen type retains
the reaction, compact tensor, Ricci-norm C2, Ricci second-derivative,
Laplacian-continuity, rough-pairing-continuity, subordinate-geometry,
tail-overlap, and compact-history inputs, while adding neither `hPairDiff` nor
joint covariant-Ricci or scalar-time-derivative continuity as replacement
arguments. The canonical exact-type probe passed and `#print axioms` reported
only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job
`automatic-scalar-tail-bochner-norm-boundary-constructor-r1-a01` is preserved
as interrupted evidence: it exhausted its 5,000-token output budget before
making a tool call and left an empty patch. Revision 2 froze the independently
checked 7,904-byte patch and completed exactly one scoped patch, one focused
Lean check, and one patch diff in a fresh supervised Pi session.

The frozen Task gate, targeted module build, root olean build, root
elaboration, interface, semantic-surface, theorem-contract, and axiom audits
passed. The root-import audit retains exactly its three established direct-
import gaps: the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe still reports `EXACT_DECLARATION_PROBE=absent`.

The next theorem-shaped dependency reduction is to prove, in
`NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean`,
the pointwise `CovTensor2DerivExtDifferentiableAt` premise for
`ricciVariationField (reaction.metric k)` from the reaction package's
`normalizedFlow`, `jointMetricEntries`, and `realizesFlow` fields, using
`ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow` and
`covTensor2DerivExtDifferentiableAt_of_extSecond`. Freeze that lemma as one
single-file Task before propagating it into a constructor without an explicit
`hRicSecond` argument. Before claiming a Job at the final clean HEAD, record,
publish, and independently verify the immutable Lake cache for that exact
base.

## 2026-07-21 Normalized-Flow-Slice Ricci Regularity Checkpoint

The integration checkout advanced from
`82c77b324b73ee7a196f4fba4fb35880bb73dc63` to accepted proof commit
`0a5915fb3c4bbb5e3b513a6911e9aed6e92af23b`. Harness Task
`reaction-flow-slice-ricci-second-regularity` revision 4 was accepted from Job
`reaction-flow-slice-ricci-second-regularity-r4-a01`; its strict gate is
`harness/v2/state/jobs/reaction-flow-slice-ricci-second-regularity-r4-a01/gate.json`
on `mj-zima`. The Job is passed, its lease is released, and no queued,
preparing, running, or reviewing Job remains.

The accepted declaration is
`Poincare.NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayAnalyticData3.ricciVariationField_covTensor2DerivExtDifferentiableAt`.
For every nonnegative time and point, it derives second differentiability of
`ricciVariationField (reaction.gt t)` from `reaction.normalizedFlow` and
`reaction.jointMetricEntries`. The proof first obtains C2 extended Ricci
entries with
`ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow`, then uses
`covTensor2DerivExtDifferentiableAt_of_extSecond` and the canonical Ricci
tensor-linearity lemmas. The exact frozen-type probe passed and `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 Job `reaction-flow-slice-ricci-second-regularity-r1-a01` is
preserved as interrupted evidence after it exhausted its budget on broker-
rejected context requests. Revision 2 is rejected evidence for the exact
missing `[SimplyConnectedSpace M]` source binder. Revision 3 produced the
green proof but is rejected because it exceeded its immutable three-call
contract after an initial patch rejection. Revision 4 froze those final patch
bytes and completed exactly one scoped patch, one focused Lean check, and one
patch diff in a fresh supervised Pi session.

The frozen Task gate, isolated and integrated root builds, root elaboration,
interface, semantic-surface, theorem-contract, and axiom audits passed. The
root-import audit reproduced exactly its three established direct-import gaps:
the two Cartan tail-overlap reductions and
`NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The exact
completion probe at the integrated commit still reports
`EXACT_DECLARATION_PROBE=absent`.

This checkpoint deliberately does not claim the stronger all-parameter result
for `reaction.metric k`. The record field `realizesFlow` states only
`reaction.metric (reaction.parameter t) = reaction.gt t`; no field makes
`reaction.parameter` surjective onto every `k : reaction.K`. Consequently the
previously proposed direct all-`k` lift is not justified by the reaction
package. The next theorem-shaped action is to isolate intrinsic Ricci C2
regularity for an arbitrary `ClosedSmoothRiemannianMetric` (starting with
`CovTensor2ExtContMDiffAt (ricciVariationField g) x 2`, using the existing
coordinate Ricci C2 lemmas), and then feed that result through
`covTensor2DerivExtDifferentiableAt_of_extSecond`. Freeze that one interface at
the final clean HEAD only after recording, publishing, and independently
verifying its exact-base immutable Lake cache.

## 2026-07-21 Chart Levi-Civita C3 Regularity Checkpoint

The integration checkout advanced from
`39054bc8268b9e4734c03ede4ccb0fe2ad8e7c2f` through the accepted proof
integration recorded by this commit. Harness Task
`chart-levicivita-section-c3-regularity` revision 4 was accepted from Job
`chart-levicivita-section-c3-regularity-r4-a01`; its reviewed worker commit is
`6e7eb9208248a2ffba8b11a71e8b566ee096fe9e` and its strict gate is
`harness/v2/state/jobs/chart-levicivita-section-c3-regularity-r4-a01/gate.json`
on `mj-zima`. The Job is passed and its lease is released.

The accepted declaration is
`CovariantDerivative.chartLeviCivita_chartTransportedLeviCivitaSection_contMDiffAt₃`.
It raises the existing chart-transported Levi-Civita section result from C2 to
C3 for a C4 metric and C4 transported section. The proof globalizes the local
section with a smooth bump, invokes the chart Levi-Civita C3 connection
regularity theorem, and transfers the resulting germ back to the original
section. The canonical exact-type probe passed and `#print axioms` reported
only `propext`, `Classical.choice`, and `Quot.sound`.

Revision-1 and revision-2 Jobs are preserved as interrupted evidence after
bounded sessions exhausted their output without a patch. Revision 3 was
interrupted before a known-unsafe zero-context patch could be broker-relocated.
Revision 4 froze the deletion-anchored patch, completed exactly one scoped
patch, one focused Lean check, and one patch diff, and then passed Codex's four
frozen acceptance commands. An independent exact-commit root build completed
all 4,068 jobs successfully before acceptance.

The local C3 interface is now resolved. Harness Task
`local-covariant-section-c3-regularity` revision 5 was accepted from Job
`local-covariant-section-c3-regularity-r5-a01`; its reviewed proof commit is
`1204566315a24f521536244b58d925f917585477`, its strict gate is
`harness/v2/state/jobs/local-covariant-section-c3-regularity-r5-a01/gate.json`,
and its lease is released. The accepted declaration is
`CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_three`. Its
canonical exact-type probe passed, and `#print axioms` reported only `propext`,
`Classical.choice`, and `Quot.sound`. The serial root build completed all 4,068
jobs. Root elaboration plus the interface, semantic-surface, and theorem-
contract audits passed; the theorem-contract audit first exposed and then
verified the required equality companion
`contMDiffAt_cov_section_of_contMDiffAt_three_eq`.

### 2026-07-22 closed Levi-Civita C3 frontier

Main now integrates
`Poincare.LeviCivitaExistence.closedLeviCivitaConnection_contMDiff₃` with
type `CovariantDerivative.ContMDiffCovariantDerivative
  (LeviCivitaExistence.closedLeviCivitaConnection g) 3`. The proof lowers the
metric's C4 regularity to the C3 chart input, applies
`chartTransportedLeviCivitaHom_contMDiffAt₃`, explicitly lowers the resulting
section regularity to C2, and supplies that C2 fact to the closed-chart germ
bridge. The exact `Poincare.poincare_conjecture` declaration remains absent.

Harness Task `closed-levicivita-connection-c3-regularity` revision 5 was
accepted through Job `closed-levicivita-connection-c3-regularity-r5-a01`.
That fresh bounded Pi session used one scoped patch, one successful Lean check,
and one diff read. Codex independently inspected the 107-line theorem proof,
committed it in the Job worktree as
`199f4173969951444c06cfc2a62f3273c3c7f715`, and passed the complete frozen
four-command focused review plus the exact canonical declaration probe before
accepting the Task. The integration checkpoint passed root elaboration at this
theorem source tree. Revision-3 Job `r3-a02` and
revision-4 Job `r4-a01` remain preserved as interrupted evidence; no Job or
file lease remains active.

The next theorem-shaped objective is arbitrary closed-metric Ricci C2
regularity,
`CovTensor2ExtContMDiffAt (ricciVariationField g) x 2`, using the new C3
closed Levi-Civita instance and the existing canonical first-regularity route
in `Poincare/Global/ScalarVariation.lean`. The first action in the next cycle
is to record, publish, and verify the immutable Lake cache for this final base,
then freeze the exact declaration name, source scope, imports, and focused gate
for that objective before dispatch. Do not reuse any interrupted worktree.

## 2026-08-31 Canonical Ricci C2 and Bochner Boundary Checkpoint

The integration branch `codex/formalization-until-6` advances clean base
`bc076f1e893c6ba834729f8bcb359a1f400a3e72` through seven reviewed commits:

- `1d44e245` proves
  `covTensor2ExtContMDiffAt_ricciVariationField_canonical`. The proof uses the
  C3 closed Levi-Civita connection and C2 Lie-bracket regularity to construct
  C2 curvature fields, pairs them with the metric, traces the auxiliary
  curvature tensor, and identifies the result with the Ricci tensor.
- `b1717bc3` packages fixed-time global C2 scalar-curvature regularity from a
  normalized Ricci flow with joint C3 metric entries.
- `81f97fc4` proves
  `covTensor2DerivExtDifferentiableAt_ricciVariationField_canonical`, deriving
  the former `hRicSecond` field from canonical Ricci C2 regularity.
- `074fc72d` adds
  `continuous_joint_covRicciNormSqAt_of_bochner_norm_fields_canonical` and
  `NormalizedFlowSphereCompactMeanEnergyMeasureReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinAnalyticData3.ofBochnerNormFieldsCanonical`.
  Both omit `hRicSecond`; the older APIs remain unchanged.
- `970026cb` lifts the same reduction into
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPrimitiveCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.
- `7b5a8b6a` carries the premise removal through
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODEPositiveTimeOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.
- `6465a615` completes the same reduction through
  `AutomaticFiniteNerveTetrahedralStarSmoothingReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinsteinGenericInverseEndpointODETailOverlapCompactHistoryBoundaryData3.ofBochnerNormFieldsCanonical`.

Focused elaboration passed for every changed Lean module. Exact declaration
probes reported only `propext`, `Classical.choice`, and `Quot.sound`. The
dependency refresh completed 3,755 jobs, root `Poincare.lean` elaboration
passed, and the interface, semantic-surface, and theorem-contract audits
passed. The axiom audit passed. The root-import audit retains exactly its
three pre-existing direct-import gaps:
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
and `NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The
project is still incomplete; an exact probe reports unknown identifier for
the reserved `Poincare.poincare_conjecture` endpoint.

The next exact theorem-shaped action is to prove
`ricciNormSqAt_contMDiffAt_two_canonical (g) (x)` in
`Poincare/Global/MetricFlowJointPinchingEvolution.lean`, using
`contMDiffAt_two_ricciNormSqAt_of_ricci_entries` and the new canonical Ricci C2
theorem. Then remove `hRicNorm₂` from new canonical Bochner constructors in
the same staged order. Do not replace or weaken the older constructors.

## 2026-09-03 Covariant-Ricci Joint Continuity Checkpoint

The isolated integration branch `codex/formalization-until-6` continued from
the unchanged `origin/main` base `bc076f1e`. The committed tree reached
`0a9d3aeb` before the next bounded proof attempt.

The first group of commits completed the canonical Bochner cleanup described
above. `bb3491ef` proves canonical C2 regularity of `ricciNormSqAt`.
`c0571e50`, `e0ee52d9`, `25ebbf90`, and `d1138972` remove the explicit
`hRicNorm₂` premise from new canonical analytic, primitive, positive-time, and
tail constructors while preserving every older API. `a7d770ff` packages the
Ricci curvature commutation theorem canonically, and `0defb8f0` removes the
duplicated commutation proofs from both flow-evolution modules.

The next group proves genuine real-time continuity of the intrinsic squared
covariant-Ricci derivative norm:

- `40b035fa` proves continuity of spatial Frechet derivatives of jointly C1
  maps, and `035a28cb` specializes it to coordinate Ricci entries.
- `9d3471e2` identifies `covRicciNormSqAt` with its full contraction in any
  tangent basis and the metric-raised dual basis.
- `85dd2462` and `cc8fd116` construct the coordinate covariant-Ricci entries
  and their six-index norm contraction.
- `bf6def94` proves that anchored tangent-field extensions remain smooth on
  the chart source.
- `ef448e97` identifies each coordinate covariant-Ricci entry with
  `covTensor2DerivAt` in the cutoff-one chart zone.
- `b98f65b2` identifies the six-index coordinate contraction with
  `covRicciNormSqAt`, transfers continuity back to `ℝ × M`, and proves
  `continuous_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three`.
  `4ab619b0` exposes this chain through direct root imports.

`9acc98c7` applies the real-time theorem on every compact interval and proves
`exists_uniformCovariantRicciDerivativeNormBound_on_compact_slab_of_metricEntriesJointContDiffAt_three`.
This is a finite-slab bound. It does not claim one constant on the noncompact
forward ray.

The compact-family boundary is now explicit instead of hidden inside a final
continuity premise:

- `a0b698a7` introduces `MetricFamilyCovRicciChartContinuousAt` and proves
  that inverse-metric coefficient continuity plus coordinate
  covariant-Ricci entry continuity on `K × E` gives the intrinsic continuity
  on `K × M` used by compactness.
- `e6d873a9` adds the analytic-data constructor
  `ofCovRicciChartContinuous`.
- `838690b1` derives the coordinate covariant-Ricci entries from inverse
  coefficients, Christoffel values, Ricci entries, and their spatial
  derivative.
- `08d06874` proves a separate quotient route: if nonnegative real time is a
  quotient parameterization of the whole family and realizes every metric,
  the real-time continuity theorem descends to `K × M`. `70dbfe04` exposes
  that route through `ofQuotientRealization`. Quotient surjectivity remains an
  explicit extra premise because the current reaction record does not supply
  it.
- `1befc74b`, `2e8d7110`, and `0a9d3aeb` lower the chart route further.
  Continuity of the blended metric gives inverse coefficients; its first
  spatial derivative gives Christoffel continuity; and the Christoffel first
  jet gives coordinate Ricci-entry continuity by the curvature formula and
  finite trace.
- `895ae4e2` differentiates the curvature formula and finite Ricci trace,
  deriving the Ricci spatial derivative from the first two Christoffel jets.
  `4d630fd7` reconstructs the full Christoffel value from the blended-metric
  first jet. `e259654f` derives the first Christoffel jet from directional
  metric jets through order two.
- `73a77f87` proves the inverse-raise and Koszul product rules needed to
  differentiate the Christoffel variation once more. It derives the second
  Christoffel jet from directional metric jets through order three and then
  constructs the full Ricci chart jet without independent Christoffel or
  Ricci regularity premises.
- `61c70659` packages that input as
  `MetricFamilyBlendedMetricThirdJetContinuousAt`, the exact `C^{0,3}`
  spatial contract over an arbitrary topological parameter space. It proves
  local and global intrinsic covariant-Ricci norm continuity. `0885296a`
  exposes this route through the analytic-data constructor
  `ofMetricFamilyThirdJets`.
- `81aaf1b3` lowers the operator-valued package to
  `MetricFamilyBlendedMetricEntryThirdJetContinuousAt`, whose fields are all
  real-valued fixed coordinate components. Finite-dimensional reconstruction
  recovers the operator jets and the same intrinsic continuity theorem.
- `dd3a1a44` and `dc17d909` add direct root imports for the compact-family
  modules. `dc3af356` and `c32177c8` expose both third-jet packages.

Focused Lean checks, targeted Lake builds, forbidden-term scans, diff checks,
and exact axiom probes passed for every accepted source commit. The new
theorems use only `propext`, `Classical.choice`, and `Quot.sound`. At
`4ab619b0`, root elaboration, the interface audit, semantic-surface audit,
6,008 theorem-contract checks, and the axiom audit passed. The root-import
audit retained exactly the three earlier wiring gaps named in the previous
checkpoint. A later 3,755-job targeted dependency repair and the subsequent
3,282 to 3,285-job module builds also passed. The known nonfatal
`LibrarySuggestions` timeout appeared during one cache build; that build
still exited successfully.

The final paused proof head is `c32177c8`. A serialized full `lake build`
completed all 4,077 targets. Root `Poincare.lean` elaboration, the interface
audit, semantic-surface audit, all 6,008 theorem-contract checks, and the axiom
audit passed. The root-import audit sees every new metric-family module and
retains exactly the same three pre-existing gaps:
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction`,
`CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction`,
and `NormalizedFlowHausdorffScalarVariationJointContinuityReduction`. The
exact final probe still reports unknown identifier
`Poincare.poincare_conjecture`; this checkpoint does not claim project
completion.

Real-time C3 regularity alone cannot prove continuity on an arbitrary compact
family. The current reaction record constrains `metric` only along
`parameter : Ici 0 → K`, and it supplies neither quotient surjectivity nor
parameter-side spatial-jet continuity. The formalization now names the latter
requirement down to scalar chart components, but no current compactification
constructor proves it for `reaction.metric`. The next theorem-shaped action is
to connect the concrete compact metric-family construction to
`MetricFamilyBlendedMetricEntryThirdJetContinuousAt`, or to strengthen that
construction with the exact componentwise `C^{0,3}` data. Do not infer this
record from compactness or from regularity of `gt` only.

## 2026-09-03 Explicit C0,3 Orbit Compactness Checkpoint

The isolated integration branch `codex/formalization-until-6` advanced from
the preceding compact-family checkpoint through proof-bearing source head
`c5179232`. The original `main` checkout was not modified.

This checkpoint replaces the previously opaque metric-topology boundary by an
explicit scalar compact-open C0,3 topology and carries that topology through
the normalized-flow positive-Einstein endpoint:

- `e6b5431f` and `9fcd8a06` connect stored joint C3 metric entries to the
  scalar third-jet covariant-Ricci constructor.
- `224e039d`, `3518a7e3`, `17faa895`, and `469e738a` define and expose the
  compact-open scalar third-jet topology, prove joint intrinsic
  `covRicciNormSqAt` continuity on an orbit closure, and turn compactness of a
  nonempty orbit closure into a uniform full covariant-Ricci derivative bound.
- `ff5723b4` and `91c95958` feed that bound directly into the reaction-decay
  positive-Einstein package and restrict the required orbit to the honest
  forward family indexed by `Ici 0`.
- `42f6d185` proves that the value slots recover the metric, so
  `metricEntryThirdJetProfile` is injective and an embedding. It also proves
  that a continuous realization from a compact parameter space has compact
  orbit closure; continuity of the indexing map is unnecessary.
- `754c4a78` exposes compact-realization and full scalar-profile joint-
  continuity constructors at the positive-Einstein boundary.
- `ae0e2cfe`, `9b9599b1`, and `0d92c260` apply componentwise
  Arzela--Ascoli and Tychonoff in the profile target, characterize metric-orbit
  compactness by the realized part of the profile closure, and derive the
  uniform covariant-Ricci bound once every profile limit is realized by an
  actual metric.
- `58f241e9` imports the new compactness modules at the root. `c5179232`
  supplies compact-containment and pointwise-bounded Ascoli constructors that
  reach the established positive-Einstein analytic data for the forward flow.

No global topology or T2 instance was installed on the metric type. The
topology remains local to each theorem. Exact declaration and axiom probes for
the new chain report only `propext`, `Classical.choice`, and `Quot.sound`. The
missing Mathlib Ascoli object was repaired with a targeted 927-job build.

At `c5179232`, a serialized full `lake build` completed all 4,082 targets.
Root `Poincare.lean` elaboration, the interface audit, semantic-surface audit,
all 6,008 theorem-contract checks, and the axiom audit passed. The root-import
audit still fails on exactly the same three pre-existing direct-import gaps:

```text
Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction
Poincare.Global.CartanFixedTargetMovingGenericInverseEndpointODETailOverlapProviderReduction
Poincare.Global.NormalizedFlowHausdorffScalarVariationJointContinuityReduction
```

An exact `import Poincare` probe still reports
`Unknown identifier Poincare.poincare_conjecture`; this checkpoint does not
claim completion.

The remaining compactness obligation is now precise. Componentwise
equicontinuity and pointwise bounds make the ambient C0,3 profile closure
compact, but they do not prove that a limit profile is a smooth positive-
definite metric. The forward endpoint therefore retains
`hForwardProfileLimitsRealized`. This premise cannot be inferred from the
embedding alone: finite C0,3 limits can lose smoothness, and positive
definiteness can degenerate without a uniform lower bound. The alternative
compact-parameter route retains the equally explicit requirement that
`reaction.metric` be continuous in the full profile topology; the reaction
record's local real-time C3 field does not imply continuity of its arbitrary
extension over `reaction.K`.

The exact first action for the next proof cycle is to freeze one theorem with
conclusion

```text
closure (Set.range (metricEntryThirdJetProfile ∘ forward)) ⊆
  Set.range metricEntryThirdJetProfile
```

for `forward t = reaction.gt t.1`, and prove it from explicit uniform higher-
regularity and two-sided metric nondegeneracy hypotheses. If the repository
does not yet supply those estimates, stop with their exact Lean types rather
than weakening or assuming the realized-limit conclusion.

## Executable Harness Boundary

The primary path is:

```text
Codex GPT on mj-zima
  -> Harness v2 Task/Job SQLite, leases, artifacts, worktrees, and gates
  -> one fresh bounded Pi JSON Job session
  -> Leanstral on the existing private vLLM endpoint
```

Codex is the only frontier selector, worktree allocator, reviewer, gate owner,
Task acceptance authority, and commit authority. Each Job gets a new Pi
process/session. Pi built-ins are disabled, and Leanstral receives exactly:

- `read_context`
- `search_symbol`
- `apply_patch_scoped`
- `lean_check`
- `git_diff`
- `report_blocked`

As of 2026-07-20 the executable worker plane can fill up to four fixed Pi
execution slots from fully prepared queued Jobs with disjoint SQLite file
leases. The supervisor renews each running lease, releases its execution slot
when Pi exits, and routes a sealed successful result to Codex-owned
`reviewing`. Blocked or unsuccessful runs keep immutable evidence; only Codex
may create a fresh attempt. Reviewing Jobs do not consume Leanstral execution
capacity, so independent serial review can overlap another disjoint proof Job.

The 2026-07-21 throughput control update adds a configured execution-backlog
target, defaulting to four and never exceeding the four-session ceiling. The
target counts queued, preparing, and running Jobs; reviewing Jobs do not hide
unused inference capacity. Codex must replenish a safe disjoint same-base batch
before optional repository-wide audits or record the concrete lease, cache,
dependency, resource, or theorem-shape reason for underfill. Compatible
accepted Jobs still pass independent frozen gates and one serial Codex merge
queue, while broad root audits may run once per compatible integration batch.
Cycle results, `status.sh`, and the three-hour heartbeat expose the target and
underfill. This policy does not authorize overlapping leases, duplicate or
filler Tasks, extra Leanstral tools, or any worker acceptance/commit authority.

There is no worker access to an unrestricted shell, SSH, arbitrary filesystem
or network tools, Git mutation, worktree deletion, Docker, Ray, tmux, or model
service management. `harness/v2/worker/` is fallback-only: keep its endpoint
health check, deterministic prompt snapshot, and explicit one-shot inference
path, but do not extend it into another agent loop.

The control plane stores validated Task/Job transitions and fenced leases in
SQLite and keeps prompts, Pi JSON events, tool results, diffs, compiler output,
blocked reports, gates, and reviews append-only under ignored Job artifacts. A
passed Job never accepts its Task; Codex must inspect the diff and independently
rerun the frozen gate first.

## Verified Live Deployment Facts

Checks and the bounded release exercise on 2026-07-20 established:

- The integration checkout is `/srv/projects/poincare`; the committed control
  checkout is `/srv/data/poincare-harness/control`; Job worktrees are beneath
  `/srv/projects/poincare-worktrees`.
- The project toolchain reports Lean `4.30.0-rc2` on `mj-zima`.
- Production Pi is the fresh sealed installation
  `/srv/data/poincare-harness/pi-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`,
  with owner-only attestations under
  `/srv/data/poincare-harness/pi-attestation-0.80.10-e755c49fe6ad637ee5a7531735e8c3129f6f6247`.
  The legacy unsealed `/srv/data/poincare-harness/pi` tree was not mutated or
  reused.
- Fresh runtime state is
  `/srv/projects/poincare/harness/v2/state/harness.sqlite3`; no Mac SQLite,
  WAL, staging directory, or prior Mac Job artifact was transferred.
- The existing private vLLM API is healthy, serves model ID `leanstral-1.5`,
  and reports a 200,000-token model limit.
- The model artifact is `mistralai/Leanstral-1.5-119B-A6B`, revision
  `81592da95d94ab0439bfce16df1d55b402e598b6`.
- The exact-base root bootstrap completed successfully: 4,064/4,064 jobs,
  `exit_code=0`, at `2026-07-20T00:39:27Z`. The focused automatic scalar-time
  derivative module then completed 3,382/3,382 jobs, `exit_code=0`, at
  `2026-07-20T00:40:20Z`. No overlapping Lean build or owned bootstrap tmux
  session remained at the subsequent read-only check.
- The bounded accepted Job used a fresh Pi JSON session, exactly the six scoped
  tools, dispatch generation 1 and lease token 1. Its sealed Pi run reported
  success with 8 tool events; Codex's clean accepted tree is
  `0581d0c497d584406dbfd75386214e1ed67426b6`.
- Serial integration verification passed root elaboration plus the interface,
  semantic-surface, theorem-contract, and axiom audits. The portable
  root-import audit then reported five pre-existing direct-import ledger gaps,
  so the root-import and full completion audits correctly remain non-green.

The private endpoint URL belongs only in ignored configuration and Job
evidence. Do not restart or modify the live vLLM/Ray service, inspect or manage
its GPU processes, change model files, or take ownership of the Spark runtime.

The Mac tldraw offline canvas is titled inside the drawing `Poincare Proof
Orchestration`, stable document ID `nPBFgUN4xNLuW1nWbbtkE` (the app currently
lists the unsaved canvas as `Untitled`). It shows the Pi-centered chain, exact
six tools, Codex-only authority, and the exact long-term Harness completion
terminal. The Mac lane records the final setup-thread handoff and future
on-demand inspection; it does not imply that this thread remains alive. The
`mj-zima` observe process produces durable evidence every 10,800 seconds.

## Operator Handoff

The persistent deployment owns exactly `poincare-control`,
`poincare-workers`, and `poincare-observe`. From the Mac, use:

```sh
ssh -i ~/.ssh/id_ed25519_zimaboard_ai_lab -o IdentitiesOnly=yes \
  mj-kang@192.168.30.227 \
  '/srv/data/poincare-harness/control/harness/v2/deploy/status.sh /srv/data/poincare-harness/private/deploy.env'
```

Durable three-hour evidence is under
`/srv/projects/poincare/harness/v2/state/deploy/`, especially
`observe/heartbeats.jsonl` and `observe/snapshots/`. To request a graceful
drain without deleting state:

```sh
/srv/data/poincare-harness/control/harness/v2/deploy/stop.sh \
  /srv/data/poincare-harness/private/deploy.env
```

Restart with the corresponding `launch.sh` command. The SQLite store and Job
artifacts, not tmux scrollback, are recovery state. This Mac setup thread ends
after its one deployment report; it does not remain alive for the three-hour
loop. The long-term Harness may report proof completion only after the exact
declaration probe, allowed-axiom check, clean stable HEAD, and full completion
audit all pass.

Known non-blocking release follow-ups are bounded: Pi 0.80.10 emits harmless
read-only global-settings lock warnings in the sealed namespace, and its
cumulative JSON message updates made this successful 7,116-token Job's event
files large. Both are retained as evidence and remain within the Job disk
budget; neither expands Leanstral's authority or blocks restart/recovery. The
root-import ledger still needs direct `Poincare.lean` imports for the two
Cartan tail-overlap reductions and the scalar-variation continuity reduction.
Their current transitive visibility remains sufficient for exact
`import Poincare` type probes; they are separate wiring follow-ups rather than
proof completion.
