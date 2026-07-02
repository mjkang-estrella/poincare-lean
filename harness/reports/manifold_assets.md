# M1 Asset Audit: Existing Manifold-Level Layer

## Scope and method

Contract read first: `harness/worker_contract.md`. I treated the honesty rules
as binding: no credit for opaque certificates, trivial `Prop` fields, or
projection stacks that only repackage assumptions.

Discovery command used:

```sh
rg -l "CovariantDerivative|TangentSpace I|ModelWithCorners" Poincare | sort
```

That search found the files listed in the inventory below. I also included
`Poincare/MaximumPrinciple.lean` because the task named it explicitly, even
though it does not contain any of the three discovery strings.

I used these integrity classes:

- `GENUINE`: the file proves concrete mathematical facts about explicit
  objects, not just about arbitrary certificates.
- `MIXED`: the file has useful typed data or real reductions, but also relies
  on large package assumptions, downstream certificates, or projection fields.
- `VACUOUS`: the file's main result can be obtained by arbitrary `Prop` fields,
  `True`, or equivalent empty evidence.
- `LEGACY-SCAFFOLD`: the file is mainly a deprecated/compatibility/progress
  layer. It may not be literally `True`-vacuous, but it should not be credited
  as new Ricci-flow analysis.

One global check for forbidden Lean placeholders/declarations found no Lean
source uses. Matches were only in harness/docs/ledger text.

## Executive findings

There is a real manifold-level track now. The strongest theorem-bearing layer is
the `CovariantDerivative` route:

- `KoszulExistence.lean` constructs a global Levi-Civita
  `CovariantDerivative` from a symmetric, nondegenerate, pairing-regular metric.
- `LeviCivitaUniqueness.lean` proves pointwise uniqueness of torsion-free,
  metric-compatible connections.
- `RiemannCurvatureOperator.lean`, `LocalConnectionRegularity.lean`,
  `CurvatureTensoriality.lean`, and `BianchiIdentity.lean` define and prove
  tensoriality/symmetry/Bianchi facts for curvature and Ricci contractions.
- `RicciFlowEquation.lean` defines a real pointwise Ricci-flow PDE:
  the time derivative of the metric pairing equals `-2 * Ricci`.
- `Global/LeviCivitaExistence.lean` specializes the Koszul construction to
  `ClosedSmoothRiemannianMetric` and proves existence of a metric-compatible,
  zero-torsion global Levi-Civita connection in the closed smooth context.

The key limitation is also clear: the repo proves only flat/static concrete
Ricci-flow instances, plus conditional theorems such as Einstein scaling once
the Einstein/Ricci trace hypothesis is supplied. I found no nontrivial closed
manifold Ricci-flow solution constructed from real manifold data.

`Poincare/RicciFlow.lean` and the older finite-extinction/surgery package layers
must be treated separately. `RicciFlow.lean` has a typed candidate equation
interface, but its built-in constructors are stationary-zero routes and stored
candidate equalities; it is not the same as the derivative statement in
`RicciFlowEquation.lean`. `INTEGRITY_ASSESSMENT.md` already records that
`FiniteExtinctionByRicciFlowWithSurgeryProductionCertificate` in
`Poincare/RicciFlowInterface.lean` is vacuous because it stores arbitrary
`Prop` fields and proofs. `ProofProgress/GroundedFiniteExtinctionCertificate.lean`
mitigates that by requiring named packages, but those packages are still
frontier assumptions rather than Perelman analysis.

## Core manifold analytic files

### `Poincare/KoszulExistence.lean` - GENUINE

Key definitions and theorems:

- `koszulRHS`: the Koszul formula right-hand side for three vector fields.
- `koszulRHS_smul_right`, `koszulRHS_add_right`,
  `koszulRHS_eq_zero_of_value_eq_zero`, `koszulRHS_congr_of_value_eq`:
  tensoriality/locality in the test field.
- `koszulRHS_smul_left`, `koszulRHS_add_left`,
  `koszulRHS_eq_zero_of_direction_value_eq_zero`,
  `koszulRHS_congr_of_direction_value_eq`: tensoriality/locality in the
  direction field.
- `koszulFunctionalAt`, `leviCivitaValueAt`, `b_leviCivitaValueAt`: use
  nondegeneracy to recover the connection value represented by the Koszul
  functional.
- `leviCivitaValueAt_torsionFree`: the constructed point value is symmetric in
  the torsion-free sense.
- `leviCivitaValueAt_compat`: the constructed point value satisfies metric
  compatibility.
- `leviCivitaCovFun` and `leviCivitaConnection`: build the bundled
  `CovariantDerivative`.
- `isCovariantDerivativeOn_leviCivitaCovFun`: proves the connection axioms.
- `leviCivitaConnection_torsionFreeAt`,
  `leviCivitaConnection_metricCompatibleAt`,
  `leviCivitaConnection_isLeviCivitaAt`: the connection is Levi-Civita.
- `isRicciFlowSolutionAt_of_metric`: for a time-dependent metric family, the
  Levi-Civita side of `IsRicciFlowSolutionAt` is discharged by the Koszul
  connection; the actual flow equation remains an explicit hypothesis.
- `leviCivitaConnection_eq_of_isLeviCivita`: constructed connection agrees
  pointwise with any other Levi-Civita connection.

Integrity check:

This is theorem-bearing. The hypotheses are mathematical: symmetry,
nondegeneracy, and differentiability of metric pairings. The construction uses
`if h : MDiffAt (T% Y) x then ... else 0` inside `leviCivitaCovFun`; that is
not vacuity, because all connection laws are stated under section
differentiability hypotheses and the file proves the bundled
`IsCovariantDerivativeOn` obligations. No opaque `Prop` certificate controls the
main results.

### `Poincare/LeviCivitaUniqueness.lean` - GENUINE

Key definitions and theorems:

- `MetricCompatibleAt`: pointwise metric-compatibility identity for a
  `CovariantDerivative`.
- `TorsionFreeAt`: pointwise zero torsion identity.
- `leviCivita_unique_at`: pointwise uniqueness of a torsion-free,
  metric-compatible connection.
- `koszul_formula`: recovers the Koszul formula for any such connection.

Integrity check:

Genuine. The proof is an actual algebraic uniqueness argument using the
metric-compatibility and torsion-free identities. No certificate structures.

### `Poincare/RiemannCurvatureOperator.lean` - GENUINE

Key definitions and theorems:

- `curvatureOp`: `R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z -
  nabla_[X,Y] Z`.
- `IsFlat`: all curvature operators vanish.
- `DerivRegularAt`: regularity hypothesis ensuring the differentiated fields
  needed by tensoriality exist at a point.
- `curvatureOp_antisymm`, `curvatureOp_self`: curvature is antisymmetric in the
  first two slots.
- `curvatureOp_tensorialAt_fst`,
  `curvatureOp_tensorialAt_snd`: pointwise tensoriality in first and second
  slots under `DerivRegularAt`.
- `curvatureTensorAt`: pointwise multilinear curvature tensor from extensions.
- `curvatureEndAt`: curvature endomorphism for fixed first/two point vectors.
- `ricciTraceAt`: Ricci contraction by trace of the curvature endomorphism.
- `curvatureEndAt_add`, `curvatureEndAt_smul`,
  `ricciTraceAt_add`, `ricciTraceAt_smul`: linearity in the traced direction.

Integrity check:

Genuine. `DerivRegularAt` is a real regularity side condition; it is proven from
local extension/smoothness elsewhere (`LocalConnectionRegularity.lean`) rather
than being an impossible or arbitrary certificate.

### `Poincare/LocalConnectionRegularity.lean` - GENUINE

Key definitions and theorems:

- `mdiffAt_cov_section_of_contMDiffAt`: local regularity for applying a `C^1`
  connection to `C^2`/differentiable sections.
- `derivRegularAt_of_contMDiff`: supplies `DerivRegularAt` from smooth data.
- `derivRegularAt_extend`: extensions of a tangent vector satisfy the regularity
  predicate.
- `ricciBilinearAt`: pointwise Ricci bilinear form using extended vector fields
  and `ricciTraceAt`.
- `curvatureOp_congr_of_eventuallyEq`,
  `curvatureTensorAt_congr_of_eventuallyEq`: germ locality for curvature.

Integrity check:

Genuine. The file turns smoothness and extension hypotheses into the regularity
objects required by the curvature layer. No opaque certificate layer.

### `Poincare/CurvatureTensoriality.lean` - GENUINE

Key definitions and theorems:

- `curvatureOp_smul_field`, `curvatureOp_add_field`,
  `curvatureOp_eq_zero_of_value_eq_zero`: field-slot tensoriality and locality.
- `ricciTraceAt_eq_ricciBilinearAt`: identifies traced curvature with the
  bilinear Ricci definition.
- `ricciBilinearAt_add_left`, `ricciBilinearAt_smul_left`,
  `ricciBilinearAt_add_right`, `ricciBilinearAt_smul_right`: Ricci is bilinear.
- `bianchi_first_at`: first Bianchi identity at a point from torsion-freeness.
- `curvature_pair_antisymm_of_compat`, `curvature_pair_symm`: metric curvature
  symmetries under compatibility hypotheses.
- `ricciBilinearAt_symm`: Ricci symmetry for compatible torsion-free
  connections.
- `pairCurvatureEndAt`, `sectionalNumeratorAt`, `ricciDualAt`,
  `scalarCurvatureAt`: derived metric pairings, sectional numerator, Ricci
  endomorphism, and scalar curvature.

Integrity check:

Genuine. Some theorems require strong metric-compatibility and pairing
differentiability hypotheses, but those hypotheses are meaningful and are
supplied in the Levi-Civita/model layers. I found no `of_agree`-style
unsatisfiable hypothesis here.

### `Poincare/BianchiIdentity.lean` - GENUINE

Key definitions and theorems:

- `bianchi_first`: for a torsion-free `CovariantDerivative`, the cyclic sum of
  `curvatureOp X Y Z` is zero.

Integrity check:

Genuine. The theorem is a direct curvature identity, not an interface
projection.

### `Poincare/RicciFlowEquation.lean` - GENUINE

Key definitions and theorems:

- `IsLeviCivitaAt`: `MetricCompatibleAt g cov x` and `TorsionFreeAt cov x`.
- `IsRicciFlowSolutionAt`: a real pointwise Ricci-flow PDE. For every time
  slice, `cov t` is Levi-Civita for `g t` at `x`; for every `C^2` field `Z`,
  regularity witness `hreg`, and tangent vector `w`,
  `deriv (fun t => g t x (Z x) w) t0 =
   -2 * ricciTraceAt (cov t0) hreg w`.
- `flat_metricCompatibleAt`, `flat_torsionFreeAt`, `flat_isLeviCivitaAt`:
  the flat connection is Levi-Civita for the Euclidean metric.
- `flat_ricciTraceAt_eq_zero`, `flat_ricciBilinearAt_eq_zero`: flat Ricci
  contractions vanish.
- `euclidean_static_isRicciFlowSolutionAt`: the Euclidean static metric is a
  solution.
- `IsRicciFlowSolutionAt.time_shift`: time translation of a solution.

Integrity check:

Genuine. `IsRicciFlowSolutionAt` is not the old candidate-field interface; it
contains the metric time derivative and Ricci trace in the same theorem
statement. The only direct concrete solution in this file is flat/static
Euclidean. I found no nontrivial closed-manifold Ricci-flow instance here.

### `Poincare/CurvatureConditions.lean` - GENUINE

Key definitions and theorems:

- `IsEinsteinAt`: `ricciBilinearAt cov x v w = lam * g x v w` pointwise.
- `HasNonnegRicciAt`, `HasPosRicciAt`: pointwise Ricci sign predicates.
- `scalarCurvatureAt_of_einstein`: scalar curvature trace under the Einstein
  condition.
- `HasNonnegRicciAt.of_agree`, `HasPosRicciAt.of_agree`,
  `IsEinsteinAt.of_agree`: transfer curvature conditions across connections
  that agree on the needed extensions.
- `flat_isEinsteinAt_zero`, `flat_hasNonnegRicciAt`: flat examples.
- `einstein_isRicciFlowSolutionAt`: if `cov` is Levi-Civita for `g0` at `x`
  and the Ricci trace satisfies the Einstein trace formula, then
  `(1 - 2 * lam * t) * g0` with fixed `cov` solves the pointwise Ricci-flow
  equation.
- `leviCivitaConnection_const_smul`: constant scaling preserves the
  Levi-Civita connection under pairing-regularity assumptions.
- `IsRicciFlowSolutionAt.parabolic_rescale` and
  `IsRicciFlowSolutionAt.parabolic_reparam`: scaling/reparametrization
  symmetries of the pointwise equation.
- `ricciTraceAt_eq_zero_of_static`,
  `isRicciFlowSolutionAt_const_of_ricciFlat`: static Ricci-flat metrics solve
  the pointwise equation.
- `IsEinsteinAt.hasPosRicciAt`, `IsEinsteinAt.const_smul`,
  `IsEinsteinAt.flow_evolution`: pointwise Einstein/sign/evolution helpers.

Integrity check:

Genuine, but conditional. The `of_agree` lemmas have strong agreement
hypotheses, yet those are not obviously unsatisfiable: they can be supplied by
equality or Levi-Civita uniqueness. `einstein_isRicciFlowSolutionAt` is a real
PDE theorem, but it assumes the Einstein trace identity rather than deriving it
from a concrete nonflat metric. I found no nontrivial concrete Einstein/closed
manifold flow instance proved in this repo.

### `Poincare/ChartIdentification.lean` - GENUINE

Key definitions and theorems:

- `mlieBracket_apply_chart`: chart expression for the manifold Lie bracket.
- `mpullbackWithin_extChartAt_symm_self`: chart pullback identity at the chart
  center.
- `extDerivFun_apply_chart`: exterior derivative in chart coordinates.
- `extDerivFun_apply_mlieBracket`: bracket derivative identity by chart
  reduction.

Integrity check:

Genuine. These are chart-calculus identities used by the connection layer.

### `Poincare/ChartTransport.lean` - GENUINE

Key definitions and theorems:

- `chartMetric`: pulls a model bilinear form back to a chart tangent space.
- `chartMetric_symm`, `chartMetric_nondegenerate`, `chartMetric_posDef`,
  `chartMetric_nondegenerate_center`: pointwise metric properties under
  chart-derivative invertibility.
- `chartMetric_model_space`: recovers the model-space metric in the identity
  chart case.
- `blendedChartMetric`: blends a model metric with a background metric by a
  cutoff.
- `exists_blending_cutoff`: produces the cutoff used by the local metric.
- `exists_global_chart_metric`: local chart metric existence payload.
- `contMDiffOn_chartMetric_pairing`: smoothness of chart metric pairings on a
  chart domain.
- `chartBilin`, `chartBilin_nondegenerate`: model-space bilinear form used for
  chart Levi-Civita.
- `chartLeviCivita_torsionFreeAt`,
  `chartLeviCivita_metricCompatibleAt`,
  `chartLeviCivita_contMDiff`: local chart Levi-Civita is torsion-free,
  compatible, and smooth.

Integrity check:

Genuine as a local chart/model bridge. Its frontier is explicit in the comments
of `Global/LeviCivitaExistence.lean`: the remaining hard part for this route is
transporting chart-domain operators back into one global `CovariantDerivative`
and proving overlap agreement. The file does not claim that global gluing step.

### `Poincare/FlatModelConnection.lean` - GENUINE

Key definitions and theorems:

- `flatCovariantDerivative`: flat covariant derivative on a model vector space.
- `flatCovariantDerivative_apply`: identifies it with the Frechet derivative.
- `flat_curvatureOp_eq_zero` and flat Ricci/curvature consequences used by
  `RicciFlowEquation.lean`.
- `flatCovariantDerivative_torsionFreeAt` and flat metric-compatibility facts.

Integrity check:

Genuine. It constructs and proves facts about the actual flat connection.

### `Poincare/EuclideanLeviCivitaCheck.lean` - GENUINE

Key definitions and theorems:

- Euclidean metric symmetry, nondegeneracy, and pairing differentiability.
- `leviCivitaConnection_euclidean_eq_flat`: the Koszul Levi-Civita connection
  agrees with the flat connection.
- Euclidean curvature/sectional numerator zero facts.

Integrity check:

Genuine concrete sanity check of the Levi-Civita construction.

### `Poincare/ModelChristoffel.lean` - GENUINE, MODEL-SPACE

Key definitions and theorems:

- `christoffelAt`, `christoffelOneForm`, `modelLeviCivita`: coordinate/model
  Christoffel and Levi-Civita connection.
- `modelLeviCivita_torsionFreeAt`,
  `modelLeviCivita_metricCompatibleAt`,
  `modelLeviCivita_contMDiff`: model connection has the expected LC properties.
- `modelLeviCivita_ricciBilinearAt_symm`: Ricci symmetry for the model LC.
- `isRicciFlowSolutionAt_of_model_metric`: wraps a model metric family into
  `IsRicciFlowSolutionAt` once the explicit metric derivative equals Ricci.
- `modelLeviCivita_const_eq_flat`,
  `modelLeviCivita_const_ricciBilinearAt_eq_zero`,
  `const_metric_static_model_flow`: constant metrics give flat/static flows.
- `covariantHessian`, `curvedLaplacian`, `curvatureOp_modelLeviCivita_extend`,
  `ricci_identity`: model-space second-derivative and curvature identities.

Integrity check:

Genuine but not an abstract-manifold port. It is the cleanest bridge between
the coordinate `ModelLaplacian.lean` world and the pointwise manifold Ricci-flow
predicate.

### `Poincare/ModelLaplacian.lean` - GENUINE, SINGLE-CHART SOURCE

Key definitions and theorems:

- `modelLaplacian` and algebraic rules:
  `modelLaplacian_add`, `modelLaplacian_smul`, `modelLaplacian_quadratic`,
  `modelLaplacian_nonneg_of_isLocalMin`, `modelLaplacian_eq_trace_hessianOperator`.
- Parabolic principles:
  `parabolic_min_principle_strict`, `parabolic_min_principle`,
  `heat_supersolution_nonneg_preserved`, `curved_parabolic_min_principle`,
  and time-varying variants.
- Scalar curvature and Hamilton chain:
  `scalarCurvatureAt_eq_trace_E`, `flat_scalarCurvatureAt_eq_zero`,
  `hamilton_scalar_lower_bound`, `hamilton_finite_time_singularity`,
  `hamilton_scalar_evolution_of_bianchi`,
  `hamilton_scalar_evolution_ricci_flow`,
  `curved_hamilton_ricci_flow_singularity_bianchi_free`.
- Bianchi/variation:
  `coord_first_bianchi`, `coord_second_bianchi`,
  `coord_twice_contracted_bianchi`, `ricciDeriv_*`,
  `lichnerowiczLaplacian_*`.
- Pinching/round-model ODEs:
  `ricciNormSq_ge_scalar_sq_div`,
  `pinching_gap_nonneg`, `pinching_gap_eq_n_mul_tracelessNormSq`,
  `round_sphere_*`, `hyperbolic_*`.
- Bochner:
  `bochner_flat`, `bochner_inequality`, `bochner_eigenfunction`,
  `curvedLaplacian_coordGradNormSq_bochner*`.

Integrity check:

Genuine, but mostly single-chart/model-coordinate. It should not be counted as
already ported to the abstract closed-manifold track.

### `Poincare/ModelLaplacianRootAliases.lean` - LEGACY-SCAFFOLD

Key definitions and theorems:

- Alias/equality-export layer for selected `ModelLaplacian` theorems, e.g.
  `eventually_mdiffAt_of_contMDiffAt`.

Integrity check:

Not vacuous in the arbitrary-`Prop` sense, but it is an alias/compatibility
layer, not new analysis.

### `Poincare/MaximumPrinciple.lean` - GENUINE, SCALAR ANALYTIC

Key definitions and theorems:

- `ode_comparison_nonpos`, `ode_comparison_nonneg`: scalar ODE comparison.
- `riccati_lower_bound`, `riccati_forces_finite_time`,
  `riccati_upper_bound`, `riccati_doubling_time`: Riccati inequalities and
  finite-time forcing.
- `einstein_scalar_hasDerivAt_riccati`: scalar ODE for Einstein scaling.
- `secondDeriv_nonneg_of_isLocalMin`, `hessian_nonneg_of_isLocalMin`: calculus
  at local minima.
- `exists_first_zero`: first-zero existence helper.

Integrity check:

Genuine scalar calculus. It is not itself manifold tensor PDE, but it ports
cleanly once scalar curvature evolution/minimum infrastructure exists on the
manifold side.

## Global closed-manifold files

### `Poincare/Global/RiemannianContext.lean` - GENUINE

Key definitions and theorems:

- `ClosedSmoothModel`, `closedSmoothModelWithCorners`: finite-dimensional
  Euclidean smooth model.
- `ClosedSmoothRiemannianMetric`: alias for Mathlib's smooth Riemannian metric
  on a closed smooth manifold context.
- `contMDiff_inner`, `contMDiff_fiber_inner`: smoothness of metric pairings.
- `inner_symm`, `inner_pos`, `inner_nonneg`: metric positivity and symmetry.
- `induced_edist_ne_top`: induced metric-space sanity fact under compactness.

Integrity check:

Genuine packaging around Mathlib Riemannian metrics.

### `Poincare/Global/LeviCivita.lean` - GENUINE

Key definitions and theorems:

- `MDiffAtTangentField`: pointwise differentiability predicate for tangent
  vector fields.
- `IsMetricCompatible`: global closed-manifold metric-compatibility identity.
- `levi_civita_unique`: uniqueness of a torsion-free, metric-compatible
  `CovariantDerivative` on differentiable tangent fields.

Integrity check:

Genuine. The proof uses Mathlib's `CovariantDerivative.difference`, torsion,
and positive definiteness.

### `Poincare/Global/LeviCivitaExistence.lean` - GENUINE

Key definitions and theorems:

- `metric_pairing_mdiffAt`: a smooth Riemannian metric differentiates pairings
  of differentiable tangent fields.
- `metric_nondegenerate`: positive-definiteness gives left nondegeneracy.
- `closedLeviCivitaConnection`: the Koszul `CovariantDerivative` specialized to
  a `ClosedSmoothRiemannianMetric`.
- `closedLeviCivitaConnection_metricCompatible`: compatibility with the closed
  smooth metric.
- `closedLeviCivitaConnection_torsion`: zero Mathlib torsion tensor.
- `levi_civita_exists`: existence of a metric-compatible, zero-torsion global
  connection.

Integrity check:

Genuine and the current live frontier of the closed-manifold track. It proves
the closed smooth Levi-Civita existence theorem, but it does not yet prove
smoothness of the constructed global connection as a
`ContMDiffCovariantDerivative`, nor does it define the closed-manifold Ricci
tensor/scalar fields from that connection.

### `Poincare/Global/Statement.lean` - GENUINE STATEMENT

Key definitions and theorems:

- `PoincareConjecture`: the project-level Poincare statement as a `Prop`.

Integrity check:

Statement only. It is not an analytic theorem.

### `Poincare/Global/Alignment.lean` - GENUINE STATEMENT ALIGNMENT

Key definitions and theorems:

- `MathlibPoincareStatement`: alignment statement against Mathlib-style
  topological data.
- `poincareConjecture_of_mathlibPoincareStatement`: implication from the
  aligned Mathlib statement to the local statement.

Integrity check:

Genuine statement alignment, not analytic progress.

## Legacy and package layers found by grep

These files contain the discovery strings because they are generic over
`ModelWithCorners`, `TangentSpace`, or package data built around the analytic
layer. They are not all theorem-bearing manifold analysis. I audited them as
follows.

| File | Key role | Integrity |
| --- | --- | --- |
| `Poincare/AnalyticFoundation.lean` | Typed package interfaces for time-dependent tangent connections, curvature tensor fields, Bianchi data, Ricci/scalar contraction, parabolic regularity, Shi estimates, and DeTurck/short-time obligations. Early fields now store concrete `CovariantDerivative` and tensor data; later fields remain package obligations. | MIXED |
| `Poincare/RicciFlow.lean` | Older `RicciFlowData`, `SatisfiesRicciFlowEquation`, candidate Ricci tensor and metric-derivative fields. The built-in identification constructors are stationary-zero/candidate equality routes. | LEGACY-SCAFFOLD |
| `Poincare/RicciFlowInterface.lean` | Legacy finite-extinction certificate with arbitrary `Prop` evidence fields. This is the vacuous scaffold identified in `INTEGRITY_ASSESSMENT.md`. | VACUOUS |
| `Poincare/Surgery.lean` | Surgery and Perelman-control package interfaces; many payloads carry positive scales, bump functions, neck/cap data, and long-time assumptions, but no Perelman proof. | MIXED |
| `Poincare/Smoothability.lean` | Moise/smoothability proof-bearing interfaces. Many constructors reduce broad Moise subobligations to one-point recognition, so they are useful project plumbing but not manifold Ricci analysis. | MIXED |
| `Poincare/TopologyExtraction.lean` | Large topology-extraction/homeomorphism package layer. Contains some real point-set/topological constructions and many theorem-contract/projection lemmas. | MIXED |
| `Poincare/Dependencies.lean` | Aggregates named proof dependencies into package records. | LEGACY-SCAFFOLD |
| `Poincare/DependencyCrosswalk.lean` | Crosswalk/projection between dependency package shapes. | LEGACY-SCAFFOLD |
| `Poincare/DependencyProjections.lean` | Large generated projection layer. Many theorems are equalities of stored projections, often by `Subsingleton.elim`. | LEGACY-SCAFFOLD |
| `Poincare/CanonicalBridges.lean` | Bridges among completion/dependency/topology/surgery package shapes. | LEGACY-SCAFFOLD |
| `Poincare/CompletionTarget.lean` | Very large generated completion-certificate layer (about 145k lines). It is dominated by payload/certificate projections and equality contracts. | LEGACY-SCAFFOLD |
| `Poincare/FullAssembly.lean` | Assembles smoothability, surgery packages, topology extraction, and Poincare statement. It proves conditional assembly, not analytic Ricci flow. | MIXED |
| `Poincare/ProofProgress/AnalyticLeviCivitaBlocker.lean` | Progress ledger around analytic foundation subobligations; first fields connect to concrete tangent connection data, many later fields are package payload projections. | MIXED |
| `Poincare/ProofProgress/AnalyticLeviCivitaInterface.lean` | Proposed nonvacuous LC-existence interface using `TimeDependentTangentConnectionField`. | MIXED |
| `Poincare/ProofProgress/AnalyticProductionPackageLeviCivita.lean` | Builds analytic package fields from explicit data payloads. Valuable as a dependency map, but not itself deriving the data. | MIXED |
| `Poincare/ProofProgress/AnalyticThreeManifoldStationary.lean` | Stationary zero/Euclidean 3-manifold analytic package evidence. Concrete only in flat/static cases; many remaining subobligations are package-level. | MIXED |
| `Poincare/ProofProgress/CompletionBlockerLedger.lean` | Ledger/projection file for remaining blockers. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FinalCertificateBoundary.lean` | Final certificate boundary/projection file. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionPackage.lean` | Finite-extinction package interface/projection layer. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterCurvature.lean` | Frontier package after curvature input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterScalarCurvature.lean` | Frontier package after scalar-curvature input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterSurgeryVolume.lean` | Frontier package after surgery-volume input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterVolume.lean` | Frontier package after volume input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterVolumeDifferential.lean` | Frontier package after volume-differential input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageAfterWidth.lean` | Frontier package after width input. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionProductionPackageBridge.lean` | Bridge from frontier packages into finite-extinction production route. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionSweepoutBoundary.lean` | Sweepout/width boundary package file. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FiniteExtinctionSweepoutInterfaceBundle.lean` | Sweepout interface bundle. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/FullAssemblyClosure.lean` | Closure/projection layer for final assembly. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/GroundedFiniteExtinctionCertificate.lean` | Defines `GroundedFiniteExtinctionProductionCertificate`, replacing the arbitrary-`Prop` legacy certificate with existence of named packages. Content-bearing as a mitigation, but still conditional on those packages. | MIXED |
| `Poincare/ProofProgress/MoiseSmoothabilityTarget.lean` | Corrected Moise target after prior false all-charts compatibility frontier. | MIXED |
| `Poincare/ProofProgress/ResearcherStepLedger.lean` | Researcher/progress ledger. | LEGACY-SCAFFOLD |
| `Poincare/ProofProgress/SmoothabilityOnePointRecognition.lean` | One-point recognition smoothability payloads. | MIXED |
| `Poincare/ProofProgress/SmoothabilityProductionPackageBridge.lean` | Smoothability package bridge from subobligation payloads. | MIXED |
| `Poincare/ProofProgress/SmoothabilityProductionPackageMoiseLocalBlocker.lean` | Large Moise local blocker/subobligation file. It proves many interfaces from one-point recognition; not Ricci analysis. | MIXED |
| `Poincare/ProofProgress/SurgeryPerelmanPackageLayer.lean` | Extracts surgery/Perelman package fields from package payloads and builds remainder structures. Does not prove Perelman's estimates. | LEGACY-SCAFFOLD |

## Ricci-flow equation integrity

`IsRicciFlowSolutionAt` in `RicciFlowEquation.lean` is a real PDE statement.
The field named `flow` is:

```lean
flow : forall {Z : forall y : M, TangentSpace I y}, CMDiff 2 (T% Z) ->
  forall (hreg : DerivRegularAt (cov t0) Z x) (w : TangentSpace I x),
    deriv (fun t => g t x (Z x) w) t0 =
      -2 * ricciTraceAt (cov t0) hreg w
```

This is pointwise and section-tested rather than a global tensor-field equality,
but it is not vacuous. The derivative and Ricci term occur in the same
equation.

Concrete instances found:

- `euclidean_static_isRicciFlowSolutionAt`: flat Euclidean static metric.
- `const_metric_static_model_flow`: constant model-space metric in
  `ModelChristoffel.lean`, again flat/static.
- `isRicciFlowSolutionAt_const_of_ricciFlat`: conditional static Ricci-flat
  solution.
- `einstein_isRicciFlowSolutionAt`: conditional Einstein scaling solution,
  assuming the pointwise Einstein Ricci trace formula.
- `isRicciFlowSolutionAt_of_model_metric` and `isRicciFlowSolutionAt_of_metric`:
  wrappers that build the Levi-Civita side once the explicit flow equation is
  provided.

I found no nontrivial closed-manifold Ricci-flow solution constructed from
actual closed-manifold data.

## Live frontier

The furthest genuine result toward Ricci flow on closed manifolds is:

1. `ClosedSmoothRiemannianMetric` is connected to Mathlib's Riemannian bundle
   API (`Global/RiemannianContext.lean`).
2. For every such metric, the repo constructs a global
   `closedLeviCivitaConnection` and proves metric compatibility plus zero
   torsion (`Global/LeviCivitaExistence.lean`).
3. The general `CovariantDerivative` layer can define curvature, Ricci trace,
   Ricci bilinear form, scalar curvature, curvature symmetries, first Bianchi,
   and the pointwise Ricci-flow equation.

The missing bridge is not philosophical; it is a concrete Lean gap:
the closed-manifold Levi-Civita connection has not yet been promoted through
the curvature/Ricci package with a smoothness/regularity theorem strong enough
to define closed-manifold Ricci tensor/scalar fields and then state/prove
closed-manifold Ricci-flow evolution.

Most valuable next lemmas:

1. Smoothness of the closed Levi-Civita connection.

```lean
theorem closedLeviCivitaConnection_contMDiff
    (g : ClosedSmoothRiemannianMetric n M) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivitaExistence.closedLeviCivitaConnection g) 1 := by
  ...
```

This is the main gateway into the regularity hypotheses used by the curvature
tensoriality files.

2. Closed-metric Ricci bilinear form and symmetry.

```lean
noncomputable def closedRicciBilinearAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TangentSpace (closedSmoothModelWithCorners n) x) : Real :=
  CovariantDerivative.ricciBilinearAt
    (LeviCivitaExistence.closedLeviCivitaConnection g) x u w

theorem closedRicciBilinearAt_symm
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TangentSpace (closedSmoothModelWithCorners n) x) :
    closedRicciBilinearAt g x u w = closedRicciBilinearAt g x w u := by
  ...
```

The proof should instantiate `ricciBilinearAt_symm` with the closed LC
connection, torsion, compatibility, pairing regularity, and connection
smoothness.

3. Closed scalar curvature from the closed LC connection.

```lean
noncomputable def closedScalarCurvatureAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) : Real :=
  CovariantDerivative.scalarCurvatureAt
    (LeviCivitaExistence.closedLeviCivitaConnection g) x
    (g.inner x)
    (by
      intro v hv
      exact LeviCivitaExistence.metric_nondegenerate g x v hv)
```

The companion theorem should identify this scalar with the trace of
`closedRicciBilinearAt` and prove invariance under change of orthonormal basis
through the existing `scalarCurvatureAt` API.

4. Closed-manifold pointwise Ricci-flow wrapper.

```lean
theorem isClosedRicciFlowSolutionAt_of_metric
    (gt : Real -> ClosedSmoothRiemannianMetric n M)
    {t0 : Real} {x : M}
    (hflow :
      forall {Z : forall y : M, TangentSpace (closedSmoothModelWithCorners n) y},
        CMDiff 2 (T% Z) ->
        forall (hreg : CovariantDerivative.DerivRegularAt
            (LeviCivitaExistence.closedLeviCivitaConnection (gt t0)) Z x)
          (w : TangentSpace (closedSmoothModelWithCorners n) x),
          deriv (fun t => (gt t).inner x (Z x) w) t0 =
            -2 * CovariantDerivative.ricciTraceAt
              (LeviCivitaExistence.closedLeviCivitaConnection (gt t0)) hreg w) :
    CovariantDerivative.IsRicciFlowSolutionAt
      (fun t y => (gt t).inner y)
      (fun t => LeviCivitaExistence.closedLeviCivitaConnection (gt t))
      t0 x := by
  ...
```

This is mostly specialization of `isRicciFlowSolutionAt_of_metric`, but it will
force the exact closed-manifold regularity hypotheses to be exposed.

5. Manifold scalar evolution skeleton.

```lean
theorem closed_scalar_evolution_ricci_flow
    (gt : Real -> ClosedSmoothRiemannianMetric n M)
    (sol : forall x : M,
      CovariantDerivative.IsRicciFlowSolutionAt
        (fun t y => (gt t).inner y)
        (fun t => LeviCivitaExistence.closedLeviCivitaConnection (gt t))
        t0 x)
    ... :
    HasDerivAt (fun t => closedScalarCurvatureAt (gt t) x)
      (closedLaplacian (gt t0) (fun y => closedScalarCurvatureAt (gt t0) y) x
        + 2 * closedRicciNormSq (gt t0) x) t0 := by
  ...
```

This statement needs new infrastructure (`closedLaplacian`,
`closedRicciNormSq`, and tensor/time-variation lemmas), so it is a frontier
target rather than a near-term one-line specialization.

## Single-chart material not yet ported

The following `ModelLaplacian.lean` assets are not yet abstract-manifold
theorems:

- The scalar evolution chain:
  `hamilton_scalar_evolution_of_bianchi`,
  `hamilton_scalar_evolution_ricci_flow`,
  `curved_ricci_flow_scalar_evolution`,
  `curved_ricci_flow_scalar_evolution_trace_form`.
- The Hamilton lower-bound/singularity chain:
  `hamilton_scalar_lower_bound`,
  `hamilton_finite_time_singularity`,
  `hamilton_ricci_flow_singularity`,
  `curved_hamilton_ricci_flow_singularity`,
  `curved_hamilton_ricci_flow_singularity_bianchi_free`.
- Coordinate Bianchi and variation:
  `coord_first_bianchi`, `coord_second_bianchi`,
  `coord_twice_contracted_bianchi`, `ricciDeriv_*`,
  `lichnerowiczLaplacian_*`.
- Pinching and model ODEs:
  `ricciNormSq_ge_scalar_sq_div`, `pinching_gap_nonneg`,
  `pinching_gap_eq_n_mul_tracelessNormSq`, `round_sphere_*`,
  `hyperbolic_*`.
- Bochner:
  `bochner_flat`, `bochner_inequality`,
  `bochner_eigenfunction`,
  `curvedLaplacian_coordGradNormSq_bochner*`.
- Heat/maximum principles tied to `modelLaplacian`:
  `parabolic_min_principle*`, `heat_supersolution_nonneg_preserved`,
  `curved_parabolic_min_principle*`.

What should port cleanly:

- Pure scalar ODE/maximum-principle lemmas from `MaximumPrinciple.lean`.
- Linear algebraic trace inequalities such as
  `ricciNormSq_ge_scalar_sq_div` once closed-manifold Ricci endomorphism,
  scalar, and norm are defined.
- Flat/static consequences, because `FlatModelConnection.lean`,
  `EuclideanLeviCivitaCheck.lean`, and `RicciFlowEquation.lean` already prove
  the flat pointwise pieces.
- Ricci symmetry/scalar trace lemmas, because `CurvatureTensoriality.lean`
  already has the abstract `CovariantDerivative` facts.

What will not port cleanly without new infrastructure:

- Any theorem mentioning `curvedLaplacian` needs a closed-manifold scalar
  Laplacian and Hessian API.
- Ricci variation and Lichnerowicz formulas need covariant derivatives of
  tensor fields, not only curvature at a point.
- Hamilton scalar evolution needs a time-dependent metric derivative object
  connected to the pointwise `IsRicciFlowSolutionAt` statement.
- Maximum-principle conclusions on closed manifolds need compactness/minimum
  existence and a global parabolic setup, not just pointwise chart calculus.
- Coordinate Bianchi/variation proofs must be re-expressed through the
  `CovariantDerivative` curvature layer or transported through charts with
  overlap agreement.

## Bottom line

The repo now has a genuine manifold-level Levi-Civita/curvature/Ricci-flow
equation substrate. It is strong enough to define the right next theorem
targets and to honestly say that `IsRicciFlowSolutionAt` is a real PDE.

It is not yet Ricci flow on closed manifolds. The live frontier is closed
Levi-Civita existence plus pointwise curvature/Ricci machinery. The missing
work is to promote the closed LC connection into smooth curvature/Ricci/scalar
objects and then port the scalar evolution, maximum principle, pinching, and
Bochner assets from the single-chart model.
