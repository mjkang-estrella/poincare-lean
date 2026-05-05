# Poincare Formalization Dependency Ledger

This ledger names the proof obligations that are still missing before
`PoincareConjectureStatement` can become a theorem.

It is not a proof. It is a work breakdown for future Lean development.

## Current Proven Surface

- The project builds with Lean `v4.30.0-rc2`.
- `Poincare/Statement.lean` imports mathlib's canonical
  `Mathlib.Geometry.Manifold.PoincareConjecture`.
- `ThreeSphere` is represented as
  `Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`.
- `Poincare/Statement.lean` proves `rfl` contracts for the target sphere model
  and for the topological and smooth Poincare proposition shapes, explicit iff
  contracts for those canonical statement shapes, and an iff contract plus both
  directions between the target statement and the explicit completion criterion;
  witness-transfer and witness-equivalence lemmas show that the universe-indexed
  completion criterion is independent of the chosen witness type, and
  `poincare_completion_payload_of_poincareConjectureStatement` centralizes the
  target/completion-criterion payload used by later assembly routes, with reverse
  target/criterion projections, a direct completion-criterion-to-payload bridge,
  and target/criterion iff contracts for that payload. Equality contracts now pin
  those canonical-statement, witness-transfer, target/criterion projection, and
  target/criterion payload routes to their named statement-layer constructions.
- `scripts/audit_formalization.sh` passes.
- `Poincare/Assembly.lean` contains a proof-bearing support lemma showing that
  a diffeomorphism to `S^3` gives a homeomorphism to `S^3`; it also handles the
  reverse smooth input direction `S^3 → M` by inversion and records the
  equivalence between the two diffeomorphism directions.
- `Poincare/Assembly.lean` also proves that this project's statement follows
  from an explicit proof-bearing theorem with the canonical mathlib 3D
  topological Poincare statement shape.
- `Poincare/Assembly.lean` proves that the canonical mathlib-shaped topological
  3D Poincare statement discharges the explicit completion criterion.
- `Poincare/Assembly.lean` exposes
  `poincare_payload_of_canonical_three_sphere_statement`, carrying the local
  target and explicit completion criterion from the canonical topological route,
  through the statement-layer completion payload.
- `Poincare/Assembly.lean` exposes the reverse topological canonical statement
  route through `canonical_three_sphere_statement_of_poincare_statement`,
  `canonical_three_sphere_statement_of_poincare_payload`, and
  `canonical_three_sphere_statement_iff_poincare_completion_payload`.
- `Poincare/Assembly.lean` exposes the reverse completion-criterion route through
  `canonical_three_sphere_statement_of_completionCriterionAtUniverse` and
  `canonical_three_sphere_statement_iff_completionCriterionAtUniverse`, so the
  explicit universe-indexed completion criterion is interchangeable with the
  canonical topological statement shape.
- `Poincare/Assembly.lean` proves that this project's smooth statement follows
  from an explicit proof-bearing theorem with the canonical mathlib 3D smooth
  Poincare statement shape.
- `Poincare/Assembly.lean` proves that the smooth Poincare statement plus a
  smoothability hypothesis implies the topological target statement.
- `Poincare/Assembly.lean` exposes `poincare_payload_of_smooth_statement`,
  carrying the local target and explicit completion criterion from the smooth
  statement plus smoothability route, through the statement-layer completion
  payload.
- `Poincare/Assembly.lean` exposes `completion_criterion_of_smooth_statement`,
  the direct criterion projection from the smooth statement plus smoothability
  route.
- `Poincare/Assembly.lean` exposes
  `canonical_three_sphere_statement_of_smooth_statement` and
  `canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement`,
  the direct canonical topological statement projections from the smooth and
  canonical-smooth routes with smoothability.
- `Poincare/Assembly.lean` exposes the reverse-direction smooth route through
  `poincare_statement_of_reverse_smooth_statement`,
  `canonical_three_sphere_statement_of_reverse_smooth_statement`,
  `poincare_payload_of_reverse_smooth_statement`, and
  `completion_criterion_of_reverse_smooth_statement`, converting a supplied
  theorem with diffeomorphisms `S^3 -> M` into the local topological target,
  canonical topological statement, payload, and explicit completion criterion.
- `Poincare/Assembly.lean` proves that the canonical mathlib-shaped smooth 3D
  Poincare statement plus smoothability implies the local topological target
  statement.
- `Poincare/Assembly.lean` proves that the canonical mathlib-shaped smooth 3D
  Poincare statement plus smoothability discharges the explicit completion
  criterion.
- `Poincare/Assembly.lean` exposes
  `poincare_payload_of_canonical_smooth_three_sphere_statement`, carrying the
  local target and explicit completion criterion from the canonical smooth route.
- `Poincare/Assembly.lean` exposes the reverse smooth canonical statement route
  through `canonical_smooth_three_sphere_statement_of_smooth_statement` and
  `canonical_smooth_three_sphere_statement_iff_smooth_statement`.
- `Poincare/Assembly.lean` also exposes
  `reverse_canonical_smooth_three_sphere_statement_of_smooth_statement`,
  `smooth_statement_of_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_smooth_three_sphere_statement_of_reverse_canonical_smooth_three_sphere_statement`,
  `reverse_canonical_smooth_three_sphere_statement_iff_smooth_statement`, and
  `canonical_smooth_three_sphere_statement_iff_reverse_canonical_smooth_three_sphere_statement`,
  so the canonical smooth statement shape is invariant under writing the
  supplied diffeomorphism as `M -> S^3` or `S^3 -> M`.
- `Poincare/Assembly.lean` now pins the statement-layer bridge surface with
  equality contracts for the canonical topological route, smoothability plus
  smooth-statement route, canonical smooth route, payload constructors,
  criterion projections, and canonical-statement iff routes.
- `Poincare/CanonicalBridges.lean` proves that the canonical mathlib-shaped
  topological and smooth 3D Poincare statement inputs imply the canonical
  completion target by destructuring the assembly-layer payloads. It also
  exposes the canonical topological statement at the remaining-dependency surface
  through the aggregate, aggregate certified extraction, projection, and
  projection certified extraction routes, and records a literal reserved-name
  certificate payload carrying that canonical statement with the target and
  criterion at both the remaining-dependency and aggregate-dependency surfaces.
- `Poincare/CanonicalBridges.lean` also lifts the reverse canonical smooth
  statement route through
  `canonical_completion_payload_of_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_completion_target_of_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_completion_criterion_of_reverse_canonical_smooth_three_sphere_statement`,
  `completion_certificate_of_remaining_dependency_and_reverse_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_poincareProofDependencies_and_reverse_canonical_smooth_three_sphere_statement`,
  so a proof-bearing smooth theorem stated with diffeomorphisms `S^3 -> M`
  reaches the canonical payload and checked-certificate surfaces directly.
- `Poincare/CanonicalBridges.lean` also exposes the canonical topological
  statement from packaged smooth-route endpoints via
  `canonical_three_sphere_statement_of_remaining_dependency_and_packaged_smooth_statement`,
  `canonical_three_sphere_statement_of_poincareProofDependencies_and_packaged_smooth_statement`,
  `canonical_three_sphere_statement_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement`,
  and
  `canonical_three_sphere_statement_of_poincareProofDependencies_and_packaged_canonical_smooth_three_sphere_statement`.
- `Poincare/CanonicalBridges.lean` exposes packaged reverse canonical smooth
  payloads through
  `packaged_reverse_canonical_smooth_three_sphere_statement_completion_payload_of_remaining_dependency`
  and
  `packaged_reverse_canonical_smooth_three_sphere_statement_completion_payload_of_poincareProofDependencies`,
  carrying the projected smoothability evidence, the reverse canonical input,
  the induced project smooth statement, the target, and the completion criterion
  at both dependency-package surfaces.
- `Poincare/CanonicalBridges.lean` now lifts those packaged reverse canonical
  smooth payloads through the full projection surface:
  `poincare_statement_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `completion_criterion_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `poincare_completion_payload_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_completion_payload_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_completion_target_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_completion_criterion_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  `canonical_three_sphere_statement_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_*packaged_reverse_canonical_smooth_three_sphere_statement`,
  with direct aggregate-to-remaining equality contracts and certificate
  projection round-trips for the dependency package, project target, project
  payload, canonical payload, canonical target, completion criterion, and
  canonical topological statement. The same route now also has direct
  `poincareCompletionCertificate_*packaged_reverse*payload` projections,
  payload-to-certificate constructors, iff contracts, and
  projection-after-constructor contracts at both dependency-package surfaces.
- `Poincare/CanonicalBridges.lean` now also gives the non-packaged reverse
  canonical-smooth checked certificate constructors the same projection
  round-trips at remaining-dependency and aggregate-dependency surfaces:
  dependency package, canonical topological statement, canonical target,
  completion criterion, project completion payload, canonical completion payload,
  and project target statement.
- `Poincare/CanonicalBridges.lean` now exposes the matching non-packaged reverse
  canonical-smooth certificate payload layer: checked certificates project to
  remaining-dependency or aggregate payloads containing the supplied
  smoothability theorem, reverse canonical-smooth statement, target, and
  criterion; those payloads reconstruct checked certificates, form certificate
  iff contracts, round-trip after reconstruction, and convert between aggregate
  and remaining dependency packages componentwise.
- `Poincare/CanonicalBridges.lean` now exposes the matching non-packaged smooth
  certificate payload layer: checked certificates project to remaining-dependency
  or aggregate payloads containing the supplied smoothability theorem, smooth
  statement, target, and criterion; those payloads reconstruct checked
  certificates, form certificate iff contracts, round-trip after reconstruction,
  and convert between aggregate and remaining dependency packages componentwise.
- `Poincare/CanonicalBridges.lean` now exposes the matching non-packaged
  canonical-smooth certificate payload layer as well: checked certificates
  project to remaining-dependency or aggregate payloads containing the supplied
  smoothability theorem, canonical-smooth statement, target, and criterion; those
  payloads reconstruct checked certificates, form certificate iff contracts,
  round-trip after reconstruction, and convert between aggregate and remaining
  dependency packages componentwise.
- `Poincare/CanonicalBridges.lean` now pins the aggregate packaged smooth and
  packaged canonical-smooth project routes, canonical completion payloads,
  canonical targets, canonical criteria, and canonical topological statement
  projections to the corresponding remaining-dependency routes after
  `remainingDependencyPackage_iff_poincareProofDependencies`; the packaged
  smooth and packaged canonical-smooth aggregate completion certificate
  constructors, payload proposition equivalences, and certificate iff
  factorizations are pinned to the remaining-dependency surface as well. The
  packaged smooth and packaged canonical-smooth certificate equivalences are
  also pinned directly to their named projection/constructor pairs, and the
  packaged reverse canonical-smooth payload equivalences now have the same
  checked-certificate reversibility. The packaged smooth, packaged
  canonical-smooth, and packaged reverse canonical-smooth payload constructors
  now also reconstruct their route completion certificates from the assembled
  route payload endpoints. Their aggregate/remaining payload equivalences are
  pinned to the componentwise dependency conversion. The
  dependency-packaged smooth payloads are also pinned to the standalone
  `SmoothabilityPackage` payloads obtained by projecting the smoothability
  component, including their project target, criterion, and project
  completion-payload, canonical payload, canonical target, canonical criterion,
  canonical statement projections, and checked completion-certificate
  constructors. The standalone smoothability-package smooth,
  canonical-smooth, and reverse canonical-smooth route payloads now also have
  reconstruction contracts from their named project and canonical completion
  payload endpoints.
- `Poincare/CanonicalBridges.lean` also exposes standalone smoothability-package
  smooth routes via `smoothability_package_smooth_statement_completion_payload`
  and
  `smoothability_package_canonical_smooth_three_sphere_statement_completion_payload`,
  so the `C∞` smoothability half can feed a proof-bearing smooth Poincare
  statement directly into the project target and canonical topological statement
  without carrying the surgery or topology packages.
- `Poincare/CompletionTarget.lean` now pins the remaining-dependency
  smoothability package, theorem-shaped `C∞` smooth-manifold statement,
  smooth-manifold projection, and paired smoothability payload projections to
  the stored smoothability component of `RemainingDependencyPackage`; it also
  pins the surgery-family projection, topology-extraction projection, raw
  component payload, and component equivalence to the corresponding stored
  fields and aggregate component equivalence. The component-slot, package-layer,
  and milestone requirement payload/iff routes are pinned to the matching
  aggregate dependency crosswalk payloads and equivalences.
- `Poincare/Milestones.lean` proves the six-item ledger length and exact membership via
  `dependencyMilestoneLedger_length` and `dependencyMilestoneLedger_mem`.
- `Poincare/RicciFlowInterface.lean` defines the finite-extinction and
  topological-extraction interfaces and proves their conditional assembly into
  `PoincareConjectureStatement`. The finite-extinction predicate has no local
  constructors, so the project cannot create that evidence without a future
  theorem. It also exposes `extinction_extraction_of_poincare_statement` and
  `poincare_statement_iff_extinction_extraction`, recording that the target
  statement supplies the post-extinction extraction interface and, once
  universal finite extinction is available, is equivalent to that interface.
  It also exposes `poincare_payload_of_extinction_and_extraction`, carrying the
  local target and explicit completion criterion from those two theorem-shaped
  inputs. The canonical endpoint route
  `canonical_three_sphere_statement_of_extinction_and_extraction` and the
  equivalence `canonical_three_sphere_statement_iff_extinction_extraction`
  expose the same boundary at the mathlib-shaped topological statement. Those
  target and canonical endpoint equivalences now have equality contracts
  pinning them to their named projection/constructor pairs.
- `Poincare/RicciFlow.lean` defines the time-dependent metric, Ricci tensor,
  Ricci-identification, curvature-data, and Ricci-flow equation interfaces, plus
  checked projections down to metric data, curvature data, time-slice metrics,
  Ricci tensor fields, scalar curvature fields, time-slice Ricci tensors,
  scalar curvature values, Ricci-identification evidence, and Ricci-flow
  equation evidence. The projection/evidence equalities record that these named
  API surfaces are definitionally the corresponding `RicciFlowData` and
  `RicciCurvatureData` fields.
- `Poincare/AnalyticFoundation.lean` defines no-constructor interfaces for
  Levi-Civita connection theory, Levi-Civita
  existence/uniqueness/torsion-free/metric-compatibility sub-obligations,
  Riemann-curvature construction, tensor symmetries, first and second Bianchi
  identities, Ricci/scalar contraction formulas, Ricci contraction,
  time-dependent metric regularity, metric time derivatives, scalar curvature,
  Ricci-flow equation derivation, short-time Ricci-flow existence, continuation
  criteria, parabolic regularity, uniqueness, and curvature evolution equations,
  with the PDE/existence layer further split into initial-metric compatibility,
  DeTurck gauge fixing, background-metric compatibility, vector-field
  construction, Ricci-DeTurck equation derivation and linearization, strict
  parabolicity, linear parabolic theory, nonlinear fixed-point arguments,
  DeTurck short-time existence, short-time regularity bootstrap, DeTurck
  diffeomorphism ODE, pullback equation identity, pullback from DeTurck flow to
  Ricci flow, maximal-time intervals, curvature blow-up continuation,
  bounded-curvature extension, parabolic Schauder estimates, Shi derivative
  estimates, curvature derivative bootstrap, Hamilton maximum principle,
  metric/Ricci/scalar curvature evolution equations, and curvature-norm
  evolution inequalities, plus a checked package projecting to `RicciFlowData`,
  Ricci-identification evidence, equation evidence, a theorem-shaped
  analytic foundation statement assembled from the fixed-flow derivation
  components, `AnalyticFoundationSubobligationsPayload`, and
  `analytic_foundation_payload_of_analytic_foundation_package`, which
  centralizes the theorem-shaped statement, fixed derivation statement, named
  sub-obligation payload, and equation evidence at the package layer. The
  analytic-package flow/evidence projection equalities record that those
  package-level surfaces delegate exactly to the stored flow data.
- `Poincare/Surgery.lean` defines no-constructor interfaces for Ricci flow with
  surgery, Perelman singularity control, and finite-extinction derivation, plus
  checked package projections to the analytic foundation. Its direct package
  projection equalities record the stored analytic foundation, stored flow,
  construction package, Perelman package, finite-extinction witness, and
  analytic equation-evidence route before the larger finite-extinction spine is
  consumed. It also projects
  `analytic_foundation_payload_of_surgery_package`, underlying Ricci-flow data,
  Ricci-flow equation evidence, surgery scale functions, scale
  continuity/separation, cutoff-parameter control, smooth cutoff bump
  functions, parameter selection, strong delta-neck detection, neck separation,
  neck parametrization, canonical neck coordinates, neck decomposition,
  standard cap models, cap-gluing smoothness, cap metric interpolation, cap
  curvature estimates, cap construction, post-surgery curvature pinching,
  post-surgery noncollapsing control, post-surgery derivative bounds,
  post-surgery canonical-neighborhood persistence, post-surgery metric control,
  surgery-time discreteness/local finiteness, long-time existence iteration,
  long-time parameter coherence, long-time nonaccumulation, long-time surgery
  continuation, theorem-shaped surgery-construction statements,
  statement-mediated surgery-construction sub-obligation projection, surgery
  evidence, theorem-shaped Perelman singularity-control statements,
  Perelman F/W-functional setup, entropy
  normalization, entropy-minimizer existence, log-Sobolev control, conjugate
  heat equation theory, adjoint heat kernels, conjugate heat-kernel estimates,
  entropy gradient, first variation, monotonicity, entropy lower-bound
  propagation, entropy-functional setup, reduced-length first variation,
  reduced-distance existence, differential inequality, estimates,
  cut-locus/barrier control, reduced-Jacobian comparison, and theory,
  reduced-volume definition, derivative formula, rigidity, positive lower
  bounds, limit rigidity, and nonincreasing evidence, reduced-volume-to-kappa
  input, no-local-collapsing contradiction setup, collapsed-ball blow-up,
  volume-ratio contradiction, no-local-collapsing volume lower bounds,
  quantified kappa-noncollapsing, Hamilton compactness, ancient kappa-solution
  limit extraction, pointed rescaling, curvature normalization, structure
  theory, nonnegative curvature-operator control, asymptotic soliton analysis,
  compactness, canonical-neighborhood scale control, model stability,
  cross-scale persistence, neck/cap dichotomy, classification,
  no-local-collapsing, reduced-volume, canonical-neighborhood,
  singularity-model classification, singularity-model blow-up classification,
  singularity-control evidence, finite-extinction fundamental-group input,
  sweepout existence,
  sweepout parameter spaces, sweepout continuity, sweepout area bounds,
  sweepout nontriviality, area-functional setup, min-max width definition,
  width compactness, width lower semicontinuity, minimizing sequences,
  pull-tight arguments, min-max stationarity, min-surface regularity, positive
  width, width theory, first and second variation, Gauss-Bonnet estimates,
  scalar-curvature width bounds, width evolution, width differential
  inequality, surgery metric comparison, surgery width-comparison maps, surgery
  width drop, surgery/discard control, discarded-component width neutrality,
  discarded-component sweepout triviality and classification, surviving
  component tracking, component topology, curvature pinching, scalar-curvature
  lower bounds, positive scalar-curvature persistence, component control,
  volume evolution, surgery volume nonincrease, scalar-curvature and volume
  differential inequalities, volume-decay estimates, time-bound evidence,
  differential-inequality integration, finite-time integration, surgery-time
  summability, extinction-time contradiction, finite-extinction derivation, the
  finite-extinction interface, the conclusion-derivation certificate,
  fixed-flow finite-extinction conclusion statements, theorem-shaped
  finite-extinction width and full sub-obligation statements with explicit
  statement-destructuring bridges, and
  theorem-shaped finite-extinction statements. The theorem-shaped surgery and
  Perelman sub-obligation stacks are named by
  `RicciFlowWithSurgeryConstructionSubobligationsPayload`,
  `PerelmanSingularityControlSubobligationsPayload`, and
  `PerelmanMonotonicityBlowupSubobligationsPayload`. The package-to-payload
  bridges `surgery_construction_payload_of_construction_package` and
  `perelman_control_payload_of_package` centralize the package,
  theorem-shaped statement, named sub-obligation payload, and aggregate witness
  routes; direct equality contracts pin the surgery construction package's
  theorem-shaped statement route to the component assembly route and its bundled
  payload to the named statement, sub-obligation payload, and aggregate witness
  extraction. The dependency-level `surgery_package_payload_of_dependencies` now
  centralizes the raw aggregate surgery package with its analytic foundation,
  projected flow, construction package, and Perelman control package. Its
  payload carries equality contracts for the analytic package and flow plus
  heterogeneous equality contracts tying the construction and Perelman-control
  packages to the corresponding projections from the same finite-extinction
  surgery package; the analytic, surgery-construction, Perelman, and
  finite-extinction dependency payloads use that named bridge, with an equality
  contract pinning the bridge to the stored surgery family. The
  dependency-level analytic-foundation package projection is now pinned to
  mapping that stored surgery family to each analytic subpackage. The
  package-routed payloads
  `analytic_foundation_statement_payload_with_surgery_package_of_dependencies`,
  `surgery_construction_statement_payload_with_surgery_package_of_dependencies`,
  `perelman_control_statement_payload_with_surgery_package_of_dependencies`,
  `finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies`,
  and `finite_extinction_statement_payload_with_surgery_package_of_dependencies`
  keep the selected surgery package in the payload. Equality contracts now pin
  the analytic, construction, and Perelman payload routes and their simplified
  dependency payloads back to the shared surgery package, while the
  finite-extinction routes pin statement, derivation, and extinction fields back
  to that package. The
  dependency-level surgery-construction route now exposes
  `surgery_construction_statement_payload_of_dependencies`, which packages the
  construction package, theorem-shaped construction statement, construction
  sub-obligation payload, and aggregate Ricci-flow-with-surgery witness by
  destructuring the shared dependency surgery package payload and then the
  package-level construction payload bridge; the construction-package projection
  itself is pinned to the same shared payload.
  Equality contracts for the construction package projection spine now tie the
  surgery scales, cutoff controls, neck data, cap data, post-surgery estimates,
  surgery-time controls, long-time continuation data, and aggregate
  Ricci-flow-with-surgery projection directly to the stored construction
  package fields. Equality contracts for the surgery package construction route
  now tie its construction statement, aggregate surgery witness, scale/cutoff
  controls, neck and cap data, post-surgery estimates, surgery-time controls,
  and long-time continuation projections directly to the stored construction
  package fields. Equality contracts for the surgery package Perelman route now
  tie its Perelman statement, entropy and conjugate-heat controls,
  reduced-distance/reduced-volume data, noncollapsing and kappa-solution
  controls, canonical-neighborhood data, and aggregate singularity-control
  projection directly to the stored Perelman package fields. Equality contracts
  for the surgery package finite-extinction route now tie its sweepout, width,
  surgery-discard, curvature, scalar/volume/time-bound, derivation, and
  conclusion-derivation projections directly to the stored finite-extinction
  fields. Equality contracts for the Perelman package projection spine
  now tie entropy and conjugate-heat controls, reduced-distance/reduced-volume
  data, noncollapsing and kappa-solution controls, canonical-neighborhood data,
  and aggregate singularity-control projection directly to the stored Perelman
  package fields. Dependency-level component equality contracts now tie the
  aggregate smoothability package, surgery-package family, and topology
  extraction projections directly to the stored `PoincareProofDependencies`
  fields. The dependency-level Perelman route now exposes
  `perelman_control_statement_payload_of_dependencies`, which packages the
  theorem-shaped Perelman statement, full Perelman
  sub-obligation payload, monotonicity/blow-up sub-obligation payload, and
  aggregate control witness; Perelman control and sub-obligation projections
  destructure that payload. The full finite-extinction sub-obligation route
  now rebuilds the
  fixed-flow conclusion statement and theorem-shaped finite-extinction
  statement through
  `finite_extinction_conclusion_statement_of_subobligations_statement` and
  `finite_extinction_statement_of_subobligations_statement`; the
  theorem-shaped statement exposes its conclusion payload through
  `finite_extinction_conclusion_statement_of_finite_extinction_statement`.
  Package-level finite-extinction payloads
  `finite_extinction_subobligations_payload_of_surgery_package` and
  `finite_extinction_statement_payload_of_surgery_package` centralize the
  width/full sub-obligation statement payloads and the rebuilt
  finite-extinction statement/derivation/extinction route.
  The dependency-level finite-extinction route now exposes
  `finite_extinction_subobligations_statement_payload_of_dependencies`, which
  packages the width/full sub-obligation statements, their statement-mediated
  width/full sub-obligation payloads, and direct finite-extinction statement
  by destructuring the package-level payload,
  plus
  `finite_extinction_statement_payload_of_dependencies`, which also carries
  the derivation certificate by destructuring the package-level statement
  payload; equality contracts pin both the surgery-package-enriched and
  simplified dependency payloads for the sub-obligation and final statement
  routes to those named destructuring routes;
  the width/full statement projections, derivation
  stack, full sub-obligation projection, statement projections, and final
  finite-extinction theorem destructure those payloads. The dependency-level
  finite-extinction width/full statement, width/full sub-obligation,
  derivation-stack, and statement-route projections now have equality contracts
  back to fields selected from those two payloads.
- `Poincare/TopologyExtraction.lean` defines no-constructor interfaces for the
  post-extinction topology decomposition, surgery-trace reconstruction,
  surgery-trace handle cancellation, component classification and inventory,
  discarded-component homeomorphism classification, component boundary-sphere
  control, 3-sphere recognition theorem, prime decomposition and existence,
  sphere-theorem input, embedded-sphere production, loop-theorem input,
  prime-decomposition compatibility and factor uniqueness, irreducibility and
  irreducible-factor recognition, connected-sum collapse, fundamental-group
  control, van Kampen calculation, simply connected prime-factor control,
  spherical-space-form reduction and classification, spherical quotient models,
  free spherical actions, spherical universal-cover, covering-model, and
  covering-projection inputs, spherical-space-form fundamental-group
  computation, deck-group identification, deck-action properness, deck-group
  triviality, deck-action trivialization, trivial deck-quotient identification,
  simply connected recognition, trivial spherical quotients, trivial-quotient
  homeomorphism, spherical homeomorphism lift, homeomorphism assembly,
  fixed-manifold topology derivation statements, derivation-statement bridges
  exposing the post-extinction classification stack through
  `ExtinctionTopologyClassificationSubobligationsPayload` and the
  homeomorphism assembly/derivation statements, theorem-shaped topology
  extraction statements, and homeomorphism derivation certificates chained
  through that assembly evidence, plus checked projections to those topology
  sub-obligations, the
  extracted homeomorphism, the package-derived extraction statement, and
  statement-mediated projection into
  `ExtinctionImpliesSphereStatement`. The fixed-extinction payload and
  homeomorphism now pass through
  `topology_derivation_statement_payload_of_extraction_statement` and
  `homeomorphism_of_topology_extraction_statement`. Package-level topology
  payloads `topology_extraction_payload_of_topology_package` and
  `topology_extraction_statement_payload_of_topology_package` centralize the
  theorem-shaped extraction interface, fixed derivation statement,
  classification payload, and homeomorphism assembly/derivation statement
  route; `topology_extraction_derivation_payload_of_topology_package` certifies
  that same package-level extraction statement as a final extractor paired with
  topology derivation evidence for the homeomorphism it returns. The dependency
  projection layer now also has equality contracts for the extracted
  homeomorphism route, direct assembly/derivation certificates, and statement
  aliases back to that extraction spine; equality
  contracts now tie the topology-package projection spine back to stored
  fields, covering surgery-trace reconstruction and handle cancellation,
  component classification/inventory/boundary control, recognition,
  prime-decomposition existence and sphere/loop-theorem inputs, embedded-sphere
  production, prime compatibility and uniqueness, irreducible-factor
  recognition, connected-sum group control and van Kampen calculation, simply
  connected prime-factor control, spherical classification/quotient/covering
  data, deck properness/trivialization, trivial deck-quotient identification,
  simply connected recognition, the package homeomorphism, trivial-quotient
  homeomorphism, homeomorphism-lift, assembly/derivation, extraction payloads,
  and final extractor, while theorem-shaped statement routes remain explicit
  where the projection is not just a stored field; the
  dependency-level classification payload
  `topology_classification_payload_of_dependencies` centralizes the
  post-extinction classification stack, and the individual dependency-level
  topology classification projections destructure that named payload instead
  of calling raw topology-package projections. Equality contracts
  `topology_classification_payload_of_dependencies_eq`,
  `topology_decomposition_of_dependencies_eq`, and
  `topology_classification_subobligations_of_dependencies_eq` pin the
  dependency-level classification payload, its first decomposition projection,
  and the explicit classification sub-obligation projection to the stored
  topology package payload route. The same equality-contract layer now covers
  the prime-decomposition/existence projections, the sphere-theorem,
  embedded-sphere, and loop-theorem inputs, prime compatibility and uniqueness,
  irreducibility, irreducible-factor recognition, connected-sum collapse,
  connected-sum fundamental-group and van Kampen control, simply connected
  prime-factor control, spherical-space-form reduction/classification,
  quotient-model, free-action, universal-cover, covering-model/projection, and
  fundamental-group computation, deck-group identification, deck-action
  properness, deck-group triviality, deck-action trivialization, trivial
  deck-quotient identification,
  simply connected recognition, trivial spherical quotient, trivial-quotient
  homeomorphism, and spherical homeomorphism-lift projections back to fields
  selected from the named classification payload. The broader dependency-level
  payload, homeomorphism, fixed derivation projection, and homeomorphism
  assembly/derivation statement projections consume the package-level payloads
  through
  `topology_extraction_statement_payload_of_dependencies`,
  `topology_derivation_statement_payload_of_dependencies`,
  `homeomorphism_of_extinction_and_dependencies`, and
  `topology_derivation_statement_via_extraction_of_dependencies`, with
  assembly and derivation statement payloads exposed by
  `topology_homeomorphism_assembly_statement_via_extraction_of_dependencies`
  and
  `topology_homeomorphism_derivation_statement_via_extraction_of_dependencies`.
  Equality contracts now pin the projected homeomorphism, derivation statement,
  assembly statement, and homeomorphism-derivation statement back to those
  named extraction payload routes.
  `topology_classification_subobligations_of_dependencies` also destructures
  the named dependency-level classification payload instead of reapplying the
  raw derivation-statement bridge.
  A separate dependency-level `topology_extraction_payload_of_dependencies`
  now carries both the theorem-shaped topology extraction statement and the
  final extraction interface by destructuring the package-level extraction
  payload; `topology_extraction_statement_of_dependencies`,
  `topology_extraction_statement_payload_of_dependencies`, and
  `extinction_extraction_of_dependencies` destructure the dependency payload,
  so the raw package-to-statement and statement-to-extraction bridges stay
  inside the topology package layer.
  Equality contracts
  `topology_extraction_payload_of_dependencies_eq`,
  `topology_extraction_statement_payload_of_dependencies_eq`,
  `topology_derivation_statement_payload_of_dependencies_eq`,
  `topology_extraction_statement_of_dependencies_eq`,
  `topology_extraction_derivation_payload_of_dependencies_eq`, and
  `extinction_extraction_of_dependencies_eq` pin those dependency-level
  topology extraction payloads, statements, derivation evidence, and final
  extractor back to the stored topology package route. The matching
  dependency-level statement-route contracts pin the payload, fixed-extinction
  payload, derivation payload, homeomorphism projection, final extractor,
  certified extractor/derivation payload, and projection target, completion,
  and statement routes to `topology_extraction_statement_of_dependencies`, the
  finite-extinction plus topology-statement assembly route, and the certified
  extractor/derivation assembly route.
  `ExtinctionTopologyDerivationForExtractionStatement`,
  `extinction_topology_extraction_statement_of_extraction_and_derivation`, and
  `extinction_topology_extraction_statement_iff_extraction_with_derivation`
  identify the theorem-shaped topology extraction statement with a final
  extractor plus derivation evidence for the homeomorphism returned by that
  extractor. The homeomorphism-recognition and extraction-with-derivation
  equivalences now have equality contracts pinning them to their named
  directional maps. The theorem-shaped package statement, fixed-extinction
  payload, homeomorphism projection, statement-mediated extractor,
  extractor-plus-derivation constructor, projection-after-reconstruction
  contracts, and package fixed-extinction payload are now pinned to their named
  routes. The direct assembly bridges
  `poincare_statement_of_finite_extinction_and_topology_extraction_statement`
  and
  `poincare_payload_of_finite_extinction_and_topology_extraction_statement`
  connect universal finite extinction and the strong topology extraction
  statement to the target/completion payload with equality contracts back to the
  finite-extinction/extraction assembly route. The matching
  `poincare_statement_of_finite_extinction_and_extraction_derivation` and
  `poincare_payload_of_finite_extinction_and_extraction_derivation` bridges
  expose that same payload from a final extractor plus its topology derivation
  certificate and are pinned to the named extractor-plus-derivation topology
  statement route.
- `Poincare/TopologyExtraction.lean` proves that `ThreeSphere` is homeomorphic
  to itself and that a homeomorphism to an intermediate space already
  homeomorphic to `ThreeSphere` composes to a homeomorphism to `ThreeSphere`;
  it also proves the opposite-direction source transport, the iff invariance of
  `ThreeSphere` recognition under replacing the source by a homeomorphic space,
  the reverse homeomorphism from `ThreeSphere`, the iff between the two
  homeomorphism directions, and the inverse-direction recognition lemma from a
  homeomorphism out of `ThreeSphere`. The self, intermediate-composition,
  opposite-source, and inverse-direction recognition maps now have direct
  equality contracts.
- `Poincare/Smoothability.lean` defines no-constructor interfaces for the
  smoothability bridge from the topological statement to the smooth structure
  needed by the surgery layer, including Moise local charts,
  locally finite cover refinement, simplicial-complex data, compatible chart
  triangulations, simplicial approximation, star-neighborhood bases,
  barycentric subdivision, regular-neighborhood compatibility, local finiteness,
  link compatibility, PL-manifold recognition, triangulation homeomorphism and
  compatibility, Moise triangulation uniqueness, the dimension-three
  Hauptvermutung input, compatible PL structure, PL transition compatibility, PL
  atlas/manifold-atlas/collar-neighborhood/homeomorphism compatibility, PL
  smoothing existence, smoothing-obstruction vanishing, microbundle smoothing,
  smoothing compatibility, smoothing uniqueness, and local-model compatibility,
  smooth-atlas construction, PL compatibility, maximality, uniqueness,
  smooth-structure uniqueness, smooth transition compatibility, transition-map
  smoothness, smooth-structure derivation, the assembled smooth-structure
  derivation statement, bridge derivation, smooth-model compatibility, and chart
  compatibility, plus checked projections to those sub-obligations, the raw
  smooth-structure input, a component-level derivation-statement assembly
  theorem, `SmoothabilitySubobligationsPayload`, a derivation-statement
  projection of the full smoothability sub-obligation stack, bridge theorem,
  derivation-dependent bridge application, and chained bridge/model/chart
  compatibility evidence. Package-level smoothability payloads
  `smoothability_smooth_structure_statement_payload_of_smoothability_package`
  and `smoothability_bridge_payload_of_smoothability_package` centralize the
  smooth-structure derivation statement route and the bridge/model/chart
  compatibility plus full sub-obligation route. Equality contracts now tie the
  package bridge, canonical smooth-manifold statement, bridge application,
  surgery-model and canonical smooth-manifold projections, compatibility
  evidence, and smoothability payloads back to the stored package fields or
  named component route. The lower Moise/PL/smooth spine also records direct
  equality contracts for the full Moise projection spine, including local
  charts, cover refinement, simplicial-complex/chart compatibility,
  triangulation, simplicial approximation, neighborhood, local-finiteness,
  link/PL-recognition, homeomorphism, uniqueness, Hauptvermutung inputs,
  PL-structure, PL transition compatibility, PL-atlas/manifold/collar/
  homeomorphism compatibility, PL-atlas maximality, PL smoothing existence,
  obstruction, microbundle, theorem, compatibility, uniqueness, local-model
  compatibility, smooth-structure, smooth-atlas construction, smooth-atlas
  PL compatibility/maximality/uniqueness, smooth-structure uniqueness,
  transition, and smooth-structure derivation projections.
  Dependency-level equality contracts
  now pin the full direct Moise/PL/smoothing/smooth-atlas/transition/derivation
  projection spine to the stored aggregate smoothability field. The dependency-level
  theorem-shaped bridge, `C∞` smooth-manifold statement, canonical smooth
  projection, and paired smoothability payload are also pinned to the stored
  smoothability fields. The dependency-level smooth-structure statement
  payload, derivation statement, raw bridge application, bridge derivation,
  smooth-model and chart compatibility, bridge payload tuple, and
  sub-obligation payload are now pinned to the stored package or the named
  reconstructed bridge route.
  The dependency-level smoothability route now consumes those package-level
  payloads through
  `smoothability_smooth_structure_statement_payload_of_dependencies`,
  `smoothability_bridge_statement_of_dependencies`, and
  `smoothability_bridge_payload_of_dependencies`. The separate theorem-shaped
  `C∞` statement `SmoothabilitySmoothManifoldStatement`, the package payload
  `smoothability_smooth_manifold_payload_of_smoothability_package`, and the
  dependency payload `smoothability_smooth_manifold_payload_of_dependencies`
  record the stronger smooth-manifold input consumed by the canonical smooth
  Poincare statement. The projections
  `smooth_manifold_of_smoothability_package` and
  `smooth_manifold_of_dependencies` destructure that route. The named
  dependency-level
  `smoothability_subobligations_payload_of_dependencies` centralizes the full
  smoothability sub-obligation witness, and the expanded sub-obligation
  projection destructures that named payload.
- `Poincare/FullAssembly.lean` proves the end-to-end conditional assembly from
  explicit smoothability-package, surgery-package, and topology-package
  hypotheses to `PoincareConjectureStatement`. The explicit finite-extinction
  input now passes through
  `finite_extinction_statement_payload_of_smoothability_and_surgery_packages`
  and `finite_extinction_input_of_smoothability_and_surgery_packages`, which
  carry the smoothability-installed manifold evidence, theorem-shaped
  finite-extinction statement, sub-obligation statement route, derivation
  certificate, and final finite-extinction witness; equality contracts pin both
  the statement payload and the projected finite-extinction input to this route.
  The extinction-to-sphere input is extracted by destructuring
  `topology_extraction_payload_of_topology_package`, so the full assembly
  layer consumes the package-level topology extraction payload instead of the
  raw final topology projection. The named
  `poincare_assembly_inputs_payload_of_surgery_and_topology_packages`
  centralizes that final input pair before the target statement is assembled.
  `poincare_target_payload_of_surgery_and_topology_packages` centralizes the
  call to `poincare_payload_of_extinction_and_extraction` and exposes the final
  input pair, target statement, and completion criterion. It also exposes
  `poincare_full_assembly_payload_of_surgery_and_topology_packages`, which
  carries the explicit smoothability package, surgery-package family, topology
  package, final finite-extinction input, extinction-to-sphere extraction input,
  and target statement by destructuring that target payload.
  `poincare_assembly_payload_of_surgery_and_topology_packages`
  destructures the full payload, while
  `poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement`,
  `poincare_target_payload_of_surgery_and_topology_extraction_statement`, and
  `poincare_statement_of_surgery_and_topology_extraction_statement` compose the
  same finite-extinction input directly with the theorem-shaped
  `ExtinctionTopologyExtractionStatement`; its completion-payload projection is
  `poincare_completion_payload_of_surgery_and_topology_extraction_statement`.
  The extractor-plus-derivation route
  `poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation`,
  `poincare_target_payload_of_surgery_and_extraction_derivation`,
  `poincare_completion_payload_of_surgery_and_extraction_derivation`, and
  `poincare_statement_of_surgery_and_extraction_derivation` composes the same
  finite-extinction input with a final extractor and its topology derivation
  certificate. The theorem-shaped topology, direct extractor/derivation,
  explicit package, and package-level certified extraction routes now have
  equality contracts for their assembly-input payload, target payload,
  completion payload, statement, and canonical-statement projections, with the
  explicit package route also pinning its full-assembly and assembly-payload
  projections. The package-level certified extraction route
  `poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_target_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  and
  `poincare_statement_of_surgery_and_topology_package_extraction_derivation`
  obtains that extractor-plus-derivation pair directly from the topology
  package before assembling the target.
  `poincare_completion_payload_of_surgery_and_topology_packages` destructures the
  target payload; the final statement theorem destructures the completion
  payload. The canonical endpoint
  `canonical_three_sphere_statement_of_surgery_and_topology_packages` exposes the
  same route as the mathlib-shaped topological 3-sphere statement.
  `canonical_three_sphere_statement_of_surgery_and_topology_extraction_statement`,
  `canonical_three_sphere_statement_of_surgery_and_extraction_derivation`, and
  `canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation`
  do the same for the theorem-shaped topology, extractor-plus-derivation, and
  package-level certified extraction routes.
- `Poincare/Dependencies.lean` aggregates the same future theorem inputs into a
  single `PoincareProofDependencies` package and projects it to the target
  statement and completion criterion. The aggregate route now exposes
  `poincareProofDependencies_components_payload` and
  `poincareProofDependencies_iff_components`, which identify that package with
  exactly the smoothability package, target-family surgery package, and
  topology extraction package; the reverse constructor from that raw component
  payload is now named, the reverse constructor has a direct equality contract,
  and the iff route is pinned to the named forward/reverse maps. It also exposes
  `poincare_assembly_inputs_payload_of_aggregate_dependencies`, which carries
  the final finite-extinction and extinction-to-sphere inputs by destructuring
  the explicit package-route assembly-input payload,
  `poincare_target_payload_of_aggregate_dependencies`, which centralizes the
  final input pair, target statement, and completion criterion, and
  `poincare_full_assembly_payload_of_dependencies`, which packages the
  smoothability package, surgery-package family, topology package, final input
  pair, and target statement by consuming that aggregate target payload. The
  shorter `poincare_assembly_payload_of_dependencies` and
  `poincare_completion_payload_of_dependencies` consume those named payloads;
  the statement and criterion projections destructure the completion payload.
  The direct aggregate certified extraction route
  `poincare_assembly_inputs_payload_of_aggregate_extraction_derivation_dependencies`,
  `poincare_target_payload_of_aggregate_extraction_derivation_dependencies`,
  `poincare_full_assembly_payload_of_aggregate_extraction_derivation_dependencies`,
  `poincare_completion_payload_of_aggregate_extraction_derivation_dependencies`,
  `poincare_statement_of_aggregate_extraction_derivation_dependencies`, and
  `completion_criterion_of_aggregate_extraction_derivation_dependencies`
  lifts the same aggregate package through the topology package's certified
  extractor-plus-derivation payload. The aggregate package also exposes
  `canonical_three_sphere_statement_of_dependencies` and
  `canonical_three_sphere_statement_of_aggregate_extraction_derivation_dependencies`,
  making both aggregate routes available as the mathlib-shaped topological
  3-sphere statement. Matching equality contracts now pin the component,
  assembly-input, target, full-assembly, assembly, completion, statement,
  canonical-statement, and completion-criterion routes to the stored aggregate
  package fields and the named package-level payload routes they consume.
- `Poincare/DependencyProjections.lean` proves named projection lemmas from a
  completed dependency package to the smoothability package, surgery packages,
  topology package, finite-extinction conclusion, and post-extinction
  extraction theorem. It also projects lower-level analytic foundation packages,
  `analytic_foundation_statement_payload_of_dependencies`, which destructures
  the surgery-level `analytic_foundation_payload_of_surgery_package` and now
  carries the projected flow directly for downstream projections,
  statement-mediated analytic foundation outputs, Ricci-flow data, Ricci-flow
  equation evidence, the statement-mediated analytic sub-obligation payload,
  the expanded analytic connection/curvature sub-obligation stack, with
  `analytic_foundation_subobligations_of_dependencies` returning the named
  `AnalyticFoundationSubobligationsPayload` instead of the raw connection/PDE
  conjunction. It also projects surgery construction packages, package-level
  surgery-construction payloads through
  `surgery_construction_payload_of_construction_package`,
  whose statement route and bundled payload are pinned by direct equality
  contracts,
  `surgery_construction_statement_payload_of_dependencies` carrying
  `RicciFlowWithSurgeryConstructionSubobligationsPayload`,
  statement-mediated surgery construction outputs, surgery construction
  sub-obligations, Perelman control packages, package-level Perelman payloads
  through `perelman_control_payload_of_package`,
  `perelman_control_statement_payload_of_dependencies` carrying
  `PerelmanSingularityControlSubobligationsPayload` and
  `PerelmanMonotonicityBlowupSubobligationsPayload`, statement-mediated
  Perelman control outputs, the expanded
  Perelman entropy/reduced-distance/reduced-volume/kappa/canonical-neighborhood
  sub-obligation stack, the Perelman
  monotonicity/blow-up sub-obligation stack, expanded finite-extinction
  min-max/variation/surgery/volume-decay sub-obligations,
  package-level finite-extinction payloads
  `finite_extinction_subobligations_payload_of_surgery_package` and
  `finite_extinction_statement_payload_of_surgery_package`,
  `finite_extinction_subobligations_statement_payload_of_dependencies`,
  statement-mediated finite-extinction width/full sub-obligation outputs
  through explicit statement destructuring,
  finite-extinction derivation stack, finite-extinction conclusion extraction
  from the full sub-obligation statement,
  topology decomposition, recognition, topology-recognition sub-obligations,
  the expanded post-extinction surgery-trace, classification, quotient, deck-action, and
  homeomorphism-assembly sub-obligation stack, the statement-mediated topology
  classification payload, `topology_extraction_payload_of_dependencies`,
  homeomorphism assembly/derivation outputs,
  extinction-to-homeomorphism outputs, and homeomorphism derivation
  certificates, plus
  `poincare_projection_assembly_inputs_payload_of_dependencies`, which
  centralizes the final projected finite-extinction and topology-extraction
  input pair before target assembly, and
  `poincare_target_payload_of_dependency_projections`, which centralizes the
  projected target statement and completion criterion, and
  `poincare_full_assembly_payload_of_dependency_projections`, which packages the
  projected smoothability package, surgery-package family, topology package,
  finite-extinction conclusion, post-extinction extraction theorem, and target
  statement. `poincare_assembly_inputs_payload_of_dependencies` reuses the named
  projection input payload for the final finite-extinction/extraction pair, and
  `poincare_completion_payload_of_dependency_projections` destructures the
  projection target payload for the target/criterion pair consumed by the final
  projection route. The projection canonical endpoints
  `canonical_three_sphere_statement_of_dependency_projections` and
  `canonical_three_sphere_statement_of_extraction_derivation_dependency_projections`
  expose those same routes as the mathlib-shaped topological statement, with
  equality contracts pinning them to the finite-extinction/topology-statement
  and certified extractor/derivation routes. The remaining-dependency canonical
  statement endpoints are also pinned to their named canonical targets, including
  the projection and certified projection target routes. The ordinary
  projection route now also reconstructs a checked completion certificate, with
  round-trip contracts for the remaining-dependency package, canonical payload,
  project payload, target, criterion, canonical topological statement, and
  literal/aggregate canonical-statement payload projections. The aggregate
  `PoincareProofDependencies` view of that ordinary projection certificate is
  now pinned through the converted remaining-dependency package, canonical and
  project completion payloads, target and criterion projections,
  aggregate-dependency/project-statement/theorem-name/literal payload
  projections, and the reverse literal, aggregate-dependency, and
  project-statement payload constructors. That aggregate projection certificate
  view is also pinned directly to the finite-extinction plus theorem-shaped
  topology-extraction route for the certificate, canonical/project payloads,
  target, criterion, and canonical topological statement, with the same direct
  topology-route contracts pinned for the remaining-dependency certificate
  payload, target, criterion, and canonical topological statement. The
  certified extraction-derivation projection certificate is likewise pinned
  directly to the finite-extinction plus extractor/derivation route at both
  remaining-dependency and aggregate proof-dependency surfaces. Those direct
  topology and extractor/derivation endpoints are also pinned through the
  theorem-name payload, literal and aggregate canonical-statement payload
  projections and constructors, plus the literal, aggregate-dependency, and
  project-statement full payload projections and constructors, for both
  projection certificates. The dependency-projection layer also exposes the
  full assembly payload and explicit completion criterion through endpoint-named
  equality contracts.
  It also projects the
  expanded smoothability Moise cover-refinement/chart-compatibility/
  simplicial-approximation/subdivision/regular-neighborhood/local-finiteness/
  link/PL-recognition/Hauptvermutung, PL-manifold/collar/homeomorphism,
  smoothing-obstruction/microbundle/uniqueness/local-model,
  smooth-atlas/PL-compatibility/transition-smoothness,
  DeTurck-linearization/parabolic-fixed-point analytic Ricci-flow PDE, and
  finite-extinction sub-obligation stacks from the aggregate dependency package.
  The analytic sub-obligation projection destructures
  `analytic_foundation_statement_payload_of_dependencies`; downstream
  Ricci-flow data, equation-evidence, derivation-statement, and sub-obligation
  projections consume the flow carried by that payload, while the raw analytic
  derivation, sub-obligation, statement, and equation-evidence bridges stay out
  of the dependency projection layer and are centralized below the surgery
  payload boundary. The downstream analytic projections now also have equality
  contracts back to the corresponding fields selected from
  `analytic_foundation_statement_payload_of_dependencies`.
  Surgery-construction and Perelman-control downstream projections now have the
  same equality-contract treatment against
  `surgery_construction_statement_payload_of_dependencies` and
  `perelman_control_statement_payload_of_dependencies`.
  The smoothability sub-obligation projection destructures
  `smoothability_subobligations_payload_of_dependencies`, which itself
  destructures `smoothability_bridge_payload_of_dependencies`; the raw
  smoothability derivation-statement bridge stays out of the dependency
  projection layer.
  The topology classification projections destructure
  `topology_classification_payload_of_dependencies`, which itself destructures
  `topology_extraction_statement_payload_of_topology_package`; raw
  classification projections from the topology package stay out of the
  dependency layer. Equality contracts now pin the classification payload,
  its decomposition projection, the surgery-trace reconstruction and
  handle-cancellation projections, the component classification/inventory/
  boundary-control projections, the 3-sphere recognition projection, the
  prime-decomposition/existence projections, the sphere-theorem, embedded-sphere,
  and loop-theorem inputs, prime
  compatibility and uniqueness, irreducibility, irreducible-factor recognition,
  connected-sum collapse, connected-sum fundamental-group and van Kampen
  control, simply connected prime-factor control, spherical-space-form
  reduction/classification, quotient-model, free-action, universal-cover,
  covering-model/projection, fundamental-group computation, deck-group
  identification, deck-action properness, deck-group triviality, deck-action
  trivialization, trivial deck-quotient identification, simply connected
  recognition, trivial spherical quotient, trivial-quotient homeomorphism,
  spherical homeomorphism-lift, and the explicit classification sub-obligation
  projection to that named route.
  The topology statement and final extraction projections destructure
  `topology_extraction_payload_of_dependencies`, which itself destructures
  `topology_extraction_payload_of_topology_package`; the raw topology
  package-to-statement and statement-to-extraction bridges stay out of the
  dependency projection layer.
  The certified extraction route also exposes
  `topology_extraction_derivation_payload_of_dependencies`, which converts the
  dependency-level theorem-shaped topology statement into a final extractor
  paired with its `ExtinctionTopologyDerivationForExtractionStatement`
  certificate, with equality contracts pinning the dependency payload,
  theorem-shaped statement, derivation-statement payload, projected
  homeomorphism route, assembly/derivation statements, direct
  assembly/derivation certificates, statement aliases, derivation payload, and
  extractor to the stored topology package route.
  The final projected Poincare theorem destructures
  `poincare_completion_payload_of_dependency_projections`, while the target and
  full payloads remain the named dependency-level sources for the completion
  criterion, package witnesses, finite-extinction and topology-extraction inputs,
  and target statement. Equality contracts now also pin the smoothability
  sub-obligation bridge, the finite-extinction via-subobligations theorem, the
  direct finite-extinction alias, and the projection assembly-input payloads to
  their named source routes. The target/full/completion payloads, conditional
  Poincare statements, canonical sphere statements, and completion criteria are
  likewise pinned back to those named projection and completion payload routes.
  The parallel extraction-derivation projection route exposes
  `poincare_projection_assembly_inputs_payload_of_extraction_derivation_dependencies`,
  `poincare_target_payload_of_extraction_derivation_dependency_projections`,
  `poincare_full_assembly_payload_of_extraction_derivation_dependency_projections`,
  `poincare_completion_payload_of_extraction_derivation_dependency_projections`,
  `poincare_statement_of_extraction_derivation_dependency_projections`, and
  `completion_criterion_of_extraction_derivation_dependency_projections`, so the
  dependency package can be consumed through the surgery-plus-certified-extractor
  route without dropping the topology derivation certificate.
- `Poincare/Milestones.lean` records the six missing dependency milestones as
  data and proves the ledger length, exact membership characterization, named
  membership for each milestone, and no-duplicate invariant.
- `Poincare/DependencyCrosswalk.lean` maps the milestone ledger to the concrete
  dependency-package layers that are intended to discharge it, with named Lean
  theorems for all six milestone-to-package links and a package-layer membership
  theorem for the mapped ledger. It also folds those package layers to the
  three aggregate dependency components with `DependencyComponentSlot`,
  `dependencyComponentForPackageLayer`,
  `dependencyComponentForMilestone`, and
  `dependencyComponentRequirement`. The component route also has the generic
  projection `dependencyComponentRequirement_of_dependencies`, named
  smoothability/surgery/topology component projections, and equality contracts
  pinning those wrappers to the generic component-slot route and to the stored
  `PoincareProofDependencies` fields. It also names the package-layer
  propositions with `dependencyPackageLayerRequirement`, proves package-layer
  requirement projections from `PoincareProofDependencies`, and records
  `dependency_package_layer_requirements_payload_of_dependencies` plus
  `poincareProofDependencies_iff_package_layer_requirements`. Generic
  package-layer projections now have equality contracts for all five concrete
  layers, including the analytic and surgery routes obtained by unpacking the
  stored surgery-family field, and the package-layer payload is pinned to the
  tuple of generic package-layer projections. The component
  route records `dependency_component_requirements_payload_of_dependencies`,
  `poincareProofDependencies_iff_component_requirements`,
  `dependency_ledger_has_component_slots`, and
  `dependency_ledger_component_slot_mem`. The milestone route now defines
  `dependencyMilestoneRequirement` through the package-layer map, with
  `dependencyMilestoneRequirement_of_dependencies`,
  `dependency_milestone_requirements_payload_of_dependencies`, and
  `poincareProofDependencies_iff_milestone_requirements`; this records analytic,
  construction/Perelman, finite-extinction, topology, and smoothability
  obligations at the milestone boundary. Equality contracts now pin the
  aggregate component-slot, package-layer, and milestone payload routes to the
  exact requirement tuples they project from `PoincareProofDependencies`; the
  reverse constructors from those requirement payloads back to
  `PoincareProofDependencies` are named and the three iff routes are pinned to
  the named forward/reverse maps. The individual component-slot, package-layer,
  and milestone projection wrappers are now pinned to their generic component,
  package-layer, or milestone projection routes. The component-slot payload is
  pinned both to the stored dependency fields and to the named component-slot
  projection tuple. The six milestone projections are also pinned directly to
  their assigned package-layer projections, and the milestone payload is pinned
  to the corresponding package-layer tuple.
- `Poincare/CompletionTarget.lean` records the canonical completion theorem name,
  target, and remaining dependency package, with `rfl` lemmas tying the target
  back to `PoincareConjectureStatement` and the explicit completion criterion,
  plus a direct equality contract for the target/criterion equality route,
  proves both directions between the target and criterion, exposes
  `extinction_extraction_of_canonical_completion_target`,
  `canonical_completion_target_of_extinction_and_extraction`, and
  `canonicalCompletionTarget_iff_extinction_extraction` for the canonical
  finite-extinction/extraction route, exposes the matching
  `canonical_completion_payload_of_extinction_and_extraction` and
  `canonical_completion_criterion_of_extinction_and_extraction` projections,
  and proves the
  explicit smoothability/surgery/topology package route plus both aggregate and
  projection-based dependency routes to the canonical target. The explicit
  package route exposes
  `canonical_completion_payload_of_surgery_and_topology_packages`, the
  finite-extinction plus theorem-shaped topology route exposes
  `canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement`,
  `canonical_completion_target_of_finite_extinction_and_topology_extraction_statement`,
  and
  `canonical_completion_criterion_of_finite_extinction_and_topology_extraction_statement`,
  while the extractor-plus-derivation route exposes
  `canonical_completion_payload_of_finite_extinction_and_extraction_derivation`,
  `canonical_completion_target_of_finite_extinction_and_extraction_derivation`,
  and
  `canonical_completion_criterion_of_finite_extinction_and_extraction_derivation`,
  the
  theorem-shaped topology route exposes
  `canonical_completion_payload_of_surgery_and_topology_extraction_statement`,
  `canonical_completion_target_of_surgery_and_topology_extraction_statement`,
  and
  `canonical_completion_criterion_of_surgery_and_topology_extraction_statement`,
  the surgery-plus-extractor-derivation route exposes
  `canonical_completion_payload_of_surgery_and_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_extraction_derivation`, and
  `canonical_completion_criterion_of_surgery_and_extraction_derivation`,
  the package-level certified extraction route exposes
  `canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_topology_package_extraction_derivation`,
  and
  `canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation`,
  the aggregate
  component-slot requirement route exposes
  `poincare_completion_payload_of_component_requirements`,
  `canonical_completion_payload_of_component_requirements`,
  `canonical_completion_target_of_component_requirements`, and
  `canonical_completion_criterion_of_component_requirements`, plus
  `canonical_three_sphere_statement_of_component_requirements`; the
  package-layer requirement route exposes
  `poincare_completion_payload_of_package_layer_requirements`,
  `canonical_completion_payload_of_package_layer_requirements`,
  `canonical_completion_target_of_package_layer_requirements`, and
  `canonical_completion_criterion_of_package_layer_requirements`, plus
  `canonical_three_sphere_statement_of_package_layer_requirements`; the
  milestone requirement route exposes
  `poincare_completion_payload_of_milestone_requirements`,
  `canonical_completion_payload_of_milestone_requirements`,
  `canonical_completion_target_of_milestone_requirements`, and
  `canonical_completion_criterion_of_milestone_requirements`, plus
  `canonical_three_sphere_statement_of_milestone_requirements`; the certified
  component-slot route exposes
  `poincare_completion_payload_of_component_extraction_derivation_requirements`,
  `canonical_completion_payload_of_component_extraction_derivation_requirements`,
  `canonical_completion_target_of_component_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_component_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_component_extraction_derivation_requirements`,
  the certified package-layer route exposes
  `poincare_completion_payload_of_package_layer_extraction_derivation_requirements`,
  `canonical_completion_payload_of_package_layer_extraction_derivation_requirements`,
  `canonical_completion_target_of_package_layer_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_package_layer_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_package_layer_extraction_derivation_requirements`,
  the certified milestone route exposes
  `poincare_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_target_of_milestone_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_milestone_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements`,
  the aggregate route exposes `canonical_completion_payload_of_dependencies`, the aggregate
  certified extraction route exposes
  `canonical_completion_payload_of_aggregate_extraction_derivation_dependencies`,
  `canonical_completion_target_of_aggregate_extraction_derivation_dependencies`,
  and
  `canonical_completion_criterion_of_aggregate_extraction_derivation_dependencies`,
  and the projection route exposes
  `canonical_completion_payload_of_dependency_projections`; those payloads carry
  the canonical target and the universe-indexed completion criterion together,
  with target and criterion projections destructuring them. The
  extraction-derivation dependency-projection route exposes
  `canonical_completion_payload_of_extraction_derivation_dependency_projections`,
  `canonical_completion_target_of_extraction_derivation_dependency_projections`,
  and
  `canonical_completion_criterion_of_extraction_derivation_dependency_projections`.
  The projection-route canonical payload, target, and criterion contracts now
  also factor through finite extinction plus
  `topology_extraction_statement_of_dependencies`; the certified
  extraction-derivation canonical contracts factor through finite extinction
  plus the dependency-level extractor/derivation payload.
  Equality contracts now pin the remaining-dependency project payload, aggregate
  canonical payload/target/criterion, aggregate certified payload/target/criterion,
  projection-route payload/target/criterion, and certified projection-route
  payload/target/criterion back to the named project payloads they consume. They
  also pin the extinction/extraction payload and criterion routes, the
  finite-extinction/topology-statement payload/target/criterion routes, the
  finite-extinction/certified-extraction payload/target/criterion routes, and the
  direct criterion-to-target bridge to their named constructions. The explicit
  package, theorem-shaped topology, surgery-plus-extractor, and package-level
  certified extraction canonical payload/target/criterion routes are now pinned
  to their shared project-payload bridges and named projection destructors too.
  The raw and certified component-slot routes now also have equality contracts
  for their project payloads, canonical payloads, target and criterion
  projections, and canonical topological statement projections. The raw and
  certified package-layer routes now have the same equality contracts, making
  explicit that the assembly consumes only the smoothability, finite-extinction,
  and topology layers while analytic and surgery-layer requirements remain
  recorded by the crosswalk. The raw and certified milestone routes now carry
  matching equality contracts, pinning them to the consumed smoothability,
  finite-extinction, and extinction-to-sphere component-slot routes while the
  analytic, surgery-construction, and Perelman-control milestones remain
  recorded by the milestone ledger.
  The canonical target
  payload is centralized in
  `canonical_completion_payload_of_canonical_completion_target`, with
  `poincare_completion_payload_of_canonical_completion_target` recording the
  direct project-payload view of a canonical target,
  `canonical_completion_target_of_canonical_completion_payload` and
  `completion_criterion_of_canonical_completion_payload` projecting the target
  and criterion back out, and
  `canonicalCompletionTarget_of_poincare_completion_payload` projecting a
  project payload back to the canonical target. The iff contracts
  `canonicalCompletionTarget_iff_canonical_completion_payload` and
  `completionCriterionAtUniverse_iff_canonical_completion_payload` identify the
  canonical target and criterion directly with that payload, while
  `canonical_completion_payload_of_completion_criterion` names the direct
  criterion-to-canonical-payload constructor. The reverse bridge
  `poincare_completion_payload_of_canonical_completion_payload` and iff
  contract `canonical_completion_payload_iff_poincare_completion_payload` make
  the canonical/project completion payload identification bidirectional.
  Equality contracts now pin these canonical target/criterion iff routes,
  extraction bridges, payload constructors, payload projections, and
  canonical/project payload iff routes to their named constructions, and they
  also pin the extinction/extraction, finite-extinction/topology-statement,
  finite-extinction/certified-extraction, and direct criterion-to-target
  canonical routes, plus the explicit package, theorem-shaped topology,
  surgery-plus-extractor, and package-level certified extraction canonical
  routes, the raw/certified component-slot routes, and the raw/certified
  package-layer and milestone routes; the
  raw and certified `RemainingDependencyPackage` component, package-layer, and
  milestone wrapper canonical payload, target, criterion, and statement routes
  now have equality contracts as well, tying the wrapper layer to the named
  remaining-dependency component, package-layer, and milestone payloads and
  crosswalk projections; the
  explicit
  package, package-level certified extraction, package-layer, aggregate
  dependency, aggregate certified extraction, projection-route, and
  extraction-derivation projection-route canonical payloads
  consume the corresponding noncanonical Poincare completion payloads through
  `canonical_completion_payload_of_poincare_completion_payload`, the shared
  bridge from the project target payload to the canonical completion payload.
  `remainingDependencyPackage_eq`,
  `remainingDependencyPackage_iff_poincareProofDependencies`, and
  `remainingDependencyPackage_iff_components` identify the remaining-dependency
  package with the aggregate package and its three component inputs; the
  remaining/aggregate iff bridge now also has an equality contract pinning it to
  the definitional equivalence. The theorem
  `remainingDependencyPackage_components_payload` exposes those components from
  the completion-target boundary, with named smoothability, surgery, and
  topology projections. The raw component payload is pinned to the stored
  remaining-dependency fields and aggregate component payload/equivalence. The
  theorem
  `remainingDependencyPackage_component_requirements_payload`, together with
  `remainingDependencyPackage_iff_component_requirements`, exposes the same
  boundary through the component-slot requirements named by the crosswalk; its
  payload is pinned directly to both the stored remaining-dependency fields and
  the named component-slot projection tuple.
  `remainingDependencyPackage_package_layer_requirements_payload`, together with
  `remainingDependencyPackage_iff_package_layer_requirements`, exposes the same
  boundary through the five package-layer requirements named by the crosswalk.
  `remainingDependencyPackage_milestone_requirements_payload`, together with
  `remainingDependencyPackage_iff_milestone_requirements`, exposes the same
  boundary through all six milestone requirements. The remaining package-layer
  and milestone payloads are now also pinned to the generic package-layer
  projection tuple and to the milestone-assigned package-layer projection tuple.
  The
  theorem
  `canonical_completion_payload_of_remaining_dependency_component_requirements`
  carries the remaining package to the canonical payload through that
  component-slot route, and
  `canonical_completion_target_of_remaining_dependency_component_requirements`
  plus
  `canonical_completion_criterion_of_remaining_dependency_component_requirements`
  expose the matching target and criterion projections, while
  `canonical_three_sphere_statement_of_remaining_dependency_component_requirements`
  exposes the canonical topological statement. The matching
  `canonical_completion_*_of_remaining_dependency_component_requirements_eq`
  contracts pin those wrapper projections to the named component payload route.
  The package-layer route similarly
  exposes
  `canonical_completion_payload_of_remaining_dependency_package_layer_requirements`,
  `canonical_completion_target_of_remaining_dependency_package_layer_requirements`,
  and
  `canonical_completion_criterion_of_remaining_dependency_package_layer_requirements`,
  plus
  `canonical_three_sphere_statement_of_remaining_dependency_package_layer_requirements`.
  Its matching
  `canonical_completion_*_of_remaining_dependency_package_layer_requirements_eq`
  contracts pin those wrapper projections to the named package-layer payload
  route.
  The milestone route
  similarly exposes
  `canonical_completion_payload_of_remaining_dependency_milestone_requirements`,
  `canonical_completion_target_of_remaining_dependency_milestone_requirements`,
  and
  `canonical_completion_criterion_of_remaining_dependency_milestone_requirements`,
  plus
  `canonical_three_sphere_statement_of_remaining_dependency_milestone_requirements`.
  Its matching
  `canonical_completion_*_of_remaining_dependency_milestone_requirements_eq`
  contracts pin those wrapper projections to the named milestone payload route.
  The certified remaining-dependency component-slot, package-layer, and
  milestone routes similarly expose
  `canonical_completion_payload_of_remaining_dependency_component_extraction_derivation_requirements`,
  `canonical_completion_target_of_remaining_dependency_component_extraction_derivation_requirements`,
  `canonical_completion_criterion_of_remaining_dependency_component_extraction_derivation_requirements`,
  `canonical_three_sphere_statement_of_remaining_dependency_component_extraction_derivation_requirements`,
  `canonical_completion_payload_of_remaining_dependency_package_layer_extraction_derivation_requirements`,
  `canonical_completion_target_of_remaining_dependency_package_layer_extraction_derivation_requirements`,
  `canonical_completion_criterion_of_remaining_dependency_package_layer_extraction_derivation_requirements`,
  `canonical_three_sphere_statement_of_remaining_dependency_package_layer_extraction_derivation_requirements`,
  `canonical_completion_payload_of_remaining_dependency_milestone_extraction_derivation_requirements`,
  `canonical_completion_target_of_remaining_dependency_milestone_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_remaining_dependency_milestone_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_remaining_dependency_milestone_extraction_derivation_requirements`.
  The certified component, package-layer, and milestone wrappers have parallel
  `canonical_completion_*_of_remaining_dependency_*_extraction_derivation_requirements_eq`
  equality contracts for their payload, target, criterion, and statement routes.
  The remaining-dependency crosswalk wrappers also expose direct project
  payload, target-statement, and criterion projections through
  `poincare_completion_payload_of_remaining_dependency_*`,
  `poincare_statement_of_remaining_dependency_*`, and
  `completion_criterion_of_remaining_dependency_*`.
  Those remaining-dependency project projections now have equality contracts
  pinning each route to the canonical remaining-dependency payload, target, or
  criterion projection it uses.
  The aggregate proof-dependency surface now exposes matching canonical
  topological statement projections for those raw and certified crosswalk
  routes:
  `canonical_three_sphere_statement_of_poincareProofDependencies_component_requirements`,
  `canonical_three_sphere_statement_of_poincareProofDependencies_component_extraction_derivation_requirements`,
  `canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_requirements`,
  `canonical_three_sphere_statement_of_poincareProofDependencies_package_layer_extraction_derivation_requirements`,
  `canonical_three_sphere_statement_of_poincareProofDependencies_milestone_requirements`,
  and
  `canonical_three_sphere_statement_of_poincareProofDependencies_milestone_extraction_derivation_requirements`.
  It also exposes matching canonical completion payload, target, and criterion
  projections for those aggregate raw and certified routes through the
  `canonical_completion_{payload,target,criterion}_of_poincareProofDependencies_*`
  theorem family, and matching project payload, target-statement, and criterion
  projections through
  `poincare_completion_payload_of_poincareProofDependencies_*`,
  `poincare_statement_of_poincareProofDependencies_*`, and
  `completion_criterion_of_poincareProofDependencies_*`.
  The aggregate component-slot, package-layer, and milestone raw and certified
  canonical statement, payload, target, and criterion routes now have equality
  contracts pinning them to the corresponding remaining-dependency wrapper
  routes after the `remainingDependencyPackage_iff_poincareProofDependencies`
  conversion.
  Their project payload, target-statement, and criterion projections now also
  have equality contracts pinning each `poincare_completion_payload_of_poincareProofDependencies_*`,
  `poincare_statement_of_poincareProofDependencies_*`, and
  `completion_criterion_of_poincareProofDependencies_*` route to the canonical
  aggregate wrapper projection it uses.
  A second aggregate project-contract layer now pins those same project routes
  directly to the corresponding remaining-dependency project routes after the
  `remainingDependencyPackage_iff_poincareProofDependencies` conversion.
  `PoincareCompletionCertificate` is a Prop-valued checked certificate for a
  completed artifact: it records the reserved theorem name, a remaining
  dependency package, the canonical target, and the universe-indexed completion
  criterion without constructing the missing theorem.
  `poincareCompletionCertificate_theoremName_payload` projects the reserved
  theorem name. The theorems
  `poincareCompletionCertificate_literal_payload`,
  `completion_certificate_of_literal_payload`, and
  `poincareCompletionCertificate_iff_literal_payload` identify the whole
  certificate with the literal reserved-name artifact payload. The target and
  criterion projections are
  `canonical_completion_payload_of_completion_certificate`,
  `poincare_completion_payload_of_completion_certificate`,
  `canonical_completion_target_of_completion_certificate`,
  `target_statement_of_completion_certificate`, and
  `completion_criterion_of_completion_certificate`.
  `remaining_dependency_package_of_completion_certificate`,
  `completion_certificate_of_remaining_dependency_and_poincare_payload`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_poincare_payload`,
  `completion_certificate_of_remaining_dependency_and_canonical_payload`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_canonical_payload`,
  `completion_certificate_of_remaining_dependency_and_target_statement`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_target_statement`,
  `completion_certificate_of_remaining_dependency_and_canonical_target`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_canonical_target`,
  `completion_certificate_of_remaining_dependency_and_completion_criterion`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_completion_criterion`,
  `poincareProofDependencies_of_completion_certificate`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage`,
  `poincareCompletionCertificate_iff_poincareProofDependencies`, and
  `completion_certificate_of_poincareProofDependencies`,
  `completion_certificate_of_poincareProofDependencies_and_poincare_payload`,
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_poincare_payload`,
  `completion_certificate_of_poincareProofDependencies_and_canonical_payload`,
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_payload`,
  `completion_certificate_of_poincareProofDependencies_and_target_statement`,
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_target_statement`,
  `completion_certificate_of_poincareProofDependencies_and_canonical_target`,
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_target`,
  `completion_certificate_of_poincareProofDependencies_and_completion_criterion`,
  and
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_completion_criterion`
  connect the certificate directly to the aggregate dependency package. The
  corresponding aggregate dependency plus payload, target, and criterion
  constructors and iff routes now have equality contracts pinning them to the
  remaining-dependency certificate constructors they delegate to after the
  `remainingDependencyPackage_iff_poincareProofDependencies` conversion.
  The remaining-dependency and aggregate-dependency payload, target, criterion,
  and package constructors now also have projection-after-constructor round-trip
  contracts. The
  theorems
  `poincareCompletionCertificate_aggregate_dependency_payload`,
  `completion_certificate_of_aggregate_dependency_payload`, and
  `poincareCompletionCertificate_iff_aggregate_dependency_payload` identify the
  whole artifact payload with that aggregate dependency package named directly.
  `poincareCompletionCertificate_project_statement_payload`,
  `completion_certificate_of_project_statement_payload`, and
  `poincareCompletionCertificate_iff_project_statement_payload` identify the
  analogous full payload with the project Poincare statement named directly.
  The literal, aggregate-dependency, and project-statement full payload
  constructors now have projection and reconstruction round-trip contracts.
  `poincareCompletionCertificate_iff_components`,
  `poincareCompletionCertificate_iff_component_requirements`,
  `poincareCompletionCertificate_iff_package_layer_requirements`, and
  `poincareCompletionCertificate_iff_milestone_requirements` show that the
  certificate is equivalent to its component, component-slot, package-layer,
  and milestone presentations.
  `poincareCompletionCertificate_components_payload`,
  `poincareCompletionCertificate_component_requirements_payload`,
  `poincareCompletionCertificate_package_layer_requirements_payload`, and
  `poincareCompletionCertificate_milestone_requirements_payload` project those
  presentations back out of the certificate. The raw-component certificate
  payload is pinned back to the certificate's remaining-dependency component
  payload and stored fields, while the component-slot, package-layer, and
  milestone certificate payloads are pinned back to the certificate's
  remaining-dependency payloads and to the corresponding component,
  generic-package, or milestone-assigned package-layer projection tuples.
  `completion_certificate_of_components`,
  `completion_certificate_of_component_requirements`,
  `completion_certificate_of_package_layer_requirements`, and
  `completion_certificate_of_milestone_requirements` build the certificate
  directly from those presentations. Those constructors and their payload
  variants are pinned back to
  `completion_certificate_of_remaining_dependency_package` after reconstructing
  the corresponding remaining-dependency package. The presentation constructors
  and payload constructors also now have projection-after-constructor
  round-trip contracts for raw components, component slots, package layers, and
  milestones.
  `completion_certificate_of_remaining_dependency_package`,
  `completion_certificate_of_component_extraction_derivation_requirements`,
  `completion_certificate_of_component_extraction_derivation_requirements_payload`,
  `poincareCompletionCertificate_iff_component_extraction_derivation_requirements`,
  `completion_certificate_of_package_layer_extraction_derivation_requirements`,
  `completion_certificate_of_package_layer_extraction_derivation_requirements_payload`,
  `poincareCompletionCertificate_iff_package_layer_extraction_derivation_requirements`,
  `completion_certificate_of_milestone_extraction_derivation_requirements`,
  `completion_certificate_of_milestone_extraction_derivation_requirements_payload`,
  `poincareCompletionCertificate_iff_milestone_extraction_derivation_requirements`,
  the certified constructors and their payload variants are pinned back to the
  corresponding remaining-dependency certified routes after reconstructing the
  remaining-dependency package, and now have projection-after-constructor
  round-trip contracts back to their certified component-slot, package-layer,
  and milestone payload presentations,
  the remaining-dependency raw component/package-layer/milestone certificate
  routes
  `completion_certificate_of_remaining_dependency_component_requirements`,
  `poincareCompletionCertificate_iff_remaining_dependency_component_requirements`,
  `completion_certificate_of_remaining_dependency_package_layer_requirements`,
  `poincareCompletionCertificate_iff_remaining_dependency_package_layer_requirements`,
  `completion_certificate_of_remaining_dependency_milestone_requirements`, and
  `poincareCompletionCertificate_iff_remaining_dependency_milestone_requirements`,
  the direct aggregate proof-dependency raw crosswalk certificate routes and
  matching iff contracts,
  the remaining-dependency certified component/package-layer/milestone
  certificate routes and matching iff contracts,
  the direct aggregate proof-dependency certified crosswalk certificate routes
  and matching iff contracts,
  `completion_certificate_of_aggregate_extraction_derivation_dependencies`, and
  `completion_certificate_of_extraction_derivation_dependency_projections` build
  that certificate from the aggregate, certified crosswalk, aggregate certified,
  and projection certified remaining-dependency routes. The matching iff contracts
  `poincareCompletionCertificate_iff_aggregate_extraction_derivation_dependencies`
  and
  `poincareCompletionCertificate_iff_extraction_derivation_dependency_projections`,
  plus the direct aggregate-package routes
  `completion_certificate_of_poincareProofDependencies_aggregate_extraction_derivation`,
  `poincareCompletionCertificate_iff_poincareProofDependencies_aggregate_extraction_derivation`,
  `completion_certificate_of_poincareProofDependencies_extraction_derivation_projections`,
  and
  `poincareCompletionCertificate_iff_poincareProofDependencies_extraction_derivation_projections`,
  make those certified certificate routes reversible at both dependency-package
  surfaces. The projection and certified projection iff contracts are also
  pinned directly to the finite-extinction plus theorem-shaped
  topology-extraction endpoint and the finite-extinction plus
  extractor/derivation endpoint at both dependency-package surfaces. Those
  dependency-package routes now also have
  projection-after-constructor round-trip contracts back to the
  remaining-dependency or aggregate dependency package they were built from,
  including the converted remaining-dependency package stored by each aggregate
  dependency route. The projection and certified projection endpoint variants
  name those dependency-package round-trips directly for the finite-extinction
  plus topology-extraction and extractor/derivation routes.
  Their certificate constructors now also have theorem-name, literal full
  payload projection/reconstruction, canonical/project payload, target,
  criterion, aggregate-dependency full payload projection/reconstruction,
  project-statement full payload projection/reconstruction, canonical
  topological statement, full literal canonical-statement artifact payload
  projection/reconstruction, and aggregate canonical-statement artifact payload
  projection/reconstruction contracts back to the named raw, certified,
  aggregate, and projection routes that built the certificates.
  The ordinary dependency-projection certificate route is also pinned across
  the aggregate proof-dependency surface for its converted remaining package,
  canonical/project payloads, target/criterion projections,
  aggregate-dependency payload, project-statement payload, theorem-name payload,
  literal payload, and reverse literal, aggregate-dependency, and
  project-statement payload constructors, plus direct finite-extinction and
  theorem-shaped topology-extraction contracts for its certificate,
  canonical/project payloads, target, criterion, and canonical topological
  statement, together with the same direct topology-route contracts for the
  remaining-dependency projection certificate's payloads, target, criterion,
  and canonical topological statement. The certified extraction-derivation
  projection certificate is also pinned directly to the finite-extinction plus
  extractor/derivation route for its certificate, canonical/project payloads,
  target, criterion, and canonical topological statement at both
  remaining-dependency and aggregate surfaces. The matching theorem-name
  payload, literal and aggregate canonical-statement payload projections and
  constructors, plus the literal, aggregate-dependency, and project-statement
  full payload projections and constructors, now also point directly at those
  topology and extractor/derivation endpoints.
  The certificate-layer equality contracts now pin the reserved-name, literal
  payload, canonical payload, target/criterion projection, remaining/aggregate
  dependency, and project-statement routes to their named projections and
  constructors without declaring the final theorem.
  The raw component/crosswalk presentation equality contracts now do the same
  for the component, component-slot, package-layer, and milestone certificate
  equivalences, projections, direct constructors, and payload constructors.
  The certified extraction-derivation presentation equality contracts now pin
  the certified component-slot, package-layer, and milestone certificate
  constructors, payload constructors, and iff routes to the canonical
  extraction-derivation payloads they use.
  The remaining/aggregate route equality contracts now pin the raw and
  certified remaining-dependency constructors, aggregate dependency
  constructors, aggregate extraction-derivation constructors, projection
  constructors, and their iff routes to the named dependency conversions.
  The
  theorem
  `poincare_completion_payload_of_remaining_dependency_package` makes the
  remaining-dependency package's noncanonical completion payload explicit before
  the aggregate canonical payload is assembled.
- `Poincare/CanonicalBridges.lean` exposes
  `canonical_completion_payload_of_canonical_three_sphere_statement` and
  `canonical_completion_payload_of_canonical_smooth_three_sphere_statement`, with
  matching target and criterion projections for the mathlib-shaped topological
  and smooth statement routes. These canonical payloads consume
  `poincare_payload_of_canonical_three_sphere_statement` and
  `poincare_payload_of_canonical_smooth_three_sphere_statement` through
  `canonical_completion_payload_of_poincare_completion_payload`. The same module
  now pins the canonical topological statement bridge with equality contracts
  for the payload, target, criterion, statement projections, certificate
  payload constructors, remaining/aggregate certificate constructors, and iff
  routes. The same module
  now also exposes
  `canonical_three_sphere_statement_of_canonical_completion_target`,
  `canonical_three_sphere_statement_of_canonical_completion_payload`,
  `canonical_three_sphere_statement_iff_canonical_completion_target`,
  `canonical_three_sphere_statement_iff_canonical_completion_payload`,
  `canonical_three_sphere_statement_of_completion_certificate`,
  `completion_certificate_of_remaining_dependency_and_canonical_three_sphere_statement`,
  `poincareCompletionCertificate_iff_remainingDependencyPackage_and_canonical_three_sphere_statement`,
  `completion_certificate_of_poincareProofDependencies_and_canonical_three_sphere_statement`,
  and
  `poincareCompletionCertificate_iff_poincareProofDependencies_and_canonical_three_sphere_statement`,
  making the canonical statement/certificate route reversible at both dependency
  package surfaces. The literal and aggregate canonical-statement payload
  constructors now have route-specific projection/reconstruction contracts,
  while the dependency-package constructors have projection-after-constructor
  contracts back to their dependency packages and canonical topological
  statement proofs. It also adds the smooth-route certificate constructors
  `completion_certificate_of_remaining_dependency_and_smooth_statement`,
  `completion_certificate_of_poincareProofDependencies_and_smooth_statement`,
  `completion_certificate_of_remaining_dependency_and_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_poincareProofDependencies_and_canonical_smooth_three_sphere_statement`,
  plus the packaged smooth-route payloads
  `packaged_smooth_statement_completion_payload_of_remaining_dependency`,
  `packaged_smooth_statement_completion_payload_of_poincareProofDependencies`,
  `packaged_canonical_smooth_three_sphere_statement_completion_payload_of_remaining_dependency`,
  `packaged_canonical_smooth_three_sphere_statement_completion_payload_of_poincareProofDependencies`,
  `packaged_reverse_canonical_smooth_three_sphere_statement_completion_payload_of_remaining_dependency`,
  and
  `packaged_reverse_canonical_smooth_three_sphere_statement_completion_payload_of_poincareProofDependencies`,
  which record the package's `C∞` smoothability statement, the smooth,
  canonical-smooth, or reverse canonical-smooth input, the induced topological target, and the completion
  criterion. The packaged smooth-route payload constructors now have reverse
  reconstruction contracts for the smooth, canonical-smooth, and reverse
  canonical-smooth route payload endpoints at both dependency surfaces. The
  matching canonical payload routes
  `canonical_completion_payload_of_remaining_dependency_and_packaged_smooth_statement`,
  `canonical_completion_payload_of_poincareProofDependencies_and_packaged_smooth_statement`,
  `canonical_completion_payload_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement`,
  `canonical_completion_payload_of_poincareProofDependencies_and_packaged_canonical_smooth_three_sphere_statement`,
  `canonical_completion_payload_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement`,
  and
  `canonical_completion_payload_of_poincareProofDependencies_and_packaged_reverse_canonical_smooth_three_sphere_statement`
  convert those one-way smooth payloads into canonical completion payloads
  after the `poincare_statement_of_*packaged*` and
  `completion_criterion_of_*packaged*` projections name the intermediate
  project target and criterion endpoints and the matching
  `poincare_completion_payload_of_*packaged*` payloads package those endpoints
  as the project-level completion payload; the matching
  `canonical_completion_target_of_*packaged*` and
  `canonical_completion_criterion_of_*packaged*` projections then name their
  canonical target and criterion endpoints, while the matching
  `canonical_three_sphere_statement_of_*packaged*` projections expose the
  canonical topological statement before the certificate constructors consume
  them, the
  `poincareCompletionCertificate_*packaged*payload` projections expose those
  packaged routes from an existing checked certificate, the matching
  `completion_certificate_of_*packaged*payload` constructors rebuild checked
  certificates directly from those packaged payloads, and the
  `poincareCompletionCertificate_iff_*packaged*payload` contracts make the
  supplied smooth/canonical-smooth packaged payload routes reversible at the
  checked certificate surface for the smooth, canonical-smooth, and reverse
  canonical-smooth routes. Those packaged payload constructors now also
  have projection-after-constructor round-trip contracts back to their
  remaining-dependency and aggregate payloads. The smooth and packaged-smooth
  routes now also
  have equality contracts pinning their canonical payload, certificate
  constructor, packaged payload, project target/criterion, project completion
  payload, canonical-payload conversion, canonical target, canonical criterion,
  and canonical-statement projection endpoints,
  with direct aggregate-to-remaining contracts for the packaged smooth, packaged
  canonical-smooth, and packaged reverse canonical-smooth project target,
  criterion, project completion payload, canonical payload, canonical target,
  canonical criterion, and canonical-statement routes after
  `remainingDependencyPackage_iff_poincareProofDependencies`,
  and certificate projections now round-trip the project payload, canonical
  payload, project target statement, canonical target, completion criterion,
  and canonical topological statement after the canonical-statement, smooth,
  canonical-smooth, packaged smooth, packaged canonical-smooth, and packaged
  reverse canonical-smooth constructors,
  and the base remaining-dependency plus aggregate-dependency constructors now
  also round-trip their dependency projection after the canonical-payload,
  target-statement, canonical-target, completion-criterion, and aggregate
  project-payload routes. The base remaining-dependency payload/target/criterion
  equivalences are now pinned to their named projection/constructor pairs as
  equality contracts,
  while the completion-target constructors
  `completion_certificate_of_*requirements_payload` and
  `completion_certificate_of_components_payload` rebuild checked certificates
  directly from the raw component, component-slot, package-layer, and milestone
  existential payloads exposed by an existing certificate,
  plus the packaged variants
  `completion_certificate_of_remaining_dependency_and_packaged_smooth_statement`,
  `completion_certificate_of_poincareProofDependencies_and_packaged_smooth_statement`,
  `completion_certificate_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement`,
  `completion_certificate_of_poincareProofDependencies_and_packaged_canonical_smooth_three_sphere_statement`,
  `completion_certificate_of_remaining_dependency_and_packaged_reverse_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_poincareProofDependencies_and_packaged_reverse_canonical_smooth_three_sphere_statement`,
  so a proof-bearing smooth statement can use the dependency package's own `C∞`
  smoothability output to reconstruct the checked completion certificate at both
  dependency package surfaces. The smooth and canonical-smooth packaged
  certificate constructors are pinned directly to their canonical-payload
  certificate routes, and those smooth and packaged smooth certificate
  constructors also have dependency projection round-trip contracts and packaged
  payload reconstruction contracts at both the remaining-dependency and
  aggregate-dependency surfaces. The standalone
  smoothability route now also
  records `smoothability_package_smooth_statement_completion_payload`,
  `poincare_completion_payload_of_smoothability_package_and_smooth_statement`,
  `canonical_completion_payload_of_smoothability_package_and_smooth_statement`,
  and their canonical-smooth and reverse canonical-smooth variants, showing that a `SmoothabilityPackage`
  alone supplies the `C∞` smooth-manifold input needed to turn a smooth
  proof-bearing Poincare statement into the project target, canonical completion
  payload, and canonical topological statement without the surgery/topology
  packages.
- `scripts/interface_audit.sh` checks that the gap-bearing predicates have no
  local constructors.
- `scripts/mathlib_gap_audit.sh` checks the local mathlib Poincare statement,
  Riemannian metric, Ricci-specific, and Ricci-flow-with-surgery surfaces, and
  runs `scripts/mathlib_proof_wanted_dependency_guard.sh` so local Lean source
  cannot reference mathlib's Poincare shortcut names while they remain
  proof-wanted upstream.
- `scripts/semantic_surface_audit.sh` asks Lean to typecheck the main
  conditional theorem surfaces, the topology extraction statement bridge, and
  lower-level package projection lemmas.
- `scripts/root_import_audit.sh` checks that `Poincare.lean` imports every
  local Lean module under `Poincare/` and exposes the canonical target contracts
  plus the canonical assembly bridges and projection-based dependency assembly
  theorem through the root import.
- `scripts/axiom_audit.sh` prints the axiom footprint for local proof-bearing
  assembly theorems and verifies that it contains no placeholders, no dependency
  on the absent final theorem, no local Lean-source references to mathlib's
  Poincare shortcut names, and no nonstandard axioms beyond mathlib's usual
  `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/completion_audit.sh` checks the dependency-spine declarations,
  confirms no local declaration claims `PoincareProofDependencies`, and fails,
  as expected, because the actual proof is absent.
- `scripts/write_status_summary.sh` writes `CURRENT_STATUS.md` as a generated
  snapshot of the current audit state.
- `scripts/completion_audit.sh` checks that `CURRENT_STATUS.md` records the
  current incomplete completion state while the canonical theorem is absent.

## Blocking Proof Obligations

1. `DependencyMilestone.smoothabilityBridge`
   - Smoothability and compatibility bridge from the topological 3-manifold
     target to the smooth category used by Ricci flow with surgery.
   - Moise triangulation, simplicial-complex, PL-atlas/smoothing, smooth-atlas,
     transition-compatibility, model-compatibility, and chart-compatibility
     sub-obligations must be supplied by real 3-dimensional smoothability
     theorems, not local constructors.
   - The current smoothability split also isolates locally finite cover
     refinement, compatible chart triangulations, simplicial approximation,
     star-neighborhood bases, barycentric subdivision, regular-neighborhood
     compatibility, local finiteness, link compatibility, PL-manifold
     recognition, the dimension-three Hauptvermutung input, PL-manifold atlas
     extraction, PL collar-neighborhood and PL-homeomorphism compatibility,
     smoothing-obstruction vanishing, microbundle smoothing, smoothing
     uniqueness, local smooth-model compatibility, smooth-atlas/PL
     compatibility, transition-map smoothness, uniqueness of the smooth
     structure up to diffeomorphism, and a smooth-structure derivation statement
     assembled from the component witnesses. The full smoothability
     sub-obligation projection, bridge theorem application, and bridge/model/chart
     compatibility witnesses must depend on that assembled statement.

2. `DependencyMilestone.ricciFlowAnalyticFoundation`
   - Riemannian metrics, curvature tensors, Ricci curvature, scalar curvature,
     and the Ricci flow equation at the required 3-manifold level.
   - DeTurck reduction, strict parabolicity, short-time existence, pullback to
     Ricci flow, maximal-time/continuation criteria, parabolic Schauder
     regularity, Shi estimates, maximum principle, and curvature evolution
     identities.
   - The current analytic split also isolates the DeTurck background metric,
     DeTurck vector field, Ricci-DeTurck linearization, linear parabolic
     theory, fixed-point construction, short-time smoothness bootstrap,
     DeTurck diffeomorphism ODE, pullback equation identity, bounded-curvature
     extension, and curvature derivative bootstrap.

3. `DependencyMilestone.ricciFlowWithSurgery`
   - Formal construction of Ricci flow with surgery for closed 3-manifolds.
   - Long-time existence with controlled surgery parameters.

4. `DependencyMilestone.perelmanSingularityControl`
   - F/W entropy functionals, conjugate heat equation theory, adjoint heat
     kernels, entropy normalization, minimizer existence, log-Sobolev control,
     heat-kernel estimates, gradient and first-variation formulas, monotonicity,
     and entropy lower-bound propagation.
   - Reduced-length, reduced-distance, and reduced-volume derivative and
     monotonicity machinery, including cut-locus/barrier control,
     reduced-Jacobian comparison, positive lower bounds, and limit rigidity.
   - No-local-collapsing volume lower bounds, quantified kappa-noncollapsing,
     the collapsed-ball contradiction, Hamilton compactness, and ancient
     kappa-solution pointed-rescaling, curvature-normalization,
     nonnegative-curvature, structure/asymptotic soliton/compactness inputs.
   - Canonical-neighborhood neck/cap dichotomy, classification, and singularity
     model blow-up/classification inputs needed by surgery, including
     canonical-neighborhood stability and cross-scale persistence.

5. `DependencyMilestone.finiteExtinction`
   - Finite extinction for compact simply connected 3-manifolds under Ricci flow
     with surgery.
   - Finite fundamental-group input, sweepouts, sweepout continuity and
     nontriviality, area-functional setup, min-max/width compactness,
     minimizing sequences, width theory, first/second variation, Gauss-Bonnet
     estimates, scalar-curvature width bounds, width evolution, surgery metric
     comparison, surgery width-drop control, discarded-component width
     neutrality/classification, positive-scalar-curvature lower bounds and
     persistence, volume evolution, surgery volume nonincrease, volume decay,
     differential-inequality integration, finite-time integration, and
     component-topology control before the final extinction conclusion.

6. `DependencyMilestone.extinctionToSphereHomeomorphism`
   - Topological extraction showing finite extinction gives a homeomorphism to
     the standard 3-sphere.
   - Surgery-trace reconstruction and handle cancellation, component inventory
     with discarded-component homeomorphism classification and boundary-sphere
     control, prime decomposition existence, sphere-theorem input,
     embedded-sphere production, loop-theorem input, prime uniqueness,
     irreducibility and irreducible factor recognition, connected-sum collapse
     with fundamental-group control, van Kampen calculation, simply connected
     prime-factor control, spherical space form recognition/classification,
     quotient-model and free-action data, universal-cover, covering-model, and
     covering-projection identification, spherical fundamental-group
     computation, deck-group identification, deck-action properness,
     deck-group triviality, deck-action trivialization, trivial deck-quotient
     identification, trivial-quotient homeomorphism, spherical homeomorphism
     lift, final homeomorphism assembly in the simply connected case, and a
     derivation certificate depending on that assembly.

## Completion Rule

The project is complete only when:

- `PoincareConjectureStatement` has a proof-bearing Lean theorem named
  `poincare_conjecture`.
- The proof does not use `axiom`, `opaque`, `constant`, `postulate`, `sorry`, or
  `admit`.
- The proof does not use local `proof_wanted` declarations.
- Mathlib's corresponding 3D Poincare declarations are not used as shortcut
  proof sources; while they remain merely `proof_wanted`, local Lean source must
  not reference their canonical names.
- `lake build`, `sh scripts/audit_formalization.sh`, and
  `sh scripts/completion_audit.sh` all pass.
