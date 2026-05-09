# Poincare Lean Formalization Scaffold

This directory is a starting scaffold for a Lean formalization project targeting the
Poincare Conjecture. It is not a completed proof.

The current artifact is intentionally conservative:

- `Poincare/Statement.lean` records the intended theorem boundary and the missing
  formalization interfaces. It uses mathlib's `Metric.sphere` for the target
  3-sphere as the unit sphere in `EuclideanSpace ℝ (Fin 4)`, aligns with
  `Mathlib.Geometry.Manifold.PoincareConjecture`, and includes `rfl` lemmas for
  the exact target sphere model plus the topological and smooth statement shapes,
  names the supplied T2, compact, charted-space, and smooth-manifold facts for
  the standard sphere, proves the ambient `ℝ^4` rank input for mathlib's
  connected-sphere theorem and the resulting path-connected, locally
  path-connected, connected, and nonempty facts for the target `S^3`, packages
  those available prerequisites except simple-connectedness into checked target
  and homotopy payloads, includes explicit iff contracts
  for those canonical topological and smooth statement shapes, and an iff
  contract plus both directions between the target statement and the explicit
  completion criterion. It also names
  witness-transfer and
  witness-equivalence lemmas for the universe-indexed completion criterion,
  centralizes the target plus completion-criterion existential payload in
  `poincare_completion_payload_of_poincareConjectureStatement`, projects that
  payload back to the target and criterion, exposes the same payload directly
  from a witness-indexed completion criterion, and records iff contracts between
  the target/criterion and the payload. The statement layer now also pins those
  canonical-statement, witness-transfer, target/criterion projection, and
  target/criterion payload routes with equality contracts.
  It also names the full standard-sphere target and homotopy prerequisite
  payloads under the explicit `SimplyConnectedSpace ThreeSphere` assumption,
  extending the existing prerequisite payloads that deliberately leave that
  input open.  The remaining simple-connectedness input is also reduced to the
  concrete `ThreeSphereLoopNullhomotopyStatement` via mathlib's
  loop-nullhomotopy criterion and the named path-connectedness proof for `S^3`,
  and that concrete obligation feeds the full standard-sphere prerequisite
  payloads directly.
  A parallel `ThreeSpherePathHomotopyStatement` records the equivalent concrete
  obligation that any two parallel paths in `S^3` are homotopic, with named
  routes to and from simple-connectedness, conversions to and from the
  loop-nullhomotopy obligation, and direct feeds into those standard-sphere
  prerequisite payloads; compatibility contracts pin those direct feeds to the
  corresponding loop-nullhomotopy-mediated routes.
- `Poincare/Milestones.lean` and `DEPENDENCY_LEDGER.md` name the missing
  Ricci-flow and topology proof obligations as data, not as proved
  propositions.
- The theorem-shaped boundary statements for finite-extinction extraction,
  analytic foundation, smoothability, finite extinction, and topology extraction
  now have direct equality contracts pinning them to their exact universal or
  existential proposition shapes. The checked completion certificate proposition
  is also pinned to the reserved theorem name, remaining dependency package,
  canonical target, and universe-indexed completion criterion it records.
- `Poincare/Assembly.lean` contains small proof-bearing assembly lemmas that do
  not prove Poincare, such as turning a diffeomorphism on either side of `S^3`
  into a homeomorphism to `S^3`, recording the equivalence between those two
  diffeomorphism directions, naming the standard sphere's reflexive smooth
  self-diffeomorphism and its smooth-to-topological self-homeomorphism route,
  pairing those reflexive endpoints with the available standard-sphere target
  prerequisites without a simple-connectedness input, and projecting those
  payloads back to their named prerequisite and endpoint components,
  exposing the standard-sphere self-case obtained by applying the topological
  or smooth target statement when `S^3` is supplied as simply connected,
  packaging those self-case endpoints with the full homotopy-oriented
  standard-sphere prerequisites, and exposing the same self-case routes and
  payloads from the concrete loop-nullhomotopy and path-homotopy obligations,
  with compatibility contracts between the direct path routes and the
  loop-nullhomotopy-mediated routes,
  and reducing the topological target to the smooth Poincare statement plus a
  smoothability hypothesis. It also bridges both the
  canonical topological and smooth mathlib-shaped 3-sphere statements into the
  local target statements when supplied as explicit proof-bearing inputs, and
  composes the canonical smooth statement with smoothability into the local
  topological target. The canonical topological, smooth-statement, and canonical
  smooth routes now expose payloads carrying the local target and the explicit
  completion criterion together; those payloads consume the statement-layer
  completion payload, the criterion bridges destructure them, and the reverse
  canonical statement bridges expose the topological and smooth canonical
  statement shapes from the local statement/payload/criterion surfaces, including
  `canonical_three_sphere_statement_of_completionCriterionAtUniverse`,
  `canonical_three_sphere_statement_iff_completionCriterionAtUniverse`, and
  `completion_criterion_of_smooth_statement`; the smooth, reverse-smooth, and
  canonical-smooth routes also expose the canonical topological statement
  directly through
  `canonical_three_sphere_statement_of_smooth_statement` and
  `canonical_three_sphere_statement_of_reverse_smooth_statement` and
  `canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement`.
  At the smooth statement layer,
  `reverse_canonical_smooth_three_sphere_statement_iff_smooth_statement` and
  `canonical_smooth_three_sphere_statement_iff_reverse_canonical_smooth_three_sphere_statement`
  pin the `S^3 -> M` and `M -> S^3` canonical smooth shapes to the same local
  smooth target.
  Equality contracts now pin these statement-layer bridges, payload
  constructors, criterion projections, and canonical-statement iff routes to
  their named assembly paths.
- `Poincare/CanonicalBridges.lean` connects the canonical topological, smooth,
  and reverse-direction smooth mathlib-shaped 3-sphere statement inputs to
  canonical completion payloads that carry both the canonical target and the
  universe-indexed completion criterion;
  those payloads now consume the assembly-layer payloads, target and criterion
  projections destructure them, and the reverse canonical statement/certificate
  bridges expose the canonical topological statement from the canonical target,
  canonical payload, checked completion certificate, and all remaining-dependency
  aggregate/projection completion routes, plus the packaged smooth and
  packaged canonical-smooth routes, with reverse canonical-smooth packaged
  payloads now lifted through the target, criterion, project-payload, canonical
  payload, canonical target, canonical criterion, canonical statement, and
  checked-certificate surfaces at both dependency-package layers. It also exposes
  standalone `SmoothabilityPackage` routes from a proof-bearing smooth,
  canonical-smooth, or reverse canonical-smooth
  Poincare statement to the project target, canonical completion payload, and
  canonical topological statement. Those standalone route payloads now have
  reconstruction contracts from their named project and canonical completion
  payload endpoints. Direct equality contracts now pin the
  aggregate packaged smooth, packaged canonical-smooth, and packaged reverse
  canonical-smooth project routes,
  canonical payloads, canonical targets, canonical criteria, and canonical
  statement projections to the corresponding remaining-dependency routes after
  `remainingDependencyPackage_iff_poincareProofDependencies`; the same
  aggregate-to-remaining pinning now covers the packaged smooth and packaged
  canonical-smooth completion certificate constructors, payload proposition
  equivalences, certificate iff factorizations, plus the packaged reverse
  canonical-smooth canonical routes, checked-certificate constructors, and
  certificate-payload equivalences. The packaged smooth, packaged
  canonical-smooth, and packaged reverse canonical-smooth payload constructors
  now also reconstruct their route completion certificates from the assembled
  route payload endpoints. The packaged smooth, packaged
  canonical-smooth, and packaged reverse canonical-smooth certificate
  equivalences are also pinned directly to
  their named projection/constructor pairs, and their aggregate/remaining
  payload equivalences are pinned to the componentwise dependency conversion.
  The dependency-packaged
  smooth payload routes are also pinned back to the standalone
  `SmoothabilityPackage` payload routes, including the reverse canonical-smooth
  standalone route, obtained by projecting the package's
  smoothability component, including their project target, criterion, and
  project completion-payload, canonical payload, canonical target, canonical
  criterion, canonical statement projections, and checked completion-certificate
  constructors. The packaged reverse canonical-smooth certificate constructors
  also have projection round-trips for their dependency package, project target,
  project payload, canonical payload, canonical target, completion criterion, and
  canonical topological statement. The non-packaged smooth, canonical-smooth,
  and reverse canonical-smooth completion certificate constructors now expose
  the same dependency, canonical statement, canonical target, criterion,
  project-payload, canonical-payload, and target-statement projection round-trips
  at both dependency-package surfaces. Those non-packaged smooth routes now have
  explicit certificate payload
  projections, payload constructors, iff contracts, projection-after-constructor
  round-trips, constructor reconstruction contracts, and an aggregate/remaining
  payload equivalence.
  The certificate layer also exposes a literal reserved-name payload that
  records the canonical statement alongside the remaining dependency package,
  canonical target, and completion criterion, plus the same payload shape with
  the aggregate dependency package named directly.
- `Poincare/RicciFlowInterface.lean` exposes the finite-extinction and
  topological-extraction interface where future Ricci-flow formalization should
  plug in. It now also exposes
  `extinction_extraction_of_poincare_statement` and
  `poincare_statement_iff_extinction_extraction`, recording that the target
  statement supplies the post-extinction extraction interface and, once
  universal finite extinction is available, is equivalent to that interface.
  It also exposes
  `poincare_payload_of_extinction_and_extraction`, carrying the local target and
  explicit completion criterion from those two theorem-shaped inputs. The
  canonical endpoint route
  `canonical_three_sphere_statement_of_extinction_and_extraction` and the
  equivalence `canonical_three_sphere_statement_iff_extinction_extraction`
  expose the same boundary at the mathlib-shaped topological statement. Those
  target assembly, reverse extraction, payload, canonical endpoint, and
  endpoint equivalence routes now have equality contracts.
  pinning them to their named projection/constructor pairs.
  The base canonical target/payload layer and the generic dependency
  projection certificates now also expose named canonical criterion projections
  alongside the older completion-criterion projections.
  The remaining-dependency certificate wrappers now expose the same canonical
  criterion projections for direct criterion certificates and for component,
  package-layer, and milestone requirement routes.
  The aggregate proof-dependency certificate wrappers and their
  aggregate-to-remaining criterion routes now expose the matching canonical
  criterion projections.
- `Poincare/RicciFlow.lean` defines a minimal typed API for time-dependent
  Riemannian metrics, candidate Ricci tensor fields, Ricci-identification
  evidence, and the Ricci-flow equation interface. It also exposes checked
  projections down to metric data, curvature data, metric time slices, Ricci
  tensor fields, scalar curvature fields, Ricci tensor time slices, scalar
  curvature time slices, Ricci-identification evidence, and Ricci-flow equation
  evidence, with rewriteable definitional-equality contracts identifying those
  named projections and evidence theorems with the stored structure fields. The
  explicit Ricci-flow equation verification now exposes its stored tensor
  equality directly at each scalar point `x v w`, plus a reusable pointwise
  equation payload, before any projection-routed wrapper is applied. The
  stationary metric-family constructor now packages a single Riemannian metric
  as a time-independent family, proves its time-slice projection, and specializes
  the zero-derivative/zero-Ricci equation-verification payload to that
  stationary route; zero Ricci-flow data also exposes checked metric, Ricci, and
  scalar-curvature time-slice projection contracts, flow-data-level zero RHS
  contracts, supplied Ricci/equation evidence contracts, plus pointwise scalar
  zero contracts for the base zero tensor, zero Ricci tensor field, zero metric
  derivative field, zero metric-derivative data, zero-curvature Ricci
  tensor/scalar data, zero-flow Ricci tensor data, and the zero-curvature
  Ricci-flow right-hand side at
  `x v w`; the zero equation verification also has a pointwise equation route
  at `x v w` and a named payload bundling both scalar-zero sides with the
  equation-at-time proof. The stationary zero-flow route now mirrors those Ricci,
  scalar, RHS, and bundled pointwise-zero facts after specializing the metric
  family. The analytic equation boundary now has the matching stationary zero
  boundary package, statement
  route, analytic-foundation package route, strengthened equation-boundary
  statement route, and generic plus zero/stationary-zero projection-routed
  pointwise equation theorems at `x v w`; equation-boundary packages,
  strengthened surgery packages, dependency projections, strengthened
  remaining/aggregate dependency packages, and boundary-aware completion
  certificates also now expose direct stored-verification pointwise equation
  payloads before the projection wrapper, and the verification-payload plus
  remaining/aggregate routes now factor those direct payloads through the
  scalar-pointwise surgery payload. The scalar-pointwise surgery payload itself
  is now reconstructible from the direct stored-verification payload at the
  package, dependency, verification-payload, remaining/aggregate, and
  boundary-aware certificate layers, and the tensor-level derivative surgery
  payload is now reconstructed from that same direct payload across those
  surfaces. The older equation-boundary pointwise-equation and
  equation/metric-derivative payload families now also route directly through
  the stored scalar equation across dependency, verification-payload,
  remaining/aggregate, and boundary-aware certificate surfaces. The
  strengthened dependency finite-extinction theorem now also has
  scalar-pointwise and direct stored-equation projection routes, matching the
  remaining/aggregate finite-extinction routes. The boundary surgery payload,
  analytic-boundary statement, and finite-extinction projections are now routed
  through the direct payload where those projection surfaces exist; the
  zero/stationary-zero boundary
  packages also expose pointwise scalar-zero derivative sides and paired
  derivative/RHS zero witnesses, plus named payloads bundling each boundary
  package with the uniform paired-zero witness for all `t x v w`.
- `Poincare/AnalyticFoundation.lean` narrows the Ricci-flow analytic foundation
  into no-constructor interfaces for Levi-Civita connection theory,
  Levi-Civita existence/uniqueness/torsion-free/metric-compatibility
  sub-obligations, Riemann-curvature construction, tensor symmetries, the first
  and second Bianchi identities, Ricci/scalar contraction formulas, Ricci
  contraction, time-dependent metric regularity, metric time derivatives,
  scalar curvature, equation derivation, short-time existence, continuation
  criteria, parabolic regularity, uniqueness, and curvature evolution
  equations. The PDE layer is further split into initial-metric compatibility,
  DeTurck gauge fixing, background-metric compatibility, vector-field
  construction, Ricci-DeTurck equation derivation and linearization, strict
  parabolicity, linear parabolic theory, nonlinear fixed-point arguments,
  DeTurck short-time existence, short-time regularity bootstrap, DeTurck
  diffeomorphism ODE, pullback equation identity, pullback to Ricci flow,
  maximal-time intervals, curvature blow-up continuation, bounded-curvature
  extension, parabolic Schauder estimates, Shi derivative estimates, curvature
  derivative bootstrap, Hamilton maximum principle, metric/Ricci/scalar
  curvature evolution equations, and curvature-norm evolution inequalities,
  with a checked package that projects back to `RicciFlowData`,
  Ricci-identification evidence, equation evidence, a theorem-shaped
  analytic foundation statement assembled from the fixed-flow derivation
  components, `AnalyticFoundationSubobligationsPayload`, and
  `analytic_foundation_payload_of_analytic_foundation_package`, which
  centralizes the theorem-shaped statement, fixed derivation statement, named
  sub-obligation payload, and equation evidence at the package layer. Its main
  component assembler is pinned to the exact tuple of connection, curvature,
  DeTurck, continuation, regularity, evolution, Ricci-identification, and
  equation witnesses; the derivation-statement sub-obligation bridge is pinned
  to the exact connection, curvature, DeTurck, continuation, regularity, and
  evolution witness stack; the direct package-field projections, package-level
  equation, DeTurck-equation, derivation-statement, statement, and payload routes,
  plus the statement-level flow/Ricci/equation bridges, now also have equality
  contracts pinning them to their stored package fields, component assemblers,
  and destructuring routes.
- `Poincare/Surgery.lean` defines typed no-constructor interfaces for Ricci flow
  with surgery, Perelman singularity control, finite-extinction derivation, and
  the package that connects them to the finite-extinction assembly layer through
  the analytic foundation package. The direct package projections now include
  equality contracts back to the stored analytic foundation, stored flow,
  construction package, Perelman package, finite-extinction witness, and
  analytic equation evidence, and the surgery-level analytic payload bridge is
  pinned back to the stored analytic-foundation package payload. It also exposes
  checked package projections for the analytic foundation,
  `analytic_foundation_payload_of_surgery_package`, underlying Ricci-flow data,
  Ricci-flow equation evidence, surgery scale
  functions, scale continuity/separation,
  cutoff-parameter control, smooth cutoff bump functions, parameter selection,
  strong delta-neck detection, neck separation, neck parametrization, canonical
  neck coordinates, neck decomposition, standard cap models, cap-gluing
  smoothness, cap metric interpolation, cap curvature estimates, cap
  construction, post-surgery curvature pinching, post-surgery noncollapsing
  control, post-surgery derivative bounds, post-surgery canonical-neighborhood
  persistence, post-surgery metric control, surgery-time discreteness/local
  finiteness, long-time existence iteration, long-time parameter coherence,
  long-time nonaccumulation, long-time surgery continuation, theorem-shaped
  surgery-construction statements, statement-mediated surgery-construction
  sub-obligation payload/projection, surgery evidence,
  theorem-shaped Perelman singularity-control statements,
  Perelman F/W-functional setup, entropy normalization, entropy-minimizer
  existence, log-Sobolev control, conjugate heat equation theory, adjoint heat
  kernels, conjugate heat-kernel estimates, entropy gradient, first variation,
  monotonicity, entropy lower-bound propagation, entropy-functional setup,
  reduced-length first variation, reduced-distance existence, differential
  inequality, estimates, cut-locus/barrier control, reduced-Jacobian comparison,
  and theory, reduced-volume definition, derivative formula, rigidity, positive
  lower bounds, limit rigidity, and nonincreasing evidence,
  reduced-volume-to-kappa input, no-local-collapsing contradiction setup,
  collapsed-ball blow-up,
  volume-ratio contradiction, no-local-collapsing volume lower bounds,
  quantified kappa-noncollapsing, Hamilton compactness, ancient kappa-solution
  limit extraction, pointed rescaling, curvature normalization, structure
  theory, nonnegative curvature-operator control, asymptotic soliton analysis,
  compactness, canonical-neighborhood scale control, model stability,
  cross-scale persistence, neck/cap dichotomy, classification,
  no-local-collapsing, reduced-volume, canonical-neighborhood,
  singularity-model classification, singularity-model blow-up classification,
  singularity-control evidence,
  finite-extinction fundamental-group input, sweepout existence, sweepout
  parameter spaces, sweepout continuity, sweepout area bounds, sweepout
  nontriviality, area-functional setup, min-max width definition, width
  compactness, width lower semicontinuity, minimizing sequences, pull-tight
  arguments, min-max stationarity, min-surface regularity, positive width,
  width theory, first and second variation, Gauss-Bonnet estimates,
  scalar-curvature width bounds, width evolution, width differential
  inequality, surgery metric comparison, surgery width-comparison maps, surgery
  width drop, surgery/discard control, discarded-component width neutrality,
  discarded-component sweepout triviality and classification, surviving
  component tracking, component topology, curvature pinching,
  scalar-curvature lower bounds, positive scalar-curvature persistence,
  component control, volume evolution, surgery volume nonincrease,
  scalar-curvature and volume differential inequalities, volume-decay
  estimates, time-bound evidence, differential-inequality integration,
  finite-time integration, surgery-time summability, extinction-time
  contradiction,
  finite-extinction derivation, finite-extinction conclusion, the
  conclusion-derivation certificate, the fixed-flow finite-extinction
  conclusion statement, theorem-shaped finite-extinction width and full
  sub-obligation statements whose bridges destructure them into explicit
  witness stacks, and the theorem-shaped finite-extinction statement.
  The statement-mediated surgery and Perelman sub-obligation stacks are now
  named as `RicciFlowWithSurgeryConstructionSubobligationsPayload`,
  `PerelmanSingularityControlSubobligationsPayload`, and
  `PerelmanMonotonicityBlowupSubobligationsPayload`.
  Package-to-payload bridges
  `surgery_construction_payload_of_construction_package` and
  `perelman_control_payload_of_package` centralize the package, theorem-shaped
  statement, named sub-obligation payload, and aggregate witness routes; direct
  equality contracts pin the surgery-construction component assembler to the
  exact tuple of construction witnesses, the surgery construction package's
  theorem-shaped statement route to that component assembly route, and its
  bundled payload to the named statement, sub-obligation payload, and aggregate
  witness extraction; the Perelman component assembler is pinned to the exact
  tuple of entropy, conjugate-heat, reduced-distance, reduced-volume,
  noncollapsing, kappa-solution, canonical-neighborhood, singularity-model, and
  aggregate control witnesses, and the Perelman package statement and bundled
  statement/sub-obligation/monotonicity payload are now pinned the same way.
  Statement-destructuring equality contracts now pin the surgery aggregate and
  sub-obligation bridges, and the Perelman aggregate, full sub-obligation, and
  monotonicity/blow-up bridges, to the exact witness stacks they destructure.
  The dependency-level `surgery_package_payload_of_dependencies` now
  centralizes the raw aggregate surgery package together with its analytic
  foundation, projected flow, construction package, and Perelman control
  package. Its payload carries equality contracts for the analytic package and
  flow plus heterogeneous equality contracts tying the construction and
  Perelman-control packages to the corresponding projections from the same
  finite-extinction surgery package, so the analytic, surgery-construction,
  Perelman, and finite-extinction dependency payloads open
  `dependencies.surgery` through one named bridge; an equality contract pins
  that shared bridge to the stored surgery family. The dependency-level
  analytic-foundation package projection is now pinned to mapping that stored
  surgery family to each analytic subpackage. The strengthened dependency
  surface also projects the selected boundary-carrying surgery package's
  pointwise equation route at `t x v w`. The package-routed payloads
  `analytic_foundation_statement_payload_with_surgery_package_of_dependencies`,
  `surgery_construction_statement_payload_with_surgery_package_of_dependencies`,
  `perelman_control_statement_payload_with_surgery_package_of_dependencies`,
  `finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies`,
  and `finite_extinction_statement_payload_with_surgery_package_of_dependencies`
  additionally keep the selected surgery package in the payload; equality
  contracts now pin the analytic, construction, and Perelman payload routes and
  their simplified dependency payloads back to the shared surgery package, while
  the finite-extinction routes pin statement, derivation, and extinction fields
  back to that package. Strengthened equation-boundary surgery packages now
  also lift the projection-routed Ricci-flow equation from their stored
  boundary package pointwise at `x v w`, bundle that scalar equation in
  `SurgeryPackageWithEquationBoundaryPointwiseEquationPayload`, and reconstruct
  the tensor-level derivative payload by extensionality. Dependency, remaining,
  aggregate, verification-payload, and boundary-aware certificate routes now
  expose that package-level pointwise payload directly, with direct
  verification-payload, projected-dependency, boundary-certificate, arbitrary
  constructor, existential-constructor, and named-constructor roundtrip
  contracts. The pointwise surgery payload also forgets back to the older
  boundary surgery-package payload, and dependency, remaining-package,
  aggregate, and certificate payload routes pin that projection. It also
  exposes the carried analytic equation-boundary statement directly, and the
  dependency, remaining-package, aggregate, and boundary-aware certificate
  analytic statement routes now pin their projections through the pointwise
  surgery payload. Arbitrary equation-boundary verification payloads now also
  route both their boundary surgery-package payload and analytic statement
  projections through that reconstructed pointwise surgery payload. The same
  pointwise payload now exposes finite extinction directly, with named
  strengthened surgery-package and arbitrary verification-payload extinction
  projections routed through it. The strengthened dependency package now also
  supplies finite extinction through its named verification payload after
  installing the smoothability bridge, and that route is pinned to the
  forgetful ordinary-dependency finite-extinction theorem. The dependency
  projection layer now pairs that boundary finite-extinction route with the
  forgetful topology-extraction theorem and certified extractor/derivation
  payload, with equality contracts back to the ordinary projection assembly
  inputs. It now also assembles those boundary projection inputs into raw and
  certified target payloads with equality contracts back to the ordinary
  dependency projection target payloads, then exposes matching completion
  payloads and Poincare statements for the boundary projection routes. The same
  boundary projection endpoints now expose canonical topological 3-sphere
  statements and universe-indexed completion criteria, with equality contracts
  back to the topology-statement and forgetful ordinary projection routes. The
  completion-target layer now also lifts those raw and certified boundary
  projection completion payloads into canonical payload, target, and
  universe-indexed criterion endpoints, pinned back to the same
  topology-statement, extractor/derivation, and forgetful ordinary projection
  routes. Those canonical boundary projection payloads now also reconstruct
  checked completion certificates directly, with certificate equality contracts
  back to the finite-extinction/topology-statement route, the
  extractor/derivation route, and the forgetful ordinary projection certificate
  routes. Their certificate projections now recover the forgetful aggregate and
  remaining packages, project payloads, target statements, canonical payloads,
  canonical targets, and universe-indexed criteria for both the raw and
  certified boundary projection routes. The same certificate constructors are
  now also pinned to the strengthened aggregate certificate, the boundary-target
  payload certificate, and the ordinary aggregate projection certificate.
  The strengthened boundary, boundary-target-payload, and boundary-preserving
  extraction-derivation target-payload certificates now also expose both
  ordinary remaining-package and aggregate endpoints for their canonical
  topological statements, canonical-statement payloads, aggregate
  canonical-statement payloads, and explicit canonical-statement payload
  reconstruction routes. The same three certificate families now also
  reconstruct ordinary remaining-package and aggregate certificates directly
  from their projected canonical-statement and aggregate canonical-statement
  payloads. The base strengthened remaining-package full-assembly payload and
  certified full-assembly payload now also have ordinary aggregate endpoints,
  and the matching certificate projections recover those endpoints directly.
  The boundary-target-payload and boundary-preserving extraction-derivation
  target-payload certificates now also project raw and certified full-assembly
  payloads to both ordinary aggregate and remaining-package endpoints.
  Their noncanonical theorem-name and literal payload projections,
  plus literal-payload reconstructions, now also expose the ordinary aggregate
  endpoints for the strengthened remaining-package routes. The completion-target
  canonical payload, project payload, target, canonical-target, and
  completion-criterion projections now have the same ordinary aggregate
  endpoints for those strengthened remaining-package routes. The raw and
  certified component-slot, package-layer, and milestone requirement-payload
  constructors now also recover those strengthened remaining-package boundary
  target certificates from the ordinary aggregate payloads after forgetting
  equation-boundary data.
  Separately, the completion-target
  wrapper layer now mirrors that
  finite-extinction route through the ordinary
  remaining package, strengthened remaining package, and strengthened aggregate
  package, with equality contracts to the verification-payload, pointwise
  surgery-payload, and forgetful ordinary-dependency routes. Boundary-aware
  verification certificates also recover the boundary surgery package payload
  through arbitrary remaining-package, arbitrary aggregate, existential
  verification-payload, named remaining-package, and named aggregate
  constructors. The public root, semantic, and axiom audits now also check the
  direct-verification-payload and projected-strengthened-dependency routes for
  the certificate-level equation-boundary projection family.
  The dependency-level surgery-construction route now exposes
  `surgery_construction_statement_payload_of_dependencies`, which packages the
  construction package, theorem-shaped construction statement, construction
  sub-obligation payload, and aggregate Ricci-flow-with-surgery witness by
  destructuring the shared dependency surgery package payload and then the
  package-level construction payload bridge; the construction-package
  projection itself is pinned to the same shared payload.
  Equality contracts for the construction package projection spine now tie the
  surgery scales, cutoff controls, neck data, cap data, post-surgery estimates,
  surgery-time controls, long-time continuation data, and aggregate
  Ricci-flow-with-surgery projection directly to the stored construction
  package fields.
  Equality contracts for the surgery package construction route now tie its
  construction statement, aggregate surgery witness, scale/cutoff controls,
  neck and cap data, post-surgery estimates, surgery-time controls, and
  long-time continuation projections directly to the stored construction
  package fields.
  Equality contracts for the surgery package Perelman route now tie its
  Perelman statement, entropy and conjugate-heat controls,
  reduced-distance/reduced-volume data, noncollapsing and kappa-solution
  controls, canonical-neighborhood data, and aggregate singularity-control
  projection directly to the stored Perelman package fields.
  Equality contracts for the surgery package finite-extinction route now tie
  its sweepout, width, surgery-discard, curvature, scalar/volume/time-bound,
  derivation, and conclusion-derivation projections directly to the stored
  finite-extinction fields.
  Equality contracts for the Perelman package projection spine now tie the
  entropy and conjugate-heat controls, reduced-distance/reduced-volume data,
  noncollapsing and kappa-solution controls, canonical-neighborhood data, and
  aggregate singularity-control projection directly to the stored Perelman
  package fields.
  Dependency-level component equality contracts now tie the aggregate
  smoothability package, surgery-package family, and topology extraction
  projections directly to the stored `PoincareProofDependencies` fields.
  The dependency-level Perelman route now exposes
  `perelman_control_statement_payload_of_dependencies`, which packages the
  theorem-shaped Perelman statement, full Perelman sub-obligation payload,
  monotonicity/blow-up sub-obligation payload, and aggregate control witness; the
  Perelman control and sub-obligation projections destructure that payload
  instead of projecting the raw Perelman package directly.
  The full finite-extinction sub-obligation route now reassembles the
  fixed-flow conclusion statement and theorem-shaped finite-extinction
  statement through
  `finite_extinction_conclusion_statement_of_subobligations_statement` and
  `finite_extinction_statement_of_subobligations_statement`; the
  theorem-shaped statement exposes its conclusion payload through
  `finite_extinction_conclusion_statement_of_finite_extinction_statement`.
  Package-level finite-extinction payloads
  `finite_extinction_subobligations_payload_of_surgery_package` and
  `finite_extinction_statement_payload_of_surgery_package` now centralize the
  width/full sub-obligation statement payloads and the rebuilt
  finite-extinction statement/derivation/extinction route.
  The finite-extinction conclusion component assembler is pinned to the exact
  tuple of finite-fundamental-group, sweepout, width, surgery-discard,
  curvature, time-bound, derivation, and conclusion-derivation witnesses.
  Equality contracts now pin the package-level finite-extinction conclusion
  statement, theorem-shaped statement, statement-mediated extinction witness,
  width/full sub-obligation statements, and both package-level payload routes to
  those explicit component and statement-mediated assemblies.
  The statement-level finite-extinction bridges are pinned as well: conclusion
  payload extraction from a theorem-shaped statement, finite-extinction witness
  extraction, derivation extraction from a full sub-obligation statement, and
  the rebuilt conclusion/statement/extinction routes all have equality
  contracts.
  The width and full finite-extinction sub-obligation statement destructuring
  bridges now also have equality contracts pinning them to the exposed stored
  components.
  The dependency-level finite-extinction route now exposes
  `finite_extinction_subobligations_statement_payload_of_dependencies`,
  which packages the width sub-obligation statement, full sub-obligation
  statement, their statement-mediated width/full sub-obligation payloads, and
  direct finite-extinction statement by destructuring the package-level
  payload, plus
  `finite_extinction_statement_payload_of_dependencies`, which packages the
  direct statement, the full sub-obligation statement, the rebuilt statement,
  the derivation certificate, and the extinction witness by destructuring the
  package-level statement payload; equality contracts pin both the
  surgery-package-enriched and simplified dependency payloads for the
  sub-obligation and final statement routes to those named destructuring
  routes; the width/full
  statement projections,
  derivation stack, full sub-obligation projection, statement projections,
  and final finite-extinction theorem destructure those payloads. The
  dependency-level finite-extinction width/full statement, width/full
  sub-obligation, derivation-stack, and statement-route projections now have
  equality contracts back to fields selected from those two payloads.
- `Poincare/TopologyExtraction.lean` defines typed no-constructor interfaces for
  the post-extinction decomposition, surgery-trace reconstruction, component
  classification and inventory, surgery-trace handle cancellation, discarded
  component homeomorphism classification, component boundary-sphere control,
  3-sphere recognition, prime decomposition and existence, sphere-theorem input,
  embedded-sphere production, loop-theorem input, prime-decomposition
  compatibility and factor uniqueness, irreducibility and irreducible-factor
  recognition, connected-sum collapse, fundamental-group control, van Kampen
  calculation, simply connected prime-factor control, spherical-space-form
  reduction and classification, spherical quotient models, free spherical
  actions, spherical universal-cover, covering-model, and covering-projection
  inputs, spherical-space-form fundamental-group computation, deck-group
  identification, deck-action properness, deck-group triviality, deck-action
  trivialization, trivial deck-quotient identification, simply connected
  recognition, trivial spherical quotients, trivial-quotient homeomorphism,
  spherical homeomorphism lift, homeomorphism assembly, the fixed-manifold
  topology derivation statement, derivation-statement bridges exposing the full
  post-extinction classification stack through
  `ExtinctionTopologyClassificationSubobligationsPayload` and the homeomorphism
  assembly/derivation statements, and the theorem-shaped topology extraction
  statement. Equality contracts also pin the dependency-level
  classification sub-obligations, derivation statement, homeomorphism
  assembly/derivation statements, concrete assembly/derivation certificates,
  and statement aliases back to that theorem-shaped extraction route and to the
  stored topology package derivation route. The
  package-to-extraction bridge now assembles the fixed derivation statement from
  the named components, with direct equality contracts for the package-built
  extraction statement's homeomorphism and two-field derivation payload; the
  fixed-extinction payload and homeomorphism are
  extracted through
  `topology_derivation_statement_payload_of_extraction_statement`,
  `homeomorphism_of_topology_extraction_statement`, and
  `topology_derivation_statement_of_extraction_statement`, with direct
  extraction-statement projections also exposing the classification payload and
  homeomorphism assembly/derivation statements, and
  `topology_extraction_statement_payload_of_extraction_statement`, a
  fixed-extinction payload route assembled from those named projections.
  Package-level topology
  payloads `topology_extraction_payload_of_topology_package` and
  `topology_extraction_statement_payload_of_topology_package` centralize the
  theorem-shaped extraction interface, fixed derivation statement,
  classification payload, and homeomorphism assembly/derivation statement
  route, with the package fixed-extinction payload pinned to the statement
  route by
  `topology_extraction_statement_payload_of_topology_package_to_extraction_statement_payload_eq`.
  `topology_extraction_derivation_payload_of_topology_package` certifies
  that same package-level extraction statement as a final extractor paired with
  topology derivation evidence for the homeomorphism it returns. Equality
  contracts now tie the topology-package projection spine back to stored
  fields, covering surgery-trace reconstruction and handle cancellation,
  component classification/inventory/boundary control, recognition,
  prime-decomposition existence and sphere/loop-theorem inputs, embedded-sphere
  production, prime compatibility and uniqueness, irreducible-factor
  recognition, connected-sum group control and van Kampen calculation, simply
  connected prime-factor control, spherical classification/quotient/covering
  data, deck properness/trivialization, trivial deck-quotient identification,
  simply connected recognition, final package homeomorphism,
  trivial-quotient homeomorphism, homeomorphism-lift, assembly/derivation,
  extraction payloads, and final extractor; theorem-shaped package-statement
  routes remain explicit where the projection is not just a stored field. The
  fixed-manifold topology derivation component assembler is now pinned to the
  exact tuple of post-extinction topology components; the package-level
  topology derivation statement route is also pinned directly to that component
  assembly route applied to the package projections. The full classification
  sub-obligation bridge plus the narrower homeomorphism assembly/derivation
  statement bridges are pinned to their destructuring routes from the full
  derivation statement. The topology layer also imports mathlib's one-point
  compactification sphere theorem and proves the finite-rank equation for
  `EuclideanSpace ℝ (Fin 3)`, a homeomorphism
  `OnePoint (EuclideanSpace ℝ (Fin 3)) ≃ₜ ThreeSphere`, its reverse route, and
  both directions of the recognition equivalence between the compactification
  model and the project target sphere. It also transports Hausdorff, compact,
  path-connected, locally path-connected, connected, and nonempty prerequisites
  to the compactification model through that homeomorphism, pushes forward a
  `ChartedSpace (EuclideanSpace ℝ (Fin 3))` structure from `ThreeSphere`, derives
  a `C^0` 3-manifold witness for those charts, and bundles the result as
  `onePoint_threeSpace_topological_prerequisites` and
  `onePoint_threeSpace_topological_manifold_prerequisites`. It also transports
  simple-connectedness in both directions between `ThreeSphere` and the
  compactification model, records
  `onePoint_threeSpace_simplyConnectedSpace_iff_threeSphere`, and packages the
  compactification model's own concrete loop-nullhomotopy obligation as
  `OnePointThreeSpaceLoopNullhomotopyStatement`, with equivalences to both
  compactification simple-connectedness and `ThreeSphereLoopNullhomotopyStatement`.
  It also names the compactification model's concrete path-homotopy uniqueness
  obligation as `OnePointThreeSpacePathHomotopyStatement`, proves its
  equivalence with compactification simple-connectedness and
  `ThreeSpherePathHomotopyStatement`, and pins the compactification path/loop
  conversions to the named loop-nullhomotopy route. It packages the
  compactification model's full homotopy/manifold prerequisites as
  `onePoint_threeSpace_homotopy_manifold_prerequisites` when the standard
  sphere's simple-connectedness input is supplied, with
  `onePoint_threeSpace_homotopy_manifold_prerequisites_of_loopNullhomotopyStatement`
  removing that raw input in favor of the concrete loop-nullhomotopy obligation.
  The parallel
  `onePoint_threeSpace_homotopy_manifold_prerequisites_of_pathHomotopyStatement`
  route is pinned to the loop route by a direct compatibility contract. It also
  adds direct compactification-side payload routes
  `onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointLoopNullhomotopyStatement`
  and
  `onePoint_threeSpace_homotopy_manifold_prerequisites_of_onePointPathHomotopyStatement`,
  with compatibility contracts back to the standard-sphere loop/path routes.
  The same layer now
  transports the `C^0` prerequisite payload to any source space already
  recognized as homeomorphic to the compactification model, transports
  simple-connectedness to that source with
  `simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace`, and packages the
  resulting full source homotopy/manifold prerequisites as
  `homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace` under
  the standard-sphere simple-connectedness input; the loop-nullhomotopy variant
  `homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_loopNullhomotopyStatement`
  uses the concrete homotopy obligation instead, and the path-homotopy source
  route is tied back to that loop route. It also adds local compactification
  source routes
  `simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement`,
  `simplyConnectedSpace_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement`,
  `homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement`,
  and
  `homotopy_manifold_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement`,
  tying the standard-sphere loop/path routes back to compactification-local
  loop/path obligations. It also packages the
  transported payload with an already supplied source `SimplyConnectedSpace` instance as
  `poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace`, and
  exposes local loop/path candidate routes
  `poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointLoopNullhomotopyStatement`
  and
  `poincare_candidate_prerequisites_of_homeomorph_to_onePoint_threeSpace_of_onePointPathHomotopyStatement`.
  For the compactification model itself,
  `onePoint_threeSpace_self_homeomorph` records the reflexive recognition
  endpoint, `onePoint_threeSpace_self_homeomorph_payload` pairs it with the
  named compactification `C^0` manifold prerequisite payload, and the self
  loop/path routes
  `poincare_candidate_prerequisites_of_onePoint_threeSpace_self_loopNullhomotopyStatement`
  and
  `poincare_candidate_prerequisites_of_onePoint_threeSpace_self_pathHomotopyStatement`
  package the model as a local Poincare candidate from compactification-local
  homotopy obligations.
  Universal compactification recognition now has an explicit model self-case:
  `onePoint_threeSpace_self_homeomorph_of_onePointThreeSpaceRecognitionStatement`
  applies `OnePointThreeSpaceRecognitionStatement` to the compactification
  model itself, and
  `onePoint_threeSpace_homeomorph_threeSphere_of_onePointThreeSpaceRecognitionStatement`
  composes that endpoint to the target sphere with direct-route contracts.  The
  loop/path variants replace the raw compactification `SimplyConnectedSpace`
  input with `OnePointThreeSpaceLoopNullhomotopyStatement` and
  `OnePointThreeSpacePathHomotopyStatement`, with path routes pinned back to
  the loop-mediated routes, and the loop/path recognition payloads pair those
  endpoints with the corresponding compactification-local homotopy/manifold
  prerequisite packages.
  The same self-case now applies a supplied `PoincareConjectureStatement` to
  the compactification model through
  `onePoint_threeSpace_homeomorph_threeSphere_of_poincare_statement`, replaces
  the simple-connectedness input with compactification-local loop/path
  obligations through the corresponding `...onePointLoopNullhomotopyStatement`
  and `...onePointPathHomotopyStatement` routes, and packages the target
  endpoint with the local homotopy/manifold prerequisite payloads.  Direct-route
  contracts pin those target-statement endpoints back to the explicit
  `onePoint_threeSpace_homeomorph_threeSphere` model homeomorphism.
  The pointwise finite-extinction compactification-recognition route
  `onePoint_threeSpace_self_homeomorph_of_extinctionOnePointThreeSpaceRecognitionStatement`
  now recovers the compactification self endpoint from a model-level extinction
  witness, and
  `onePoint_threeSpace_homeomorph_threeSphere_of_extinctionOnePointThreeSpaceRecognitionStatement`
  composes that endpoint to the target sphere, again pinned to the direct model
  homeomorphisms.  Its loop/path variants replace the raw compactification
  `SimplyConnectedSpace` input with
  `OnePointThreeSpaceLoopNullhomotopyStatement` and
  `OnePointThreeSpacePathHomotopyStatement`, with the path extinction route
  pinned back through the loop-mediated route, and the loop/path extinction
  payloads pair those endpoints with the corresponding compactification-local
  homotopy/manifold prerequisite packages.
  It
  names universal compactification recognition as
  `OnePointThreeSpaceRecognitionStatement`, and
  records
  `poincareConjectureStatement_of_onePoint_threeSpace_recognition`, the
  reduction from universal compactification recognition to the project target
  statement, plus `poincare_payload_of_onePoint_threeSpace_recognition`, the
  corresponding completion payload. The converse route
  `onePointThreeSpaceRecognitionStatement_of_poincareConjectureStatement` now
  closes this as the equivalence
  `poincareConjectureStatement_iff_onePointThreeSpaceRecognitionStatement`. It
  also records the finite-extinction extractor route
  `extinction_implies_sphere_of_onePoint_threeSpace_recognition`, names that
  compactification-recognition subgoal as
  `ExtinctionOnePointThreeSpaceRecognitionStatement`, and provides the target
  and payload assembly from finite extinction plus that named recognition
  statement. The reverse route
  `extinctionOnePointThreeSpaceRecognitionStatement_of_extinctionImpliesSphereStatement`
  closes the post-extinction extractor equivalence
  `extinctionImpliesSphereStatement_iff_extinctionOnePointThreeSpaceRecognitionStatement`,
  with equality contracts and audit coverage for those routes. The
  concrete homeomorphism glue for the standard sphere's self-homeomorphism,
  intermediate-space composition, opposite-direction source transport, and both
  inverse-direction recognition maps now also has direct equality contracts.
  The assembly layer separately pins the standard sphere's smooth reflexivity
  witness and the induced self-homeomorphism route through
  `homeomorph_of_diffeomorph_three_sphere`; the topology layer now also records
  that its reflexive self-homeomorphism witness agrees with that smooth route,
  and both layers expose matching prerequisite-plus-endpoint payloads for the
  standard sphere self-case, with projection lemmas back to the named
  prerequisite and endpoint witnesses.
  The dependency-level classification payload
  `topology_classification_payload_of_dependencies` now centralizes the
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
  topology payload, fixed derivation projection, and homeomorphism
  assembly/derivation statement projections now consume the package-level
  payloads through
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
  named extraction payload routes, and the via-extraction derivation,
  assembly-statement, and derivation-statement projections now have direct
  statement-route contracts back to the dependency theorem-shaped topology
  extraction statement.
  `topology_extraction_statement_payload_of_dependencies_to_extraction_statement_payload_eq`
  now pins the fixed-extinction dependency payload to the dependency
  theorem-shaped topology extraction statement payload route.
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
  The fixed-extinction statement payload now routes through
  `topology_extraction_statement_payload_of_extraction_statement`, and the
  package and dependency equality contracts record that route.
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
  The final `ExtinctionImpliesSphereStatement` bridge also consumes that
  extraction statement rather than bypassing the derivation certificate.
  `ExtinctionTopologyDerivationForExtractionStatement`,
  `extinction_topology_extraction_statement_of_extraction_and_derivation`, and
  `extinction_topology_extraction_statement_iff_extraction_with_derivation`
  identify the strong topology extraction theorem with a final extractor plus
  derivation evidence for the homeomorphism it returns. The
  homeomorphism-recognition and extraction-with-derivation equivalences now
  have equality contracts pinning them to their named directional maps. The
  theorem-shaped package statement, fixed-extinction payload, homeomorphism
  projection, derivation projection, statement-mediated extractor, extractor-plus-derivation
  constructor, projection-after-reconstruction contracts, and package
  fixed-extinction payload are also pinned to their named routes. The
  direct assembly bridges
  `poincare_statement_of_finite_extinction_and_topology_extraction_statement`
  and
  `poincare_payload_of_finite_extinction_and_topology_extraction_statement`
  connect universal finite extinction and the strong topology statement to the
  target/completion payload, with equality contracts back to the existing
  finite-extinction/extraction assembly route. The matching
  extractor-plus-derivation bridges
  `poincare_statement_of_finite_extinction_and_extraction_derivation` and
  `poincare_payload_of_finite_extinction_and_extraction_derivation` expose the
  same target/completion payload without hiding the derivation certificate
  inside the canonical layer, and are pinned to the named
  extractor-plus-derivation topology statement route. It also proves
  the standard self-homeomorphism of
  `ThreeSphere` and composition of a homeomorphism through an intermediate
  recognized space into `ThreeSphere`, the opposite-direction source
  transport, the iff invariance of `ThreeSphere` recognition under replacing
  the source by a homeomorphic space, the reverse homeomorphism from
  `ThreeSphere`, the iff between the two homeomorphism directions, and the
  inverse direction from a homeomorphism out of `ThreeSphere`. It exposes
  checked projections for the
  decomposition, recognition, topology sub-obligations, extracted
  homeomorphism, homeomorphism assembly, derivation-certificate fields, and
  theorem-shaped extraction statement of a completed topology package.
- `Poincare/Smoothability.lean` defines typed no-constructor interfaces for the
  smoothability bridge from the topological 3-manifold statement to the smooth
  model required by the surgery layer, including Moise local charts,
  locally finite cover refinement, simplicial-complex data, compatible chart
  triangulations, simplicial approximation, star-neighborhood bases,
  barycentric subdivision, regular-neighborhood compatibility, local finiteness,
  link compatibility, PL-manifold recognition, triangulation homeomorphism and
  compatibility, Moise triangulation uniqueness, the dimension-three
  Hauptvermutung input, compatible PL structure, PL transition compatibility, PL
  atlas/manifold-atlas/collar-neighborhood/homeomorphism compatibility, PL
  smoothing existence, obstruction vanishing, microbundle smoothing, smoothing
  compatibility, smoothing uniqueness, and local-model compatibility,
  smooth-atlas construction, PL-compatibility, maximality, uniqueness,
  smooth-structure uniqueness, smooth transition compatibility, transition-map
  smoothness, smooth-structure derivation, the assembled smooth-structure
  derivation statement, bridge derivation, smooth-model compatibility, and chart
  compatibility, with checked projections for those sub-obligations, the raw
  smooth-structure input, a component-level derivation-statement assembly
  theorem, `SmoothabilitySubobligationsPayload`, a derivation-statement
  projection of the full smoothability sub-obligation stack, bridge theorem,
  derivation-dependent bridge application, and chained bridge/model/chart
  compatibility evidence. Package-level smoothability payloads
  `smoothability_smooth_structure_statement_payload_of_smoothability_package`
  and `smoothability_bridge_payload_of_smoothability_package` centralize the
  smooth-structure derivation statement route and the bridge/model/chart
  compatibility plus full sub-obligation route. The smooth-structure
  derivation component assembler is pinned to the exact tuple of Moise, PL,
  smoothing, smooth-atlas, transition, and derivation witnesses, the package-level
  derivation statement route is pinned back to that component assembler, and the
  derivation-statement sub-obligation bridge is pinned to the exact
  Moise/PL/smoothing/smooth-atlas/bridge witness stack. Equality contracts now
  tie the package bridge, canonical smooth-manifold statement,
  bridge application, surgery-model and canonical smooth-manifold projections,
  compatibility evidence, and smoothability payloads back to the stored package
  fields or named component route. The lower Moise/PL/smooth spine also records direct
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
- `Poincare/FullAssembly.lean` proves that the smoothability package, completed
  surgery packages, and topology extraction package compose to the target
  `PoincareConjectureStatement`. The explicit finite-extinction input now
  passes through
  `finite_extinction_statement_payload_of_smoothability_and_surgery_packages`
  and `finite_extinction_input_of_smoothability_and_surgery_packages`, which
  carry the smoothability-installed manifold evidence, theorem-shaped
  finite-extinction statement, sub-obligation statement route, derivation
  certificate, and final finite-extinction witness; equality contracts pin both
  the statement payload and the projected finite-extinction input to this route.
  The extinction-to-sphere input is now extracted by destructuring
  `topology_extraction_payload_of_topology_package`, so the full assembly
  layer consumes the package-level topology extraction payload instead of the
  raw final topology projection. Package-route assembly inputs, target payload,
  completion payload, and final statement are also pinned directly to the
  package-built theorem-shaped topology extraction statement. The named
  `poincare_assembly_inputs_payload_of_surgery_and_topology_packages`
  centralizes that final input pair before the target statement is assembled.
  `poincare_target_payload_of_surgery_and_topology_packages` centralizes the
  call to `poincare_payload_of_extinction_and_extraction` and exposes the final
  input pair, target statement, and completion criterion. The end-to-end route
  exposes
  `poincare_full_assembly_payload_of_surgery_and_topology_packages`, which
  carries the explicit smoothability package, surgery-package family, topology
  package, final finite-extinction input, extinction-to-sphere extraction input,
  and target statement by destructuring that target payload.
  `poincare_assembly_payload_of_surgery_and_topology_packages`
  destructures the full payload, while
  `poincare_completion_payload_of_surgery_and_topology_packages` destructures the
  target payload; the final statement theorem destructures the completion
  payload. The canonical endpoint
  `canonical_three_sphere_statement_of_surgery_and_topology_packages` exposes the
  same route as the mathlib-shaped topological 3-sphere statement, with
  `canonical_three_sphere_statement_of_surgery_and_topology_packages_to_extraction_statement_eq`
  pinning it to the theorem-shaped topology route built from the package. The
  theorem-shaped topology route
  `poincare_assembly_inputs_payload_of_surgery_and_topology_extraction_statement`,
  `poincare_target_payload_of_surgery_and_topology_extraction_statement`, and
  `poincare_statement_of_surgery_and_topology_extraction_statement` composes the
  same finite-extinction input directly with
  `ExtinctionTopologyExtractionStatement`; its completion-payload projection is
  `poincare_completion_payload_of_surgery_and_topology_extraction_statement`,
  and its canonical endpoint is
  `canonical_three_sphere_statement_of_surgery_and_topology_extraction_statement`.
  The extractor-plus-derivation route
  `poincare_assembly_inputs_payload_of_surgery_and_extraction_derivation`,
  `poincare_target_payload_of_surgery_and_extraction_derivation`,
  `poincare_completion_payload_of_surgery_and_extraction_derivation`, and
  `poincare_statement_of_surgery_and_extraction_derivation` composes the same
  finite-extinction input with a final extractor and its topology derivation
  certificate; its canonical endpoint is
  `canonical_three_sphere_statement_of_surgery_and_extraction_derivation`.
  The theorem-shaped topology, direct extractor/derivation, explicit package,
  and package-level certified extraction routes now have equality contracts for
  their assembly-input payload, target payload, completion payload, statement,
  and canonical-statement projections, with the explicit package route also
  pinning its full-assembly and assembly-payload projections.
  The package-level certified extraction route
  `poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_target_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  and
  `poincare_statement_of_surgery_and_topology_package_extraction_derivation`
  obtains that extractor-plus-derivation pair directly from the topology
  package before assembling the target; its canonical endpoint is
  `canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation`.
  Direct equality contracts also pin its target, completion, statement, and
  canonical-statement routes to the extractor/derivation routes selected from
  the topology package.
- `Poincare/Dependencies.lean` aggregates those future inputs into one
  `PoincareProofDependencies` package and proves that the package implies the
  target statement and the explicit completion criterion. The aggregate route
  now exposes `poincareProofDependencies_components_payload` and
  `poincareProofDependencies_iff_components`, which identify the package with
  exactly its three components: smoothability, the target-family surgery
  package, and topology extraction; the reverse constructor from that raw
  component payload is now named, the reverse constructor has a direct equality
  contract, and the iff route is pinned to the named forward/reverse maps. It
  also exposes
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
- `Poincare/DependencyProjections.lean` proves named projection lemmas exposing
  the smoothability package, surgery packages, topology package, finite
  extinction, and extinction-extraction theorem supplied by a completed
  dependency package. It also exposes lower-level analytic foundation packages,
  `analytic_foundation_statement_payload_of_dependencies`, which destructures
  the package-routed analytic payload and now carries the projected flow
  directly for its downstream projections,
  statement-mediated analytic foundation outputs, Ricci-flow data, Ricci-flow
  equation evidence, the statement-mediated analytic sub-obligation payload, the
  expanded
  analytic connection/curvature sub-obligation stack, with
  `analytic_foundation_subobligations_of_dependencies` now returning the named
  `AnalyticFoundationSubobligationsPayload` instead of the raw connection/PDE
  conjunction. It also exposes surgery construction packages, package-level
  surgery-construction payloads via
  `surgery_construction_payload_of_construction_package`,
  whose statement route and bundled payload are pinned by direct equality
  contracts,
  `surgery_construction_statement_payload_of_dependencies`,
  statement-mediated surgery construction outputs, surgery construction
  sub-obligations, Perelman control packages, package-level Perelman payloads
  via `perelman_control_payload_of_package`,
  whose statement route and bundled payload are pinned by direct equality
  contracts,
  `perelman_control_statement_payload_of_dependencies`, statement-mediated
  Perelman control outputs, the expanded
  Perelman entropy/reduced-distance/reduced-volume/kappa/canonical-neighborhood
  sub-obligation stack, the Perelman monotonicity/blow-up sub-obligation stack,
  expanded finite-extinction min-max/variation/surgery/volume-decay
  sub-obligations, package-level finite-extinction payloads
  `finite_extinction_subobligations_payload_of_surgery_package` and
  `finite_extinction_statement_payload_of_surgery_package`,
  finite-extinction package route equality contracts,
  finite-extinction statement bridge equality contracts,
  finite-extinction sub-obligation bridge equality contracts,
  `finite_extinction_subobligations_statement_payload_of_dependencies`,
  statement-mediated finite-extinction width/full sub-obligation outputs
  through explicit statement destructuring,
  finite-extinction derivation stack, a finite-extinction conclusion route from
  the full sub-obligation statement, topology
  decomposition, recognition,
  topology-recognition sub-obligations, the expanded post-extinction
  surgery-trace, classification, quotient, deck-action, and homeomorphism-assembly
  sub-obligation stack, the statement-mediated topology classification payload,
  `topology_extraction_payload_of_dependencies`,
  homeomorphism assembly/derivation outputs, extinction-to-homeomorphism
  outputs, homeomorphism derivation certificates, and
  `poincare_projection_assembly_inputs_payload_of_dependencies`, which
  centralizes the final projected finite-extinction and topology-extraction
  input pair before target assembly,
  `poincare_target_payload_of_dependency_projections`, which centralizes the
  projected target statement and completion criterion,
  `poincare_full_assembly_payload_of_dependency_projections`, which packages the
  projected smoothability package, surgery-package family, topology package,
  finite-extinction conclusion, post-extinction extraction theorem, and target
  statement; `poincare_assembly_inputs_payload_of_dependencies` reuses the named
  projection input payload for the final finite-extinction/extraction pair, and
  `poincare_completion_payload_of_dependency_projections` destructures the
  projection target payload for the target/criterion pair. The projection
  canonical endpoints `canonical_three_sphere_statement_of_dependency_projections`
  and
  `canonical_three_sphere_statement_of_extraction_derivation_dependency_projections`
  expose those same routes as the mathlib-shaped topological statement, with
  equality contracts pinning them to the finite-extinction/topology-statement
  and certified extractor/derivation routes. The remaining-dependency canonical
  statement endpoints are also pinned to their named canonical targets, including
  the projection and certified projection target routes. The ordinary
  projection route now also reconstructs a checked completion certificate, with
  round-trip contracts for the remaining-dependency package, canonical payload,
  project payload, target, criterion, canonical topological statement, and
  literal/aggregate canonical-statement payload projections. Its aggregate
  `PoincareProofDependencies` certificate view is also pinned directly to the
  finite-extinction plus theorem-shaped topology-extraction route for the
  certificate, canonical/project payloads, target, criterion, and canonical
  topological statement; the same topology route is pinned for the
  remaining-dependency certificate payload, target, criterion, and canonical
  topological statement. The certified extraction-derivation projection
  certificate is likewise pinned directly to the finite-extinction plus
  extractor/derivation route at both the remaining-dependency and aggregate
  proof-dependency surfaces. Those direct topology and extractor/derivation
  endpoints are now also pinned through the theorem-name payload, literal and
  aggregate canonical-statement payload projections and constructors, plus the
  literal, aggregate-dependency, and project-statement full payload projections
  and constructors, for both projection certificates. The strengthened
  equation-boundary projection certificates now expose the same theorem-name,
  literal, aggregate-dependency, and project-statement payload projections, and
  their literal/aggregate/project payloads reconstruct the corresponding checked
  boundary projection certificates. Their canonical topological statement,
  canonical-statement payload, and aggregate canonical-statement payload
  projections are now also pinned, with payload constructors reconstructing the
  same checked boundary projection certificates. Those canonical-statement
  routes are also pinned back to the matching boundary-target-payload
  certificates and to the ordinary aggregate projection certificates after
  forgetting equation-boundary data. The theorem-name, literal,
  aggregate-dependency, and project-statement payload routes now have the same
  boundary-target and forgetful ordinary projection equalities, including their
  literal/aggregate/project payload certificate reconstructions. The certified
  extraction-derivation canonical-target, project-statement, and
  completion-criterion certificate constructors are also pinned directly to the
  ordinary remaining-dependency and aggregate certificates obtained after
  forgetting the equation-boundary data, and their canonical topological
  statement projections are pinned through the same forgetful routes. Their
  literal and aggregate canonical-statement payload projections now follow those
  same ordinary certificate routes as well, and reconstructing certificates from
  those canonical-statement payloads follows the same ordinary remaining-dependency
  and aggregate routes. The remaining-package aggregate canonical-statement
  payload routes are also pinned directly to the ordinary aggregate certificate
  after equation-boundary data is forgotten, and the remaining-package canonical
  topological statement, literal canonical-statement payload projection, and
  literal canonical-statement payload reconstruction routes now have the same
  direct ordinary aggregate endpoints. The explicit literal/aggregate
  canonical-statement payload constructors now reconstruct the checked
  equation-boundary certificates and the ordinary forgetful certificates
  directly. The matching literal, aggregate-dependency, and project-statement
  full payload reconstruction routes now also fill the remaining
  remaining-package-to-ordinary aggregate and ordinary remaining-dependency
  endpoints for the certified extraction-derivation certificates.
  It also exposes the
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
  package-to-statement and statement-to-extraction bridges therefore stay out
  of the dependency projection layer.
  The certified extraction route also exposes
  `topology_extraction_derivation_payload_of_dependencies`, which converts the
  dependency-level theorem-shaped topology statement into a final extractor
  paired with its `ExtinctionTopologyDerivationForExtractionStatement`
  certificate, with equality contracts pinning the dependency payload,
  theorem-shaped statement, derivation-statement payload, projected
  homeomorphism route, classification sub-obligations, assembly/derivation
  statements, direct assembly/derivation certificates, statement aliases,
  derivation payload, and extractor to the stored topology package,
  theorem-shaped topology statement, direct extraction-statement projection
  routes, and the fixed-extinction payload assembled from those projections.
  The final projected Poincare theorem destructures
  `poincare_completion_payload_of_dependency_projections`, while the target and
  full projection payloads remain the named sources for the completion criterion,
  package witnesses, final finite-extinction and topology-extraction inputs, and
  target statement. Equality contracts now also pin the smoothability
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
  membership for each milestone, and no-duplicate invariant. Equality contracts
  now tie the ledger literal, length proof, six named membership witnesses,
  membership characterization, and no-duplicate proof to the exact list literal
  and direct case-split or decidable proofs.
- `Poincare/DependencyCrosswalk.lean` maps every ledger milestone to the
  concrete dependency-package layer intended to discharge it, with named Lean
  theorems for all six milestone-to-package links and a package-layer membership
  theorem for the mapped ledger. It also names the package-layer propositions
  with `dependencyPackageLayerRequirement`, proves package-layer requirement
  projections from `PoincareProofDependencies`, and records
  `dependency_package_layer_requirements_payload_of_dependencies` plus
  `poincareProofDependencies_iff_package_layer_requirements`. Function-level
  equality contracts now pin the six-case milestone-to-layer map, the five-case
  layer-to-component fold, the milestone-to-component composition, and the
  component-slot, package-layer, and milestone requirement maps to their
  explicit definitions. The named milestone-layer, package-layer-to-component,
  and milestone-to-component case theorems are also pinned to their direct
  `rfl` proofs. The component-slot, package-layer, and milestone requirement
  case theorems are pinned to direct `rfl` proofs, and the generic component
  and package-layer projections from `PoincareProofDependencies` are pinned to
  their explicit destructor functions. The mapped package-layer and
  component-slot ledger image/membership theorems are pinned to their exact
  list images and case-split membership characterizations. Generic
  package-layer projections now have equality contracts for all five concrete
  layers, including the analytic and surgery routes obtained by unpacking the
  stored surgery-family field, and the package-layer payload is pinned to the
  tuple of generic package-layer projections. The package
  layers still fold to the three aggregate dependency components with
  `DependencyComponentSlot`, `dependencyComponentForPackageLayer`,
  `dependencyComponentForMilestone`, `dependencyComponentRequirement`,
  the generic projection `dependencyComponentRequirement_of_dependencies`,
  named smoothability/surgery/topology component projections and their equality
  contracts, and direct field-equality contracts tying the generic and named
  component-slot projections back to the stored `PoincareProofDependencies`
  fields,
  `dependency_component_requirements_payload_of_dependencies`,
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
  `PoincareProofDependencies` are named and now have equality contracts pinning
  them to the exact component-slot, package-layer, and milestone payload
  destructors. The three iff routes are pinned to the named forward/reverse
  maps. The individual component-slot, package-layer,
  and milestone projection wrappers are now pinned to their generic component,
  package-layer, or milestone projection routes. The component-slot payload is
  pinned both to the stored dependency fields and to the named component-slot
  projection tuple. The six milestone projections are also pinned directly to
  their assigned package-layer projections, and the milestone payload is pinned
  to the corresponding package-layer tuple.
- `Poincare/CompletionTarget.lean` records the canonical completion theorem name,
  proves by definitional equality that the canonical target is exactly the
  project statement and the explicit completion criterion, proves iff contracts
  tying the canonical target to both, pins the direct target/criterion equality
  route with its own equality contract, proves both directions between the
  canonical target and criterion, exposes the canonical target-to-extraction
  bridge `extinction_extraction_of_canonical_completion_target`, the reverse
  finite-extinction/extraction bridge
  `canonical_completion_target_of_extinction_and_extraction`, and the iff
  `canonicalCompletionTarget_iff_extinction_extraction`, with the matching
  payload and criterion projections
  `canonical_completion_payload_of_extinction_and_extraction` and
  `canonical_completion_criterion_of_extinction_and_extraction`, centralizes the
  canonical target plus
  completion-criterion payload in
  `canonical_completion_payload_of_canonical_completion_target`; the canonical
  target is also exposed as the project payload by
  `poincare_completion_payload_of_canonical_completion_target`; the canonical
  payload is projected back to its target and criterion by
  `canonical_completion_target_of_canonical_completion_payload` and
  `completion_criterion_of_canonical_completion_payload`, and the project
  payload is projected back to the canonical target by
  `canonicalCompletionTarget_of_poincare_completion_payload`; the iff contracts
  `canonicalCompletionTarget_iff_canonical_completion_payload` and
  `completionCriterionAtUniverse_iff_canonical_completion_payload` identify the
  canonical target and criterion directly with that payload, the named
  constructor `canonical_completion_payload_of_completion_criterion` exposes the
  criterion-to-canonical-payload direction, and
  `poincare_completion_payload_of_canonical_completion_payload` with
  `canonical_completion_payload_iff_poincare_completion_payload` records the
  reverse bridge to the project Poincare completion payload. Equality contracts
  now pin these canonical target/criterion iff routes, extraction bridges,
  payload constructors, payload projections, and canonical/project payload iff
  routes to their named constructions. It proves
  that the explicit smoothability/surgery/topology package route, the aggregate
  dependency route, and the projection-based dependency route imply that target.
  The finite-extinction plus theorem-shaped topology route exposes
  `canonical_completion_payload_of_finite_extinction_and_topology_extraction_statement`,
  `canonical_completion_target_of_finite_extinction_and_topology_extraction_statement`,
  and
  `canonical_completion_criterion_of_finite_extinction_and_topology_extraction_statement`.
  The extractor-plus-derivation route exposes
  `canonical_completion_payload_of_finite_extinction_and_extraction_derivation`,
  `canonical_completion_target_of_finite_extinction_and_extraction_derivation`,
  and
  `canonical_completion_criterion_of_finite_extinction_and_extraction_derivation`,
  so the final extractor is not recorded without its topology derivation
  certificate.
  The explicit package route now exposes
  `canonical_completion_payload_of_surgery_and_topology_packages`, the
  theorem-shaped topology route exposes
  `canonical_completion_payload_of_surgery_and_topology_extraction_statement`,
  `canonical_completion_target_of_surgery_and_topology_extraction_statement`,
  and
  `canonical_completion_criterion_of_surgery_and_topology_extraction_statement`,
  with equality contracts pinning the explicit package payload, target, and
  criterion to that theorem-shaped topology route after building the topology
  statement from the topology package,
  the surgery-plus-extractor-derivation route exposes
  `canonical_completion_payload_of_surgery_and_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_extraction_derivation`, and
  `canonical_completion_criterion_of_surgery_and_extraction_derivation`,
  the package-level certified extraction route exposes
  `canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_topology_package_extraction_derivation`,
  and
  `canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation`,
  with direct equality contracts pinning those canonical routes to the
  extractor/derivation routes selected from the topology package,
  the
  component-slot requirement route exposes
  `poincare_completion_payload_of_component_requirements`,
  `canonical_completion_payload_of_component_requirements`,
  `canonical_completion_target_of_component_requirements`, and
  `canonical_completion_criterion_of_component_requirements`, plus
  `canonical_three_sphere_statement_of_component_requirements`; the
  component-slot certified extraction route now pins its canonical payload,
  target, criterion, and canonical statement back to the package-level
  certified extraction route applied to the same component requirements; the
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
  `canonical_three_sphere_statement_of_milestone_requirements`; the
  certified component-slot route exposes
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
  with equality contracts pinning those canonical outputs to the package-level
  certified extraction route applied to the consumed smoothability,
  finite-extinction, and topology package layers,
  the certified milestone route exposes
  `poincare_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_target_of_milestone_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_milestone_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements`,
  with equality contracts pinning those canonical outputs to the certified
  component-slot route applied to the consumed smoothability,
  finite-extinction, and extinction-to-sphere milestones,
  the aggregate route exposes `canonical_completion_payload_of_dependencies`, the
  aggregate certified extraction route exposes
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
  The projection-based dependency routes now pin their canonical completion
  target and criterion endpoints directly to the project statement and project
  criterion endpoints exposed by `DependencyProjections.lean`, including
  certified and equation-boundary variants.
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
  The base component-slot, package-layer, and milestone routes now also pin
  their canonical target and criterion endpoints back to the corresponding
  project statement and criterion wrappers for both raw and certified
  extraction-derivation variants.
  The raw and certified `RemainingDependencyPackage` component, package-layer,
  and milestone wrapper canonical payload, target, criterion, and statement
  routes now carry equality contracts too, pinning them to the named
  remaining-dependency component, package-layer, and milestone payloads and to
  the crosswalk projections they destructure.
  Those remaining-dependency wrappers now also pin their canonical target and
  criterion endpoints back to the corresponding project statement and criterion
  wrappers for both raw and certified extraction-derivation variants.
  The explicit package, package-level certified extraction, package-layer,
  aggregate dependency, aggregate certified extraction, projection-route, and
  extraction-derivation projection-route canonical payloads
  consume the corresponding noncanonical Poincare completion payloads through
  `canonical_completion_payload_of_poincare_completion_payload`, the shared
  bridge from the project target payload to the canonical completion payload;
  the reverse payload bridge and iff contract make this canonical/project
  payload identification bidirectional.
  The aggregate and aggregate certified extraction routes now also pin their
  canonical target and criterion endpoints back to their project statement and
  criterion wrappers.
  The strengthened equation-boundary aggregate and remaining-package routes now
  expose the same canonical criterion endpoint layer and pin raw/certified
  canonical target and criterion endpoints to their project wrappers.
  The raw and certified strengthened canonical criteria are also pinned to
  dependency-level, forgetful aggregate, and forgetful remaining-dependency
  routes.
  The generic checked completion certificate projection layer now also pins its
  canonical/project payload, target, and criterion endpoints in both audited
  directions.
  The strengthened remaining-package and aggregate checked-certificate
  constructors now also expose the named canonical criterion directly and pin it
  to the forgetful aggregate and remaining-dependency routes.
  The certified extraction-derivation remaining-package certificate
  constructors now pin their canonical criterion projections through the
  strengthened certified route, the checked boundary certificate, and the
  ordinary remaining-dependency endpoint.
  The aggregate certified extraction-derivation certificate constructors mirror
  those canonical-criterion projections through the strengthened aggregate
  route, the checked strengthened aggregate certificate, the forgetful
  aggregate endpoint, and the converted remaining-dependency endpoint.
  The boundary-target-payload strengthened certificate constructors expose the
  same canonical-criterion endpoints and forgetful route pins.
  The certified boundary-extraction target-payload certificate constructors add
  the same canonical-criterion pins, including the direct route back to the
  boundary-target certificate.
  The boundary-aware equation-verification certificate wrapper mirrors that
  endpoint layer: its canonical/project payloads, canonical target/project
  statement, and canonical/project criterion projections are now pinned directly
  before routing through the projected strengthened dependency package.
  Its canonical criterion is also pinned to the projected strengthened
  dependency, checked boundary certificate, forgetful remaining-dependency, and
  finite-extinction/topology routes.
  The checked certificate projected out of that wrapper now has the same direct
  canonical/project endpoint contracts, and its canonical criterion is pinned
  to the projected strengthened dependency, finite-extinction, boundary
  certificate, and forgetful remaining-dependency routes.
  The boundary-aware certificate constructors now also recover the named
  canonical criterion for arbitrary verification payloads, existential
  verification payloads, and the named remaining-package and aggregate routes.
  Those constructor canonical criteria are also pinned directly to the checked
  boundary certificates carried by each route.
  The same constructor canonical criteria are now pinned to the forgetful
  remaining-dependency and aggregate routes wherever those routes exist.
  `remainingDependencyPackage_eq`,
  `remainingDependencyPackage_iff_poincareProofDependencies`, and
  `remainingDependencyPackage_iff_components` identify the remaining-dependency
  package with the aggregate package and its three component inputs; the
  remaining/aggregate iff bridge now also has an equality contract pinning it to
  the definitional equivalence. The theorem
  `remainingDependencyPackage_components_payload` exposes those components from
  the completion-target boundary, with named smoothability, surgery, and
  topology projections. The smoothability package, theorem-shaped `C∞`
  smooth-manifold statement, smooth-manifold projection, and paired
  smoothability payload projections now also have equality contracts pinning
  them to the stored smoothability component of the remaining-dependency package.
  The surgery-family projection, topology-extraction projection, raw component
  payload, and component equivalence are pinned to the same stored
  remaining-dependency fields and aggregate component payload/equivalence.
  The component-slot, package-layer, and milestone requirement payload/iff
  routes are likewise pinned to the corresponding aggregate dependency
  crosswalk payloads and equivalences.
  The theorem
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
  The strengthened remaining package also mirrors the dependency-level
  pointwise equation-boundary payload for the selected surgery package.
  The strengthened aggregate package now mirrors that same pointwise
  equation-boundary payload through the strengthened remaining-package route.
  Arbitrary verification payloads now also project to that pointwise equation
  payload, and the dependency, remaining-package, and aggregate routes are
  pinned through the verification-payload projection.
  The same pointwise payloads are now pinned as pointwise projections of the
  full derivative-strengthened surgery payload routes.
  Boundary-aware completion certificates now also expose a finite-extinction
  projection pinned to the projected strengthened dependency package, the direct
  dependent verification payload, the scalar-pointwise surgery payload, the
  direct stored-verification scalar equation payload, the full
  surgery-derivative payload, and the boundary surgery-package payload.
  The arbitrary, existential, named remaining-package, and named aggregate
  boundary-aware certificate constructors now recover those finite-extinction
  routes explicitly.
  The canonical-payload, project-payload, target-statement, canonical-target,
  and completion-criterion certificate projections are also pinned through that
  finite-extinction route and the projected forgetful topology statement.
  The strengthened and certified full-assembly witnesses built from a
  boundary-aware certificate are now also pinned to that certificate-level
  finite-extinction projection.
  The ordinary checked certificate extracted from a boundary-aware
  certificate now exposes the same finite-extinction endpoint for its
  canonical payload, project payload, target statement, canonical target,
  completion criterion, and raw/certified full-assembly witnesses.
  The canonical 3-sphere statement plus canonical-statement and aggregate
  canonical-statement payloads for those boundary-aware and checked
  certificate routes are also pinned to that finite-extinction/topology
  endpoint, including the corresponding payload-constructor round trips.
  The reserved theorem-name and literal payload routes for both the
  boundary-aware certificate and its checked-certificate projection now point
  at the same finite-extinction/topology endpoint.
  The aggregate-dependency and project-statement payload projections for both
  certificate surfaces now rebuild from that same finite-extinction/topology
  endpoint.
  The literal, aggregate-dependency, and project-statement payload constructors
  for those same certificate routes now round-trip through the same
  finite-extinction/topology reconstruction.
  The canonical-statement and aggregate canonical-statement payload
  constructors for the checked-certificate projection now also round-trip
  through that finite-extinction/topology reconstruction.
  Those checked canonical-statement payloads and constructors are also routed
  back through the projected boundary certificate, the ordinary
  remaining-dependency certificate, and the aggregate forgetful certificate
  where applicable.
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
  The certified remaining-dependency component wrapper also has direct equality
  contracts pinning those canonical outputs to the package-level certified
  extraction route selected by the stored component requirements.
  The certified remaining-dependency package-layer wrapper has the same direct
  package-route contracts after selecting the stored smoothability,
  finite-extinction, and topology package layers.
  The certified remaining-dependency milestone wrapper similarly pins its
  canonical outputs to the certified component route after selecting the stored
  smoothability, finite-extinction, and extinction-to-sphere milestones.
  The remaining-dependency crosswalk wrappers also expose direct project
  payload, target-statement, and criterion projections through
  `poincare_completion_payload_of_remaining_dependency_*`,
  `poincare_statement_of_remaining_dependency_*`, and
  `completion_criterion_of_remaining_dependency_*`.
  Those remaining-dependency project projections now have equality contracts
  pinning each route to the canonical remaining-dependency payload, target, or
  criterion projection it uses.
  The base component-slot, package-layer, and milestone crosswalk routes now
  also expose named project statement and project criterion wrappers, including
  certified extraction-derivation variants, with equality contracts pinning each
  one to the canonical target or criterion projection it uses.
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
  The aggregate certified component wrapper also has direct package-route
  contracts after that conversion and remaining component-payload projection.
  The certified remaining-dependency component, package-layer, and milestone
  project payload/statement/criterion routes have direct endpoint contracts to
  the package-level certified extraction route or certified component-slot
  route selected by the stored remaining-dependency payloads.
  The aggregate certified package-layer and milestone wrappers likewise have
  direct endpoint contracts to the package-level certified extraction route and
  certified component-slot route selected after converting through the stored
  remaining-dependency package-layer and milestone payloads.
  The certified aggregate component, package-layer, and milestone project
  payload/statement/criterion routes now carry the same direct endpoint
  contracts at the project-facing layer.
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
  They also expose ordinary and certified full-assembly projection contracts,
  pinning each payload constructor back to the dependency witness carried by
  that payload.
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
  their ordinary and certified full-assembly projections are pinned back to the
  same remaining-dependency package, and the direct aggregate proof-dependency
  raw/certified crosswalk routes have the same full-assembly projection
  contracts after the aggregate-to-remaining dependency conversion,
  as do the aggregate-extraction and projection-route certificate constructors,
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
  The ordinary dependency-projection certificate route is now also pinned at the
  aggregate `PoincareProofDependencies` surface for its converted
  remaining-dependency package, canonical/project completion payloads,
  target/criterion projections, aggregate-dependency payload,
  project-statement payload, theorem-name payload, literal payload, and the
  reverse literal, aggregate-dependency, and project-statement payload
  constructors, with direct finite-extinction plus theorem-shaped
  topology-extraction contracts for the aggregate projection certificate,
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
  topology and extractor/derivation endpoints, with certified boundary literal,
  aggregate-dependency, and project-statement payload reconstructions routed
  through the ordinary forgetful remaining-dependency and aggregate certificates,
  including the remaining-package certified literal-to-aggregate and
  aggregate/project-to-remaining reconstruction endpoints,
  and certified extraction-derivation theorem-name, literal,
  aggregate-dependency, project-statement, canonical/project payload, target,
  canonical-target, and completion-criterion projections now name the same
  ordinary forgetful endpoints. The base remaining-package full-assembly and
  certified full-assembly certificate projections now also name the ordinary
  aggregate endpoints directly; the boundary-target-payload and
  boundary-preserving extraction-derivation target-payload certificates now name
  raw and certified full-assembly endpoints at both the ordinary aggregate and
  remaining-package surfaces. The remaining-package theorem-name and literal
  payload projections, together with the matching literal-payload
  reconstructions, now also name the ordinary aggregate endpoints directly.
  The remaining-package raw and certified requirement-payload constructors now
  do the same for component-slot, package-layer, and milestone payload routes at
  both boundary-target and boundary-preserving extraction-derivation target
  surfaces.
  The dependency-projection layer
  also names those endpoint contracts for the full assembly payload and explicit
  completion criterion.
  The checked certificate projected from a boundary-aware verification payload
  now also has ordinary and certified full-assembly contracts for its projected
  strengthened dependency, boundary-certificate, and forgetful
  remaining-dependency routes, including constructor-specific contracts for the
  named remaining-package, named aggregate, arbitrary verification-payload, and
  existential verification-payload constructors.
  Its boundary-aware verification certificate route now also projects the
  boundary package, derivative, pointwise equation, and analytic
  equation-boundary payloads through the full surgery-derivative path,
  alongside the direct verification, projected strengthened dependency, and
  boundary-certificate paths.
  Its theorem-name, literal, aggregate-dependency, and project-statement
  artifact payload projections are also pinned directly to the projected
  strengthened dependency, boundary-certificate, ordinary remaining-dependency,
  and ordinary aggregate routes where those routes are defined.
  Those ordinary artifact payload projections are now also pinned for the
  named remaining-package, named aggregate, arbitrary verification-payload, and
  existential verification-payload constructors, including their routes through
  the ordinary remaining-dependency certificates after equation-boundary data is
  forgotten and their aggregate routes through the fully forgetful dependency
  certificate.
  The reverse literal, aggregate-dependency, and project-statement payload
  constructors for that checked certificate are pinned to the same projected,
  boundary, remaining-dependency, and aggregate routes.
  Their constructor-specific ordinary checked routes also recover the named or
  unpacked strengthened certificates before any forgetful projection is taken,
  and now pin the corresponding ordinary remaining-dependency and fully
  forgetful aggregate routes.
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
  supplied smooth/canonical-smooth/reverse-canonical-smooth packaged payload
  routes reversible at the checked certificate surface. Those packaged payload constructors now also
  have projection-after-constructor round-trip contracts back to their
  remaining-dependency and aggregate payloads, and the packaged certificate
  payload projections themselves are pinned to the exact component payload
  assemblers for smooth, canonical-smooth, and reverse canonical-smooth routes.
  The reverse payload-to-certificate constructors are pinned to the matching
  payload destructors across the same route family.
  The smooth and packaged-smooth
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
  smoothability-package route
  `smoothability_package_smooth_statement_completion_payload` and its
  canonical-smooth and reverse canonical-smooth variants now also show that a
  `SmoothabilityPackage` alone
  supplies the `C∞` smooth-manifold input needed to turn a proof-bearing smooth
  Poincare statement into the project target, canonical completion payload, and
  canonical topological 3-sphere statement, without requiring the surgery or
  topology dependency packages.
- `MATHLIB_GAP_ANALYSIS.md` records the local mathlib surface that exists and
  the Ricci-flow/Perelman surface that is absent.
- `EXTERNAL_RESEARCH_STATUS.md` records current external search findings about
  available Lean/Ricci-flow/Poincare formalizations.
- `Poincare.lean` is the root module.
- `POINCARE_FORMALIZATION_REPORT.md` audits the current gap between the requested
  theorem and available local/project evidence.
- `lakefile.lean` and `lean-toolchain` are included as a conventional Lean project
  shape.

## Verification Status

The main verification target is:

```sh
lake build
```

Current result: `lake build` completed successfully with Lean `v4.30.0-rc2`
and 2856 jobs.

The broader scaffold audit is:

```sh
sh scripts/audit_formalization.sh
```

Current result: the scaffold audit passes.

It builds the project, rejects any local `sorry`, `axiom`, `constant`,
`postulate`, `opaque`, `admit`, or `proof_wanted` declaration, rejects local declarations that claim the
aggregate dependency package including anonymous `example` claims, and rejects a
noncanonical local declaration that directly claims either the topological or
smooth Poincare target statement.
It also rejects a local `poincare_conjecture` declaration unless Lean confirms
the canonical target type. It also runs
`scripts/interface_audit.sh`,
which checks that the gap-bearing interface predicates still have no local
constructors, `scripts/mathlib_gap_audit.sh`, which records the local mathlib
Ricci-flow and Poincare-statement gaps and runs
`scripts/mathlib_proof_wanted_dependency_guard.sh` to reject local Lean-source
references to mathlib's Poincare shortcut names while they remain
`proof_wanted`, `scripts/semantic_surface_audit.sh`,
which asks Lean to typecheck the main conditional theorem surfaces and
lower-level package projection lemmas, and
`scripts/root_import_audit.sh`, which verifies that `Poincare.lean` imports every
local Lean module under `Poincare/` and exposes the canonical target contracts
plus the canonical assembly bridges and projection-based dependency assembly
theorem through the root import.
Finally, `scripts/axiom_audit.sh` prints the axiom footprint for the local
proof-bearing assembly surface and rejects placeholder/final-theorem dependencies
or local Lean-source references to mathlib's Poincare shortcut names, as well as
nonstandard axioms beyond mathlib's usual `propext`, `Classical.choice`, and
`Quot.sound`.

The stricter completion audit is:

```sh
sh scripts/completion_audit.sh
```

Current result: expected failure. It confirms that the scaffold builds, but the
upstream mathlib Poincare statements are still `proof_wanted`, the local
source does not reference those proof-wanted shortcut names, the local
dependency-spine declarations are present, their gap-bearing predicates have no
local constructors, the local mathlib Ricci-flow-with-surgery/Ricci tensor
surface is absent, the main conditional theorem surfaces, theorem-shaped
topology extraction bridge, and lower-level package projection lemmas typecheck,
Lean confirms the package-layer and component-level aggregate dependency
contracts plus the six-item milestone/crosswalk surface with named
package-layer, component-slot, and milestone-requirement links, the root module exposes the
canonical target contracts,
canonical assembly bridges, and projection-based dependency
assembly, the canonical theorem-name declaration and `rfl` contract are present,
the local proof-bearing assembly surface has only the standard mathlib axiom
footprint, no local declaration claims `PoincareProofDependencies`,
`CURRENT_STATUS.md` records the incomplete completion-audit state, the reserved
theorem name `poincare_conjecture` is absent, and Lean cannot typecheck a
canonical local theorem
`Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`.
If that canonical theorem ever typechecks, the completion audit also prints its
Lean axiom footprint for review.

To write a generated snapshot of the current build/audit state:

```sh
sh scripts/write_status_summary.sh
```

The generated `CURRENT_STATUS.md` records each sub-check's exit status, including
the expected nonzero completion-audit status while the proof is still missing,
plus the generation timestamp and Lean toolchain. The completion audit checks
this generated file and its Lean-toolchain line so stale or falsely green status
snapshots do not mask the missing theorem or a toolchain mismatch.

Any use of `sorry`, `axiom`, `constant`, `postulate`, `proof_wanted`, or
placeholder theorem statements must be treated as a formalization gap, not as a
proof.
