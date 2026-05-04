# Poincare Lean Formalization Scaffold

This directory is a starting scaffold for a Lean formalization project targeting the
Poincare Conjecture. It is not a completed proof.

The current artifact is intentionally conservative:

- `Poincare/Statement.lean` records the intended theorem boundary and the missing
  formalization interfaces. It uses mathlib's `Metric.sphere` for the target
  3-sphere as the unit sphere in `EuclideanSpace ℝ (Fin 4)`, aligns with
  `Mathlib.Geometry.Manifold.PoincareConjecture`, and includes `rfl` lemmas for
  the exact target sphere model plus the topological and smooth statement shapes,
  explicit iff contracts for those canonical topological and smooth statement
  shapes, and an iff contract plus both directions between the target statement
  and the explicit completion criterion. It also names witness-transfer and
  witness-equivalence lemmas for the universe-indexed completion criterion,
  centralizes the target plus completion-criterion existential payload in
  `poincare_completion_payload_of_poincareConjectureStatement`, projects that
  payload back to the target and criterion, exposes the same payload directly
  from a witness-indexed completion criterion, and records iff contracts between
  the target/criterion and the payload. The statement layer now also pins those
  canonical-statement, witness-transfer, target/criterion projection, and
  target/criterion payload routes with equality contracts.
- `Poincare/Milestones.lean` and `DEPENDENCY_LEDGER.md` name the missing
  Ricci-flow and topology proof obligations as data, not as proved
  propositions.
- `Poincare/Assembly.lean` contains small proof-bearing assembly lemmas that do
  not prove Poincare, such as turning a diffeomorphism to `S^3` into a
  homeomorphism to `S^3` and reducing the topological target to the smooth
  Poincare statement plus a smoothability hypothesis. It also bridges both the
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
  `completion_criterion_of_smooth_statement`; the smooth and canonical-smooth
  routes also expose the canonical topological statement directly through
  `canonical_three_sphere_statement_of_smooth_statement` and
  `canonical_three_sphere_statement_of_canonical_smooth_three_sphere_statement`.
  Equality contracts now pin these statement-layer bridges, payload
  constructors, criterion projections, and canonical-statement iff routes to
  their named assembly paths.
- `Poincare/CanonicalBridges.lean` connects the canonical topological and smooth
  mathlib-shaped 3-sphere statement inputs to canonical completion payloads that
  carry both the canonical target and the universe-indexed completion criterion;
  those payloads now consume the assembly-layer payloads, target and criterion
  projections destructure them, and the reverse canonical statement/certificate
  bridges expose the canonical topological statement from the canonical target,
  canonical payload, checked completion certificate, and all remaining-dependency
  aggregate/projection completion routes, plus the packaged smooth and
  packaged canonical-smooth routes. It also exposes a standalone
  `SmoothabilityPackage` route from a proof-bearing smooth or canonical-smooth
  Poincare statement to the project target, canonical completion payload, and
  canonical topological statement. Direct equality contracts now pin the
  aggregate packaged smooth and packaged canonical-smooth project routes,
  canonical payloads, canonical targets, canonical criteria, and canonical
  statement projections to the corresponding remaining-dependency routes after
  `remainingDependencyPackage_iff_poincareProofDependencies`; the same
  aggregate-to-remaining pinning now covers the packaged smooth and packaged
  canonical-smooth completion certificate constructors, payload proposition
  equivalences, and certificate iff factorizations. The dependency-packaged
  smooth payload routes are also pinned back to the standalone
  `SmoothabilityPackage` payload routes obtained by projecting the package's
  smoothability component, including their project target, criterion, and
  project completion-payload, canonical payload, canonical target, canonical
  criterion, canonical statement projections, and checked completion-certificate
  constructors. The certificate layer also exposes a literal
  reserved-name payload that records the canonical statement alongside the
  remaining dependency package, canonical target, and completion criterion, plus
  the same payload shape with the aggregate dependency package named directly.
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
  expose the same boundary at the mathlib-shaped topological statement.
- `Poincare/RicciFlow.lean` defines a minimal typed API for time-dependent
  Riemannian metrics, candidate Ricci tensor fields, Ricci-identification
  evidence, and the Ricci-flow equation interface. It also exposes checked
  projections down to metric data, curvature data, metric time slices, Ricci
  tensor fields, scalar curvature fields, Ricci tensor time slices, scalar
  curvature time slices, Ricci-identification evidence, and Ricci-flow equation
  evidence, with rewriteable definitional-equality contracts identifying those
  named projections and evidence theorems with the stored structure fields.
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
  Ricci-flow/evidence projections now also have equality contracts back to the
  stored package flow and the flow-level evidence theorems.
- `Poincare/Surgery.lean` defines typed no-constructor interfaces for Ricci flow
  with surgery, Perelman singularity control, finite-extinction derivation, and
  the package that connects them to the finite-extinction assembly layer through
  the analytic foundation package. The direct package projections now include
  equality contracts back to the stored analytic foundation, stored flow,
  construction package, Perelman package, finite-extinction witness, and
  analytic equation evidence. It also exposes checked package projections for
  the analytic foundation, `analytic_foundation_payload_of_surgery_package`,
  underlying Ricci-flow data, Ricci-flow equation evidence, surgery scale
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
  statement, named sub-obligation payload, and aggregate witness routes.
  The dependency-level `surgery_package_payload_of_dependencies` now
  centralizes the raw aggregate surgery package together with its analytic
  foundation, projected flow, construction package, and Perelman control
  package. Its payload carries equality contracts for the analytic package and
  flow plus heterogeneous equality contracts tying the construction and
  Perelman-control packages to the corresponding projections from the same
  finite-extinction surgery package, so the analytic, surgery-construction,
  Perelman, and finite-extinction dependency payloads open
  `dependencies.surgery` through one named bridge. The dependency-level
  analytic-foundation package projection is now pinned to mapping that stored
  surgery family to each analytic subpackage. The package-routed payloads
  `analytic_foundation_statement_payload_with_surgery_package_of_dependencies`,
  `surgery_construction_statement_payload_with_surgery_package_of_dependencies`,
  `perelman_control_statement_payload_with_surgery_package_of_dependencies`,
  `finite_extinction_subobligations_statement_payload_with_surgery_package_of_dependencies`,
  and `finite_extinction_statement_payload_with_surgery_package_of_dependencies`
  additionally keep the selected surgery package in the payload and pin the
  downstream flow, construction, Perelman, statement, derivation, and extinction
  routes back to that package.
  The dependency-level surgery-construction route now exposes
  `surgery_construction_statement_payload_of_dependencies`, which packages the
  construction package, theorem-shaped construction statement, construction
  sub-obligation payload, and aggregate Ricci-flow-with-surgery witness by
  destructuring the shared dependency surgery package payload and then the
  package-level construction payload bridge.
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
  The dependency-level finite-extinction route now exposes
  `finite_extinction_subobligations_statement_payload_of_dependencies`,
  which packages the width sub-obligation statement, full sub-obligation
  statement, their statement-mediated width/full sub-obligation payloads, and
  direct finite-extinction statement by destructuring the package-level
  payload, plus
  `finite_extinction_statement_payload_of_dependencies`, which packages the
  direct statement, the full sub-obligation statement, the rebuilt statement,
  the derivation certificate, and the extinction witness by destructuring the
  package-level statement payload; the width/full
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
  homeomorphism assembly/derivation certificates and statement aliases back to
  that theorem-shaped extraction route. The
  package-to-extraction bridge now assembles the fixed derivation statement from
  the named components; the fixed-extinction payload and homeomorphism are
  extracted through
  `topology_derivation_statement_payload_of_extraction_statement` and
  `homeomorphism_of_topology_extraction_statement`. Package-level topology
  payloads `topology_extraction_payload_of_topology_package` and
  `topology_extraction_statement_payload_of_topology_package` centralize the
  theorem-shaped extraction interface, fixed derivation statement,
  classification payload, and homeomorphism assembly/derivation statement
  route. `topology_extraction_derivation_payload_of_topology_package` certifies
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
  routes remain explicit where the projection is not just a stored field.
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
  extractor back to the stored topology package route.
  The final `ExtinctionImpliesSphereStatement` bridge also consumes that
  extraction statement rather than bypassing the derivation certificate.
  `ExtinctionTopologyDerivationForExtractionStatement`,
  `extinction_topology_extraction_statement_of_extraction_and_derivation`, and
  `extinction_topology_extraction_statement_iff_extraction_with_derivation`
  identify the strong topology extraction theorem with a final extractor plus
  derivation evidence for the homeomorphism it returns. The direct assembly
  bridges
  `poincare_statement_of_finite_extinction_and_topology_extraction_statement`
  and
  `poincare_payload_of_finite_extinction_and_topology_extraction_statement`
  connect universal finite extinction and the strong topology statement to the
  target/completion payload. The matching extractor-plus-derivation bridges
  `poincare_statement_of_finite_extinction_and_extraction_derivation` and
  `poincare_payload_of_finite_extinction_and_extraction_derivation` expose the
  same target/completion payload without hiding the derivation certificate
  inside the canonical layer. It also proves
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
  compatibility plus full sub-obligation route. Equality contracts now tie the
  package bridge, canonical smooth-manifold statement, bridge application,
  surgery-model and canonical smooth-manifold projections, compatibility
  evidence, and smoothability payloads back to the stored package fields or
  named component route. The lower Moise/PL/smooth spine also records direct
  equality contracts for the local-chart, triangulation, PL-structure,
  PL-atlas, PL-smoothing, smooth-structure, smooth-atlas, transition, and
  smooth-structure derivation projections. Dependency-level equality contracts
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
  certificate, and final finite-extinction witness. The extinction-to-sphere
  input is now extracted by destructuring
  `topology_extraction_payload_of_topology_package`, so the full assembly
  layer consumes the package-level topology extraction payload instead of the
  raw final topology projection. The named
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
  same route as the mathlib-shaped topological 3-sphere statement. The
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
  The package-level certified extraction route
  `poincare_assembly_inputs_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_target_payload_of_surgery_and_topology_package_extraction_derivation`,
  `poincare_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  and
  `poincare_statement_of_surgery_and_topology_package_extraction_derivation`
  obtains that extractor-plus-derivation pair directly from the topology
  package before assembling the target; its canonical endpoint is
  `canonical_three_sphere_statement_of_surgery_and_topology_package_extraction_derivation`.
- `Poincare/Dependencies.lean` aggregates those future inputs into one
  `PoincareProofDependencies` package and proves that the package implies the
  target statement and the explicit completion criterion. The aggregate route
  now exposes `poincareProofDependencies_components_payload` and
  `poincareProofDependencies_iff_components`, which identify the package with
  exactly its three components: smoothability, the target-family surgery
  package, and topology extraction; the reverse constructor from that raw
  component payload is now named, and the iff route is pinned to the named
  forward/reverse maps. It also exposes
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
  `surgery_construction_statement_payload_of_dependencies`,
  statement-mediated surgery construction outputs, surgery construction
  sub-obligations, Perelman control packages, package-level Perelman payloads
  via `perelman_control_payload_of_package`,
  `perelman_control_statement_payload_of_dependencies`, statement-mediated
  Perelman control outputs, the expanded
  Perelman entropy/reduced-distance/reduced-volume/kappa/canonical-neighborhood
  sub-obligation stack, the Perelman monotonicity/blow-up sub-obligation stack,
  expanded finite-extinction min-max/variation/surgery/volume-decay
  sub-obligations, package-level finite-extinction payloads
  `finite_extinction_subobligations_payload_of_surgery_package` and
  `finite_extinction_statement_payload_of_surgery_package`,
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
  expose those same routes as the mathlib-shaped topological statement.
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
  homeomorphism route, assembly/derivation statements, direct
  assembly/derivation certificates, statement aliases, derivation payload, and
  extractor to the stored topology package route.
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
  membership for each milestone, and no-duplicate invariant.
- `Poincare/DependencyCrosswalk.lean` maps every ledger milestone to the
  concrete dependency-package layer intended to discharge it, with named Lean
  theorems for all six milestone-to-package links and a package-layer membership
  theorem for the mapped ledger. It also names the package-layer propositions
  with `dependencyPackageLayerRequirement`, proves package-layer requirement
  projections from `PoincareProofDependencies`, and records
  `dependency_package_layer_requirements_payload_of_dependencies` plus
  `poincareProofDependencies_iff_package_layer_requirements`. The package
  layers still fold to the three aggregate dependency components with
  `DependencyComponentSlot`, `dependencyComponentForPackageLayer`,
  `dependencyComponentForMilestone`, `dependencyComponentRequirement`,
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
  `PoincareProofDependencies` are named and the three iff routes are pinned to
  the named forward/reverse maps. The individual package-layer and milestone
  projection wrappers are now pinned to their generic package-layer or
  milestone projection routes.
- `Poincare/CompletionTarget.lean` records the canonical completion theorem name,
  proves by definitional equality that the canonical target is exactly the
  project statement and the explicit completion criterion, proves iff contracts
  tying the canonical target to both, proves both directions between the
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
  the surgery-plus-extractor-derivation route exposes
  `canonical_completion_payload_of_surgery_and_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_extraction_derivation`, and
  `canonical_completion_criterion_of_surgery_and_extraction_derivation`,
  the package-level certified extraction route exposes
  `canonical_completion_payload_of_surgery_and_topology_package_extraction_derivation`,
  `canonical_completion_target_of_surgery_and_topology_package_extraction_derivation`,
  and
  `canonical_completion_criterion_of_surgery_and_topology_package_extraction_derivation`,
  the
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
  the certified milestone route exposes
  `poincare_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_payload_of_milestone_extraction_derivation_requirements`,
  `canonical_completion_target_of_milestone_extraction_derivation_requirements`,
  and
  `canonical_completion_criterion_of_milestone_extraction_derivation_requirements`,
  plus
  `canonical_three_sphere_statement_of_milestone_extraction_derivation_requirements`,
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
  The raw and certified `RemainingDependencyPackage` component, package-layer,
  and milestone wrapper canonical payload, target, criterion, and statement
  routes now carry equality contracts too, pinning them to the named
  remaining-dependency component, package-layer, and milestone payloads and to
  the crosswalk projections they destructure.
  The explicit package, package-level certified extraction, package-layer,
  aggregate dependency, aggregate certified extraction, projection-route, and
  extraction-derivation projection-route canonical payloads
  consume the corresponding noncanonical Poincare completion payloads through
  `canonical_completion_payload_of_poincare_completion_payload`, the shared
  bridge from the project target payload to the canonical completion payload;
  the reverse payload bridge and iff contract make this canonical/project
  payload identification bidirectional.
  `remainingDependencyPackage_eq`,
  `remainingDependencyPackage_iff_poincareProofDependencies`, and
  `remainingDependencyPackage_iff_components` identify the remaining-dependency
  package with the aggregate package and its three component inputs. The theorem
  `remainingDependencyPackage_components_payload` exposes those components from
  the completion-target boundary, with named smoothability, surgery, and
  topology projections. The smoothability package, theorem-shaped `C∞`
  smooth-manifold statement, smooth-manifold projection, and paired
  smoothability payload projections now also have equality contracts pinning
  them to the stored smoothability component of the remaining-dependency package.
  The surgery-family projection, topology-extraction projection, raw component
  payload, and component equivalence are pinned to the same stored
  remaining-dependency fields and aggregate component equivalence.
  The component-slot, package-layer, and milestone requirement payload/iff
  routes are likewise pinned to the corresponding aggregate dependency
  crosswalk payloads and equivalences.
  The theorem
  `remainingDependencyPackage_component_requirements_payload`, together with
  `remainingDependencyPackage_iff_component_requirements`, exposes the same
  boundary through the component-slot requirements named by the crosswalk.
  `remainingDependencyPackage_package_layer_requirements_payload`, together with
  `remainingDependencyPackage_iff_package_layer_requirements`, exposes the same
  boundary through the five package-layer requirements named by the crosswalk.
  `remainingDependencyPackage_milestone_requirements_payload`, together with
  `remainingDependencyPackage_iff_milestone_requirements`, exposes the same
  boundary through all six milestone requirements. The
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
  `remainingDependencyPackage_iff_poincareProofDependencies` conversion. The
  theorems
  `poincareCompletionCertificate_aggregate_dependency_payload`,
  `completion_certificate_of_aggregate_dependency_payload`, and
  `poincareCompletionCertificate_iff_aggregate_dependency_payload` identify the
  whole artifact payload with that aggregate dependency package named directly.
  `poincareCompletionCertificate_project_statement_payload`,
  `completion_certificate_of_project_statement_payload`, and
  `poincareCompletionCertificate_iff_project_statement_payload` identify the
  analogous full payload with the project Poincare statement named directly.
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
  presentations back out of the certificate.
  `completion_certificate_of_components`,
  `completion_certificate_of_component_requirements`,
  `completion_certificate_of_package_layer_requirements`, and
  `completion_certificate_of_milestone_requirements` build the certificate
  directly from those presentations.
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
  surfaces.
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
  package surfaces. It also adds the smooth-route certificate constructors
  `completion_certificate_of_remaining_dependency_and_smooth_statement`,
  `completion_certificate_of_poincareProofDependencies_and_smooth_statement`,
  `completion_certificate_of_remaining_dependency_and_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_poincareProofDependencies_and_canonical_smooth_three_sphere_statement`,
  plus the packaged smooth-route payloads
  `packaged_smooth_statement_completion_payload_of_remaining_dependency`,
  `packaged_smooth_statement_completion_payload_of_poincareProofDependencies`,
  `packaged_canonical_smooth_three_sphere_statement_completion_payload_of_remaining_dependency`,
  and
  `packaged_canonical_smooth_three_sphere_statement_completion_payload_of_poincareProofDependencies`,
  which record the package's `C∞` smoothability statement, the smooth or
  canonical-smooth input, the induced topological target, and the completion
  criterion. The matching canonical payload routes
  `canonical_completion_payload_of_remaining_dependency_and_packaged_smooth_statement`,
  `canonical_completion_payload_of_poincareProofDependencies_and_packaged_smooth_statement`,
  `canonical_completion_payload_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement`,
  and
  `canonical_completion_payload_of_poincareProofDependencies_and_packaged_canonical_smooth_three_sphere_statement`
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
  checked certificate surface. The smooth and packaged-smooth routes now also
  have equality contracts pinning their canonical payload, certificate
  constructor, packaged payload, project target/criterion, project completion
  payload, canonical-payload conversion, canonical target, canonical criterion,
  and canonical-statement projection endpoints,
  with direct aggregate-to-remaining contracts for the packaged smooth and
  packaged canonical-smooth project target, criterion, and project completion
  payload routes after `remainingDependencyPackage_iff_poincareProofDependencies`,
  while the completion-target constructors
  `completion_certificate_of_*requirements_payload` and
  `completion_certificate_of_components_payload` rebuild checked certificates
  directly from the raw component, component-slot, package-layer, and milestone
  existential payloads exposed by an existing certificate,
  plus the packaged variants
  `completion_certificate_of_remaining_dependency_and_packaged_smooth_statement`,
  `completion_certificate_of_poincareProofDependencies_and_packaged_smooth_statement`,
  `completion_certificate_of_remaining_dependency_and_packaged_canonical_smooth_three_sphere_statement`,
  and
  `completion_certificate_of_poincareProofDependencies_and_packaged_canonical_smooth_three_sphere_statement`,
  so a proof-bearing smooth statement can use the dependency package's own `C∞`
  smoothability output to reconstruct the checked completion certificate at both
  dependency package surfaces. The standalone smoothability-package route
  `smoothability_package_smooth_statement_completion_payload` and its
  canonical-smooth variant now also show that a `SmoothabilityPackage` alone
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
Ricci-flow and Poincare-statement gaps, `scripts/semantic_surface_audit.sh`,
which asks Lean to typecheck the main conditional theorem surfaces and
lower-level package projection lemmas, and
`scripts/root_import_audit.sh`, which verifies that `Poincare.lean` imports every
local Lean module under `Poincare/` and exposes the canonical target contracts
plus the canonical assembly bridges and projection-based dependency assembly
theorem through the root import.
Finally, `scripts/axiom_audit.sh` prints the axiom footprint for the local
proof-bearing assembly surface and rejects placeholder/final-theorem dependencies
or nonstandard axioms beyond mathlib's usual `propext`, `Classical.choice`, and
`Quot.sound`.

The stricter completion audit is:

```sh
sh scripts/completion_audit.sh
```

Current result: expected failure. It confirms that the scaffold builds, but the
upstream mathlib Poincare statements are still `proof_wanted`, the local
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
