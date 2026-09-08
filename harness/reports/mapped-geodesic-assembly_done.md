# Mapped geodesic assembly: all four targets proved

Date: 2026-09-08. Branch: `worker/mapped-geodesic-assembly`.
Base: `cead6503839868571c4f1f8f71a4c3fc63283fd2`.
Verified proof head: `2023d14b`.
Worktree: `/private/tmp/poincare-workers/mapped-geodesic-assembly`.

## Result and scope

All four frozen targets are proved in the one new Lean file
`Poincare/Global/FixedChartMappedGeodesicAssembly.lean`:

- `Poincare.FixedChartUniformEndpointReanchoring.uniformMappedGeodesicEquation_of_constantCurvature`
- `Poincare.FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature`
- `Poincare.FixedChartLocalSuccessorEquality.exists_onCompact`
- `Poincare.FixedChartLocalSuccessorEquality.exists_radii`

The last declaration uses the exact task-9 statement from
`harness/reports/parametrization-plan-2.md`, section 9, in its specified
namespace. The first two extend the landed reanchoring namespace. The six
public supporting lemmas are in `FixedChartMappedGeodesicAssembly`.
No existing Lean file or `Poincare.lean` changed. The existing `Patch`,
`Data`, `UniformMappedGeodesicEquation`, `UniformEndpointReanchoring`, and
both `OnCompact` definitions remain unchanged. There is no new remainder
definition or conditional substitute for a target.

This closes the requested patchwise H1/H2 assembly. It does not assert the
Poincare conjecture or complete downstream global recognition. The worker
has not merged or marked a harness task accepted. Independent orchestrator
review and import integration remain separate.

## Mathematical content

`coordinateEndpoint_contDiffAt_two` proves C2 regularity of the actual
coordinate endpoint at every point in its retained source. Its source law
puts the time-rescaled initial state inside the original open state ball.
The full-time endpoint C2 theorem then composes with the fixed linear time
rescaling and position projection. The actual partial chart cancels on a
neighborhood in the endpoint source.

`chartMap_contDiffAt_two_of_coordinateData` applies
`OpenPartialHomeomorph.contDiffAt_symm` directly to the existing supplied
source exponential. The stored invertible endpoint derivative and actual
source membership discharge the inverse theorem. Composition with the
continuous linear equivalence and target C2 endpoint proves regularity of
the actual supplied chart map, without replacing it by an auxiliary inverse.

`exists_uniform_chartMap_contDiffAt_two` uses the landed H1 radius to obtain
coordinate data. That radius precedes every moving anchor and alignment.
`exists_uniform_christoffel_transition` takes the minimum of this radius
and the landed conditional transition radius, then discharges
`DifferentiableAt ℝ (fderiv ℝ F)` using C2 regularity. It retains C2 and the
signed diagonal Christoffel identity together on that uniform ball.

`chartMap_fderiv_eq_successor_linear` handles every actual datum. The
identity between the target-frame composition of the host map and the
source-frame composition of the reanchored map holds as a neighborhood
germ. Differentiating both sides and using derivative uniqueness gives
`patchFrame D p ∘ DF = alignment ∘ patchFrame C z`. Applying the inverse
target frame identifies `DF` with `linear (patch C D) d.successor`.
No datum is selected for this assertion.

`exists_uniform_flow_displacement_radius` proves full-interval displacement
control over a compact anchor set. Joint flow continuity on an open
initial-state domain and stationary zero-velocity solutions give the local
claim. Compactness of the anchor set times the closed time interval gives
one velocity radius. The conclusion retains the actual initial-state ball
and chart-target membership at every time in `[-C.T,C.T]`.

The mapped-geodesic theorem first enlarges the compact source anchor set
inside the retained open anchors. Its predecessor radius is
`min ηd (min δ (ηt / 2))`; its velocity radius is selected for displacement
less than `ηt / 2` over that compact enlargement. The triangle inequality
keeps every source trajectory position in the predecessor's transition
ball. The normalized retained-flow law and mapped-state chain rule prove
the target ODE on all of `[0,1]`. The actual datum identity proves the initial
velocity; the host-chart cancellation proves the initial position.

Both radii precede `x,p,L,z,d,v`, and the time interval is never shortened.
Empty compact sets require no exception. The endpoint and H2 consequences
apply the landed reductions. The final theorem uses the landed H1
`exists_radius` and takes the minimum of two already uniform predecessor
radii, retaining the independent evaluation radius. H2 includes full-ball
source containment and equality for every datum.

## Proof commits and direct checks

Every public theorem was committed after the cumulative file passed:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartMappedGeodesicAssembly.lean
```

Each successful compiler log is empty, with exit 0. The invocation wrapper
printed `LEAN_EXIT=0`. Evidence is under
`/tmp/mapped-geodesic-assembly-evidence/`.

| Commit | Theorem | Successful log |
| --- | --- | --- |
| `0e0a628c` | `coordinateEndpoint_contDiffAt_two` | `03-endpoint.log` |
| `aa195fec` | `chartMap_contDiffAt_two_of_coordinateData` | `07-chart.log` |
| `405788e2` | `exists_uniform_chartMap_contDiffAt_two` | `08-uniform-C2.log` |
| `336667e5` | `exists_uniform_christoffel_transition` | `09-transition.log` |
| `4fca719f` | `chartMap_fderiv_eq_successor_linear` | `13-velocity.log` |
| `422f81c2` | `exists_uniform_flow_displacement_radius` | `15-displacement.log` |
| `1b20be72` | `uniformMappedGeodesicEquation_of_constantCurvature` | `18-mapped-namespace.log` |
| `4f9a991b` | `uniformEndpointReanchoring_of_constantCurvature` | `19-endpoint-target.log` |
| `1ff71c09` | `exists_onCompact` | `20-onCompact.log` |
| `2023d14b` | `exists_radii` | `21-radii.log` |

The two private coordinate/frame helpers were committed with the initial
velocity theorem after the same successful cumulative check.

Failed compiler output is preserved in `01-endpoint.log`, `02-endpoint.log`,
`04-chart.log`, `05-chart.log`, `06-chart.log`, `10-velocity.log`,
`11-velocity.log`, `12-velocity.log`, `14-displacement.log`, and
`16-mapped.log`. These record syntax, scalar-type inference, local-definition
rewrites, composition inference, and the time-zero normalization rewrite.
All were corrected. The first invocation captured the compiler errors but
its shell returned the following `cat` status, so its compiler exit status
was not recorded separately. Later invocations recorded `LEAN_EXIT=1` for
failures. `17-mapped.log` passed before placing the target in its canonical
namespace; `18-mapped-namespace.log` rechecked the final namespace.

## Focused build and dependency gate

Command:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/mapped-geodesic-assembly Poincare.Global.FixedChartMappedGeodesicAssembly Poincare.FixedChartMappedGeodesicAssembly.coordinateEndpoint_contDiffAt_two Poincare.FixedChartMappedGeodesicAssembly.chartMap_contDiffAt_two_of_coordinateData Poincare.FixedChartMappedGeodesicAssembly.chartMap_fderiv_eq_successor_linear Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_chartMap_contDiffAt_two Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_christoffel_transition Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_flow_displacement_radius Poincare.FixedChartUniformEndpointReanchoring.uniformMappedGeodesicEquation_of_constantCurvature Poincare.FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature Poincare.FixedChartLocalSuccessorEquality.exists_onCompact Poincare.FixedChartLocalSuccessorEquality.exists_radii
```

Exit 0. Actual `22-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartMappedGeodesicAssembly.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartMappedGeodesicAssembly ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3616/3616] Built Poincare.Global.FixedChartMappedGeodesicAssembly (3.0s)
Build completed successfully (3616 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=10 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartMappedGeodesicAssembly.coordinateEndpoint_contDiffAt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMappedGeodesicAssembly.chartMap_contDiffAt_two_of_coordinateData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMappedGeodesicAssembly.chartMap_fderiv_eq_successor_linear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_chartMap_contDiffAt_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_christoffel_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_flow_displacement_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.uniformMappedGeodesicEquation_of_constantCurvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_onCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartLocalSuccessorEquality.exists_radii' depends on axioms: [propext, Classical.choice, Quot.sound]
=== GATE: PASS ===
```

The warning is replayed from an unchanged dependency. No warning came from
the new file. The focused build completed successfully with 3616 jobs.
No root build or root integration audit was run by this worker.

## Exact target and complete closure probes

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/mapped-geodesic-assembly-evidence/23-frozen-targets.lean
```

Exit 0, empty compiler output; wrapper printed `PROBE_EXIT=0`. This file
checks all four target declarations against explicit signatures. It includes
the universally quantified task-9 signature, with both unchanged `OnCompact`
conjuncts and no new premise.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/mapped-geodesic-assembly-evidence/24-all-closures.lean
```

Exit 0; wrapper printed `CLOSURES_EXIT=0`. This checks every theorem from the
new module, including private declarations, against exactly the three
standard dependencies. Actual output:

```text
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_flow_displacement_radius
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.chartMap_contDiffAt_two_of_coordinateData
EXACT_STANDARD_CLOSURE Poincare.FixedChartLocalSuccessorEquality.exists_onCompact
EXACT_STANDARD_CLOSURE _private.Poincare.Global.FixedChartMappedGeodesicAssembly.0.Poincare.FixedChartMappedGeodesicAssembly.chartMap_apply_host
EXACT_STANDARD_CLOSURE Poincare.FixedChartUniformEndpointReanchoring.uniformMappedGeodesicEquation_of_constantCurvature
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.coordinateEndpoint_contDiffAt_two
EXACT_STANDARD_CLOSURE _private.Poincare.Global.FixedChartMappedGeodesicAssembly.0.Poincare.FixedChartMappedGeodesicAssembly.patchFrame_hasFDerivAt
EXACT_STANDARD_CLOSURE Poincare.FixedChartLocalSuccessorEquality.exists_radii
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.chartMap_fderiv_eq_successor_linear
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_chartMap_contDiffAt_two
EXACT_STANDARD_CLOSURE Poincare.FixedChartMappedGeodesicAssembly.exists_uniform_christoffel_transition
EXACT_STANDARD_CLOSURE Poincare.FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature
EXACT_STANDARD_CLOSURES=12
```

## Token and diff checks

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartMappedGeodesicAssembly.lean
git diff --check
git diff cead6503839868571c4f1f8f71a4c3fc63283fd2 --check
```

The token scan exited 1 with no matches. Both diff checks exited 0 with no
output. The final Lean diff is saved as `proof.diff` in the evidence directory
and can be reproduced with:

```sh
git diff cead6503839868571c4f1f8f71a4c3fc63283fd2 2023d14b -- Poincare/Global/FixedChartMappedGeodesicAssembly.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartMappedGeodesicAssembly.lean
```
