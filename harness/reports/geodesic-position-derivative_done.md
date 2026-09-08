# Geodesic initial-state derivative worker result

Date: 2026-09-08. Status: done, pending orchestrator review.
Branch: `worker/geodesic-position-derivative`.
Base: `1e8df02f77da1b7e8879839991ad75c259f82301`.
Verified proof head: `de042d582b8146f760af74ea404ed7ef164dcc04`.

## Result

The new `Poincare/Global/GeodesicFlowJointDerivative.lean` proves joint C1
initial-position and initial-velocity dependence for the fixed-chart geodesic
flow. It contains 14 theorems. No existing Lean file or `Poincare.lean` changed.

`Poincare.GeodesicFlowJointDerivative.geodesic_flow_hasFDerivAt_initialState`
has the frozen conclusion

```lean
∀ q ∈ ball (z₀, (0 : E)) r, ∀ t ∈ Ioo (-ε) ε,
  HasFDerivAt (fun q' : E × E => α q' t) (Φ q t) q
```

The hypotheses are finite-dimensional real normed `E`, an open `U`,
`∀ z ∈ U, ContDiffAt ℝ 2 Γ z`, and the supplied continuous closed-ball-times-
closed-interval PL flow whose position stays in `U`. The fundamental solution
has initial value `ContinuousLinearMap.id ℝ (E × E)` and satisfies

```lean
HasDerivWithinAt (Φ q)
  ((linearizedGeodesicFlowOperator Γ (α q t)).comp (Φ q t))
  (Icc (-ε) ε) t
```

The existence of this fundamental solution is proved separately and assembled
in `exists_geodesic_flow_initialState_C1`. That theorem retains the supplied
`α` and the initial-state ball, chooses one positive `T ≤ ε`, and constructs
`Φ` on `[-T,T]`. It proves the derivative statement even at the closed time
endpoints, joint continuity of `(q,t) ↦ Φ q t` in operator norm, and
`ContDiffOn ℝ 1 (fun q => α q t)` on the open state ball for every such `t`.
Shrinking time is part of choosing the uniform local package, not an
assumption about an unconstructed family.

`exists_uniform_local_geodesic_chart_flow_initialState_C1` instantiates the
result in `ClosedSmoothModel 3` using exactly
`GeodesicTransport.exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn`.
It exports positive radius and time, the original PL selector after time
restriction, its initial value and ODE, the prescribed position-neighborhood
retention, joint continuity of the flow, the constructed fundamental solution,
its variational ODE, the joint derivative, derivative continuity, and C1
endpoint regularity. Existing global C2 regularity of the fixed chart field is
supplied by `geodesicFlowField_chartChristoffelField_contDiff_two`.

## Proof route and commits

- `e7315be8`: solve `Φ' = A(t) ∘ Φ` directly in continuous linear endomorphisms,
  with initial identity and a prescribed interval satisfying `K*T ≤ 1/4`.
  Evaluating this one operator solution supplies every joint direction.
- `d4aeb10e`: feed the identity injection on the entire state space into
  `parameterizedFlowEndpoint_hasFDerivAt_of_linearized_gronwall_eventually`.
  Derive its perturbed-trajectory hypotheses from the open state ball and
  its uniform Taylor bound from compactness. Export the little-o residual
  `α(q+h,t) - α(q,t) - Φ(t)h`.
- `458ab50b`: convert that residual to the Frechet derivative, including
  negative times by reflection of the flow and coefficient equation.
- `a0201371`: compare the two full-state coefficient curves through
  `projected_linearODE_endpoint_clm_lipschitz_of_base_curves`, with both
  injection and projection the identity. Obtain a time-uniform Lipschitz
  constant in the initial state; combine it with time continuity to prove
  joint continuity.
- `8dd7bd1c`: construct one common interval and family for all initial states,
  then derive C1 endpoints with `contDiffAt_one_iff`.
- `ff50ceb5`: extend a locally C2 field smoothly near a compact trajectory
  image, with germ equality at every point of that image.
- `5a733b1e`: remove the global regularity assumption and assemble the general
  local-C2 Christoffel package. Germ equality identifies both field values and
  derivatives along the unchanged original trajectories.
- `07c26339`: expose the exact frozen derivative theorem.
- `de042d58`: instantiate the repository's actual uniform PL flow package.

The local-C2 extension uses finite dimensionality and compactness. No
infinite-dimensional local-field result or C1-with-Lipschitz-derivative variant
is claimed. The globally C2 intermediate theorem is more general in its state
space assumptions.

## Verification

All commands ran in this worktree on the verified proof head.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/GeodesicFlowJointDerivative.lean
```

Exit 0; stdout/stderr empty. The new module emits no warnings.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.GeodesicFlowJointDerivative
```

Exit 0. Final output:

```text
✔ [3258/3258] Built Poincare.Global.GeodesicFlowJointDerivative (3.8s)
Build completed successfully (3258 jobs).
```

The full build log contains replayed warnings from existing dependency files.
It is preserved as `joint-focused-build.log` in the evidence directory below.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/GeodesicFlowJointDerivative.lean
git diff 1e8df02f77da1b7e8879839991ad75c259f82301 --check
```

The token scan produces no output, exit 1 as expected for no matches. The diff
check produces no output, exit 0.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/joint_axioms.lean
```

Exit 0. The probe imports the new module, prints each of the 14 theorem
closures, and scans all module declarations, including internal declarations.
Actual output:

```text
'Poincare.GeodesicFlowJointDerivative.exists_fundamentalSolution_on_prescribed_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.initialState_residual_isLittleO' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.hasDerivWithinAt_reflect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.flow_hasFDerivAt_initialState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_fundamentalSolution_lipschitzOn_initialState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.continuousOn_fundamentalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_flow_initialState_C1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_contDiff_extension_near_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_smoothField_near_uniformFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_flow_initialState_C1_of_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.contDiffAt_geodesicFlowField_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_geodesic_flow_initialState_C1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.geodesic_flow_hasFDerivAt_initialState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.GeodesicFlowJointDerivative.exists_uniform_local_geodesic_chart_flow_initialState_C1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
GATE_SCAN declarations=15 nonstandard=[]
```

Root integration audits and a full root build were not run by this worker.
The new module is deliberately not wired into `Poincare.lean`.

## Failed attempts and retained evidence

Evidence directory: `/private/tmp/geodesic-position-derivative-evidence-2026-09-08`.
It contains all compiler/probe logs, the complete focused-build output, the
axiom probe, the final proof diff, the verified Lean source, and full commit
IDs. Earlier failures are retained rather than overwritten.

The substantive elaboration failures were nested operator-norm instance
synthesis, unresolved implicit tube-radius arguments, reflection rewriting of
`fderiv (-F)`, beta reduction before rewriting operator initial values,
unsupported subscript-plus identifiers, and mistaken smooth-extension API
names. The final module resolves these. The first operator-existence proof
used a direct norm bound and increased recursion/heartbeat limits, following
the neighboring ODE modules. There is no remaining resisting statement for
the required target.

## Scope and next action

The optional zero-velocity explicit endpoint differential was not proved.
For the joint inverse-function step the position endpoint map is
`(z,v) ↦ (z, (α (z,v) T).1)`. Its expected differential at rest is
`(δz,δv) ↦ (δz, δz + T • δv)`. The literal map retaining the full state
`(z,v) ↦ (z, α (z,v) T)` has a larger codomain, so it is not the square map for
that inverse-function argument.

This result does not re-found the anchor-dependent exponential family, prove
H1/H2, or prove the Poincare conjecture. It completes the requested joint-flow
regularity brick and awaits independent orchestrator acceptance.

Exact first review action against the recorded base:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.GeodesicFlowJointDerivative
```

Then rerun the preserved axiom probe and inspect the actual diff. The next
mathematical action is the explicit differential of the position endpoint at
zero velocity, followed by the joint inverse-function construction.
