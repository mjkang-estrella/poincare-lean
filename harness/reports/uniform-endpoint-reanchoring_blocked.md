# Uniform endpoint reanchoring: verified partial, blocked producer

Date: 2026-09-08 UTC. Branch: `worker/uniform-endpoint-reanchoring`.
Base: `5baf6aa82f8b8d58e5cda9ada1d3b124fcaae770`. Verified proof head: `ff760da6e95ae9768966634873b67300aa9dc036`.
Worktree: `/private/tmp/poincare-workers/uniform-endpoint-reanchoring`.

## Result

The curvature-only `uniformEndpointReanchoring_of_constantCurvature` is not
proved. Neither unconditional `exists_onCompact` nor unconditional
`exists_radii` is declared in the new namespace. This is a worker partial
result awaiting independent orchestrator review, not task acceptance.

Exactly one Lean file was added,
`Poincare/Global/FixedChartUniformEndpointReanchoring.lean`. No existing Lean
file or `Poincare.lean` changed. The supplied `UniformEndpointReanchoring`
and both `OnCompact` definitions remain verbatim in their original files.
The report and dated `HANDOFF.md` entry record the result.

## Verified mathematical progress

The actual supplied chart derivative now has a canonical metric identity,
independent of the derivative witnesses stored in `CoordinateData`.
`exists_uniform_chartMetric_pullback_germ` promotes the landed H1 data to a
host-coordinate neighborhood germ at every point of one uniform manifold
ball. The radius precedes `x,p,L,z`; the proof uses continuity of the inverse
fixed chart to transport that ball to a coordinate neighborhood.

The chart-level Koszul argument is discharged conditionally on exactly
`DifferentiableAt ℝ (fderiv ℝ F) q`. Nearby strict first derivatives give
second-derivative symmetry through
`second_derivative_symmetric_of_eventually`. Differentiation of the metric
pullback gives the three-term identity, and nondegenerate chart metrics give
the signed diagonal Christoffel transition law. Cutoff-one containment is
proved at the moving anchors from the retained patch flow. The resulting
`exists_uniform_christoffel_transition_of_differentiable_fderiv` keeps its
radius before all moving parameters. It does not assume Hessian symmetry,
a differentiated metric identity, or a preferred-chart transition law.

The new mapped-state chain rule also needs only a differentiable derivative,
and works with derivatives within the closed interval. Thus full C2
regularity is not required by the new calculus consumer.

The retained flow is normalized by
`γ(t) = ((C.α q (C.T*t)).1, C.T • (C.α q (C.T*t)).2)`.
`normalizedFlow_hasDerivWithinAt` proves the original geodesic equation on
all of `[0,1]`. It preserves the full original time interval, including its
endpoints. Source and target times may differ.
`geodesic_eqOn_unitInterval` proves uniqueness on the full unit interval:
a compact ball containing both trajectories supplies the needed Lipschitz
constant for the smooth target vector field. That bound is selected for
uniqueness after fixing trajectories; no output radius is selected there.

`exists_uniform_endpoint_displacement_radius` gives an arbitrarily
prescribed displacement tolerance for all anchors in a compact set.
`target_of_uniformMappedGeodesicEquation` combines this with the previously
proved common-source radii. Both actual endpoint domains follow from the
common sources and the partial inverse law. Full-interval uniqueness gives
coordinate endpoint equality; injectivity on the actual target chart gives
the exact frozen manifold endpoint identity.

The two final conditional consequences use this same single remainder.
H1 in `exists_radii_of_uniformMappedGeodesicEquation` comes directly from
the landed `FixedChartMovingPositionJacobi.exists_radius`. The final radius
is the minimum of two already uniform predecessor radii. No per-anchor or
per-datum radii are minimized. Empty compact sets are allowed.

## One exact remaining statement

The only new proposition definition is the concrete mapped geodesic
initial-value problem below. The curve is fixed by the actual supplied
chart map and retained source flow. It is not an arbitrary witness curve.

```lean
def UniformMappedGeodesicEquation
    {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ η > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
      (d : Data (patch C D) ⟨x, p, L⟩ z), dist z x < η →
      ∀ v : E, ‖v‖ < ρ → v ∈ (C.endpoint z).source →
        let F := chartMap (patch C D) ⟨x, p, L⟩
        let q := (extChartAt I x₀ z, C.T⁻¹ • v)
        let γ := fun t : ℝ => ((C.α q (C.T * t)).1, C.T • (C.α q (C.T * t)).2)
        let β := FTransitionGeodesicMap.mappedState F γ
        β 0 = (extChartAt I p₀ (map (patch C D) ⟨x, p, L⟩ z),
          linear (patch C D) d.successor v) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt β
          (geodesicFlowField (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀) (β t))
          (Icc (0 : ℝ) 1) t

```

The checked conditional theorem is
`target_of_uniformMappedGeodesicEquation C D K H hK hKC hH hHD he`, with
conclusion exactly
`FixedChartLocalSuccessorEquality.UniformEndpointReanchoring (patch C D) K H`.
It needs neither a curvature premise nor a separate regularity premise once
this initial-value problem is supplied. This is a sufficient analytic
remainder; equivalence with the frozen endpoint assertion is not claimed.

## Why the producer remains blocked

The first unclosed analytic step is differentiability of the first
derivative of the *supplied fixed-chart map*, uniformly near the moving
anchors. The stored `Patch.endpoint_C1` proves only
`ContDiffOn ℝ 1 (fun q => C.α q C.T)` on the original state ball. C1 alone
does not imply differentiability of that derivative. The flow equation is
additional information that could support a second-variation argument;
this attempt does not prove that argument for the arbitrary retained patch.

The inspected `UniformAnchoredSecondVariation` theorems concern
`GeodesicTransport.expAtChartOpenPartialHomeomorph g x₀` and
`CartanDifferential.cartanChartMap g x₀ p₀ L`. They do not apply by
instantiation to `chartMap (patch C D) ⟨x,p,L⟩`. Their output radius also
comes after the preferred anchor. The old per-anchor naturality theorem
places its output radius after the datum. Neither supplies the required
uniform quantifier order. Fixed-anchor germ agreement with the generic
map does not provide agreement around every moving `z` on a uniform radius.

To produce the displayed initial-value problem through the proved lemmas,
the remaining work is to obtain the supplied derivative regularity on one
uniform neighborhood, retain the full source trajectory in that
neighborhood, and identify its mapped initial velocity with
`linear (patch C D) d.successor v`. The last identity is explicit in the
remainder and is not separately proved here. The source/target time
normalization, closed-interval uniqueness, and endpoint-domain assembly
are proved. No counterexample to the frozen target is asserted.

The next mathematical action is to prove, for the actual supplied map,
`DifferentiableAt ℝ (fderiv ℝ (chartMap (patch C D) ⟨x,p,L⟩))
  (extChartAt I x₀ z)` on a radius selected before `x,p,L,z`, using the
retained flow's variational equation at arbitrary initial positions.

## Proof commits and direct checks

Each row was committed after the cumulative new module elaborated.
The exact command for every row was:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformEndpointReanchoring.lean
```

All successful compiler logs below are empty. Each command exited 0;
the invocation wrapper printed `LEAN_EXIT=0`.

| Commit | Theorem | Compiler log |
| --- | --- | --- |
| `611aae39` | `chartMap_fderiv_metric` | `01-differential.log` |
| `e8af003c` | `exists_uniform_chartMetric_pullback_germ` | `04-germ.log` |
| `7c1d19a4` | `christoffel_transition_of_metric_germ` | `06-transition.log` |
| `a9122897` | `exists_uniform_christoffel_transition_of_differentiable_fderiv` | `08-uniform-transition.log` |
| `43543223` | `normalizedFlow_hasDerivWithinAt` | `13-normalized-flow.log` |
| `7a90e9cd` | `geodesic_eqOn_unitInterval` | `14-uniqueness.log` |
| `1f985de8` | `exists_uniform_endpoint_displacement_radius` | `17-displacement.log` |
| `a2a7e503` | `target_of_uniformMappedGeodesicEquation` | `20-target.log` |
| `9de279bf` | `mappedState_hasDerivWithinAt_of_differentiable_fderiv` | `22-chain-rule.log` |
| `ebed0516` | `exists_onCompact_of_uniformMappedGeodesicEquation` | `23-h2.log` |
| `ff760da6` | `exists_radii_of_uniformMappedGeodesicEquation` | `24-h1h2.log` |

Evidence directory: `/tmp/uniform-endpoint-reanchoring-evidence/`.
Private chart-coordinate and cutoff helpers were committed with the public
theorems they support.

Compiler retries are preserved in `02-germ.log`, `03-germ.log`,
`05-transition.log`, `07-uniform-transition.log`, `09-normalized-flow.log`,
`10-normalized-flow.log`, `11-normalized-flow.log`, `12-normalized-flow.log`,
`15-displacement.log`, `16-displacement.log`, `18-target.log`,
`19-target.log`, and `21-chain-rule.log`. Each failed command exited 1.
They record, respectively, partial-equivalence versus open-chart APIs,
required manifold instances, a host projection rewrite, scalar versus
vector derivative composition and projection APIs, metric-space instance
requirements, a recursion-depth limit, time multiplication normalization,
and composition unfolding in the final chain-rule algebra. These were
corrected and the same cumulative module recompiled. The compiler options
are `maxHeartbeats 1200000` and `maxRecDepth 4000`.

The live type probe ran as:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-endpoint-reanchoring-evidence/regularity-types.lean
```

Exit 0. Full actual output is in `25-regularity-types.log`. It checks
`Patch.endpoint_C1`, both preferred second-variation declarations, the
landed uniform pullback, and `second_derivative_symmetric_of_eventually`.

## Focused build and axiom gate

Exact command, saved in `gate-command.txt`:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/uniform-endpoint-reanchoring Poincare.Global.FixedChartUniformEndpointReanchoring Poincare.FixedChartUniformEndpointReanchoring.chartMap_fderiv_metric Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_chartMetric_pullback_germ Poincare.FixedChartUniformEndpointReanchoring.christoffel_transition_of_metric_germ Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_christoffel_transition_of_differentiable_fderiv Poincare.FixedChartUniformEndpointReanchoring.normalizedFlow_hasDerivWithinAt Poincare.FixedChartUniformEndpointReanchoring.geodesic_eqOn_unitInterval Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_endpoint_displacement_radius Poincare.FixedChartUniformEndpointReanchoring.mappedState_hasDerivWithinAt_of_differentiable_fderiv Poincare.FixedChartUniformEndpointReanchoring.target_of_uniformMappedGeodesicEquation Poincare.FixedChartUniformEndpointReanchoring.exists_onCompact_of_uniformMappedGeodesicEquation Poincare.FixedChartUniformEndpointReanchoring.exists_radii_of_uniformMappedGeodesicEquation
```

Exit 0. Actual `26-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartUniformEndpointReanchoring.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartUniformEndpointReanchoring ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3613/3613] Built Poincare.Global.FixedChartUniformEndpointReanchoring (5.6s)
Build completed successfully (3613 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=12 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartUniformEndpointReanchoring.chartMap_fderiv_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_chartMetric_pullback_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.christoffel_transition_of_metric_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_christoffel_transition_of_differentiable_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.normalizedFlow_hasDerivWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.geodesic_eqOn_unitInterval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.exists_uniform_endpoint_displacement_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.mappedState_hasDerivWithinAt_of_differentiable_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.target_of_uniformMappedGeodesicEquation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.exists_onCompact_of_uniformMappedGeodesicEquation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformEndpointReanchoring.exists_radii_of_uniformMappedGeodesicEquation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is replayed from an unchanged dependency. The module scan
reports 12 public declarations, the 11 theorems and the remainder definition.
All 11 named theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`. A separate parser check of every
named closure prints `EXACT_STANDARD_CLOSURES=11/11` in
`28-exact-closures.log`.

No root build or root integration audit was run by this worker.

## Frozen target probe and diff checks

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-endpoint-reanchoring-evidence/27-frozen-targets.lean
```

Expected exit 1. Actual output:

```text
/tmp/uniform-endpoint-reanchoring-evidence/27-frozen-targets.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformEndpointReanchoring.uniformEndpointReanchoring_of_constantCurvature`
/tmp/uniform-endpoint-reanchoring-evidence/27-frozen-targets.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformEndpointReanchoring.exists_onCompact`
/tmp/uniform-endpoint-reanchoring-evidence/27-frozen-targets.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformEndpointReanchoring.exists_radii`
```

The conditional theorems retain the remainder in both their names and
types. They do not substitute weaker declarations for these names.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartUniformEndpointReanchoring.lean
git diff --check
git diff 5baf6aa82f8b8d58e5cda9ada1d3b124fcaae770 --check
```

The token scan exited 1 with no matches. Both whitespace checks exited 0
with no output. The verified Lean diff is preserved as `proof.diff` and is
reproducible with:

```sh
git diff 5baf6aa82f8b8d58e5cda9ada1d3b124fcaae770 ff760da6e95ae9768966634873b67300aa9dc036 -- Poincare/Global/FixedChartUniformEndpointReanchoring.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformEndpointReanchoring.lean
```
