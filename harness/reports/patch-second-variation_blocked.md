# Patch second variation: verified short-time C2, blocked at the retained time

Date: 2026-09-08. Branch: `worker/patch-second-variation`.
Base: `d1a10d376fd432458fb791259c60dc9fd7d5d5c0`.
Verified proof head: `f13ece96`.
Worktree: `/private/tmp/poincare-workers/patch-second-variation`.

## Result and scope

This is the step-1 blocked result allowed by the worker prompt. The frozen
`uniformMappedGeodesicEquation_of_constantCurvature` is not proved. Its three
requested unconditional consequences are not declared. The original
`UniformMappedGeodesicEquation` definition is imported verbatim and unchanged.

Exactly one new Lean file was added,
`Poincare/Global/FixedChartPatchSecondVariation.lean`. No existing Lean file
or `Poincare.lean` changed. Six theorems were committed individually after
successful direct elaboration. This report and a dated `HANDOFF.md` entry
record the result. The worker has not merged or marked the task accepted.

The conditional theorem `target_of_augmentedSystemRegularity` concludes the
step-1 C2 endpoint assertion. It does **not** conclude the frozen mapped
geodesic equation. The inverse-map, uniform trajectory, initial-velocity,
and final consequence assembly in steps 2–4 remain unproved by this worker.
No conditional result is presented under an unconditional frozen name.

## Verified mathematical progress

`operatorAugmentedField F (q, Y) = (F q, (fderiv ℝ F q).comp Y)` is the actual
operator-valued augmented vector field. Global C2 regularity of `F` gives C1
regularity of this field. For the fixed-chart geodesic field, the stronger
C2 augmented regularity is proved without a curvature hypothesis. The proof
extracts each evaluation of the linearized operator from the existing C2
vector-valued augmented field, then uses finite-dimensional operator
regularity and smooth composition of continuous linear maps.

`operatorAugmentedFlow_hasDerivWithinAt` proves the augmented ODE for
`(α t, (Φ t).comp Y)` for every initial operator `Y`. Thus the second use of
the flow theorem has an open ball of full augmented initial states, rather
than just the lower-dimensional slice initialized with the identity.

`patch_flow_hasFDerivAt_of_fundamentalSolution` identifies any supplied
full-interval fundamental solution with the derivative of the actual patch
flow. The assertion includes both closed-interval endpoints. Compactness of
the continuous retained flow gives its state bound; the global Gronwall
initial-state derivative theorem then applies on the original interval.
No first-derivative identity is assumed in this theorem.

The strongest unconditional second-variation result is:

```lean
theorem exists_patch_flow_contDiffOn_two_short_time
    {x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    ∃ τ > (0 : ℝ), τ ≤ C.T ∧
      ∀ t ∈ Icc (-τ) τ, ContDiffOn ℝ 2 (fun q => C.α q t)
        (ball (extChartAt I x₀ x₀, 0) ((C.r : ℝ) / 2))
```

Both `τ` and the fixed half-radius precede every initial state. The theorem
applies to a general patch, including a sphere patch. It uses the original
flow, not a replacement selector. The first flow theorem constructs `Φ`;
the full augmented flow is `(C.α y.1 t, (Φ y.1 t).comp y.2)`. A second
application gives C1 dependence of this flow. Restriction to initial operator
identity gives C1 dependence of `Φ`, and the derivative identification gives
C2 dependence of `C.α` on both initial position and velocity.

The time restriction is real: this theorem proves C2 at all times in
`[-τ,τ]`, with `τ ≤ C.T`, not necessarily at `C.T`. It neither changes `C.T`
nor claims that the half-radius ball contains every compact subset of
`C.anchors`.

## One exact resisting statement

The sole new proposition definition is the following full-time augmented
regularity assertion. It keeps the original retained time and original open
state ball. Those choices are made from the patch before any moving anchor.

```lean
def AugmentedSystemRegularity {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) : Prop :=
  ∃ Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E),
    (∀ q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ),
      (C.α q 0, Φ q 0) = (q, ContinuousLinearMap.id ℝ (E × E)) ∧
      ∀ t ∈ Icc (-C.T) C.T,
        HasDerivWithinAt (fun s => (C.α q s, Φ q s))
          (operatorAugmentedField
            (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀))
            (C.α q t, Φ q t)) (Icc (-C.T) C.T) t) ∧
    ContDiffOn ℝ 1 (fun q => (C.α q C.T, Φ q C.T))
      (ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
```

The checked step-1 reduction is:

```lean
theorem target_of_augmentedSystemRegularity
    {x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (h : AugmentedSystemRegularity C) :
    ContDiffOn ℝ 2 (fun q => C.α q C.T)
      (ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
```

The proof projects the initial condition and augmented ODE to obtain the
fundamental-solution equation, invokes the verified full-interval derivative
identification, and applies `contDiffAt_succ_iff_hasFDerivAt`. It assumes no
Hessian identity, endpoint C2 assertion, or map to the sphere.

## Why step 1 still resists

The suggested `exists_flow_initialState_C1` and its local-regularity variant
both require **C2**, not merely C1, of their input vector field. This
regularity mismatch has been discharged for the fixed-chart operator system
by the new `chart_operatorAugmentedField_contDiff_two` theorem.

The remaining mismatch is the time interval. Both flow theorems return
`∃ T > 0, T ≤ ε ∧ ...`; neither preserves a prescribed `ε`. Their proof
chooses a bound involving `min ε (1 / (4 * (K + 1)))`. Applying the theorem
twice therefore gives a possibly shorter interval twice. The patch endpoint
map uses the previously retained `C.T`, so replacing it with either returned
time would change the supplied map and violate the task.

The full augmented solution must be continued to the original retained time,
with C1 dependence in initial state. A proof by concatenating uniformly
bounded linear/augmented evolution over finitely many short intervals would
address this statement; no such continuation proof was completed here.
Shrinking only the initial-state radius has not been proved to remove the
time restriction. No counterexample to the frozen theorem is asserted.

## Proof commits and direct Lean checks

Every successful row used exactly:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartPatchSecondVariation.lean
```

The successful compiler logs are empty, with Lean exit 0. The invocation
wrapper printed `LEAN_EXIT=0`.

| Commit | Theorem | Compiler log |
| --- | --- | --- |
| `322812f2` | `operatorAugmentedField_contDiff_one` | `01-field-c1.log` |
| `764872be` | `chart_operatorAugmentedField_contDiff_two` | `03-field-c2.log` |
| `5fecfce3` | `operatorAugmentedFlow_hasDerivWithinAt` | `04-lift-law.log` |
| `2db9a053` | `patch_flow_hasFDerivAt_of_fundamentalSolution` | `06-full-derivative.log` |
| `5e9b3617` | `exists_patch_flow_contDiffOn_two_short_time` | `09-short-c2.log` |
| `f13ece96` | `target_of_augmentedSystemRegularity` | `11-full-time-target.log` |

Evidence directory: `/tmp/patch-second-variation-evidence/`.

Failed direct compiler attempts, each Lean exit 1, are retained in
`02-field-c2.log`, `05-full-derivative.log`, `07-short-c2.log`,
`08-short-c2.log`, and `10-full-time-target.log`. They record respectively a
line break in a qualified name, a line break in field notation, product
distance and continuity-domain inference issues, a malformed nested tactic,
and the need to simplify the projected scalar derivative. All were corrected
and followed by successful elaboration before the corresponding commit.

The exact API probe ran as:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/patch-second-variation-evidence/13-api.lean
```

Exit 0. Full output is in `13-api.log`; it prints the two C1 flow APIs, the
short-time C2 theorem, the resisting definition, and the step-1 reduction.

## Focused build and dependency gate

Exact command:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/patch-second-variation Poincare.Global.FixedChartPatchSecondVariation Poincare.FixedChartPatchSecondVariation.operatorAugmentedField_contDiff_one Poincare.FixedChartPatchSecondVariation.chart_operatorAugmentedField_contDiff_two Poincare.FixedChartPatchSecondVariation.operatorAugmentedFlow_hasDerivWithinAt Poincare.FixedChartPatchSecondVariation.patch_flow_hasFDerivAt_of_fundamentalSolution Poincare.FixedChartPatchSecondVariation.exists_patch_flow_contDiffOn_two_short_time Poincare.FixedChartPatchSecondVariation.target_of_augmentedSystemRegularity
```

Exit 0. Actual output in `12-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartPatchSecondVariation.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartPatchSecondVariation ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3614/3614] Built Poincare.Global.FixedChartPatchSecondVariation (3.0s)
Build completed successfully (3614 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=9 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartPatchSecondVariation.operatorAugmentedField_contDiff_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartPatchSecondVariation.chart_operatorAugmentedField_contDiff_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartPatchSecondVariation.operatorAugmentedFlow_hasDerivWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartPatchSecondVariation.patch_flow_hasFDerivAt_of_fundamentalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartPatchSecondVariation.exists_patch_flow_contDiffOn_two_short_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartPatchSecondVariation.target_of_augmentedSystemRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning comes from an unchanged dependency. The module scan checks nine
public declarations and finds no nonstandard dependencies. All six named
theorem closures are exactly `[propext, Classical.choice, Quot.sound]`.
A separate parser check prints `EXACT_STANDARD_CLOSURES=6/6` in
`17-exact-closures.log`.

No root build or root integration audit was run by this worker.

## Frozen names, token scan, and diff

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/patch-second-variation-evidence/14-frozen-targets.lean
```

Expected exit 1. Actual output:

```text
/tmp/patch-second-variation-evidence/14-frozen-targets.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartPatchSecondVariation.uniformMappedGeodesicEquation_of_constantCurvature`
/tmp/patch-second-variation-evidence/14-frozen-targets.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartPatchSecondVariation.uniformEndpointReanchoring_of_constantCurvature`
/tmp/patch-second-variation-evidence/14-frozen-targets.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartPatchSecondVariation.exists_onCompact`
/tmp/patch-second-variation-evidence/14-frozen-targets.lean:5:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartPatchSecondVariation.exists_radii`
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartPatchSecondVariation.lean
git diff --check
git diff d1a10d376fd432458fb791259c60dc9fd7d5d5c0 --check
```

The token scan exits 1 with no matches. Both whitespace checks exit 0 with no
output. The proof diff is preserved as `proof.diff` and is reproducible with:

```sh
git diff d1a10d376fd432458fb791259c60dc9fd7d5d5c0 f13ece96 -- Poincare/Global/FixedChartPatchSecondVariation.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartPatchSecondVariation.lean
```

The next proof task is to establish `AugmentedSystemRegularity C` on the
original retained interval, before attempting the supplied inverse-map and
mapped-geodesic steps.
