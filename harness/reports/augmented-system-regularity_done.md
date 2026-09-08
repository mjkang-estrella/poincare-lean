# Augmented system regularity: full-time C1 and full-ball C2

Date: 2026-09-08. Branch: `worker/augmented-system-regularity`.
Base: `2992f59d30aec3c1769b1eec27288e06f1b9af22`.
Verified proof head: `3347f3e5`.
Worktree: `/private/tmp/poincare-workers/augmented-system-regularity`.

## Result and scope

Both frozen targets are proved in namespace
`Poincare.FixedChartAugmentedSystemRegularity`:

```lean
theorem augmentedSystemRegularity
    {x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    FixedChartPatchSecondVariation.AugmentedSystemRegularity C

theorem patch_endpoint_contDiffOn_two
    {x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    ContDiffOn ℝ 2 (fun q => C.α q C.T)
      (ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
```

The existing definition is imported verbatim. The endpoint theorem uses the
existing `target_of_augmentedSystemRegularity`. Neither `C.T`, the retained
state ball, nor `C.α` changes. No curvature hypothesis is added.

Exactly one new Lean file was added,
`Poincare/Global/FixedChartAugmentedSystemRegularity.lean`.
No existing Lean file or `Poincare.lean` changed. This report and a dated
`HANDOFF.md` entry record the result. The worker has not merged or marked the
task accepted. The mapped-geodesic equation, H1/H2, and recognition are outside
this task and are not claimed here.

## Mathematical proof

`exists_flow_initialState_C1_full_interval` proves a general prescribed-time
C1 theorem for a C2 vector field and a supplied flow in a compact state tube.
For each initial state, the derivative of the field along its trajectory is
continuous on the closed time interval. The existing finite-step linear
continuation theorem `exists_fundamentalSolution_on_Icc` constructs its
fundamental solution on that exact interval. Compactness supplies the needed
coefficient bounds inside the continuation theorem. The general
`flow_hasFDerivAt_initialState` identifies this operator solution as the actual
initial-state derivative on both halves of the interval, including endpoints.
`continuousOn_fundamentalSolution` gives joint operator-norm continuity, hence
C1 dependence. No smallness constraint on the retained time is introduced.

`flow_contDiffOn_one_full_interval` extends this result to any open domain of
initial states with a jointly continuous supplied flow. Around each point,
a closed ball contained in the open domain has compact product with the full
time interval. Its continuous image bounds the trajectory tube. The first
theorem applies on the interior of this closed ball, proving C1 at the chosen
point. Since the point is arbitrary, the conclusion holds on the entire
original open domain. Local balls are proof neighborhoods, not a replacement
for the retained ball in either target.

`exists_patch_operatorAugmentedFlow` takes the full-time Φ from
`exists_patch_fundamentalSolution` and constructs the actual augmented flow

```lean
β y t = (C.α y.1 t, (Φ y.1 t).comp y.2)
```

on the open domain `ball p C.r ×ˢ univ` of full augmented initial states.
The existing augmented ODE lemma proves its flow law for every initial
operator. Joint continuity follows from the joint continuity of α and Φ and
continuous operator composition.

The Φ API only provides joint continuity over the open base ball, so taking
a compact image of its entire closed-ball boundary would be unjustified.
The open-domain theorem supplies valid compact neighborhoods inside that ball
instead. It applies with
`X := (E × E) × ((E × E) →L[ℝ] (E × E))` and the proved C2 augmented field.
Restriction along `q ↦ (q, id)` gives the exact augmented regularity target.
The existing second-variation reduction then proves the exact C2 endpoint.

## Individually verified proof commits

Every successful row ran exactly:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartAugmentedSystemRegularity.lean
```

All successful compiler logs are empty, with exit 0. The command wrapper
printed `LEAN_EXIT=0`.

| Commit | Theorem | Compiler log |
| --- | --- | --- |
| `be09fb4d` | `exists_flow_initialState_C1_full_interval` | `01-full-interval.log` |
| `6e08a2f2` | `flow_contDiffOn_one_full_interval` | `02-open-set.log` |
| `ce1ac05f` | `exists_patch_operatorAugmentedFlow` | `04-augmented-flow.log` |
| `d72ab4c3` | `augmentedSystemRegularity` | `05-regularity.log` |
| `3347f3e5` | `patch_endpoint_contDiffOn_two` | `06-endpoint.log` |

Evidence directory: `/tmp/augmented-system-regularity-evidence/`.
The failed first lift-continuity attempt is retained as
`03-augmented-flow.log`, Lean exit 1:

```text
Poincare/Global/FixedChartAugmentedSystemRegularity.lean:128:45: error: Invalid projection: Type of
  hyt
is not known; cannot resolve projection `1`
Poincare/Global/FixedChartAugmentedSystemRegularity.lean:128:54: error: Invalid projection: Type of
  hyt
is not known; cannot resolve projection `2`
```

Giving `Continuous.continuousOn` its explicit product domain resolved that
elaboration ambiguity. The corrected file compiled before its commit.

## Focused build and dependency gate

Exact command:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/augmented-system-regularity Poincare.Global.FixedChartAugmentedSystemRegularity Poincare.FixedChartAugmentedSystemRegularity.exists_flow_initialState_C1_full_interval Poincare.FixedChartAugmentedSystemRegularity.flow_contDiffOn_one_full_interval Poincare.FixedChartAugmentedSystemRegularity.exists_patch_operatorAugmentedFlow Poincare.FixedChartAugmentedSystemRegularity.augmentedSystemRegularity Poincare.FixedChartAugmentedSystemRegularity.patch_endpoint_contDiffOn_two
```

Exit 0. Actual output, preserved in `07-gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartAugmentedSystemRegularity.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartAugmentedSystemRegularity ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3615/3615] Built Poincare.Global.FixedChartAugmentedSystemRegularity (3.3s)
Build completed successfully (3615 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=5 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartAugmentedSystemRegularity.exists_flow_initialState_C1_full_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartAugmentedSystemRegularity.flow_contDiffOn_one_full_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartAugmentedSystemRegularity.exists_patch_operatorAugmentedFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartAugmentedSystemRegularity.augmentedSystemRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartAugmentedSystemRegularity.patch_endpoint_contDiffOn_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is from an unchanged dependency. All five module declarations
have only standard dependencies. A parser of the five named closure outputs
also confirmed `EXACT_STANDARD_CLOSURES=5/5`, recorded in
`09-exact-closures.log`.

The gate runs `lake build Poincare.Global.FixedChartAugmentedSystemRegularity`.
No root build or root integration audit was run by this worker.

## Exact target probes, token scan, and diff

`08-targets.lean` contains two `example` declarations with the exact frozen
types, discharged solely by the two new unconditional theorem names, plus
`#print axioms` on both names.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/augmented-system-regularity-evidence/08-targets.lean
```

Exit 0. Actual output:

```text
'Poincare.FixedChartAugmentedSystemRegularity.augmentedSystemRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartAugmentedSystemRegularity.patch_endpoint_contDiffOn_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartAugmentedSystemRegularity.lean
git diff --check
git diff 2992f59d30aec3c1769b1eec27288e06f1b9af22 --check
```

The token scan exits 1 with no matches. Both whitespace checks exit 0 with no
output. The proof diff is preserved as `proof.diff` and is reproducible with:

```sh
git diff 2992f59d30aec3c1769b1eec27288e06f1b9af22 3347f3e5 -- Poincare/Global/FixedChartAugmentedSystemRegularity.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartAugmentedSystemRegularity.lean
```
