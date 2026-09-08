# Uniform fixed-chart normal radius: done

Date: 2026-09-08. Branch: `worker/uniform-normal-radius`.
Base: `41cfdfd2007e4dc0faed5e0a67641ae435f65019`.
Verified proof head: `2cb7348ebb797b4caaa25704d42444971b637af7`.

## Result

All four requested steps are proved in
`Poincare/Global/FixedChartUniformNormalRadius.lean`, namespace
`Poincare.FixedChartUniformNormalRadius`. The file contains 11 theorems.

- `flow_zero_velocity` proves stationarity on the full closed time interval by
  ODE uniqueness on a compact trajectory tube.
- `linearized_zero_velocity` computes the field derivative as `(u,w) ↦ (w,0)`.
  `fundamentalSolution_zero_velocity` and
  `flow_fundamentalSolution_zero_velocity` prove
  `Φ (z,0) t = freeVariation t`, where
  `freeVariation t (u,w) = (u + t • w,w)`.
- `hasFDerivAt_F_at_zero_velocity` gives the derivative
  `endpointDerivative T (u,w) = (u,u + T • w)`.
  `endpointEquiv T hT` has inverse `(a,b) ↦ (a,T⁻¹ • (b-a))`.
  `hasStrictFDerivAt_F` upgrades this derivative using the supplied C1 endpoint.
- `uniform_normal_radius_near` constructs an open partial homeomorphism whose
  function is exactly `F α T`. Its source `W` contains `(z,0)`, stays in the
  original open state ball, and stays within any prescribed velocity bound
  `R > 0`. It contains `ball z ρ ×ˢ ball 0 ρ` for a positive `ρ`. Every anchor
  `y ∈ ball z ρ` has injectivity on `ball 0 ρ` and
  `ball y ρ ⊆ expChart α T y '' ball 0 R`.
- `exists_uniform_normal_radius_on_compact` proves, for any compact
  `K ⊆ ball c r` and any prescribed `R > 0`,

  ```lean
  ∃ ρ > (0 : ℝ), ∀ z ∈ K,
    InjOn (expChart α T z) (ball (0 : E) ρ) ∧
    ball z ρ ⊆ expChart α T z '' ball (0 : E) R
  ```

  The proof takes a finite subcover of the local anchor balls and a positive
  common lower bound for their radii. Here `R` is the task's `ρ'`.
- `exists_uniform_local_geodesic_chart_flow_normal_neighborhoods` applies all
  this to the exact selector produced by
  `GeodesicFlowJointDerivative.exists_uniform_local_geodesic_chart_flow_initialState_C1`.
  It retains the supplied position neighborhood `U`, the closed-ball ODE
  package, joint continuity, C1 endpoint, strict derivative, local inverse
  neighborhoods, and compact radius conclusion. No derivative, inverse, or
  radius premise remains in this existence theorem.

The compact anchor region is the open initial-position ball of the supplied
uniform flow. No assertion extends this selector to arbitrary compact sets
outside that ball. No identification with `expAt`, H1/H2, sphere recognition,
or the Poincare conjecture is claimed. No existing Lean file or root import
was changed. This worker result awaits orchestrator review; no merge or task
acceptance was performed.

## Verification

Commands were run with `LEAN_NUM_THREADS=1` for Lean and Lake.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformNormalRadius.lean
```

Exit code 0; output empty.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformNormalRadius
```

Exit code 0. Final output:

```text
✔ [3259/3259] Built Poincare.Global.FixedChartUniformNormalRadius (4.0s)
Build completed successfully (3259 jobs).
```

The build replayed warnings from unchanged dependencies. There were no warnings
from the new module. Full output is retained at
`/tmp/uniform-normal-radius-evidence/build.log`.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-normal-radius-evidence/axioms.lean
```

Exit code 0. The probe prints every new theorem's closure and scans every
noninternal declaration owned by the new module using `Lean.collectAxioms`.
Actual output:

```text
'Poincare.FixedChartUniformNormalRadius.flow_zero_velocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformNormalRadius.linearized_zero_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.fundamentalSolution_zero_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.uniform_normal_radius_near_of_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.exists_uniform_normal_radius_on_compact_of_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.flow_fundamentalSolution_zero_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.hasFDerivAt_F_at_zero_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.hasStrictFDerivAt_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformNormalRadius.uniform_normal_radius_near' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.exists_uniform_normal_radius_on_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformNormalRadius.exists_uniform_local_geodesic_chart_flow_normal_neighborhoods' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
GATE_SCAN declarations=19 nonstandard=[]
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartUniformNormalRadius.lean
git diff --check
```

The token scan returned exit code 1 with empty output, meaning no matches.
The diff check returned exit code 0 with empty output.
Raw commands, exit codes, and outputs are in
`/tmp/uniform-normal-radius-evidence/checks.json`.
Root integration audits were left to the orchestrator as required.

## Commits

```text
26870e98 Prove fixed-chart zero-velocity flow is stationary
ec0db9dd Compute the full zero-velocity fundamental solution
294419e9 Prove the joint exponential derivative and strict differentiability
e28172b9 Derive uniform fiber neighborhoods by joint inversion and compactness
d74a53cf Prove local and compact normal radii for the supplied geodesic flow
2cb7348e Instantiate uniform normal radii on the fixed-chart PL selector
```

## First action for independent review

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformNormalRadius
```

The next mathematical task is to construct the chart exponential family from
these joint inverse neighborhoods. It does not require identifying this flow
with the old per-anchor selectors.

## Preserved failed compiler attempts

All direct-check logs `01-lean.log` through `12-lean.log` remain under
`/tmp/uniform-normal-radius-evidence/`. The nonempty failed outputs are copied
below so the evidence also survives in this committed report. All errors were
elaboration or tactic issues resolved before the final checks.

### 02-lean.log

```text
Poincare/Global/FixedChartUniformNormalRadius.lean:83:63: error: Application type mismatch: The argument
  p
has type
  E
but is expected to have type
  E × E
in the application
  (Φ u) p
Poincare/Global/FixedChartUniformNormalRadius.lean:84:14: error: Application type mismatch: The argument
  p
has type
  E
but is expected to have type
  E × E
in the application
  (Φ s) p
Poincare/Global/FixedChartUniformNormalRadius.lean:86:40: error: Application type mismatch: The argument
  hasDerivWithinAt_const s (Icc (-T) T) p
has type
  HasDerivWithinAt (fun x => p) 0 (Icc (-T) T) s
but is expected to have type
  HasDerivWithinAt ?m.240 ?m.241 (Icc (-T) T) s
in the application
  HasDerivWithinAt.clm_apply (hd s hs) (hasDerivWithinAt_const s (Icc (-T) T) p)
Poincare/Global/FixedChartUniformNormalRadius.lean:88:26: error: Application type mismatch: The argument
  p
has type
  E
but is expected to have type
  E × E
in the application
  (freeVariation s) p
Poincare/Global/FixedChartUniformNormalRadius.lean:87:61: error: Application type mismatch: The argument
  p
has type
  E
but is expected to have type
  E × E
in the application
  (freeVariation u) p
```

### 04-lean.log

```text
Poincare/Global/FixedChartUniformNormalRadius.lean:141:60: error(lean.unknownIdentifier): Unknown identifier `hΓ`
Poincare/Global/FixedChartUniformNormalRadius.lean:141:64: error(lean.unknownIdentifier): Unknown identifier `hT`
Poincare/Global/FixedChartUniformNormalRadius.lean:142:5: error(lean.unknownIdentifier): Unknown identifier `hα`
Poincare/Global/FixedChartUniformNormalRadius.lean:142:22: error(lean.unknownIdentifier): Unknown identifier `hα`
Poincare/Global/FixedChartUniformNormalRadius.lean:140:54: error: unsolved goals
E : Type u_1
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedSpace ℝ E
inst✝ : FiniteDimensional ℝ E
Φ : E × E → ℝ → E × E →L[ℝ] E × E
c z : E
r T : ℝ
hz : (z, 0) ∈ ball (c, 0) r
⊢ ∀ t ∈ Icc (-T) T, Φ (z, 0) t = freeVariation t
Poincare/Global/FixedChartUniformNormalRadius.lean:150:53: error(lean.unknownIdentifier): Unknown identifier `hΓ`
Poincare/Global/FixedChartUniformNormalRadius.lean:150:56: error(lean.unknownIdentifier): Unknown identifier `hT`
Poincare/Global/FixedChartUniformNormalRadius.lean:150:59: error(lean.unknownIdentifier): Unknown identifier `hα`
Poincare/Global/FixedChartUniformNormalRadius.lean:149:57: error: unsolved goals
E : Type u_1
inst✝² : NormedAddCommGroup E
inst✝¹ : NormedSpace ℝ E
inst✝ : FiniteDimensional ℝ E
α : E × E → ℝ → E × E
c z : E
r T : ℝ
hz : (z, 0) ∈ ball (c, 0) r
⊢ HasFDerivAt (F α T) (endpointDerivative T) (z, 0)
Poincare/Global/FixedChartUniformNormalRadius.lean:165:36: error(lean.unknownIdentifier): Unknown identifier `hΓ`
```

### 05-lean.log

```text
Poincare/Global/FixedChartUniformNormalRadius.lean:159:2: error: No goals to be solved
```

### 07-lean.log

```text
Poincare/Global/FixedChartUniformNormalRadius.lean:189:17: error: Type mismatch
  hd
has type
  HasStrictFDerivAt (F α T) (endpointDerivative T) (z₀, 0)
but is expected to have type
  HasStrictFDerivAt (F α T) ?m.165 (z₀, 0)
```

### 08-lean.log

```text
Poincare/Global/FixedChartUniformNormalRadius.lean:188:38: error: Type mismatch
  endpointEquiv T ⋯
has type
  (?m.158 × ?m.158) ≃L[ℝ] ?m.158 × ?m.158
but is expected to have type
  E × E →L[ℝ] E × E
```
