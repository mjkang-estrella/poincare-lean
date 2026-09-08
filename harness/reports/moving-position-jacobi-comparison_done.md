# Moving-position Jacobi comparison proved

Date: 2026-09-08. Branch: `worker/moving-position-jacobi-comparison`.
Base: `b21c171adea6827143f56c3c2e18d06fa1628ca7`.
Verified proof head: `229e19cda7bb692abf53bc6a3c4d8992ad4cc84e`.

All four requested conclusions are proved in the namespace
`Poincare.FixedChartMovingPositionJacobi`:

- `movingInitialPositionJacobiComparison` inhabits the exact landed
  `FixedChartUniformJacobiComparison.MovingInitialPositionJacobiComparison g`.
- `uniformNonzeroMetricPullback` discharges the exact landed nonzero interface
  through `target_of_movingInitialPositionJacobiComparison`.
- `uniformDifferentialPullback_of_constantCurvature` gives the original uniform
  differential pullback on the prescribed compact anchor sets.
- `exists_radius` gives the frozen task-8 `OnCompact` conclusion.

There is no remaining Jacobi premise or resisting definition in this file.
The comparison itself needs no compactness or connectedness; the uniform
consequences retain the landed instance context. The result awaits independent
orchestrator review. It does not assert H1, H2, sphere recognition, or the
Poincare conjecture beyond these precise frozen conclusions.

Only the new `Poincare/Global/FixedChartMovingPositionJacobi.lean` and this
report are changed. No existing Lean file or `Poincare.lean` was edited.
The assigned isolated worker branch was retained. No merge, task acceptance,
ledger change, root integration, or infrastructure action was performed.
The task's one-module/report scope was used; dated handoff facts and the next
review command are recorded here rather than editing `HANDOFF.md`.

## Mathematical content

The flow arguments retain arbitrary initial states in the original patch
ball, including their moving initial position. They preserve the full
`Icc (-C.T) C.T` interval and its endpoints. `flow_mem_target_cutoffOne`
uses the retained position control and cutoff support to prove target and
neighborhood cutoff-one membership. Speed is constant on the open interval;
continuity extends it to the closed endpoints. This proves both blended-metric
and chart-metric speed preservation.

`perturbed_flow_speed_eq_initial` supplies the Gauss lemma's eventual speed
identity for nearby initial velocities. `velocityVariation_hasDerivAt`
identifies each actual velocity variation with the arbitrary supplied
fundamental solution using the earlier full-time flow derivative theorem.
The integrated Gauss lemma then proves `transverse_orthogonal`, including both
closed endpoints. All its speed, variation, and metric-differentiability
premises are discharged. The lower-level norm lemma is actually named
`JacobiNormClose.chart_linearized_state_feeds_speed_norm_system_at`.

For `gamma = C.alpha (z,v)`, `Psi(t) = Phi(t)(0,w)`, and initial orthogonality
`B(v,w)=0`, put

```text
B = chartMetric g.inner x0 z
J(t) = Psi(t).1
D(t) = Psi(t).2 + Gamma(gamma(t).1)(gamma(t).2,J(t))
A(t) = G(t)(J(t),J(t))
b(t) = G(t)(J(t),D(t))
c(t) = G(t)(D(t),D(t))
```

Here `G` is the blended chart metric, equal to the chart metric on this patch.
`transverse_normSystem` proves exactly

```text
(A', b', c') = (2*b, c - speed^2*A, -2*speed^2*b)
```

at every interior time, from the initial speed `B(v,v)=speed^2` and initial
orthogonality alone. `normSystem_eq_pinned` applies global Lipschitz ODE
uniqueness for this constant linear operator. It needs no Picard radius or
smallness bound. `transverse_norms_eq_pinned` identifies the actual triple,
through both endpoints, with

```text
q = B(w,w)
A(t) = sin(speed*t)^2 / speed^2 * q
b(t) = sin(speed*t)*cos(speed*t) / speed * q
c(t) = cos(speed*t)^2 * q
```

for nonzero speed. Thus the sine factor is derived from the scalar equations.

The radial proof does not use the old selected exponential or a fixed-anchor
ray theorem. `radial_state_hasDerivAt` differentiates the time-dilation state

```text
R(t) = (t * velocity(t), velocity(t) + t * acceleration(t))
```

and checks its exact linearized geodesic equation. Bounded continuous
coefficients and ODE uniqueness identify this state with the fundamental
solution applied to `(0,v)`. Consequently
`radial_position_eq_time_smul_velocity` proves
`(Phi(t)(0,v)).1 = t * velocity(t)` on the entire retained interval.

`pairing_of_radial_transverse` splits each input `a` as
`c*v + (a-c*v)`, with `c=B(a,v)/B(v,v)`. It proves the transverse component is
orthogonal and uses bilinearity and polarization to assemble all pairings.
After applying the patch's inverse-time input normalization,
`normalized_pairing_formula` proves the exact endpoint identity

```text
speed^2 = B(v,v), speed != 0
kappa = sin(speed)^2 / speed^2
G(endpoint)(J(a),J(a')) =
  kappa*B(a,a') + (1-kappa)*B(a,v)*B(a',v)/B(v,v)
```

This equals `B(a_rad,a'_rad) + kappa*B(a_perp,a'_perp)`.
Both radial and transverse time factors cancel separately. Source and sphere
therefore keep their independent positive times `C.T` and `D.T`.

All these patch lemmas apply to the source and round sphere. The final
comparison uses the proved round-sphere curvature witness and
`FixedChartLocalSuccessorExistence.linear_metric` for every anchor pairing.
For nonzero velocity it chooses the common positive square-root speed; all
terms in the two normalized formulas agree. At zero velocity,
`normalized_zero_velocity` proves stationary flow and identity normalized
position variations. There is no division-by-zero branch left implicit.

## Proof commits and direct checks

Each of the 18 theorem additions was compiled successfully before its commit:

```text
2c3a1853 Retain chart target and cutoff-one membership along moving-position flows
25e929c1 Prove constant speed through both retained flow endpoints
a268e75f Transfer retained speed preservation to the moving chart metric
0eba3c57 Supply perturbed-flow speed identity for moving-position Gauss variations
c5cfa4be Identify moving-position velocity variations with arbitrary fundamental solutions
d5e1a883 Propagate moving-position transverse orthogonality through retained endpoints
c8eda6b6 Feed moving-position transverse variations into the curvature-one norm system
66e60474 Integrate the scalar Jacobi norm system without a short-time bound
a05b1a77 Identify the actual moving-position transverse norms with full-time sine solutions
b3275659 Construct the radial Jacobi state by differentiating geodesic time dilation
36728d9f Identify full-time radial Jacobi transport for arbitrary patch initial positions
7a928d2a Assemble arbitrary pairings from radial and transverse metric blocks
b60848d7 Derive the normalized moving-anchor Jacobi pairing formula with independent patch times
4b6663ee Close normalized Jacobi variations at zero initial velocity
237d97a4 Prove the frozen moving-initial-position Jacobi pairing comparison
fc093f05 Discharge the uniform nonzero metric pullback target
5d83b0ef Derive uniform differential pullback from constant curvature
229e19cd Prove the frozen compact uniform-radius consequence

```

Cumulative direct elaboration command:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartMovingPositionJacobi.lean
```

Final direct output, recorded in `30-radius-consequence.log`:

```text

EXIT=0

```

Successful intermediate outputs are retained in `02`, `04`, `06`, `07`, `09`,
`12`, `13`, `14`, `16`, `18`, `20`, `22`, `23`, `24`, `25`, `26`, `27`, `28`,
`29`, and `30` logs in the evidence directory. Later checks remove the transient
linter warnings. Final direct elaboration has no warnings.

## Focused build and axiom checks

Exact command:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/moving-position-jacobi-comparison Poincare.Global.FixedChartMovingPositionJacobi Poincare.FixedChartMovingPositionJacobi.flow_mem_target_cutoffOne Poincare.FixedChartMovingPositionJacobi.flow_speed_eq_initial Poincare.FixedChartMovingPositionJacobi.flow_chartMetric_speed_eq_initial Poincare.FixedChartMovingPositionJacobi.perturbed_flow_speed_eq_initial Poincare.FixedChartMovingPositionJacobi.velocityVariation_hasDerivAt Poincare.FixedChartMovingPositionJacobi.transverse_orthogonal Poincare.FixedChartMovingPositionJacobi.transverse_normSystem Poincare.FixedChartMovingPositionJacobi.normSystem_eq_pinned Poincare.FixedChartMovingPositionJacobi.transverse_norms_eq_pinned Poincare.FixedChartMovingPositionJacobi.radial_state_hasDerivAt Poincare.FixedChartMovingPositionJacobi.radial_position_eq_time_smul_velocity Poincare.FixedChartMovingPositionJacobi.pairing_of_radial_transverse Poincare.FixedChartMovingPositionJacobi.normalized_pairing_formula Poincare.FixedChartMovingPositionJacobi.normalized_zero_velocity Poincare.FixedChartMovingPositionJacobi.movingInitialPositionJacobiComparison Poincare.FixedChartMovingPositionJacobi.uniformNonzeroMetricPullback Poincare.FixedChartMovingPositionJacobi.uniformDifferentialPullback_of_constantCurvature Poincare.FixedChartMovingPositionJacobi.exists_radius

```

Actual output:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartMovingPositionJacobi.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartMovingPositionJacobi ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3611/3611] Built Poincare.Global.FixedChartMovingPositionJacobi (5.7s)
Build completed successfully (3611 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=18 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartMovingPositionJacobi.flow_mem_target_cutoffOne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.flow_speed_eq_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.flow_chartMetric_speed_eq_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.perturbed_flow_speed_eq_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.velocityVariation_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.transverse_orthogonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.transverse_normSystem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.normSystem_eq_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.transverse_norms_eq_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.radial_state_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.radial_position_eq_time_smul_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.pairing_of_radial_transverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.normalized_pairing_formula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.normalized_zero_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.movingInitialPositionJacobiComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.uniformNonzeroMetricPullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.uniformDifferentialPullback_of_constantCurvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartMovingPositionJacobi.exists_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
=== GATE: PASS ===

EXIT=0

```

The focused build passes with 3611 jobs. All 18 named theorem closures are
exactly `[propext, Classical.choice, Quot.sound]`; the module-wide scan checks
all 18 declarations and finds no nonstandard dependencies. The build warning
is from an unchanged imported file.

## Exact conclusions and final checks

The scratch probe explicitly assigns each new theorem to its full frozen
conclusion, without a Jacobi hypothesis. Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/moving-position-jacobi-comparison-evidence/exact-targets.lean
```

Actual output:

```text
EXACT_TARGETS_OK: all four frozen conclusions have unconditional inhabitants

EXIT=0

```

Checks at the verified proof head before adding this report:

```text
$ rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartMovingPositionJacobi.lean
EXIT=1

$ git diff --check
EXIT=0

$ git diff b21c171adea6827143f56c3c2e18d06fa1628ca7 --check
EXIT=0

$ git status --short --branch
## worker/moving-position-jacobi-comparison
EXIT=0

$ lake env lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
EXIT=0


```

The token scan exits 1 because it finds no matches. Both whitespace checks
pass and the assigned branch was clean at the verified proof head.
Root audits and root import changes belong to orchestrator integration and
were not run by this worker.

## Failed attempts and evidence

All raw compiler outputs, the exact-target probe, the capture wrapper, and the
final proof diff are retained under
`/tmp/moving-position-jacobi-comparison-evidence/`.
The wrapper `run.py` records the subprocess output and actual exit status.
No failed attempt was committed as verified.

| Failed log | Resolved issue |
| --- | --- |
| `03-speed.log` | `closure_Ioo` needs distinct endpoints, expressed with `≠`. |
| `05-chart-speed.log` | The metric abbreviation needed explicit unfolding before rewriting. |
| `08-variation.log` | Bare numeral zero inferred natural scalars; typed real zeros and normalized the composition point. |
| `10-gauss.log`, `11-gauss.log` | Inference timed out at 200000 and 1200000 heartbeats. Explicit flow, state, interval, and variation arguments resolved it in `12`. |
| `15-transverse-integration.log` | The constant input pair required `(0 : E)` to fix its first component type. |
| `17-radial-state.log` | `convert` generated only the derivative equality; removed an incorrect reflexivity branch. |
| `19-radial-transport.log` | The Lipschitz constant comparison uses `weaken`, not `mono`; also made the coefficient coercion explicit. |
| `21-block-algebra.log` | The transverse pairing goal needed ring normalization after clearing denominators. |

Representative actual failed output:

```text
Poincare/Global/FixedChartMovingPositionJacobi.lean:386:27: error: unsolved goals
B G : E →L[ℝ] E →L[ℝ] ℝ
J : E →L[ℝ] E
v : E
κ : ℝ
hB : ∀ (a b : E), (B a) b = (B b) a
hG : ∀ (a b : E), (G a) b = (G b) a
hv : (B v) v ≠ 0
hr : (G (J v)) (J v) = (B v) v
ho : ∀ (w : E), (B v) w = 0 → (G (J w)) (J v) = 0
hn : ∀ (w : E), (B v) w = 0 → (G (J w)) (J w) = κ * (B w) w
a✝ b a : E
c : ℝ := (B a) v / (B v) v
w : E := a - c • v
⊢ (B a) v * (1 - 1) = 0

EXIT=1

```

The verified final diff is `proof.diff`, reproduced by:

```sh
git diff b21c171adea6827143f56c3c2e18d06fa1628ca7 229e19cda7bb692abf53bc6a3c4d8992ad4cc84e -- Poincare/Global/FixedChartMovingPositionJacobi.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartMovingPositionJacobi.lean
```

Then rerun the recorded focused gate and inspect the diff from the recorded
base. All requested worker conclusions are proved; integration and acceptance
remain with the orchestrator.
