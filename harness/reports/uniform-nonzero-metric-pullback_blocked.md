# Uniform nonzero metric pullback: verified full-time variations, geometric comparison blocked

Date: 2026-09-08. Branch: `worker/uniform-nonzero-metric-pullback`.
Base: `72d1541fd86973c317c89fd5a5c22798b887744b`.
Verified proof head: `b4424f74`.

Step 1 is proved for the actual source patch and, by the same generic theorem,
the round-sphere patch. The moving-position curvature Jacobi pairing identity
in step 2 is unproved. The frozen `uniformNonzeroMetricPullback` and its two
unconditional consequences are not declared. This worker result awaits
independent orchestrator review; it does not complete task 8, H1, H2, or sphere
recognition.

Only `Poincare/Global/FixedChartUniformJacobiComparison.lean` and this report
are changed. No existing Lean file, root import, task, ledger, or audit wiring
is changed. The explicit worker scope overrides the general instruction to
update `HANDOFF.md`. The assigned isolated worker branch is retained. No merge
or acceptance was performed.

## Verified progress

`flow_hasFDerivAt_of_fundamentalSolution` proves derivative identification at
every time in the closed interval, including the retained endpoint `C.T`.
It uses the existing full-interval Grönwall residual theorem. It removes the
strict-interior restriction of the public geodesic derivative theorem without
changing that existing file.

`coordinateEndpoint_fderiv` identifies the canonical derivative of the actual
supplied coordinate exponential with the position component of the derivative
of `q ↦ C.α q C.T`. It uses endpoint C1, the actual open endpoint source, the
fixed-chart cancellation law, and the velocity map `v ↦ C.T⁻¹ • v`.

`coordinateEndpoint_fderiv_of_fundamentalSolution` then proves, on that exact
source,

```lean
fderiv ℝ ((C.endpoint x).trans (chartAt E x₀)) v a =
  (Φ C.T (0, C.T⁻¹ • a)).1
```

Here the coefficient curve is the linearized fixed-chart field along
`C.α (extChartAt I x₀ x, C.T⁻¹ • v)`. The moving position is retained. The
inverse-time input is necessary: the unnormalized position variation has
initial derivative `C.T⁻¹ • a`. `normalizedJacobiField_initialData` proves
that `t ↦ (Φ (C.T * t) (0, C.T⁻¹ • a)).1` has initial value zero and initial
derivative exactly `a`.

The fundamental solution is now constructed on the **whole retained interval**.
`hasDerivAt_glue` joins matching solutions. `exists_linearODE_on_Icc` continues
bounded continuous linear equations by finitely many short Picard intervals,
with ordinary derivatives agreeing at each join. The symmetric-interval
lemma extends a continuous coefficient by interval projection, solves the
positive and reflected negative equations, and joins them at zero.
`exists_fundamentalSolution_on_Icc` applies this to the operator equation.
There is no coefficient-times-interval smallness hypothesis.

`exists_patch_fundamentalSolution` applies this construction to the actual
`C.α`, for every initial state in the original open state ball. It proves:

- identity initial operator;
- the full linearized operator ODE on `Icc (-C.T) C.T`;
- full-state `HasFDerivAt` at every time, including both endpoints;
- joint operator-norm continuity in initial state and time.

No fresh flow replaces `C.α`; no smaller time replaces `C.T`. Compactness of
the retained flow image supplies its bounded state tube. The existing
Gronwall continuity theorem then applies over the full interval. This closes
the discarded-fundamental-solution and endpoint-continuation issues identified
in the previous worker report.

## One exact resisting definition

The only new proposition definition is the following full-time Jacobi pairing
comparison. It quantifies over actual endpoint-source velocities and arbitrary
fundamental solutions satisfying their exact ODEs. It uses neither canonical
exponential derivatives nor manifold normal vectors. All the fundamental
solutions it needs are now constructed above.

```lean
def MovingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ x ∈ C.anchors, ∀ p ∈ D.anchors,
  ∀ (L : CartanMap.TangentAlignment g x p) (v : E),
    let l := linear (patch C D) ⟨x, p, L⟩
    let qs : E × E := (extChartAt I x₀ x, C.T⁻¹ • v)
    let qt : E × E := (extChartAt I p₀ p, D.T⁻¹ • l v)
    v ∈ (C.endpoint x).source → l v ∈ (D.endpoint p).source →
    ∀ (Φs Φt : ℝ → (E × E) →L[ℝ] (E × E)),
      Φs 0 = ContinuousLinearMap.id ℝ (E × E) →
      (∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φs
        ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
          (C.α qs t)).comp (Φs t)) (Icc (-C.T) C.T) t) →
      Φt 0 = ContinuousLinearMap.id ℝ (E × E) →
      (∀ t ∈ Icc (-D.T) D.T, HasDerivWithinAt Φt
        ((linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 p₀)
          (D.α qt t)).comp (Φt t)) (Icc (-D.T) D.T) t) →
      ∀ a a' : E,
        CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ (D.α qt D.T).1
          (Φt D.T (0, D.T⁻¹ • l a)).1 (Φt D.T (0, D.T⁻¹ • l a')).1 =
        CovariantDerivative.chartMetric g.inner x₀ (C.α qs C.T).1
          (Φs C.T (0, C.T⁻¹ • a)).1 (Φs C.T (0, C.T⁻¹ • a')).1
```

This is a domainwise pointwise statement with no radius existential. It is a
stronger sufficient geometric input, not a weakening of the frozen target.
The source and sphere keep their separate retained times. The alignment is
exactly `linear (patch C D) ⟨x, p, L⟩`; its anchor metric law is already
`FixedChartLocalSuccessorExistence.linear_metric`.

`target_of_movingInitialPositionJacobiComparison` derives the exact landed
`FixedChartUniformDifferentialPullback.UniformNonzeroMetricPullback g` from
this single remainder. It constructs both fundamental families, obtains
compact source and target endpoint radii and the compact alignment operator
bound, and uses the uniform small-normal-vector radius. One positive `η` is
chosen before `x,p,L,z,a,a'`. No point-dependent radius is minimized, and no
pointwise generic germ replaces the retained exponential.

The two further consequences have explicitly conditional names:

- `uniformDifferentialPullback_of_movingInitialPositionJacobiComparison`;
- `exists_radius_of_movingInitialPositionJacobiComparison`.

Their conclusions are the original uniform differential interface and the
frozen task-8 `OnCompact` conclusion. They use the landed reductions from the
nonzero metric target, including its already-proved zero-velocity case.

## Why the geometric step remains open

The high-level `RigidityComplete.cartanMap_isLocalIsometry_of_selector_aop_bound`
consumes `EnrichedCascade.BaseCurvePackage` and `LinearizedFamilyPackage`.
Both fix initial position at `extChartAt I x₀ x₀`; the supplied curve starts
at `extChartAt I x₀ x`. They also identify the endpoint with the old selected
exponential, require ordinary time derivatives on a closed interval with a
strict margin, use one common source/target time, and impose a scalar short-time
bound. None of those fields can be copied into the retained moving-position
patch merely by substituting its flow.

The exact initial-position mismatch was probed. Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-nonzero-metric-pullback-evidence/per-anchor-probe.lean
```

Actual output:

```text
/tmp/uniform-nonzero-metric-pullback-evidence/per-anchor-probe.lean:14:2: error: Type mismatch
  (C.flow_law (↑(extChartAt I x₀) x, C.T⁻¹ • v) hq).left
has type
  C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v) 0 = (↑(extChartAt I x₀) x, C.T⁻¹ • v)
but is expected to have type
  C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v) 0 = (↑(extChartAt I x₀) x₀, C.T⁻¹ • v)

LEAN_EXIT=1

```

The lower-level route is mathematically applicable, but has not been completed.
`GeodesicTransport.chart_initialVelocity_integrated_transverse_gauss_orthogonal_chartMetric`
already allows arbitrary `z₀`. It requires speed preservation for the perturbed
flow and chart-metric differentiability along that family. The curvature
contraction in
`coordinateCovariantJacobiSecond_chartChristoffelField_eq_neg_speed_zone`
also allows arbitrary chart points. Its use requires speed and orthogonality
identities along the variation, rather than only at time zero.

`JacobiNormSystem.chart_linearized_state_feeds_speed_norm_system_at` is the
precise lower scalar-ODE input to reuse. It needs the base and variational
ordinary derivatives, target/cutoff membership, speed, orthogonality, and metric
differentiability. The new fundamental family supplies the variational ODE and
interior time derivatives. The geometric Gauss/speed feed and resulting
radial/transverse pairing formula have not been assembled for these moving
initial states. The existing speed-pinned norm comparison also carries
Picard interval bounds and ordinary derivatives at the closed endpoints.
A completion should integrate the scalar comparison on the interior and
extend the pairings to `C.T` by continuity, or prove the equivalent
within-derivative comparison directly. The source and target formulas then
need their separate inverse-time normalizations reconciled via `linear_metric`.

The verified continuation result addresses existence of the linearized family;
it does not establish that curvature metric identity. There is no counterexample
claim. The permitted partial-result stop condition is met by full step 1, the
single exact geometric remainder above, and its checked reduction to the
unchanged frozen target.

## Proof commits and direct checks

```text
628a4e59 Identify retained flow derivatives through the closed time endpoints
2623e965 Identify supplied exponential differentials with retained position variations
2ef94d81 Transfer fundamental solution values to the actual rescaled exponential
7852e3d6 Glue linear solution derivatives at a time boundary
26c3ec38 Continue bounded linear ODE solutions to any finite positive time
d3adae96 Solve continuous linear equations on full prescribed symmetric intervals
915f86dc Construct fundamental solutions without a small-time restriction
56148d52 Reconstruct the joint fundamental solution through every retained patch endpoint
81e6cebd Reduce the uniform metric target to full-time moving-position Jacobi comparison
b460f684 Verify the normalized Jacobi initial value and initial velocity
13272ac5 Derive uniform differential pullback from the Jacobi comparison remainder
b4424f74 Derive the frozen compact radius conclusion from the Jacobi remainder

```

Direct elaboration command for the cumulative new file:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformJacobiComparison.lean
```

Successful logs in the evidence directory are `01-flow.log`,
`03-coordinate.log`, `06-fundamental-endpoint.log`, `08-glue.log`,
`09-positive-continuation.log`, `10-symmetric.log`, `11-full-fundamental.log`,
`12-patch-fundamental.log`, `14-jacobi-reduction.log`, `16-initial-data.log`,
`18-differential-consequence.log`, and `19-radius-consequence.log`.
Each contains empty compiler output followed by `LEAN_EXIT=0`.
The capture wrapper is retained as `run.py`.

## Focused build and dependency gate

Exact invocation:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/uniform-nonzero-metric-pullback Poincare.Global.FixedChartUniformJacobiComparison Poincare.FixedChartUniformJacobiComparison.hasDerivAt_glue Poincare.FixedChartUniformJacobiComparison.exists_linearODE_on_Icc Poincare.FixedChartUniformJacobiComparison.exists_linearODE_on_symmetric_Icc Poincare.FixedChartUniformJacobiComparison.exists_fundamentalSolution_on_Icc Poincare.FixedChartUniformJacobiComparison.flow_hasFDerivAt_of_fundamentalSolution Poincare.FixedChartUniformJacobiComparison.coordinateEndpoint_fderiv Poincare.FixedChartUniformJacobiComparison.coordinateEndpoint_fderiv_of_fundamentalSolution Poincare.FixedChartUniformJacobiComparison.exists_patch_fundamentalSolution Poincare.FixedChartUniformJacobiComparison.normalizedJacobiField_initialData Poincare.FixedChartUniformJacobiComparison.target_of_movingInitialPositionJacobiComparison Poincare.FixedChartUniformJacobiComparison.uniformDifferentialPullback_of_movingInitialPositionJacobiComparison Poincare.FixedChartUniformJacobiComparison.exists_radius_of_movingInitialPositionJacobiComparison

```

Actual output:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartUniformJacobiComparison.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartUniformJacobiComparison ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3610/3610] Built Poincare.Global.FixedChartUniformJacobiComparison (4.0s)
Build completed successfully (3610 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=13 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartUniformJacobiComparison.hasDerivAt_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.exists_linearODE_on_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.exists_linearODE_on_symmetric_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.exists_fundamentalSolution_on_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.flow_hasFDerivAt_of_fundamentalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.coordinateEndpoint_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.coordinateEndpoint_fderiv_of_fundamentalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.exists_patch_fundamentalSolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.normalizedJacobiField_initialData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.target_of_movingInitialPositionJacobiComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.uniformDifferentialPullback_of_movingInitialPositionJacobiComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformJacobiComparison.exists_radius_of_movingInitialPositionJacobiComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===

GATE_EXIT=0

```

All 12 named theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`. The module-wide scan includes the
single resisting definition and finds no nonstandard dependencies.
The new module produced no compiler warnings; the displayed build warning
comes from an unchanged imported file.

## Frozen names and final checks

Command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-nonzero-metric-pullback-evidence/target-names.lean
```

Actual output:

```text
/tmp/uniform-nonzero-metric-pullback-evidence/target-names.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformJacobiComparison.uniformNonzeroMetricPullback`
/tmp/uniform-nonzero-metric-pullback-evidence/target-names.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformJacobiComparison.uniformDifferentialPullback_of_constantCurvature`
/tmp/uniform-nonzero-metric-pullback-evidence/target-names.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformJacobiComparison.exists_radius`

LEAN_EXIT=1

```

These failures are expected for a blocked result. The frozen unconditional
names were not introduced with extra hypotheses.

Actual final source/toolchain checks before adding this report:

```text
$ rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartUniformJacobiComparison.lean
EXIT=1

$ git diff --check
EXIT=0

$ git diff 72d1541fd86973c317c89fd5a5c22798b887744b --check
EXIT=0

$ git status --short --branch
## worker/uniform-nonzero-metric-pullback
EXIT=0

$ lake env lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
EXIT=0


```

The forbidden-token scan exits 1 because there are no matches. Both whitespace
checks pass, and the assigned branch was clean at the verified proof head.

## Failed attempts and retained evidence

All evidence is under `/tmp/uniform-nonzero-metric-pullback-evidence/`.
Failed compiler outputs were retained:

| Log | Resolved issue |
| --- | --- |
| `02-coordinate.log` | The eventual-equality orientation for `HasFDerivAt.congr_of_eventuallyEq`. |
| `04-fundamental-endpoint.log` | A source-domain membership inferred an unreduced rescaling expression; a typed initial state fixed the rewrite. |
| `05-continuation.log` | Piecewise equality simplification, vector-valued scalar composition, and the zero-length induction interval; also retained the endpoint rewrite failure. |
| `13-jacobi-reduction.log` | `intro` bound the frozen target's let-expressions before tangent inputs; explicit let reduction fixed it. |
| `15-initial-data.log` | The scalar composition needed an explicitly normalized `C.T * 0` evaluation point. |

The first endpoint-transfer commit was made before its asynchronous failed
compiler result was inspected. It was corrected and amended after the successful
`06-fundamental-endpoint.log` check; `2ef94d81` is the verified amended commit.
The original failed output is retained. A prose use of the forbidden token
`admit` was also removed from a comment before the final gate.

The complete verified proof diff is `proof.diff`, reproduced by:

```sh
git diff 72d1541fd86973c317c89fd5a5c22798b887744b b4424f74 -- Poincare/Global/FixedChartUniformJacobiComparison.lean
```

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformJacobiComparison.lean
```

Then rerun the recorded focused gate and inspect the diff from the base commit.
The next mathematical action is to prove
`MovingInitialPositionJacobiComparison`, starting with the moving-position
Gauss/constant-speed feed into
`JacobiNormSystem.chart_linearized_state_feeds_speed_norm_system_at` for the
now-constructed full-time fundamental family. Flow construction, endpoint
identification, normalized initial data, and uniform domain radii are proved.
