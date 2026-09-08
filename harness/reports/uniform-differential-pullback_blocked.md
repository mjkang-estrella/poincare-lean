# Uniform differential pullback: blocked after verified differential step

Date: 2026-09-08. Branch: `worker/uniform-differential-pullback`.
Base: `ff85a298a835630b835e5699599db7d4021b0686`.
Verified proof head: `e82a4893`.

Step 1 is proved. The zero-velocity part of step 2 is proved. The nonzero
curvature metric comparison and both unconditional frozen targets are not
proved. This result awaits independent orchestrator review. It does not
complete task 8, H1, H2, or sphere recognition.

Only the new `Poincare/Global/FixedChartUniformDifferentialPullback.lean`
and this report are changed. No existing Lean file, `Poincare.lean`, task,
ledger, audit wiring, or `HANDOFF.md` is changed. The explicit worker file
scope takes precedence over the general handoff-update instruction. The
assigned worker branch is retained; no merge or acceptance was performed.

## Verified progress

`normalizedEndpoint_hasStrictFDerivAt_zero` composes the retained joint
endpoint derivative with time rescaling. Its velocity derivative is the
identity at every retained anchor.

`coordinateEndpoint_eq_normalizedEndpoint` proves equality with the actual
supplied coordinate endpoint on its exact endpoint source. It uses the fixed
chart's right inverse law with the retained target membership.

`normalizedEndpoint_eventually_equiv` derives joint C1 regularity after time
rescaling, continuity of the vertical derivative, and persistence of
invertibility from the identity. Invertibility is the open unit condition
in the continuous endomorphism algebra. The resulting equivalences represent
strict derivatives of the actual velocity slices.

`exists_uniform_coordinateEndpoint_derivative_radius` uses
`IsCompact.eventually_forall_of_forall_eventually` to choose one velocity
ball before the moving anchor. It intersects this ball with the already
verified uniform endpoint-domain radius and transfers derivatives through
the endpoint equality. This theorem applies to both patches, including
empty compact anchor sets.

`exists_uniform_differential_radius` combines those two velocity radii,
the earlier compact framed-alignment operator bound, and the earlier
uniform small-normal-vector radius. Its exact checked signature is:

```lean
theorem exists_uniform_differential_radius {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (K : Set M) (H : Set RoundSphere3)
    (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
        let Q := patch C D
        let v := Q.sourceNormal x z
        ∃ A B : E ≃L[ℝ] E,
          HasStrictFDerivAt (sourceExp Q x) (A : E →L[ℝ] E) v ∧
          HasStrictFDerivAt (targetExp Q p) (B : E →L[ℝ] E)
            (linear Q ⟨x, p, L⟩ v)
```

Thus the supplied source and target exponentials have the required strict
continuous-linear-equivalence derivatives at the actual supplied normal
vector. One radius precedes `x,p,L,z`. No per-anchor radius minimum or
pointwise generic-germ replacement is used. Curvature and cutoff-one
hypotheses are unnecessary for this differential result.

`coordinateEndpoint_hasStrictFDerivAt_zero` transfers the identity derivative
to the actual supplied endpoint. `metric_pullback_zero` then proves the
metric identity at zero, using the two anchor endpoint laws and
`FixedChartLocalSuccessorExistence.linear_metric`.

## One exact resisting definition

The only remaining proposition definition is the following curvature-only
metric assertion in the file's frozen manifold/metric instance context.
It contains no derivative-existence, invertibility, `Data`, or domain premise.
It uses canonical `fderiv` values of the supplied exponentials. The `z ≠ x`
restriction removes only the zero case already proved above.

```lean
def UniformNonzeroMetricPullback (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    letI : MetricSpace M := g.toMetricSpace
    ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η → z ≠ x →
        let Q := patch C D
        let v := Q.sourceNormal x z
        let l := linear Q ⟨x, p, L⟩
        ∀ a a' : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (targetExp Q p (l v))
            (fderiv ℝ (targetExp Q p) (l v) (l a))
            (fderiv ℝ (targetExp Q p) (l v) (l a')) =
          CovariantDerivative.chartMetric g.inner x₀ (sourceExp Q x v)
            (fderiv ℝ (sourceExp Q x) v a) (fderiv ℝ (sourceExp Q x) v a')

```

This is an unproved proposition, not a new assumption inserted into either
frozen target name. Its single positive radius still precedes all moving
anchors, alignments, successor points, and tangent inputs.

`uniformDifferentialPullback_of_uniformNonzeroMetricPullback` intersects the
metric radius with the proved derivative radius. At `z = x` it uses
`metric_pullback_zero`; otherwise it uses the displayed remainder. Derivative
uniqueness identifies canonical `fderiv` with the constructed equivalences.
Applying the pairing identity to `A.symm u` and `A.symm u'` yields the exact
original `chartDifferential` pullback in `UniformDifferentialPullback`.

`target_of_uniformNonzeroMetricPullback` derives the frozen task-8 conclusion
from that same single remainder through
`exists_onCompact_of_uniformDifferentialPullback`. Its conclusion is the
exact quantification of section 8 of `parametrization-plan-2.md`, using the
unchanged `FixedChartLocalSuccessorExistence.OnCompact` definition. It is a
conditional theorem. Neither `uniformDifferentialPullback_of_constantCurvature`
nor `exists_radius` is declared in the new namespace.

## Routes examined and why step 2 stops

1. The retained endpoint C1 and zero strict-derivative fields now close the
   whole uniform differential-existence step. They do not imply a Riemannian
   metric identity at nonzero velocity.
2. The actual `Patch` structure has no `Φ` field. The uniform flow constructor
   obtains a fundamental solution upstream but discards it when retaining
   the patch. A proof for an arbitrary supplied `C` must reconstruct or
   identify a variational family for `C.α`, not substitute a fresh flow.
   `GeodesicFlowJointDerivative.exists_flow_initialState_C1` constructs a
   fundamental solution only after choosing a possibly smaller time. That
   time cannot simply replace the already frozen endpoint `C.T`.
3. `geodesic_flow_hasFDerivAt_initialState` accepts a supplied fundamental
   solution, but concludes derivative identification only for
   `t ∈ Ioo (-ε) ε`. The patch retains flow laws on `Icc (-C.T) C.T` and its
   endpoint is exactly `C.T`. Using this route requires an additional
   endpoint/continuation argument. Endpoint C1 alone supplies the derivative
   but not its identification with the full-time Jacobi family.
4. `RigidityComplete.cartanMap_isLocalIsometry_of_selector_aop_bound` requires
   `EnrichedCascade.BaseCurvePackage` and `LinearizedFamilyPackage` with
   initial position `extChartAt I x₀ x₀`, the old selected exponential,
   ordinary time derivatives through a strict time margin, and common
   source/target time. The retained source curve starts at
   `extChartAt I x₀ x`, and the source and target use their separately
   retained times. These are different Lean types, not missing coercions.
   The older scalar selector also requires
   `T ≤ 1 / (2 * (4 * max 1 S + 1))`; arbitrary retained patch times do not
   have that field.
5. The lower Gauss and Jacobi metric-compatibility lemmas are compatible with
   a moving coordinate position, but need actual base-curve and variational
   time derivatives and the curvature oscillator equation. The Jacobi
   pairings follow a scalar ODE; they are not individually constant along
   radial geodesics. One must prove matching normalized source and target
   pairings at their retained endpoints. That full-time, moving-anchor
   comparison has not been constructed here.

These observations identify the missing proof route, not a counterexample.
The task-specific stop condition is met by the verified full step 1, the
verified zero metric case, the single exact metric remainder, and the
checked conditional reductions to both frozen conclusions.

## Proof commits and direct checks

Each theorem was committed only after successful direct elaboration of the
cumulative new module. The nine commits, in order, are:

```text
b5682d93 Prove retained normalized endpoint derivative at zero velocity
f29010f6 Identify supplied coordinate endpoints on their retained sources
063c023e Prove joint persistence of invertible velocity derivatives
15657c09 Choose one strict endpoint derivative radius over compact anchors
04466884 Prove compact uniform strict differentials for both supplied exponentials
b3a092e6 Transfer the identity derivative to the actual coordinate endpoint
5ee0e067 Prove endpoint metric pullback at the retained anchors
a23b1d05 Reduce uniform differential pullback to nonzero metric pairings
e82a4893 Derive the frozen compact successor target from the metric remainder

```

Successful compiler logs correspond to those commits in the same order:
`04-zero.log`, `06-coordinate.log`, `10-local-equiv.log`,
`11-compact-derivatives.log`, `12-both-derivatives.log`,
`13-coordinate-zero.log`, `14-zero-metric.log`,
`16-metric-reduction.log`, and `17-target-reduction.log`.
Each has empty compiler output and `LEAN_EXIT=0`.

The exact compiler command was:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformDifferentialPullback.lean
```

All logs and the invocation wrapper `run.py` are retained under
`/tmp/uniform-differential-pullback-evidence/`. The wrapper captures stdout,
stderr, and the Lean exit status and returns that status.

## Focused build and axiom gate

Exact command:

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh /private/tmp/poincare-workers/uniform-differential-pullback Poincare.Global.FixedChartUniformDifferentialPullback Poincare.FixedChartUniformDifferentialPullback.normalizedEndpoint_hasStrictFDerivAt_zero Poincare.FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint Poincare.FixedChartUniformDifferentialPullback.normalizedEndpoint_eventually_equiv Poincare.FixedChartUniformDifferentialPullback.exists_uniform_coordinateEndpoint_derivative_radius Poincare.FixedChartUniformDifferentialPullback.coordinateEndpoint_hasStrictFDerivAt_zero Poincare.FixedChartUniformDifferentialPullback.metric_pullback_zero Poincare.FixedChartUniformDifferentialPullback.exists_uniform_differential_radius Poincare.FixedChartUniformDifferentialPullback.uniformDifferentialPullback_of_uniformNonzeroMetricPullback Poincare.FixedChartUniformDifferentialPullback.target_of_uniformNonzeroMetricPullback
```

Exit 0. Actual `gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartUniformDifferentialPullback.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartUniformDifferentialPullback ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3609/3609] Built Poincare.Global.FixedChartUniformDifferentialPullback (10s)
Build completed successfully (3609 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=11 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartUniformDifferentialPullback.normalizedEndpoint_hasStrictFDerivAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.normalizedEndpoint_eventually_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.exists_uniform_coordinateEndpoint_derivative_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.coordinateEndpoint_hasStrictFDerivAt_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.metric_pullback_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.exists_uniform_differential_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.uniformDifferentialPullback_of_uniformNonzeroMetricPullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformDifferentialPullback.target_of_uniformNonzeroMetricPullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===

```

All nine theorem closures are exactly `[propext, Classical.choice, Quot.sound]`.
The module-wide scan checks 11 declarations with no nonstandard dependencies.
The warning comes from an unchanged imported module. The new file's direct
check has no warnings. No full root build or integration audit was run.

## Signature and missing-target probes

The nine delivered theorem signatures were each re-elaborated as independent
`example` declarations and proved by the corresponding named theorem:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-differential-pullback-evidence/partial-signatures.lean
```

Exit 0. Actual output:

```text
/tmp/uniform-differential-pullback-evidence/partial-signatures.lean:20:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/uniform-differential-pullback-evidence/partial-signatures.lean:27:49: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/uniform-differential-pullback-evidence/partial-signatures.lean:36:44: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/uniform-differential-pullback-evidence/partial-signatures.lean:53:50: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/tmp/uniform-differential-pullback-evidence/partial-signatures.lean:112:47: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

LEAN_EXIT=0

```

The task-8 statement was extracted unchanged from the specification and
probed using the requested name:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-differential-pullback-evidence/frozen-target.lean
```

Actual output:

```text
/tmp/uniform-differential-pullback-evidence/frozen-target.lean:26:8: error(lean.unknownIdentifier): Unknown identifier `exists_radius`

LEAN_EXIT=1

```

Both requested unconditional names were also probed directly:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/uniform-differential-pullback-evidence/target-names.lean
```

Actual output:

```text
/tmp/uniform-differential-pullback-evidence/target-names.lean:2:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformDifferentialPullback.uniformDifferentialPullback_of_constantCurvature`
/tmp/uniform-differential-pullback-evidence/target-names.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `Poincare.FixedChartUniformDifferentialPullback.exists_radius`

LEAN_EXIT=1

```

Those failures are expected for this blocked result. Passing the partial
module gate does not prove the absent targets.

## Compiler retries and final diff evidence

Failed source-check logs are preserved in the same evidence directory:

| Log | Exit | Resolved issue |
| --- | --- | --- |
| `01-zero.log` | 1 | Constant strict-derivative arguments were reversed. |
| `02-zero.log` | 1 | The composed derivative needed an explicit linear-map equality. |
| `03-zero.log` | 1 | Recursive `ext` descended into model-space coordinates; explicit CLM extensionality fixed it. |
| `05-coordinate.log` | 1 | The chart right-inverse rewrite needed explicitly typed target membership. |
| `07-local-equiv.log` | 1 | Scalar type inference needed the time-rescaling constant specified. |
| `08-local-equiv.log` | 1 | The rescaled zero evaluation point needed explicit simplification. |
| `09-local-equiv.log` | 1 | Composition elaboration needed the inner function specified. |
| `15-metric-reduction.log` | 1 | The rewrite needed typed derivative identities at `C.normal x z`. |

The API probes `check.lean` and `check2.lean` are also retained. The second
contains two unsuccessful name lookups; no source proof relies on them.
The complete verified proof diff is retained as `proof.diff` and reproduced by:

```sh
git diff ff85a298a835630b835e5699599db7d4021b0686 e82a4893 -- Poincare/Global/FixedChartUniformDifferentialPullback.lean
```

Actual final source/whitespace/toolchain check output before adding this report:

```text
$ rg -n \b(sorry|admit|axiom)\b|native_decide Poincare/Global/FixedChartUniformDifferentialPullback.lean
EXIT=1

$ git diff --check
EXIT=0

$ git diff ff85a298a835630b835e5699599db7d4021b0686 --check
EXIT=0

$ git status --short --branch
## worker/uniform-differential-pullback
EXIT=0

$ lake env lean --version
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
EXIT=0

```

The forbidden-token scan exits 1 because it has no matches. Both whitespace
checks pass. The assigned branch was clean at the verified proof head.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformDifferentialPullback.lean
```

Then rerun the focused gate and inspect the diff from the recorded base.
The next mathematical action is to construct and identify the velocity
Jacobi family for the retained moving-position flow through its full endpoint,
then prove `UniformNonzeroMetricPullback`. Uniform strict derivatives,
compact alignment bounds, domain radii, and the zero metric case no longer
need to be assumed.
