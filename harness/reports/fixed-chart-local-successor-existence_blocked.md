# Fixed-chart local successor existence blocked

Date: 2026-09-08. Branch: `worker/fixed-chart-local-successor-existence`.
Frozen base: `54cf83a1ea9f9e673bfa77640bfcd358b2e59c6f`.
Verified proof head: `b076752d6391a351eebe14096ba609d70f5e9730`.

The exact target `Poincare.FixedChartLocalSuccessorExistence.exists_radius`
is not proved and is not declared. Its frozen-signature probe fails with an
unknown identifier. This is a blocked worker result awaiting independent
review, with eight verified partial theorems. It does not complete task 8,
H1, H2, or sphere recognition.

Only the new `Poincare/Global/FixedChartLocalSuccessorExistence.lean` and this
report are changed. The assigned isolated worker branch is retained. No
existing Lean file, root import, audit wiring, task, ledger, or `HANDOFF.md`
was edited. The task's explicit scope overrides the general handoff-update
rule. No merge or acceptance was performed.

## Verified mathematical progress

`exists_uniform_domain_radius` proves the first three conjuncts of the frozen
`OnCompact`, with one positive radius chosen before `x,p,L,z`, for arbitrary
compact `K ⊆ C.anchors` and `H ⊆ D.anchors`:

```lean
letI : MetricSpace M := g.toMetricSpace
∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
  ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
    z ∈ (patch C D).sourceAnchors ∧
    map (patch C D) ⟨x, p, L⟩ z ∈ (patch C D).targetAnchors ∧
    z ∈ (germ (patch C D) ⟨x, p, L⟩).source
```

This result includes actual supplied-germ source membership. It needs no
curvature or cutoff-one premise. It applies to singleton centers and every
other compact subset in the task, but does not produce `Data`.

The proof closes the moving-anchor operator estimate:

* `exists_uniform_normal_radius` applies compact thickening to the diagonal
  over `K` inside the jointly open normal source, intersected with the retained
  endpoint anchor set and a prescribed normal-vector ball.
* `exists_uniform_endpoint_radius` uses the retained product map's continuity
  and compactness of `K` to put every sufficiently small velocity in the exact
  endpoint source and its endpoint back in the open retained anchor set.
* `exists_uniform_host_metric_comparison` gives positive lower and upper
  quadratic bounds for the fixed host metric. The lower bound comes from its
  positive minimum on `K × sphere 0 1`; the upper bound comes from boundedness
  of the continuous bilinear-form-valued metric on `K`. Empty compact sets
  are handled by the same compactness theorems.
* `patchFrame_metric` and `linear_metric` identify the actual fixed-host metric
  transport. They use chart derivative covariance and `L.map_app`, without
  requiring continuity of the preferred chart selector.
* `exists_uniform_linear_bound` combines the target lower constant `a > 0`
  and source upper constant `b > 0` to bound every framed alignment by
  `sqrt (b / a)`, uniformly over `x ∈ K`, `p ∈ H`, and `L`.

Combining the endpoint radius with this positive operator bound and the
normal-vector estimate gives the displayed domain radius. No minimum of
separately selected per-anchor radii is taken.

## Exact resisting statement

The remaining analytic requirement is defined in the new module as follows,
in the frozen manifold and metric instance context:

```lean
def UniformDifferentialPullback (Q : Interpretation g) (K : Set M)
    (H : Set RoundSphere3) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ η > (0 : ℝ), ∀ x ∈ K, ∀ p ∈ H,
    ∀ (L : CartanMap.TangentAlignment g x p) (z : M), dist z x < η →
      let s : CartanChain.ChainState g := ⟨x, p, L⟩
      let v := Q.sourceNormal x z
      ∃ A B : E ≃L[ℝ] E,
        HasStrictFDerivAt (sourceExp Q x) (A : E →L[ℝ] E) v ∧
        HasStrictFDerivAt (targetExp Q p) (B : E →L[ℝ] E) (linear Q s v) ∧
        ∀ u u' : E,
          CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost p)
            (targetExp Q p (linear Q s v))
            (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
          CovariantDerivative.chartMetric g.inner (Q.sourceHost x)
            (sourceExp Q x v) u u'
```

The curvature-only statement still needing a proof has this exact checked
Lean type. `resisting_spec` below is a proposition definition in the scratch
probe, not a theorem or an added premise of the frozen `exists_radius`:

```lean
def resisting_spec : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  HasConstantSectionalCurvature3 g 1 →
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (K : Set M) (H : Set RoundSphere3), IsCompact K → K ⊆ C.anchors →
    IsCompact H → H ⊆ D.anchors →
    UniformDifferentialPullback (patch C D) K H
```

The resisting fields are `CoordinateData.source_exp_derivative`,
`CoordinateData.target_exp_derivative`, and `CoordinateData.metric_pullback`,
with the two derivatives represented by continuous linear equivalences.
Their radius must precede all four moving parameters. The vector is fixed to
`Q.sourceNormal x z`; there is no freedom to replace it by another selected
exponential coordinate. The pullback must hold at that vector's actual
supplied endpoints, including the zero vector.

`exists_onCompact_of_uniformDifferentialPullback` is the checked conditional
reduction from this single remainder to the full compact conclusion. It
intersects the already uniform domain radius with the assumed analytic
radius, derives both endpoint-domain fields and both host-chart memberships,
proves the source-coordinate identity by the partial inverse law, and uses
the actual forward-map formula for the target-coordinate identity. The
inverse-function and chain rules derive `cartan_chart_derivative` from the
two endpoint derivatives. Task 7's `data_of_coordinateData` then constructs
the actual reanchored alignment and its derivative witness.

Thus the remaining statement contains neither `Data` nor the geometric domain
conclusion as an assumed field. The conditional theorem is partial progress,
not success under the task's exact stop condition. The original `OnCompact`
text matches the frozen task verbatim; `exists_radius` has not been weakened
or replaced by a conditional declaration of that name.

## Routes examined and why they stop

1. Joint openness and continuity in S3 prove domain and vector control. The
   new theorems above complete that route and the required moving-anchor
   operator bound. These estimates do not establish an isometry identity
   for the derivative away from the anchor.
2. S3's `endpoint_C1` and `endpoint_strict` control the retained forward flow
   and its derivative at zero velocity. They do not directly furnish the
   displayed uniform witnesses for the supplied coordinate endpoints and
   their metric pullback. This attempt does not claim that the strict
   derivative estimates alone are impossible to derive from S3.
3. S4 and task 7 prove `patch_germ_eventuallyEq_generic` after the anchor and
   alignment have been fixed. The equality neighborhood is not quantified
   uniformly over `K,H,L`. It therefore cannot transport the old local
   isometry witnesses to every point of one compact-uniform radius.
4. `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`
   chooses its radius after fixed source and target anchors, returns old
   `expAtChartOpenPartialHomeomorph` derivatives, and excludes zero velocity.
   S10's fixed-anchor data theorem also returns old `Data`. Neither has the
   supplied maps or the quantifier order of `resisting_spec`.
5. The lower-level
   `RigidityComplete.cartanMap_isLocalIsometry_of_selector_aop_bound` retains
   `EnrichedCascade.BaseCurvePackage` and `LinearizedFamilyPackage` for a
   chart centered at its own anchor. In particular, its curve is
   `α (extChartAt I x₀ x₀, T⁻¹ • v)`. The retained patch uses the moving
   initial position `extChartAt I x₀ x`, and source and target patches have
   their separately retained times. A joint fixed-host variational and
   metric-pullback argument, with the necessary time normalization, remains
   to be proved. Renaming those packages or supplying the old center-based
   witnesses does not establish the required types.

This is an unproved analytic interface, not a counterexample to the target.
The task-specific blocked stop condition and the M5-glob-69 partial-result
condition are met by the domain theorem, the exact `UniformDifferentialPullback`
remainder, and its verified conditional reduction.

## Verified proof commits

Each commit followed successful direct elaboration of the cumulative new file.
Successful logs have empty compiler output and recorded Lean exit 0.
All evidence below is in `/tmp/fixed-chart-local-successor-existence-evidence/`.

| Commit | Theorem | Successful log |
| --- | --- | --- |
| `0280edb1` | `exists_uniform_normal_radius` | `02-normal.log` |
| `bc8c0d33` | `exists_uniform_endpoint_radius` | `07-endpoint.log` |
| `ed1fee4a` | `exists_uniform_host_metric_comparison` | `09-metric.log` |
| `64722038` | `patchFrame_metric` | `10-frame.log` |
| `bf6723bb` | `linear_metric` | `11-linear-metric.log` |
| `779365ef` | `exists_uniform_linear_bound` | `12-linear-bound.log` |
| `651f2f6e` | `exists_uniform_domain_radius` | `13-domain.log` |
| `b076752d` | `exists_onCompact_of_uniformDifferentialPullback` | `14-reduction.log` |

The command run by each successful compiler wrapper was:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorExistence.lean
```

The wrapper captures stdout and stderr in the named log, prints
`LEAN_EXIT=0`, and exits with the compiler's status. The toolchain check was:

```sh
lake env lean --version
```

Actual output, exit 0:

```text
Lean (version 4.30.0-rc2, arm64-apple-darwin24.6.0, commit 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc, Release)
```

## Focused build and axiom checks

```sh
LEAN_NUM_THREADS=1 bash harness/gate.sh \
  /private/tmp/poincare-workers/fixed-chart-local-successor-existence \
  Poincare.Global.FixedChartLocalSuccessorExistence \
  Poincare.FixedChartLocalSuccessorExistence.exists_uniform_normal_radius \
  Poincare.FixedChartLocalSuccessorExistence.exists_uniform_endpoint_radius \
  Poincare.FixedChartLocalSuccessorExistence.exists_uniform_host_metric_comparison \
  Poincare.FixedChartLocalSuccessorExistence.patchFrame_metric \
  Poincare.FixedChartLocalSuccessorExistence.linear_metric \
  Poincare.FixedChartLocalSuccessorExistence.exists_uniform_linear_bound \
  Poincare.FixedChartLocalSuccessorExistence.exists_uniform_domain_radius \
  Poincare.FixedChartLocalSuccessorExistence.exists_onCompact_of_uniformDifferentialPullback
```

Exit 0. Actual `gate.log`:

```text
=== GATE: forbidden tokens in Poincare/Global/FixedChartLocalSuccessorExistence.lean ===
=== GATE: git diff --check ===
=== GATE: lake build Poincare.Global.FixedChartLocalSuccessorExistence ===
warning: Poincare/Global/CartanFixedChartGenericInverseEndpointODEPrimitive.lean:123:4: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
✔ [3608/3608] Built Poincare.Global.FixedChartLocalSuccessorExistence (4.4s)
Build completed successfully (3608 jobs).
=== GATE: module-wide axiom scan ===
GATE_SCAN declarations=15 nonstandard=[]
=== GATE: #print axioms (named) ===
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_normal_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_endpoint_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_host_metric_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.patchFrame_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.linear_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_linear_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_domain_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_onCompact_of_uniformDifferentialPullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== GATE: PASS ===
```

The warning is replayed from an unchanged dependency. The new module's final
direct check has no warnings. All eight theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`; the module-wide scan checks 15
non-internal declarations with no nonstandard dependencies. The build was
serial. No full root build or integration audit was run.

## Signature probes

Each partial theorem was independently checked as an `example` with its full
source signature and the corresponding named theorem as the proof. These
freeze the delivered partial signatures; they do not substitute for the
missing task target. The same probe prints all eight axiom closures.

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-existence-evidence/partial-signatures.lean
```

Exit 0. Actual `partial-signatures.log`:

```text
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_normal_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_endpoint_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_host_metric_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.patchFrame_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.linear_metric' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_linear_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_uniform_domain_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartLocalSuccessorExistence.exists_onCompact_of_uniformDifferentialPullback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The complete curvature-only resisting signature was elaborated as the
proposition `resisting_spec`, not as a proof:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-existence-evidence/resisting-signature.lean
```

Exit 0, no output.

The exact task-8 target was extracted from the task unchanged as an `example`
whose proof is the requested named declaration:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/fixed-chart-local-successor-existence-evidence/frozen-target.lean
```

Exit 1. Actual `frozen-target.log`:

```text
/tmp/fixed-chart-local-successor-existence-evidence/frozen-target.lean:26:50: error(lean.unknownIdentifier): Unknown identifier `exists_radius`
```

Its axiom closure cannot be inspected because that declaration is absent.
The green partial-module gate does not override this failed target probe.

## Compiler retries and diff evidence

All failed compiler output is retained, and each implementation issue was
resolved before its theorem was committed:

| Log | Recorded status | Resolved error |
| --- | --- | --- |
| `01-normal.log` | Compiler error; Lean exit not captured | An image-membership tuple needed its set specified explicitly. The initial shell wrapper ended in `cat` and returned 0; this is not counted as a passing Lean check. |
| `03-endpoint.log` | Lean exit 1 | `extChartAt` is a `PartialEquiv`; host membership and composition coercions needed explicit types. |
| `04-endpoint.log` | Lean exit 1 | `continuousAt_extChartAt'` needs extended-chart source membership. |
| `05-endpoint.log` | Lean exit 1 | Composition inference selected the inner projection before the joint evaluator. |
| `06-endpoint.log` | Lean exit 1 | The inner function argument to `ContinuousAt.comp` is named `f`, not `g`. |
| `08-metric.log` | Lean exit 1 | The imported metric-regularity theorem needs `T2Space`; the bounded-image type needed an explicit annotation. |

The verified 367-line proof diff is preserved in `proof.diff` and can be
regenerated exactly:

```sh
git diff 54cf83a1ea9f9e673bfa77640bfcd358b2e59c6f b076752d6391a351eebe14096ba609d70f5e9730 -- Poincare/Global/FixedChartLocalSuccessorExistence.lean
```

Final source and whitespace checks:

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartLocalSuccessorExistence.lean
git diff --check
git diff 54cf83a1ea9f9e673bfa77640bfcd358b2e59c6f --check
```

Token scan: exit 1, no matches. Whitespace checks: exit 0, no output.

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartLocalSuccessorExistence.lean
```

Then rerun the displayed focused gate and inspect the exact partial diff.
The next mathematical action is a proof of the displayed `resisting_spec`,
using uniform variational and metric-pullback witnesses for the retained
fixed-host endpoints. The moving-anchor framed-operator bound and domain
radius no longer need to be assumed.
