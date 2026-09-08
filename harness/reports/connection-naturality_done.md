# Connection and curvature naturality: done

Date: 2026-09-08 UTC. Branch: `worker/connection-naturality`.
Base: `0af3ddc6008aa53120b04d91a1caea455e89b4ae`.
Verified proof head: `487a4158bbaf486c88ade47d81c730024c55981c`.

## Result

Stop condition (a). All five steps are proved in the new file
`Poincare/Global/ConnectionInstanceNaturality.lean`.
The frozen theorem is
`Poincare.ConnectionInstanceNaturality.connectionCurvatureNaturality`.
It proves the existing `CurvatureInstanceTransport.ConnectionCurvatureNaturality`
for every original metric, with both clauses and without a naturality premise.

Both requested consumers are proved without `hN`:

- `ConnectionInstanceNaturality.unitConstantCurvatureSphereRecognition3_of_controlled`
- `ConnectionInstanceNaturality.exists_controlled_recognition_reduction'`

The first consumer still takes recognition for the compatible instance, as
requested. The second produces a finite controlled atlas, a positive uniform
source-ball radius, and reduction of recognition to that atlas. Neither
consumer proves sphere recognition by itself, and this result does not prove
the Poincare conjecture.

No existing Lean file or `Poincare.lean` changed. `HANDOFF.md` is updated under
the repository handoff rule. No task, mission, or ledger changed. This is a
worker result awaiting independent orchestrator review; no merge or acceptance
was performed.

## Mathematical content

1. The identity map from the new atlas to the old atlas is smooth.
   `mfderiv_identity` identifies its derivative with `J` using the actual
   chart-derivative definition. `extDerivFun_naturality` applies the manifold
   chain rule to a scalar function differentiable at the point.
2. `mpullback_identity` identifies inverse-J field transport with Mathlib
   pullback. `mlieBracket_transportField` applies
   `VectorField.mpullback_mlieBracket`, retaining pointwise differentiability
   of the two fields. No global regularity assumption was added.
3. `extDerivFun_naturality_total` additionally covers the zero derivative at
   nondifferentiable points, using differentiability equivalence across
   instances. The conjugated operator satisfies Leibniz and bundles as a
   covariant derivative. The metric pullback formula gives compatibility;
   bracket naturality gives zero torsion. Repository Levi-Civita uniqueness
   proves agreement on differentiable fields, exactly the first clause.
4. `inverseTransportField_contMDiffAt` transfers local section regularity.
   `leviCivita_naturality_twice` uses
   `CovariantDerivative.mdiffAt_cov_section_of_contMDiffAt` and
   `IsCovariantDerivativeOn.congr_of_eventuallyEq` to compare nested
   derivatives. `curvatureOp_naturality` combines the two nested terms and
   bracket naturality for locally C2 fields. `curvatureValue_naturality`
   applies `curvatureTensorAt_apply` in the direction arguments and
   `curvatureOp_congr_of_value_eq` in the field argument to replace the
   transported extensions by canonical old-instance extensions. It does
   not equate those extensions as total functions.
5. The two clauses assemble the frozen target and discharge the previous
   consumers' naturality premises.

## Verification and actual output

Direct check of the final proof source:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ConnectionInstanceNaturality.lean
```

Exit 0; no output. Retained as `28.log` in the evidence directory below.
Each of the 20 declarations was part of a successful direct elaboration
before its separate commit.

Focused build:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.ConnectionInstanceNaturality
```

Exit 0. The complete log includes replayed warnings from existing dependencies.
The new module produced no warnings. Actual final build lines:

```text
✔ [3072/3072] Built Poincare.Global.ConnectionInstanceNaturality (4.2s)
Build completed successfully (3072 jobs).
```

Forbidden-token check:

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/ConnectionInstanceNaturality.lean
```

Exit 1, no matches, no output.

Whitespace checks:

```sh
git diff --check
git diff --check 0af3ddc6008aa53120b04d91a1caea455e89b4ae
```

Both exit 0 with no output.

Frozen-signature probe:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/connection-naturality-evidence/Frozen.lean
```

Exit 0; no output. The probe imports the built module and supplies each of
the three requested declarations to an `example` with the exact requested
signature, including the compatible metric's topology equality and all
conjuncts of the existential conclusion.

All new declaration closures:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/connection-naturality-evidence/Axioms.lean
```

Exit 0. The probe contains `#print axioms` for all 20 new declarations.
A parser also checked that all 20 closures are exactly
`[propext, Classical.choice, Quot.sound]`. Actual Lean output:

```text
'Poincare.ConnectionInstanceNaturality.contMDiffAt_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ConnectionInstanceNaturality.mfderiv_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ConnectionInstanceNaturality.extDerivFun_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.mpullback_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ConnectionInstanceNaturality.mlieBracket_transportField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.extDerivFun_naturality_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.inverseTransportField_contMDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedDerivative_leibniz' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedDerivative_isCovariantDerivativeOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedConnection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedConnection_metricCompatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedConnection_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.conjugatedConnection_eq_leviCivita' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.leviCivita_naturality_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.leviCivita_naturality_twice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.curvatureOp_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.curvatureValue_naturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.connectionCurvatureNaturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.unitConstantCurvatureSphereRecognition3_of_controlled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ConnectionInstanceNaturality.exists_controlled_recognition_reduction'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No full repository build or root integration audit was run. The orchestrator
must independently rerun the focused gate from the recorded base and choose
root import wiring and integration checks.

## Proof commits

```text
ebcf151a Prove smooth identity between compatible chart instances
7a3f6fbe Identify cross-instance identity derivative with J
0735dbbb Prove scalar exterior derivative naturality across instances
46cd68c6 Identify field transport as identity pullback
d7984f5b Prove Lie bracket naturality across compatible chart instances
49f113c2 Prove total scalar derivative naturality
56321d68 Prove the conjugated derivative Leibniz law
ac12c416 Bundle conjugated derivative laws without naturality assumptions
c82bc7f2 Construct the unconditional conjugated connection
8221603a Prove metric compatibility of the conjugated connection
d232b6df Prove zero torsion of the conjugated connection
913543e6 Prove unconditional Levi-Civita connection naturality
342ab81d Transfer local tangent section regularity across chart instances
d601b1b4 Orient pointwise Levi-Civita naturality for curvature transport
ba65ddae Prove naturality of nested covariant derivatives using germ locality
f5ff86be Prove curvature operator naturality on locally regular fields
45b07c85 Prove curvature value naturality using tensoriality of local extensions
8e6f721b Discharge connection and curvature naturality across compatible atlases
960ce6db Derive controlled-instance sphere recognition without naturality premises
487a4158 Reduce recognition to a finite controlled atlas unconditionally
```

## Evidence and next action

`/tmp/connection-naturality-evidence/` retains every numbered compiler attempt,
API probes, source snapshots, the complete focused-build log, frozen-signature
and axiom probes, acceptance JSON, and the final proof diff. It is also
archived at `/tmp/connection-naturality-evidence.tar.gz`.

Failed attempts are retained, not overwritten. They concerned explicit
source/target instances, tangent-fiber coercions in rewriting, the comparison
of finite differentiability with smoothness, and inference of the vector
bundle for local extensions. All were resolved; no resisting statement remains
for this task.

Exact first action for independent review:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.ConnectionInstanceNaturality
```

Review the proof diff against `0af3ddc6008aa53120b04d91a1caea455e89b4ae` and rerun the
frozen-signature and axiom probes before acceptance.
