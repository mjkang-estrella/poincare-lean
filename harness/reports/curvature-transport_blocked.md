# Curvature instance transport: verified partial, differential naturality open

Date: 2026-09-08 UTC. Worker branch `worker/curvature-transport`.
Base: `99419b12559e2f220d868c56983a26cc10716603`.
Proof head: `330e7f07806a51fc6ec71f5be9380aceb5805667`.
The report commit adds prose and a source-comment cleanup after that proof head.

## Result

Stop condition (b). Step 1 is proved. Step 2 has an unconditional conjugated
operator, its pointwise formula, and additivity. The bundled connection,
metric compatibility, zero torsion, pointwise Levi-Civita agreement, constant
curvature transport, and recognition reductions are conditional on the exact
`ConnectionCurvatureNaturality` definition below. No unconditional connection
or curvature naturality theorem is claimed.

Only one new Lean file was added, `Poincare/Global/CurvatureInstanceTransport.lean`.
No existing Lean file, root import, task, mission, or ledger was modified.
The handoff is updated as required by AGENTS.md. This is a worker result;
no merge or acceptance was performed.

## Unconditional content

- `transportField` maps an old tangent field by `(J x).symm` into the new
  tangent fiber. `inverseTransportField` maps back by `J x`. The result
  signatures explicitly select the new and old chart instances respectively.
- `tangentCoordinates_transportField` derives the direction from the existing
  `tangentCoordinates_transport` bridge and the common-atlas derivative
  cocycle. Its new coordinate is `D (oldChart a) (newChart a) x` applied to
  the old coordinate. This holds on the intersection of both anchor sources.
- `modelContMDiffAt_iff_of_le` transfers model-valued pointwise regularity
  for every `n ≤ ∞`. `transportField_contMDiff` and
  `inverseTransportField_contMDiff` transfer tangent-section regularity in
  both directions. `transportField_contMDiff_iff` is their equivalence.
  `fieldContMDiff` is the actual `ContMDiff` of the section into the tangent
  total space, with its bundle topology and charts selected explicitly.
- `modelMDifferentiableAt_iff` and `inverseTransportField_mdiffAt` also
  transfer pointwise differentiability, the hypothesis required by the
  bundled covariant-derivative laws. They do not assume global C1 regularity.
- `conjugatedDerivative` is
  `J(x)⁻¹ ∘ g.leviCivita (inverseTransportField X) x ∘ J(x)`.
  `conjugatedDerivative_apply` gives its pointwise formula, and
  `conjugatedDerivative_add` proves additivity on fields differentiable at
  the point, with no differential-naturality premise.

## Exact remaining definition

In the file's context, `E = ClosedSmoothModel 3` and
`I = closedSmoothModelWithCorners 3`. The manifold is Hausdorff here.
`curvatureValue g x u w a` is exactly `CovariantDerivative.curvatureOp`
for `g.leviCivita` applied to the three `FiberBundle.extend` sections used
by `HasConstantSectionalCurvature3`, evaluated at `x`.

```lean
def ConnectionCurvatureNaturality (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) : Prop :=
  let R := curvatureValue (inst := inst) g
  let cov := conjugatedDerivative (inst := inst) inst' h g
  letI := inst'
  letI : IsManifold I ∞ M :=
    (ControlledChartInstance.isManifold_and_maximalAtlas_eq (inst := inst) inst' h).1
  let g' := transport (inst := inst) inst' h g
  (∀ (X : M → E) (x : M), MDiffAtTangentField X x → cov X x = g'.leviCivita X x) ∧
    (∀ (x : M) (u w a : E),
      J (inst := inst) inst' h x (curvatureValue g' x u w a) =
        R x (J (inst := inst) inst' h x u) (J (inst := inst) inst' h x w)
          (J (inst := inst) inst' h x a))
```

This is one named boundary with two explicit, still-unproved clauses.
The curvature clause is independently assumed. It has not been derived from
the connection clause. Neither clause is replaced by a constant-curvature
or sphere-recognition assumption.

## Conditional consumers and limits

`conjugatedDerivative_isCovariantDerivativeOn` transfers the new canonical
connection's laws through the first naturality clause. The construction
`conjugatedConnection` has the raw conjugated operator as its actual `toFun`.
`conjugatedConnection_metricCompatible_torsion` proves metric compatibility
and torsion zero under the same boundary.

`conjugatedConnection_eq_leviCivita` applies the repository uniqueness theorem.
The exact conclusion is

```lean
∀ (X : M → E) (x : M), MDiffAtTangentField X x →
  conjugatedConnection inst' h g hN X x = (transport inst' h g).leviCivita X x
```

with the new instances installed. It is not unconditional equality of the
bundled connections on all fields. Mathlib's bundled derivative permits
unspecified values on fields not differentiable at the point.

`hasConstantSectionalCurvature3_transport` proves the forward direction for
any real `κ`, hence for `1`, using the second naturality clause and the
verified metric pullback. The four terms of `tensorKulkarniNomizuAt` transform
definitionally under that pullback.

`target_of_ConnectionCurvatureNaturality` takes `hN` for every original metric
and the explicitly instantiated recognition statement for `inst'`. It proves
the original recognition statement. `exists_controlled_recognition_reduction`
combines this with
`ControlledChartInstance.exists_controlled_chartedSpace_of_compatibleMetric`:
any compatible metric supplies some finite controlled chart instance, a
positive source-ball radius, and a reduction of recognition to that instance.
It still requires naturality for compatible atlases.

The requested unconditional
`unitConstantCurvatureSphereRecognition3_of_controlled` is not supplied.
Its conclusion cannot be claimed from this partial result without discharging
the displayed boundary.

## Why this stops here

The coordinate cocycle controls tangent-bundle section regularity. It does
not itself identify scalar derivatives or Lie brackets. The raw conjugated
operator's remaining Leibniz calculation needs, for a scalar function
pointwise differentiable at `x`, the cross-instance identity

```text
extDerivFun_new f x v = extDerivFun_old f x (J x v).
```

Metric compatibility uses that identity on the metric pairing. Torsion also
needs naturality of `VectorField.mlieBracket`. Curvature then nests the
connection twice and uses locally extended fields. The arbitrary preferred
extensions do not agree as total functions, so a proof must use local
regularity, germ equality, and curvature tensoriality to compare them.
The first-order connection comparison alone was not used to assert that
second-order comparison.

Attempted routes and actual progress:

1. Applied the common-atlas cocycle to the existing forward coordinate bridge;
   this closed the inverse-J tangent coordinate identity.
2. Transferred local coefficient regularity through fixed smooth anchor
   transitions and converted back to the actual bundle-section predicate;
   this closed both global Cn directions.
3. Read the actual `IsCovariantDerivativeOn` laws and uniqueness statement.
   Their assumptions are pointwise differentiability, so global Cn transport
   alone could not instantiate them. Proved the pointwise differentiability
   bridge separately, then closed raw additivity.
4. Formulated the remaining operator and tensor identities explicitly and
   checked the downstream consequences. These conditional proofs do not
   constitute a proof of either naturality identity.

This is a formalization boundary, not a counterexample to naturality or a
claim that the mathematical statement is false.

Exact next mathematical action: prove the displayed scalar exterior-derivative
identity by the cross-instance chain rule, using `J_apply` and
`modelMDifferentiableAt_iff`. Then use it in the raw conjugated Leibniz law.

## Verification: actual commands and outputs

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.CurvatureInstanceTransport
```

Exit 0. Final output tail:

```text
ℹ [3069/3071] Replayed Poincare.Global.Statement
info: Poincare/Global/Statement.lean:38:0: inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) ↑(Metric.sphere 0 1)
info: Poincare/Global/Statement.lean:42:0: inferInstance : IsManifold (𝓡 3) ∞ ↑(Metric.sphere 0 1)
✔ [3071/3071] Built Poincare.Global.CurvatureInstanceTransport (3.1s)
Build completed successfully (3071 jobs).
```

Lake replayed existing dependency warnings and informational messages.
The new module's direct elaboration has no warnings or errors. Full build
output is retained in the evidence archive described below.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CurvatureInstanceTransport.lean
```

Exit 0, empty output.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CurvatureInstanceTransport.lean
```

Exit 1, empty output, meaning no matches. An earlier scan matched only the
word `axiom` in the additivity docstring. It was changed to `law` before the
final build and scan.

```sh
git diff --check
git diff 99419b12559e2f220d868c56983a26cc10716603 --check
```

Both exit 0, empty output.

The probe imports the new module and runs `#print axioms` for all 23 new
functions, definitions, and theorems:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/curvature-transport-evidence/axioms.lean
```

Exit 0. Actual output:

```text
'Poincare.CurvatureInstanceTransport.fieldContMDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.fieldContMDiff_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.transportField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.inverseTransportField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.tangentCoordinates_transportField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.modelContMDiffAt_iff_of_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.transportField_contMDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.inverseTransportField_contMDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.transportField_contMDiff_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.modelMDifferentiableAt_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.inverseTransportField_mdiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedDerivative_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedDerivative_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.curvatureValue' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.ConnectionCurvatureNaturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedDerivative_isCovariantDerivativeOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedConnection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedConnection_metricCompatible_torsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.conjugatedConnection_eq_leviCivita' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.hasConstantSectionalCurvature3_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.target_of_ConnectionCurvatureNaturality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.CurvatureInstanceTransport.exists_controlled_recognition_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No root integration audit or full repository build was run by this worker.
The orchestrator must independently rerun the focused gate from the recorded
base before acceptance.

## Proof commits

Each addition was directly elaborated successfully before its commit.

```text
2def2829 Prove tangent field coordinate transport across compatible atlases
07ca1d2b Generalize model map chart independence to every order up to smoothness
c26fd0fe Prove regularity of transported tangent sections
8b5e6cb3 Prove regularity of inverse tangent field transport
7ba73632 Prove equivalence of tangent section regularity across instances
429f9ac2 Define geometric conjugated derivative and exact differential naturality boundary
48dc6542 Bundle the conjugated derivative conditional on differential naturality
37fa3717 Derive metric compatibility and zero torsion from differential naturality
618f216f State exact pointwise Levi-Civita uniqueness for the conditional transport
d575b705 Transport constant sectional curvature conditional on tensor naturality
fcf56b3f Reduce sphere recognition across instances to explicit naturality
95f25c99 Select a finite controlled chart instance for conditional sphere recognition
af1be1ac Transfer pointwise differentiability with explicit old and new tangent fibers
330e7f07 Prove additivity of the raw conjugated derivative without naturality assumptions
```

## Retained evidence

`/tmp/curvature-transport-evidence/` contains the numbered compiler attempts,
API probe, full builds, final direct check, axiom probe, acceptance JSON, and
final patch. A copy is archived at `/tmp/curvature-transport-evidence.tar.gz`.
Git preserves the final diff and all proof commits. The failed compiler
attempts are also included below so they survive outside the temporary archive.

<details>
<summary>Failed compiler attempts, retained verbatim</summary>

### 01.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:26:15: error(lean.unknownIdentifier): Unknown identifier `«I».prod`
Poincare/Global/CurvatureInstanceTransport.lean:34:2: error: Type mismatch
  forall_congr' fun a => contMDiffAt_section a
has type
  (∀ (a : M), ContMDiffAt I (I.prod 𝓘(ℝ, E)) (?m.92 a) (fun x => ⟨x, X x⟩) a) ↔
    ∀ (a : M), ContMDiffAt I 𝓘(ℝ, E) (?m.92 a) (fun x => (↑(trivializationAt E (TangentSpace I) a) ⟨x, X x⟩).2) a
but is expected to have type
  fieldContMDiff inst ⋯ n X ↔ ∀ (a : M), ContMDiffAt I 𝓘(ℝ, E) n (fun x => tangentCoordinates inst ⋯ a x (X x)) a
Poincare/Global/CurvatureInstanceTransport.lean:59:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/CurvatureInstanceTransport.lean:55:61: error: unsolved goals
M : Type u_1
inst✝¹ : TopologicalSpace M
inst : ChartedSpace E M
inst✝ : IsManifold I ∞ M
inst' : ChartedSpace E M
h : ChartedSpace.atlas ⊆ StructureGroupoid.maximalAtlas M (contDiffGroupoid ∞ I)
X : M → E
a x : M
ha : x ∈ (ChartedSpace.chartAt a).source
ha' : x ∈ (ChartedSpace.chartAt a).source
hb :
  tangentCoordinates inst ⋯ a x (X x) =
    (D (newChart inst' h a) (oldChart a) x) (tangentCoordinates inst' ⋯ a x ((J inst' h x).symm (X x)))
⊢ tangentCoordinates inst' ⋯ a x (transportField inst' h X x) =
    (D (oldChart a) (newChart inst' h a) x)
      ((D (newChart inst' h a) (oldChart a) x) (tangentCoordinates inst' ⋯ a x ((J inst' h x).symm (X x))))
```

### 02.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:55:61: error: unsolved goals
M : Type u_1
inst✝¹ : TopologicalSpace M
inst : ChartedSpace E M
inst✝ : IsManifold I ∞ M
inst' : ChartedSpace E M
h : ChartedSpace.atlas ⊆ StructureGroupoid.maximalAtlas M (contDiffGroupoid ∞ I)
X : M → E
a x : M
ha : x ∈ (ChartedSpace.chartAt a).source
ha' : x ∈ (ChartedSpace.chartAt a).source
this : ChartedSpace E M := inst
hb :
  tangentCoordinates inst ⋯ a x (X x) =
    (D (newChart inst' h a) (oldChart a) x) (tangentCoordinates inst' ⋯ a x ((J inst' h x).symm (X x)))
⊢ tangentCoordinates inst' ⋯ a x (transportField inst' h X x) =
    tangentCoordinates inst' ⋯ a x ((J inst' h x).symm (X x))
```

### 07.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:139:4: error: Type mismatch: After simplification, term
  hback
 has type
  fieldContMDiff inst ⋯ n (inverseTransportField inst' h (transportField inst' h X))
but is expected to have type
  fieldContMDiff inst ⋯ n X
```

### 09.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:167:24: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IsManifold I ∞ M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/CurvatureInstanceTransport.lean:186:10: error: Application type mismatch: The argument
  x
has type
  M
of sort `Type u_1` but is expected to have type
  E
of sort `Type` in the application
  R x
```

### 11.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:198:4: error: typeclass instance problem is stuck
  ChartedSpace ?m.102 M

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `ChartedSpace` are metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
Poincare/Global/CurvatureInstanceTransport.lean:220:4: error(lean.unknownIdentifier): Unknown identifier `conjugatedDerivative_isCovariantDerivativeOn`
Poincare/Global/CurvatureInstanceTransport.lean:219:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace (TotalSpace E (TangentSpace I))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

### 12.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:198:30: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/CurvatureInstanceTransport.lean:223:4: error(lean.unknownIdentifier): Unknown identifier `conjugatedDerivative_isCovariantDerivativeOn`
```

### 16.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:284:9: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this✝
inferred
  inst
```

### 19.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:331:16: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  charts
inferred
  inst
```

### 21.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:177:4: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this
inferred
  inst'
Poincare/Global/CurvatureInstanceTransport.lean:186:61: error: Application type mismatch: The argument
  hX
has type
  MDiffAtTangentField X a
but is expected to have type
  MDiffAt (T% X) ?m.158
in the application
  (mdifferentiableAt_section I X).mp hX
```

### 22.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:177:4: error: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  this
inferred
  inst'
```

### 24.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:234:61: error: unsolved goals
case h.h
M : Type u_1
inst✝² : TopologicalSpace M
inst : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst' : ChartedSpace E M
h : ChartedSpace.atlas ⊆ StructureGroupoid.maximalAtlas M (contDiffGroupoid ∞ I)
inst✝ : T2Space M
g : ClosedSmoothRiemannianMetric 3 M
X Y : M → E
x : M
hX : MDiffAtTangentField X x
hY : MDiffAtTangentField Y x
this : ChartedSpace E M := inst
hXold : MDiffAtTangentField (inverseTransportField inst' h X) x
hYold : MDiffAtTangentField (inverseTransportField inst' h Y) x
hadd : inverseTransportField inst' h (X + Y) = inverseTransportField inst' h X + inverseTransportField inst' h Y
v : E
i✝ : Fin 3
⊢ ((J inst' h x).symm
          (((↑g.leviCivita (inverseTransportField inst' h X) x).comp ↑(J inst' h x) +
              (↑g.leviCivita (inverseTransportField inst' h Y) x).comp ↑(J inst' h x))
            v)).ofLp
      i✝ =
    ((J inst' h x).symm (((↑g.leviCivita (inverseTransportField inst' h X) x).comp ↑(J inst' h x)) v)).ofLp i✝ +
      ((J inst' h x).symm (((↑g.leviCivita (inverseTransportField inst' h Y) x).comp ↑(J inst' h x)) v)).ofLp i✝
```

### 25.log

```text
Poincare/Global/CurvatureInstanceTransport.lean:234:61: error: unsolved goals
case h
M : Type u_1
inst✝² : TopologicalSpace M
inst : ChartedSpace E M
inst✝¹ : IsManifold I ∞ M
inst' : ChartedSpace E M
h : ChartedSpace.atlas ⊆ StructureGroupoid.maximalAtlas M (contDiffGroupoid ∞ I)
inst✝ : T2Space M
g : ClosedSmoothRiemannianMetric 3 M
X Y : M → E
x : M
hX : MDiffAtTangentField X x
hY : MDiffAtTangentField Y x
this : ChartedSpace E M := inst
hXold : MDiffAtTangentField (inverseTransportField inst' h X) x
hYold : MDiffAtTangentField (inverseTransportField inst' h Y) x
hadd : inverseTransportField inst' h (X + Y) = inverseTransportField inst' h X + inverseTransportField inst' h Y
v : E
⊢ ↑(J inst' h x).symm
      (((↑g.leviCivita (inverseTransportField inst' h X) x + ↑g.leviCivita (inverseTransportField inst' h Y) x).comp
          ↑(J inst' h x))
        v) =
    ↑(J inst' h x).symm (((↑g.leviCivita (inverseTransportField inst' h X) x).comp ↑(J inst' h x)) v) +
      ↑(J inst' h x).symm (((↑g.leviCivita (inverseTransportField inst' h Y) x).comp ↑(J inst' h x)) v)
Poincare/Global/CurvatureInstanceTransport.lean:247:76: warning: This simp argument is unused:
  map_add

Hint: Omit it from the simp argument list.
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,̵ ̵m̵a̵p̵_̵a̵d̵d̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

</details>
