# Fixed-chart uniform source normal completed

Date: 2026-09-08. Branch: `worker/fixed-chart-uniform-source-normal`.
Base: `0218a20262fa75f6d96a775eabb917b78f7e0309`. Verified proof head: `26efa2d4855415c24b121eb675a15711b6388005`.

## Result

`Poincare/Global/FixedChartUniformSourceNormal.lean` supplies the exact retained
`Patch`, constructs it with `exists_patch`, and defines `Patch.normal` and
`Patch.rawLocalFamily`. This meets stop condition (a), subject to independent
orchestrator review and acceptance. No merge or task acceptance was performed.

The patch keeps the common `r,T,α`, ODE law, position control in the supplied
`U`, joint continuity, C¹ endpoint information, strict derivative, and a single
product inverse `P`. Its open coordinate-anchor set is the zero-section
preimage of `P.source`. The retained source-ball inclusion proves that this
set lies in `ball c r`; ODE uniqueness proves stationarity there. The compact
clause is copied unchanged, with coverage by the image of `ball 0 R` and
injectivity on `ball 0 ρ`.

`Patch.endpoint` composes the `T⁻¹` continuous linear equivalence, task 3's
exact slice, and the inverse fixed manifold chart. `Patch.normal` is its
inverse. The forward function is exactly the prescribed rescaled endpoint.
The source of `normal x` is exactly the fixed chart source intersected with
the preimage of the product target at anchor `extChartAt I x₀ x`. This keeps
all inverse laws on their proper domains. Both anchor laws are proved for
all anchors in the retained manifold patch, and the center belongs to it.

`sourceLocus_eq_endpointLocus` identifies the joint normal source with the
existing endpoint locus. Its openness and the continuous normal evaluator
follow from `CartanSourceExponentialLocalFamilyTransport` and multiplication
by `T`. `rawLocalFamily` has definitionally the required anchors, joint
normal-source locus, and normal evaluator. It has no endpoint-agreement
premise. The two final lemmas retain initial-ball and position-control facts
for every velocity in the composed endpoint source.

The result does not compare the old selected exponential or prove H1, H2,
sphere recognition, or the Poincare conjecture. The next mathematical task
is the fixed-anchor frame/germ comparison in inventory task 5.

The current worktree status, worktree list, and commit were checked before
editing. The assigned worker branch was retained as explicitly requested.
Only one new Lean file was added; no existing Lean file or `Poincare.lean`
was changed. The report and the required dated HANDOFF update are the only
other deliverables.

## Verification commands and actual output

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformSourceNormal.lean
```

Final direct elaboration: exit 0, no output, recorded in
`/tmp/source-normal-06.log`. Earlier successful checkpoints were
`/tmp/source-normal-01.log`, `03.log`, and `05.log`, each exit 0 with no output.
Every proof commit contains compiler-verified work.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformSourceNormal
```

Exit 0. Final output:

```text
✔ [3548/3548] Built Poincare.Global.FixedChartUniformSourceNormal (2.0s)
Build completed successfully (3548 jobs).
```

The build replayed warnings from unchanged dependencies. There were no
warnings from the new module. The full build log is
`/tmp/source-normal-build.log`. No full root build or integration audit was
launched by this worker.

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartUniformSourceNormal.lean
git diff --check
git diff 0218a20262fa75f6d96a775eabb917b78f7e0309 --check
```

Forbidden-token scan: exit 1, no matches. Both diff checks: exit 0, no output.

### Exact declaration and field probe

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/source-normal-probe.lean
```

Exit 0. Reproducible probe source:

```lean
import Poincare.Global.FixedChartUniformSourceNormal
open Poincare Poincare.FixedChartUniformSourceNormal
open Filter Metric Set
open scoped Topology Manifold NNReal ContDiff
#check Patch
#check exists_patch
#check Patch.normal
#check Patch.normal_anchor
#check Patch.anchor_mem_normal_source
#check Patch.rawLocalFamily
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set E)
example : U ∈ 𝓝 (extChartAt I x₀ x₀) → Nonempty (Patch g x₀ U) := exists_patch g x₀
variable (C : Patch g x₀ U)
example : ∀ x ∈ C.anchors, C.normal x x = 0 := C.normal_anchor
example : ∀ x ∈ C.anchors, x ∈ (C.normal x).source := C.anchor_mem_normal_source
example : C.rawLocalFamily.anchors = C.anchors := rfl
example : C.rawLocalFamily.sourceLocus =
    {q : M × M | q.1 ∈ C.anchors ∧ q.2 ∈ (C.normal q.1).source} := rfl
example : C.rawLocalFamily.normal = fun q => C.normal q.1 q.2 := rfl
example (x : M) (v : E) : C.endpoint x v = (extChartAt I x₀).symm
    (FixedChartUniformNormalRadius.expChart C.α C.T (extChartAt I x₀ x) (C.T⁻¹ • v)) :=
  C.endpoint_apply x v
example : ∀ K : Set E, IsCompact K → K ⊆ ball (extChartAt I x₀ x₀) (C.r : ℝ) →
    ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ z ∈ K,
      InjOn (FixedChartUniformNormalRadius.expChart C.α C.T z) (ball 0 ρ) ∧
      ball z ρ ⊆ FixedChartUniformNormalRadius.expChart C.α C.T z '' ball 0 R :=
  C.compact_radius
```

Actual output:

```text
Poincare.FixedChartUniformSourceNormal.Patch.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set (ClosedSmoothModel 3)) : Type
Poincare.FixedChartUniformSourceNormal.exists_patch.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {U : Set (ClosedSmoothModel 3)}
  (hU : U ∈ 𝓝 (↑(extChartAt (closedSmoothModelWithCorners 3) x₀) x₀)) : Nonempty (Patch g x₀ U)
Poincare.FixedChartUniformSourceNormal.Patch.normal.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  OpenPartialHomeomorph M (ClosedSmoothModel 3)
Poincare.FixedChartUniformSourceNormal.Patch.normal_anchor.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  x ∈ C.anchors → ↑(C.normal x) x = 0
Poincare.FixedChartUniformSourceNormal.Patch.anchor_mem_normal_source.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  x ∈ C.anchors → x ∈ (C.normal x).source
Poincare.FixedChartUniformSourceNormal.Patch.rawLocalFamily.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) :
  CartanSourceExponential.LocalFamily g
```

### Named and module-wide axiom gate

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/source-normal-axioms.lean
```

Exit 0. All 16 theorem closures are exactly
`[propext, Classical.choice, Quot.sound]`. The scan includes all 64 declarations
under the module namespace, including structure projections and recursors.

Probe source:

```lean
import Poincare.Global.FixedChartUniformSourceNormal
import Lean
#print axioms Poincare.FixedChartUniformSourceNormal.exists_patch
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.preserves_fst
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.isOpen_anchors
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.center_mem_anchors
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.endpoint_apply
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.zero_mem_endpoint_source
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.endpoint_zero
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.anchor_mem_normal_source
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.normal_anchor
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.normal_source
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.normal_apply
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.sourceLocus_eq_endpointLocus
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.isOpen_normal_sourceLocus
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.continuousOn_normal_eval
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.endpoint_source_initial_mem
#print axioms Poincare.FixedChartUniformSourceNormal.Patch.endpoint_source_position_mem
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.FixedChartUniformSourceNormal).isPrefixOf n then
      count := count + 1
      let axs ← collectAxioms n
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "nonstandard dependency {a} in {n}"
  logInfo m!"Checked {count} module declarations; all dependencies permitted."
```

Actual output:

```text
'Poincare.FixedChartUniformSourceNormal.exists_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.preserves_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.isOpen_anchors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.center_mem_anchors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.endpoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.zero_mem_endpoint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.endpoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.anchor_mem_normal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.normal_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.normal_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.normal_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.sourceLocus_eq_endpointLocus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.isOpen_normal_sourceLocus' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.continuousOn_normal_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.endpoint_source_initial_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformSourceNormal.Patch.endpoint_source_position_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Checked 64 module declarations; all dependencies permitted.
```

## Failed compiler evidence

The first endpoint/anchor attempt exited 1 because `extChartAt.source` needs
its named source equality to match `chartAt.source`, and rewriting the anchor
value backwards also rewrote the chart's anchor argument. Using
`extChartAt_source` and simplifying the already-established inverse-law
conclusion fixed these errors without changing a hypothesis or target.
`/tmp/source-normal-02.log`:

```text
Poincare/Global/FixedChartUniformSourceNormal.lean:154:36: error: Application type mismatch: The argument
  hx.left
has type
  x ∈ (extChartAt I x₀).source
but is expected to have type
  x ∈ (chartAt E x₀).source
in the application
  OpenPartialHomeomorph.map_source (chartAt E x₀) hx.left
Poincare/Global/FixedChartUniformSourceNormal.lean:161:32: error: Application type mismatch: The argument
  hx.left
has type
  x ∈ (extChartAt I x₀).source
but is expected to have type
  x ∈ (chartAt E x₀).source
in the application
  OpenPartialHomeomorph.left_inv (chartAt E x₀) hx.left
Poincare/Global/FixedChartUniformSourceNormal.lean:167:2: error: Type mismatch
  OpenPartialHomeomorph.map_source (C.endpoint x) (zero_mem_endpoint_source C x hx)
has type
  ↑(C.endpoint x) 0 ∈ (C.endpoint x).target
but is expected to have type
  ↑(C.endpoint x) 0 ∈ (C.normal (↑(C.endpoint x) 0)).source
Poincare/Global/FixedChartUniformSourceNormal.lean:173:2: error: Type mismatch
  OpenPartialHomeomorph.left_inv (C.endpoint x) (zero_mem_endpoint_source C x hx)
has type
  ↑(C.endpoint x).symm (↑(C.endpoint x) 0) = 0
but is expected to have type
  ↑(C.normal (↑(C.endpoint x) 0)) (↑(C.endpoint x) 0) = 0
```

The first continuity attempt supplied the constant argument to `smul`
instead of `continuousOn_const`. Exit 1; moving that argument fixed the
elaboration error. `/tmp/source-normal-04.log`:

```text
Poincare/Global/FixedChartUniformSourceNormal.lean:218:58: error: Invalid argument name `c` for function `ContinuousOn.smul`

Hint: Perhaps you meant one of the following parameter names:
  • `M`: c̵M̲
  • `X`: c̵X̲
  • `Y`: c̵Y̲
  • `f`: c̵f̲
  • `g`: c̵g̲
  • `s`: c̵s̲
  • `hf`: c̵h̲f̲
  • `hg`: c̵h̲g̲
  • `x`: c̵x̲
  • `U`: c̵U̲
Poincare/Global/FixedChartUniformSourceNormal.lean:214:61: error: unsolved goals
M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : Patch g x₀ U
B : CartanSourceExponential.LocalFamily g :=
  CartanSourceExponentialLocalFamilyTransport.localFamilyOfAnchorEndpoint g x₀ C.P C.A ⋯ ⋯ ⋯
⊢ ContinuousOn (fun q => ↑(C.normal q.1) q.2) (CartanSourceExponentialLocalFamilyTransport.endpointLocus x₀ C.P C.A)
```

The first scratch exact-field probe omitted `open scoped ContDiff`, so its
`∞` binder failed to parse, causing subsequent instance errors. Adding the
scope made the unchanged target checks pass. The first attempt exited 1;
its full output is preserved below from
`/tmp/source-normal-probe-first-failure.log`:

```text
Poincare.FixedChartUniformSourceNormal.Patch.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set (ClosedSmoothModel 3)) : Type
Poincare.FixedChartUniformSourceNormal.exists_patch.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) {U : Set (ClosedSmoothModel 3)}
  (hU : U ∈ 𝓝 (↑(extChartAt (closedSmoothModelWithCorners 3) x₀) x₀)) : Nonempty (Patch g x₀ U)
Poincare.FixedChartUniformSourceNormal.Patch.normal.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  OpenPartialHomeomorph M (ClosedSmoothModel 3)
Poincare.FixedChartUniformSourceNormal.Patch.normal_anchor.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  x ∈ C.anchors → ↑(C.normal x) x = 0
Poincare.FixedChartUniformSourceNormal.Patch.anchor_mem_normal_source.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) (x : M) :
  x ∈ C.anchors → x ∈ (C.normal x).source
Poincare.FixedChartUniformSourceNormal.Patch.rawLocalFamily.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set (ClosedSmoothModel 3)} (C : Patch g x₀ U) :
  CartanSourceExponential.LocalFamily g
/tmp/source-normal-probe.lean:13:75: error: expected token
/tmp/source-normal-probe.lean:14:14: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:15:17: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:15:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:15:66: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:16:14: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:17:10: error: typeclass instance problem is stuck
  Membership ?m.13 (?m.21 x)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Membership` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
/tmp/source-normal-probe.lean:18:27: error: typeclass instance problem is stuck
  Membership ?m.13 (?m.23 x)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Membership` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
/tmp/source-normal-probe.lean:21:17: error: typeclass instance problem is stuck
  Membership M (?m.26 q)

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Membership` contains metavariables. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
/tmp/source-normal-probe.lean:22:40: error(lean.inferBinderTypeFailed): Failed to infer type of binder `q`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
/tmp/source-normal-probe.lean:23:44: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
/tmp/source-normal-probe.lean:26:47: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  TopologicalSpace M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Pre-edit API probes also rejected guessed names
`ContinuousLinearEquiv.smulOfNeZero`, `extChartAt_toOpenPartialHomeomorph`,
`ContinuousLinearEquiv.unitsSMul`, and `ContinuousLinearEquiv.smulOfUnit`.
The implemented continuous linear equivalence extends the existing
`LinearEquiv.smulOfNeZero`, and the fixed manifold chart is `chartAt E x₀`,
whose forward and inverse functions were checked definitionally equal to
those of `extChartAt I x₀` in this boundaryless model.

## Proof commits

```text
b55b72d4 Construct retained uniform fixed-chart flow patch
dd95ecb9 Construct time-normalized endpoint charts and prove anchor laws
f9f3122f Prove joint inverse regularity and construct the exact local family
26efa2d4 Retain flow position control on the composed endpoint source
```

## Final proof diff

Reproduce with `git diff 0218a20262fa75f6d96a775eabb917b78f7e0309 26efa2d4855415c24b121eb675a15711b6388005 -- Poincare/Global/FixedChartUniformSourceNormal.lean`.

```diff
diff --git a/Poincare/Global/FixedChartUniformSourceNormal.lean b/Poincare/Global/FixedChartUniformSourceNormal.lean
new file mode 100644
index 00000000..7a712c44
--- /dev/null
+++ b/Poincare/Global/FixedChartUniformSourceNormal.lean
@@ -0,0 +1,248 @@
+import Poincare.Global.FixedChartUniformNormalRadius
+import Poincare.Global.FixedChartEndpointSlices
+import Poincare.Global.CartanSourceExponentialLocalFamilyTransport
+
+/-!
+# Normal coordinates from one retained fixed-chart flow
+
+The common flow, product inverse, and compact radii are retained together.
+Manifold normal charts use the exact vertical slices and normalize velocity
+by the common positive time. All inverse laws retain their chart domains.
+-/
+
+noncomputable section
+
+open Filter Function Metric Set
+open scoped Topology ContDiff NNReal Manifold
+
+namespace Poincare.FixedChartUniformSourceNormal
+
+universe u
+local notation "E" => ClosedSmoothModel 3
+local notation "I" => closedSmoothModelWithCorners 3
+
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
+  [IsManifold I ∞ M]
+
+/-- One common flow and product inverse, with the original quantitative bounds. -/
+structure Patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set E) where
+  r : ℝ≥0
+  r_pos : 0 < r
+  T : ℝ
+  T_pos : 0 < T
+  α : (E × E) → ℝ → E × E
+  flow_law : ∀ q ∈ closedBall (extChartAt I x₀ x₀, 0) (r : ℝ),
+    α q 0 = q ∧ ∀ t ∈ Icc (-T) T, HasDerivWithinAt (α q)
+      (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀) (α q t))
+      (Icc (-T) T) t
+  position_mem : ∀ q ∈ closedBall (extChartAt I x₀ x₀, 0) (r : ℝ),
+    ∀ t ∈ Icc (-T) T, (α q t).1 ∈ U
+  continuous_flow : ContinuousOn (Function.uncurry α)
+    (closedBall (extChartAt I x₀ x₀, 0) (r : ℝ) ×ˢ Icc (-T) T)
+  endpoint_C1 : ContDiffOn ℝ 1 (fun q => α q T)
+    (ball (extChartAt I x₀ x₀, 0) (r : ℝ))
+  endpoint_strict : ∀ z ∈ ball (extChartAt I x₀ x₀) (r : ℝ),
+    HasStrictFDerivAt (FixedChartUniformNormalRadius.F α T)
+      (FixedChartUniformNormalRadius.endpointDerivative T) (z, 0)
+  P : OpenPartialHomeomorph (E × E) (E × E)
+  P_eq : (P : (E × E) → (E × E)) = FixedChartUniformNormalRadius.F α T
+  P_source_subset : P.source ⊆ ball (extChartAt I x₀ x₀, 0) (r : ℝ)
+  A : Set E
+  A_open : IsOpen A
+  center_mem : extChartAt I x₀ x₀ ∈ A
+  A_subset : A ⊆ ball (extChartAt I x₀ x₀) (r : ℝ)
+  zero_mem_source : ∀ z ∈ A, (z, (0 : E)) ∈ P.source
+  stationary : ∀ z ∈ A, P (z, 0) = (z, z)
+  compact_radius : ∀ K : Set E, IsCompact K →
+    K ⊆ ball (extChartAt I x₀ x₀) (r : ℝ) →
+    ∀ R > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ z ∈ K,
+      InjOn (FixedChartUniformNormalRadius.expChart α T z) (ball 0 ρ) ∧
+      ball z ρ ⊆ FixedChartUniformNormalRadius.expChart α T z '' ball 0 R
+
+/-- Construct the retained patch from the uniform fixed-chart flow theorem. -/
+theorem exists_patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
+    {U : Set E} (hU : U ∈ 𝓝 (extChartAt I x₀ x₀)) :
+    Nonempty (Patch g x₀ U) := by
+  obtain ⟨r, hr, T, hT, α, hflow, hpos, hcont, hC1, hstrict, hlocal, hcompact⟩ :=
+    FixedChartUniformNormalRadius.exists_uniform_local_geodesic_chart_flow_normal_neighborhoods
+      g x₀ hU
+  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
+  obtain ⟨ρ, hρ, P, hP, hcenter, hsub, _, _, _⟩ :=
+    hlocal (extChartAt I x₀ x₀) (mem_ball_self hr') 1 zero_lt_one
+  let A : Set E := {z | (z, (0 : E)) ∈ P.source}
+  have hAsub : A ⊆ ball (extChartAt I x₀ x₀) (r : ℝ) := by
+    intro z hz
+    simpa using hsub hz
+  refine ⟨{
+    r := r, r_pos := hr, T := T, T_pos := hT, α := α
+    flow_law := hflow, position_mem := hpos, continuous_flow := hcont
+    endpoint_C1 := hC1, endpoint_strict := hstrict
+    P := P, P_eq := hP, P_source_subset := hsub
+    A := A
+    A_open := P.open_source.preimage (continuous_id.prodMk continuous_const)
+    center_mem := hcenter, A_subset := hAsub
+    zero_mem_source := fun _ hz => hz
+    stationary := ?_
+    compact_radius := hcompact }⟩
+  intro z hz
+  have hzball := ball_subset_closedBall (hsub hz)
+  have hstat := FixedChartUniformNormalRadius.flow_zero_velocity
+    (contDiff_geodesicFlowField (GeodesicTransport.chartChristoffelField_contDiff g x₀))
+    hT (hflow (z, 0) hzball).1 (hflow (z, 0) hzball).2 T
+    (by constructor <;> linarith)
+  rw [congrFun hP]
+  exact Prod.ext rfl (congrArg Prod.fst hstat)
+
+namespace Patch
+
+variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
+variable (C : Patch g x₀ U)
+
+/-- The retained product map preserves the anchor coordinate. -/
+theorem preserves_fst : ∀ q ∈ C.P.source, (C.P q).1 = q.1 := by
+  intro q _
+  rw [congrFun C.P_eq]
+  rfl
+
+/-- Time normalization, from time-one velocities to the common flow time. -/
+def timeRescaling : E ≃L[ℝ] E :=
+  { LinearEquiv.smulOfNeZero ℝ E C.T⁻¹ (inv_ne_zero C.T_pos.ne') with
+    continuous_toFun := continuous_const.smul continuous_id
+    continuous_invFun := continuous_const.smul continuous_id }
+
+/-- Exact endpoint slice followed by the inverse fixed manifold chart. -/
+def endpoint (x : M) : OpenPartialHomeomorph E M :=
+  (C.timeRescaling.toHomeomorph.toOpenPartialHomeomorph.trans
+    (FixedChartEndpointSlices.slice C.P C.preserves_fst (extChartAt I x₀ x))).trans
+      (chartAt E x₀).symm
+
+/-- Normal vectors in the fixed chart's time-one velocity frame. -/
+def normal (x : M) : OpenPartialHomeomorph M E := (C.endpoint x).symm
+
+/-- Anchors retained in both the fixed manifold chart and the product patch. -/
+def anchors : Set M :=
+  CartanSourceExponentialLocalFamilyTransport.anchorSet x₀ C.A
+
+/-- The manifold anchor set is open. -/
+theorem isOpen_anchors : IsOpen C.anchors :=
+  CartanSourceExponentialLocalFamilyTransport.isOpen_anchorSet x₀ C.A_open
+
+/-- The central manifold point is retained. -/
+theorem center_mem_anchors : x₀ ∈ C.anchors :=
+  ⟨mem_extChartAt_source x₀, C.center_mem⟩
+
+/-- The forward chart is exactly the specified time-normalized endpoint. -/
+theorem endpoint_apply (x : M) (v : E) :
+    C.endpoint x v = (extChartAt I x₀).symm
+      (FixedChartUniformNormalRadius.expChart C.α C.T
+        (extChartAt I x₀ x) (C.T⁻¹ • v)) := by
+  change (chartAt E x₀).symm
+    (C.P (extChartAt I x₀ x, C.T⁻¹ • v)).2 = _
+  rw [congrFun C.P_eq]
+  rfl
+
+/-- Zero belongs to the composed endpoint source at every retained anchor. -/
+theorem zero_mem_endpoint_source : ∀ x ∈ C.anchors, 0 ∈ (C.endpoint x).source := by
+  intro x hx
+  change (0 ∈ (C.timeRescaling.toHomeomorph.toOpenPartialHomeomorph.trans
+    (FixedChartEndpointSlices.slice C.P C.preserves_fst (extChartAt I x₀ x))).source) ∧ _
+  constructor
+  · change (0 ∈ (Set.univ : Set E)) ∧ (extChartAt I x₀ x, C.T⁻¹ • (0 : E)) ∈ C.P.source
+    exact ⟨mem_univ _, by simpa using C.zero_mem_source _ hx.2⟩
+  · change (C.P (extChartAt I x₀ x, C.T⁻¹ • (0 : E))).2 ∈ (chartAt E x₀).target
+    rw [smul_zero, C.stationary _ hx.2]
+    exact (chartAt E x₀).map_source (by simpa only [extChartAt_source] using hx.1)
+
+/-- The endpoint at zero is the retained anchor. -/
+theorem endpoint_zero : ∀ x ∈ C.anchors, C.endpoint x 0 = x := by
+  intro x hx
+  change (chartAt E x₀).symm (C.P (extChartAt I x₀ x, C.T⁻¹ • (0 : E))).2 = x
+  rw [smul_zero, C.stationary _ hx.2]
+  exact (chartAt E x₀).left_inv (by simpa only [extChartAt_source] using hx.1)
+
+/-- Each retained anchor lies in its normal source. -/
+theorem anchor_mem_normal_source : ∀ x ∈ C.anchors, x ∈ (C.normal x).source := by
+  intro x hx
+  simpa only [C.endpoint_zero x hx] using
+    (C.endpoint x).map_source (C.zero_mem_endpoint_source x hx)
+
+/-- Normal coordinates send each retained anchor to zero. -/
+theorem normal_anchor : ∀ x ∈ C.anchors, C.normal x x = 0 := by
+  intro x hx
+  simpa only [C.endpoint_zero x hx] using
+    (C.endpoint x).left_inv (C.zero_mem_endpoint_source x hx)
+
+/-- The normal source retains precisely the fixed chart and slice target domains. -/
+theorem normal_source (x : M) :
+    (C.normal x).source = (extChartAt I x₀).source ∩
+      {y | (extChartAt I x₀ x, extChartAt I x₀ y) ∈ C.P.target} := by
+  ext y
+  change (y ∈ (chartAt E x₀).source ∧
+    ((extChartAt I x₀ x, extChartAt I x₀ y) ∈ C.P.target ∧
+      (C.P.symm (extChartAt I x₀ x, extChartAt I x₀ y)).2 ∈ (univ : Set E))) ↔ _
+  simp only [mem_univ, and_true, mem_inter_iff, mem_setOf_eq, extChartAt_source]
+
+/-- The inverse multiplies the retained inverse-flow velocity by the common time. -/
+theorem normal_apply (x y : M) :
+    C.normal x y = C.T • (C.P.symm (extChartAt I x₀ x, extChartAt I x₀ y)).2 := by
+  change (C.T⁻¹)⁻¹ • (C.P.symm (extChartAt I x₀ x, extChartAt I x₀ y)).2 = _
+  rw [inv_inv]
+
+/-- The joint inverse domain is the existing fixed-chart endpoint locus. -/
+theorem sourceLocus_eq_endpointLocus :
+    {q : M × M | q.1 ∈ C.anchors ∧ q.2 ∈ (C.normal q.1).source} =
+      CartanSourceExponentialLocalFamilyTransport.endpointLocus x₀ C.P C.A := by
+  ext q
+  rw [mem_setOf_eq, C.normal_source]
+  change (q.1 ∈ C.anchors ∧ (q.2 ∈ (extChartAt I x₀).source ∧
+    (extChartAt I x₀ q.1, extChartAt I x₀ q.2) ∈ C.P.target)) ↔
+    (q.1 ∈ C.anchors ∧ ((q.1 ∈ (extChartAt I x₀).source ∧
+      q.2 ∈ (extChartAt I x₀).source) ∧
+      (extChartAt I x₀ q.1, extChartAt I x₀ q.2) ∈ C.P.target))
+  exact ⟨fun h => ⟨h.1, ⟨h.1.1, h.2.1⟩, h.2.2⟩,
+    fun h => ⟨h.1, h.2.1.2, h.2.2⟩⟩
+
+/-- The exact joint normal source over the retained anchors is open. -/
+theorem isOpen_normal_sourceLocus :
+    IsOpen {q : M × M | q.1 ∈ C.anchors ∧ q.2 ∈ (C.normal q.1).source} := by
+  rw [C.sourceLocus_eq_endpointLocus]
+  exact CartanSourceExponentialLocalFamilyTransport.isOpen_endpointLocus x₀ C.P C.A_open
+
+/-- Normal evaluation is jointly continuous on its exact source locus. -/
+theorem continuousOn_normal_eval :
+    ContinuousOn (fun q : M × M => C.normal q.1 q.2)
+      {q | q.1 ∈ C.anchors ∧ q.2 ∈ (C.normal q.1).source} := by
+  rw [C.sourceLocus_eq_endpointLocus]
+  let B := CartanSourceExponentialLocalFamilyTransport.localFamilyOfAnchorEndpoint
+    g x₀ C.P C.A C.A_open C.zero_mem_source C.stationary
+  have h := (continuousOn_const (c := C.T)).smul B.continuousOn_normal
+  simpa only [normal_apply] using h
+
+/-- The local family has exactly the retained anchors, normal sources, and inverse evaluator. -/
+def rawLocalFamily : CartanSourceExponential.LocalFamily g where
+  anchors := C.anchors
+  isOpen_anchors := C.isOpen_anchors
+  sourceLocus := {q | q.1 ∈ C.anchors ∧ q.2 ∈ (C.normal q.1).source}
+  isOpen_sourceLocus := C.isOpen_normal_sourceLocus
+  sourceLocus_fst := fun _ hq => hq.1
+  normal q := C.normal q.1 q.2
+  continuousOn_normal := C.continuousOn_normal_eval
+  diagonal_mem x hx := ⟨hx, C.anchor_mem_normal_source x hx⟩
+  normal_diagonal := C.normal_anchor
+
+/-- Every endpoint-source velocity lies in the retained flow's initial ball. -/
+theorem endpoint_source_initial_mem {x : M} {v : E}
+    (hv : v ∈ (C.endpoint x).source) :
+    (extChartAt I x₀ x, C.T⁻¹ • v) ∈
+      closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ) := by
+  exact ball_subset_closedBall (C.P_source_subset hv.1.2)
+
+/-- The retained position control applies along every endpoint-source trajectory. -/
+theorem endpoint_source_position_mem {x : M} {v : E}
+    (hv : v ∈ (C.endpoint x).source) :
+    ∀ t ∈ Icc (-C.T) C.T,
+      (C.α (extChartAt I x₀ x, C.T⁻¹ • v) t).1 ∈ U :=
+  C.position_mem _ (C.endpoint_source_initial_mem hv)
+
+end Patch
+end Poincare.FixedChartUniformSourceNormal
```

## Handoff

Exact first independent review action:
`LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformSourceNormal`.
Then replay the two retained probes and check the diff against the recorded
base. The following mathematical action is inventory task 5, the fixed-anchor
preferred-frame germ comparison, using this patch with its supplied position
neighborhood inside the fixed chart's cutoff-one zone.
