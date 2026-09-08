# Parametrization task 5 completed

Date: 2026-09-08. Branch: `worker/parametrization-task-5`.
Base: `3e81aac61f86edba35a124d0e1599b68c65fe005`. Verified proof head: `005384bd897e81c893ac993659687fdb538ec3aa`.

## Result

`Poincare/Global/FixedChartUniformPreferredGermAgreement.lean` proves all three
requested targets in namespace `Poincare.FixedChartUniformPreferredGermAgreement`:

- `anchorFrame_isInvertible`
- `normalized_endpoint_eventuallyEq_expAt`
- `normal_eventuallyEq_generic_in_anchor_frame`

This meets stop condition (a), subject to independent orchestrator review.
No merge or task acceptance was performed. The diff adds exactly one Lean
file and this report. Existing Lean files, `Poincare.lean`, and `HANDOFF.md`
were not edited, following the task-specific file scope.

The shared instance binders are `[TopologicalSpace M] [ChartedSpace E M]
[IsManifold I ∞ M]`, where `E := ClosedSmoothModel 3` and
`I := closedSmoothModelWithCorners 3`. The comparisons take the retained
`C : FixedChartUniformSourceNormal.Patch g x₀ U` and the required fixed-zone
containment `hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀`.
`anchorFrame x₀ x` is exactly
`GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)`.
The exact-type examples below expand that definition and check the requested
quantifier order `∀ x ∈ C.anchors, EventuallyEq ...`.

The fixed-zone premise is the task's supplied position-neighborhood condition.
It is available by taking `U := IsometryInstantiate.cutoffOneLocus x₀` in
`FixedChartUniformSourceNormal.exists_patch`, using
`IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor`. The comparison adds no
joint preferred-chart continuity, uniform legacy radius, constant-curvature
premise, or `TransitionAgreementPackage`.

## Proof

The actual chart-transition derivative equals the composition of the forward
and inverse manifold chart differentials on the overlap. Both are invertible,
which proves the named frame lemma.

`eventually_position_mem_forall_time` uses stationarity at zero velocity and
the patch's joint continuity. Compactness of the subtype of `[-C.T,C.T]`
provides one small-velocity neighborhood whose trajectories stay in any
prescribed neighborhood of the fixed anchor for the whole interval.

`eventually_transported_solves` applies this to the common chart/cutoff-one
neighborhood. Chart-transition naturality supplies the preferred geodesic
ODE at every interior time. Smoothness of the transition and continuity of
its derivative give continuity at both interval endpoints as well.

For the endpoint theorem, the actual public exponential trajectory package
is reparameterized to `C.T`. Its velocity radius changes with that time,
which is harmless at a fixed anchor. The two continuous trajectory images
fit in a common compact ball, where the smooth preferred geodesic vector
field is Lipschitz. `ODE_solution_unique_of_mem_Icc` identifies their states
on the entire closed interval. At `C.T`, the public endpoint law and the
fixed chart's inverse law give the requested manifold equality with velocity
`anchorFrame x₀ x v`.

The inverse theorem pulls this endpoint neighborhood back along `C.normal x`.
The retained endpoint inverse law and the public exponential's eventual left
inverse identify the normal vectors. Both inverse laws retain their source
conditions. This direction of comparison only needs continuity of the frame;
its invertibility is proved separately as requested.

## Verification

All final commands below exited as recorded. The build replayed warnings in
existing dependencies; the new module's direct elaboration emitted no output.
Full root integration audits are left to the orchestrator. No full root build
was launched.

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformPreferredGermAgreement.lean
# output: empty
# exit: 0
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformPreferredGermAgreement
```

Build output, final lines:

```text
✔ [3605/3605] Built Poincare.Global.FixedChartUniformPreferredGermAgreement (2.8s)
Build completed successfully (3605 jobs).
EXIT_CODE=0
```

```sh
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/FixedChartUniformPreferredGermAgreement.lean
# output: empty; exit: 1 (no matches)
git diff --check
# output: empty; exit: 0
git diff 3e81aac61f86edba35a124d0e1599b68c65fe005 --check
# output: empty; exit: 0
```

### Exact declaration and statement probe

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/parametrization-task-5-evidence/probe.lean`.
Exit: 0. Scratch source is preserved here for independent replay:

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
open Filter Set
open scoped Manifold ContDiff Topology NNReal
open Poincare
open Poincare.FixedChartUniformPreferredGermAgreement
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
variable (C : FixedChartUniformSourceNormal.Patch g x₀ U)
variable (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
#check anchorFrame_isInvertible
#check normalized_endpoint_eventuallyEq_expAt
#check normal_eventuallyEq_generic_in_anchor_frame
example : ∀ x ∈ C.anchors,
    (GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)).IsInvertible :=
  anchorFrame_isInvertible C
example : ∀ x ∈ C.anchors,
    (fun v : E => (extChartAt I x₀).symm
      (FixedChartUniformNormalRadius.expChart C.α C.T
        (extChartAt I x₀ x) (C.T⁻¹ • v))) =ᶠ[𝓝 (0 : E)]
    (fun v => GeodesicTransport.expAt g x
      (GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x) v)) :=
  normalized_endpoint_eventuallyEq_expAt C hU
example : ∀ x ∈ C.anchors,
    (fun z : M => GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)
      (C.normal x z)) =ᶠ[𝓝 x]
    (fun z : M => (CartanSourceExponential.genericFamily g).normal x z) :=
  normal_eventuallyEq_generic_in_anchor_frame C hU
```

Actual output:

```text
Poincare.FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible.{u} {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold I ∞ M] {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
  (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) (hx : x ∈ C.anchors) : (anchorFrame x₀ x).IsInvertible
Poincare.FixedChartUniformPreferredGermAgreement.normalized_endpoint_eventuallyEq_expAt.{u} {M : Type u}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M] {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
  (C : FixedChartUniformSourceNormal.Patch g x₀ U) (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀) (x : M)
  (hx : x ∈ C.anchors) :
  (fun v =>
      ↑(extChartAt I x₀).symm
        (FixedChartUniformNormalRadius.expChart C.α C.T (↑(extChartAt I x₀) x) (C.T⁻¹ • v))) =ᶠ[𝓝 0]
    fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
Poincare.FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame.{u} {M : Type u}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M] {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
  (C : FixedChartUniformSourceNormal.Patch g x₀ U) (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀) (x : M)
  (hx : x ∈ C.anchors) :
  (fun z => (anchorFrame x₀ x) (↑(C.normal x) z)) =ᶠ[𝓝 x] fun z =>
    ↑((CartanSourceExponential.genericFamily g).normal x) z
```

### Module-wide dependency gate

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/parametrization-task-5-evidence/axioms.lean`.
Exit: 0. All seven theorem closures are exactly the permitted three axioms.
The namespace scan covers all 12 declarations generated by this module;
there are no private declarations outside that namespace.

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Lean
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame_of_endpoint_agreement
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.eventually_position_mem_forall_time
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.chartTransition_contDiffAt
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.eventually_transported_solves
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.normalized_endpoint_eventuallyEq_expAt
#print axioms Poincare.FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (n, _) in env.constants.toList do
    if (`Poincare.FixedChartUniformPreferredGermAgreement).isPrefixOf n then
      count := count + 1
      let axs ← collectAxioms n
      for a in axs do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
          throwError "nonstandard dependency {a} in {n}"
  logInfo m!"Checked {count} module declarations; all dependencies permitted."
```

Actual output:

```text
'Poincare.FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame_of_endpoint_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.eventually_position_mem_forall_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.chartTransition_contDiffAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.eventually_transported_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.normalized_endpoint_eventuallyEq_expAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FixedChartUniformPreferredGermAgreement.normal_eventuallyEq_generic_in_anchor_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Checked 12 module declarations; all dependencies permitted.
```

## Proof commits and diff

Each theorem was directly verified before its proof commit:

```text
fbc351b1 Prove preferred anchor frame invertibility on retained overlaps
b399c698 Transfer endpoint germ equality to preferred inverse normal coordinates
7aa609b6 Control fixed-anchor trajectories uniformly over the retained interval
5ba1d5c7 Prove smoothness of the transition on an honest chart overlap
d07f9e1d Prove the preferred-frame ODE for small velocities on the retained interval
7d6efa2a Identify normalized retained endpoints with the preferred exponential germ
005384bd Prove preferred-frame agreement of retained and generic normal germs
```

The final proof diff is preserved by these commits. Reproduce it with:

```sh
git diff 3e81aac61f86edba35a124d0e1599b68c65fe005 005384bd897e81c893ac993659687fdb538ec3aa -- Poincare/Global/FixedChartUniformPreferredGermAgreement.lean
```

## Compiler retries

The following are the complete nonempty outputs from intermediate direct
Lean checks. Each was a failed attempt, then corrected before committing the
associated theorem. The command for each numbered log was
`LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FixedChartUniformPreferredGermAgreement.lean`.
The numbered scratch logs also remain under `/tmp/parametrization-task-5-evidence`.
These errors were elaboration issues: implicit dimensions or functions,
set-preimage notation, coercion eta expansion, and rewriting after excessive
unfolding. No failed proof remains in the delivered module.

<details>
<summary>02-inverse.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:59:4: error: Type mismatch: After simplification, term
  ContinuousAt.tendsto (Continuous.continuousAt (ContinuousLinearMap.continuous (anchorFrame x₀ x)))
 has type
  Tendsto (⇑(anchorFrame x₀ x)) (𝓝 ?m.197) (𝓝 ((anchorFrame x₀ x) ?m.197))
but is expected to have type
  Tendsto (⇑(anchorFrame x₀ x)) (𝓝 0) (𝓝 0)
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:65:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  GeodesicTransport.expAt g x ((anchorFrame x₀ x) (↑(C.normal x) z))
in the target expression
  z ∈
    ⇑(anchorFrame x₀ x) ∘ ↑(C.normal x) ⁻¹'
      {x_1 |
        ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
            (↑(extChartAt I x) (GeodesicTransport.expAt g x x_1)) =
          x_1}

case h
M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
x : M
hx : x ∈ C.anchors
h : ↑(C.endpoint x) =ᶠ[𝓝 0] fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
hn : Tendsto (↑(C.normal x)) (𝓝 x) (𝓝 0)
hJ : Tendsto (⇑(anchorFrame x₀ x)) (𝓝 0) (𝓝 0)
hinv :
  ∀ᶠ (v : E) in 𝓝 0,
    ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm (↑(extChartAt I x) (GeodesicTransport.expAt g x v)) =
      v
z : M
hz : z ∈ ↑(C.normal x) ⁻¹' {x_1 | ↑(C.endpoint x) x_1 = GeodesicTransport.expAt g x ((anchorFrame x₀ x) x_1)}
hi :
  z ∈
    ⇑(anchorFrame x₀ x) ∘ ↑(C.normal x) ⁻¹'
      {x_1 |
        ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
            (↑(extChartAt I x) (GeodesicTransport.expAt g x x_1)) =
          x_1}
hs : z ∈ (C.normal x).source
he : GeodesicTransport.expAt g x ((anchorFrame x₀ x) (↑(C.normal x) z)) = z
⊢ (anchorFrame x₀ x) (↑(C.normal x) z) = ↑((CartanSourceExponential.genericFamily g).normal x) z
```

</details>

<details>
<summary>03-inverse.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:65:2: error: `dsimp` made no progress
```

</details>

<details>
<summary>04-inverse.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:65:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  GeodesicTransport.expAt g x ((anchorFrame x₀ x) (↑(C.normal x) z))
in the target expression
  z ∈
    ⇑(anchorFrame x₀ x) ∘ ↑(C.normal x) ⁻¹'
      {x_1 |
        ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
            (↑(extChartAt I x) (GeodesicTransport.expAt g x x_1)) =
          x_1}

case h
M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
x : M
hx : x ∈ C.anchors
h : ↑(C.endpoint x) =ᶠ[𝓝 0] fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
hn : Tendsto (↑(C.normal x)) (𝓝 x) (𝓝 0)
hJ : Tendsto (⇑(anchorFrame x₀ x)) (𝓝 0) (𝓝 0)
hinv :
  ∀ᶠ (v : E) in 𝓝 0,
    ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm (↑(extChartAt I x) (GeodesicTransport.expAt g x v)) =
      v
z : M
hz : z ∈ ↑(C.normal x) ⁻¹' {x_1 | ↑(C.endpoint x) x_1 = GeodesicTransport.expAt g x ((anchorFrame x₀ x) x_1)}
hi :
  z ∈
    ⇑(anchorFrame x₀ x) ∘ ↑(C.normal x) ⁻¹'
      {x_1 |
        ↑(GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
            (↑(extChartAt I x) (GeodesicTransport.expAt g x x_1)) =
          x_1}
hs : z ∈ (C.normal x).source
he : GeodesicTransport.expAt g x ((anchorFrame x₀ x) (↑(C.normal x) z)) = z
⊢ (anchorFrame x₀ x) (↑(C.normal x) z) = ↑((CartanSourceExponential.genericFamily g).normal x) z
```

</details>

<details>
<summary>08-transport.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:143:11: error: typeclass instance problem is stuck
  ChartedSpace (ClosedSmoothModel ?m.209) M

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `ChartedSpace` contain metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

</details>

<details>
<summary>09-transport.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:166:6: error: Tactic `apply` failed: could not unify the conclusion of `ContinuousAt.tendsto
  (ContDiffAt.continuousAt (chartTransition_contDiffAt x₀ x hz hx'))`
  ?U ∈ map (GeodesicTransport.chartTransition x₀ x) (𝓝 z)
with the goal
  ∀ᶠ (r : E) in 𝓝 z, GeodesicTransport.cutoff x (F r) = 1

Note: The full type of `ContinuousAt.tendsto (ContDiffAt.continuousAt (chartTransition_contDiffAt x₀ x hz hx'))` is
  Tendsto (GeodesicTransport.chartTransition x₀ x) (𝓝 z) (𝓝 (GeodesicTransport.chartTransition x₀ x z))

M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀
x : M
hx : x ∈ C.anchors
z : E := ↑(extChartAt I x₀) x
F : E → E := GeodesicTransport.chartTransition x₀ x
hz : z ∈ (extChartAt I x₀).target
hinv : ↑(extChartAt I x₀).symm z = x
hx' : ↑(extChartAt I x₀).symm z ∈ (extChartAt I x).source
hq : (z, 0) ∈ closedBall (↑(extChartAt I x₀) x₀, 0) ↑C.r
hzU : z ∈ U
V : Set E :=
  {q |
    ∀ᶠ (r : E) in 𝓝 q,
      r ∈ (extChartAt I x₀).target ∧
        ↑(extChartAt I x₀).symm r ∈ (extChartAt I x).source ∧
          GeodesicTransport.cutoff x₀ r = 1 ∧ GeodesicTransport.cutoff x (F r) = 1}
h1 : (extChartAt I x₀).target ∈ 𝓝 z
h2 : ↑(extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝 z
h3 : ∀ᶠ (z' : E) in 𝓝 z, GeodesicTransport.cutoff x₀ z' = 1
⊢ ∀ᶠ (r : E) in 𝓝 z, GeodesicTransport.cutoff x (F r) = 1
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:171:10: error(lean.invalidField): Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  h1
has type
  (𝓝 z).1 (extChartAt I x₀).target
which does not have the necessary form.
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:189:59: error: Application type mismatch: The argument
  hpos
has type
  ContinuousWithinAt (fun x => (C.α (z, w) x).1) (Icc (-C.T) C.T) t
but is expected to have type
  ContinuousWithinAt Prod.fst ?m.990 (C.α (z, w) t)
in the application
  ContinuousAt.comp_continuousWithinAt (ContDiffAt.continuousAt hF) hpos
```

</details>

<details>
<summary>10-transport.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:166:6: error: Tactic `apply` failed: could not unify the conclusion of `Tendsto.eventually
  (ContinuousAt.tendsto (ContDiffAt.continuousAt (chartTransition_contDiffAt x₀ x hz hx')))`
  ∀ᶠ (x_1 : E) in 𝓝 z, ?m.668 (GeodesicTransport.chartTransition x₀ x x_1)
with the goal
  ∀ᶠ (r : E) in 𝓝 z, GeodesicTransport.cutoff x (F r) = 1

Note: The full type of `Tendsto.eventually
  (ContinuousAt.tendsto (ContDiffAt.continuousAt (chartTransition_contDiffAt x₀ x hz hx')))` is
  (∀ᶠ (y : E) in 𝓝 (GeodesicTransport.chartTransition x₀ x z), ?m.668 y) →
    ∀ᶠ (x_1 : E) in 𝓝 z, ?m.668 (GeodesicTransport.chartTransition x₀ x x_1)

M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀
x : M
hx : x ∈ C.anchors
z : E := ↑(extChartAt I x₀) x
F : E → E := GeodesicTransport.chartTransition x₀ x
hz : z ∈ (extChartAt I x₀).target
hinv : ↑(extChartAt I x₀).symm z = x
hx' : ↑(extChartAt I x₀).symm z ∈ (extChartAt I x).source
hq : (z, 0) ∈ closedBall (↑(extChartAt I x₀) x₀, 0) ↑C.r
hzU : z ∈ U
V : Set E :=
  {q |
    ∀ᶠ (r : E) in 𝓝 q,
      r ∈ (extChartAt I x₀).target ∧
        ↑(extChartAt I x₀).symm r ∈ (extChartAt I x).source ∧
          GeodesicTransport.cutoff x₀ r = 1 ∧ GeodesicTransport.cutoff x (F r) = 1}
h1 : (extChartAt I x₀).target ∈ 𝓝 z
h2 : ↑(extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝 z
h3 : ∀ᶠ (z' : E) in 𝓝 z, GeodesicTransport.cutoff x₀ z' = 1
⊢ ∀ᶠ (r : E) in 𝓝 z, GeodesicTransport.cutoff x (F r) = 1
```

</details>

<details>
<summary>12-endpoint.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:214:4: error: Type mismatch: After simplification, term
  ContinuousAt.tendsto (Continuous.continuousAt (Continuous.const_smul continuous_id C.T⁻¹))
 has type
  Tendsto (fun x => C.T⁻¹ • id x) (𝓝 0) (𝓝 (C.T⁻¹ • id 0))
but is expected to have type
  Tendsto (fun v => C.T⁻¹ • v) (𝓝 0) (𝓝 0)
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:209:73: error: unsolved goals
M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀
x : M
hx : x ∈ C.anchors
P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x
Q : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x := P.reparameterize C.T ⋯
hQt : Q.time = C.T
hscale : Tendsto (fun v => C.T⁻¹ • v) (𝓝 0) (𝓝 0)
hJ : Tendsto (⇑(anchorFrame x₀ x)) (𝓝 0) (𝓝 0)
hsmall : ∀ᶠ (v : E) in 𝓝 0, ‖(anchorFrame x₀ x) (C.T⁻¹ • v)‖ < Q.velocityRadius
hendsource : (C.endpoint x).source ∈ 𝓝 0
hend : Tendsto (↑(C.endpoint x)) (𝓝 0) (𝓝 x)
⊢ (fun v =>
      ↑(extChartAt I x₀).symm
        (FixedChartUniformNormalRadius.expChart C.α C.T (↑(extChartAt I x₀) x) (C.T⁻¹ • v))) =ᶠ[𝓝 0]
    fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
```

</details>

<details>
<summary>13-endpoint.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:228:5: error: typeclass instance problem is stuck
  ChartedSpace ?m.494 M

Note: Lean will not try to resolve this typeclass instance problem because the first and second type arguments to `ChartedSpace` are metavariables. These arguments must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

</details>

<details>
<summary>14-endpoint.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:254:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v) 0
in the target expression
  (↑(chartAt E x) (↑(chartAt E x₀).symm (C.α (↑(chartAt E x₀) x, w) 0).1),
      (fderiv ℝ (GeodesicTransport.chartTransition x₀ x) (C.α (↑(chartAt E x₀) x, w) 0).1)
        (C.α (↑(chartAt E x₀) x, w) 0).2) =
    Q.trajectory u 0

M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
g : ClosedSmoothRiemannianMetric 3 M
x₀ : M
U : Set E
C : FixedChartUniformSourceNormal.Patch g x₀ U
hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀
x : M
hx : x ∈ C.anchors
P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x
Q : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x := P.reparameterize C.T ⋯
hQt : Q.time = C.T
hscale : Tendsto (fun v => C.T⁻¹ • v) (𝓝 0) (𝓝 0)
hJ : Tendsto (⇑(anchorFrame x₀ x)) (𝓝 0) (𝓝 0)
hsmall : ∀ᶠ (v : E) in 𝓝 0, ‖(anchorFrame x₀ x) (C.T⁻¹ • v)‖ < Q.velocityRadius
hendsource : (C.endpoint x).source ∈ 𝓝 0
hend : Tendsto (↑(C.endpoint x)) (𝓝 0) (𝓝 x)
hchart : ∀ᶠ (v : E) in 𝓝 0, ↑(C.endpoint x) v ∈ (extChartAt I x).source
v : E
hsol :
  ContinuousOn (GeodesicTransport.chartTransitionState x₀ x (C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v))) (Icc (-C.T) C.T) ∧
    ∀ t ∈ Ioo (-C.T) C.T,
      HasDerivAt (GeodesicTransport.chartTransitionState x₀ x (C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v)))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x)
          (GeodesicTransport.chartTransitionState x₀ x (C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v)) t))
        t
hv : ‖(anchorFrame x₀ x) (C.T⁻¹ • v)‖ < Q.velocityRadius
hvs : v ∈ (C.endpoint x).source
hvchart : ↑(C.endpoint x) v ∈ (extChartAt I x).source
w : E := C.T⁻¹ • v
u : E := (anchorFrame x₀ x) w
γ : ℝ → E × E := GeodesicTransport.chartTransitionState x₀ x (C.α (↑(extChartAt I x₀) x, w))
η : ℝ → E × E := Q.trajectory u
hu : ‖u‖ < Q.velocityRadius
hγc : ContinuousOn γ (Icc (-C.T) C.T)
hηd :
  ∀ t ∈ Icc (-C.T) C.T,
    HasDerivWithinAt η (geodesicFlowField (GeodesicTransport.chartChristoffelField g x) (η t)) (Icc (-C.T) C.T) t
hηc : ContinuousOn η (Icc (-C.T) C.T)
R : ℝ
hR : γ '' Icc (-C.T) C.T ∪ η '' Icc (-C.T) C.T ⊆ closedBall (↑(extChartAt I x) x, 0) R
K : ℝ≥0
hK :
  LipschitzOnWith K (geodesicFlowField (GeodesicTransport.chartChristoffelField g x))
    (closedBall (↑(extChartAt I x) x, 0) R)
h0 : C.α (↑(extChartAt I x₀) x, C.T⁻¹ • v) 0 = (↑(extChartAt I x₀) x, C.T⁻¹ • v)
hη0 : Q.trajectory u 0 = (↑(extChartAt I x) x, u)
⊢ (↑(chartAt E x) (↑(chartAt E x₀).symm (C.α (↑(chartAt E x₀) x, w) 0).1),
      (fderiv ℝ (GeodesicTransport.chartTransition x₀ x) (C.α (↑(chartAt E x₀) x, w) 0).1)
        (C.α (↑(chartAt E x₀) x, w) 0).2) =
    Q.trajectory u 0
```

</details>

<details>
<summary>16-final.log</summary>

```text
Poincare/Global/FixedChartUniformPreferredGermAgreement.lean:292:2: error: Type mismatch: After simplification, term
  normalized_endpoint_eventuallyEq_expAt C hU x hx
 has type
  (fun v =>
      ↑(extChartAt I x₀).symm
        (FixedChartUniformNormalRadius.expChart C.α C.T (↑(extChartAt I x₀) x) (C.T⁻¹ • v))) =ᶠ[𝓝 0]
    fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
but is expected to have type
  ↑(C.endpoint x) =ᶠ[𝓝 0] fun v => GeodesicTransport.expAt g x ((anchorFrame x₀ x) v)
```

</details>

API discovery probes also rejected guessed names. Their complete outputs
are retained below; the final implementation uses the checked APIs.

<details>
<summary>api.log</summary>

```text
/tmp/parametrization-task-5-evidence/api.lean:3:7: error(lean.unknownIdentifier): Unknown constant `ContinuousWithinAt.comp_continuousAt`
ContinuousWithinAt.comp.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] {f : α → β} {s : Set α} {x : α} {g : β → γ} {t : Set β}
  (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : Set.MapsTo f s t) :
  ContinuousWithinAt (g ∘ f) s x
ContinuousOn.comp_continuous.{u_1, u_2, u_3} {α : Type u_1} {β : Type u_2} {γ : Type u_3} [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ] {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
  (hf : Continuous f) (hs : ∀ (x : α), f x ∈ s) : Continuous (g ∘ f)
ContinuousOn.continuousAt.{u_1, u_2} {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
  {s : Set α} {x : α} (h : ContinuousOn f s) (hx : s ∈ nhds x) : ContinuousAt f x
IsCompact.eventually_forall_of_forall_eventually.{u, v} {X : Type u} {Y : Type v} [TopologicalSpace X]
  [TopologicalSpace Y] {x₀ : X} {K : Set Y} (hK : IsCompact K) {P : X → Y → Prop}
  (hP : ∀ y ∈ K, ∀ᶠ (z : X × Y) in nhds (x₀, y), P z.1 z.2) : ∀ᶠ (x : X) in nhds x₀, ∀ y ∈ K, P x y
continuous_subtype_val.{u} {X : Type u} [TopologicalSpace X] {p : X → Prop} : Continuous Subtype.val
/tmp/parametrization-task-5-evidence/api.lean:9:7: error(lean.unknownIdentifier): Unknown constant `HasFDerivAt.contDiffAt`
/tmp/parametrization-task-5-evidence/api.lean:10:7: error(lean.unknownIdentifier): Unknown identifier `contDiffOn_extChartAt_symm_comp_extChartAt`
/tmp/parametrization-task-5-evidence/api.lean:11:7: error(lean.unknownIdentifier): Unknown identifier `contDiffWithinAt_extChartAt_symm_comp_extChartAt`
/tmp/parametrization-task-5-evidence/api.lean:12:7: error(lean.unknownIdentifier): Unknown identifier `contDiffAt_extChartAt_symm_comp_extChartAt`
ContDiffAt.fderiv_right.{u_1, u_2, u_3} {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x₀ : E}
  {m n : WithTop ℕ∞} (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
ContDiffAt.continuousAt_fderiv.{u_1, u_2, u_3} {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E} {n : WithTop ℕ∞}
  (hf : ContDiffAt 𝕜 n f x) (hn : n ≠ 0) : ContinuousAt (fderiv 𝕜 f) x
```

</details>

## Handoff

Exact first independent review action:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.FixedChartUniformPreferredGermAgreement
```

Then replay the exact-type and module-wide probes above and inspect the diff
against the recorded base. This closes the fifth bounded foundation task.
The supplied successor/data interfaces, joint-radius tasks, and recognition
remain separate work. No uniform comparison radius over moving anchors is
claimed by this module.
