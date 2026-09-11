# heat-duhamel-hessian-time-holder: done

2026-09-11. Worker branch `worker/heat-duhamel-hessian-time-holder`.
Base `c165951b1506056533cbb63ccc0e52e45cffb0ab`. Verified proof head `b2537b0dd188544bcd759f4be0ad124e10581900`.

The exact frozen `Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder`
is proved in `Poincare/Global/HeatDuhamelHessianTimeHolder.lean`. The complete source compiles without warnings, and
an assignment of this declaration to the unchanged task statement compiles.
The module contains 22 theorems, one concrete bilinear-form definition, and
two local instances. All 25 declarations have exactly
`[propext, Classical.choice, Quot.sound]`, checked with `#print axioms` and an
exact-set assertion over the compiled module.

Only the new Lean module and this report belong to this worker diff.
The frozen task, existing Lean modules, root import file and handoff ledger
were kept read-only under the explicit worker scope. This is a worker result
awaiting independent review, not an acceptance or merge.

## Mathematical result

Write `H_t(y)` for the actual spatial Hessian of the Gaussian, and `D_t(y)`
for its actual time derivative. The proof establishes the derivative through
the fixed bilinear tensor formula, proves a quartic Gaussian envelope and
weighted integrability, and obtains exact dilation and moment scaling:

```text
JH = integral_y norm(H_1(y)) * norm(y)^alpha
JD = integral_y norm(D_1(y)) * norm(y)^alpha
integral_y norm(D_t(y)) * norm(y)^alpha = t^(alpha/2 - 2) * JD
```

For `0 < a <= b`, it also proves joint time-space integrability and

```text
integral_y norm(H_b(y) - H_a(y)) * norm(y)^alpha
  <= (b-a) * a^(alpha/2 - 2) * JD.
```

The cancelled kernel representation of the actual Duhamel Hessian then gives:

- Tail: `(JH * (2/alpha)) * K * tau^(alpha/2)`.
- Near shared interval: twice that bound.
- Far shared interval: `(JD * (2/(2-alpha))) * K * tau^(alpha/2)`.

The final constant is `max 1 (3 * (JH * (2/alpha)) + JD * (2/(2-alpha)))`.
It depends only on the exponent and the fixed Gaussian. The proof covers
equal times, zero time, and both time orders. It uses the original forcing
hypotheses; no time Hölder hypothesis on the forcing is introduced.
`euclideanForm` is just the existing Euclidean inner product packaged with
an explicit real bilinear operator type. The clamped time in the joint
integrability lemma keeps a continuous extension positive and equals the
original time on the integration slab.

This closes the requested time half of the Duhamel Hessian Hölder estimate.
It does not claim the full constant-coefficient Schauder inverse or the
Poincare endpoint.

## Reviewer first action

```sh
git diff c165951b1506056533cbb63ccc0e52e45cffb0ab..b2537b0dd188544bcd759f4be0ad124e10581900 -- Poincare/Global/HeatDuhamelHessianTimeHolder.lean
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean
```

Then rerun the exact-statement and compiled-module probes below. The final
module audit expects 25 declarations, with the exact three dependencies on
each declaration. No root build or root integration audit was run by this
worker.

## Final gates

The `rg` exit code is 1 because there were no matching forbidden tokens.

### Focused Lean check

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean
```

```text
EXIT 0
```

### Forbidden-token scan

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HeatDuhamelHessianTimeHolder.lean
```

```text

EXIT 1
```

### Whitespace check

```sh
git diff --check c165951b1506056533cbb63ccc0e52e45cffb0ab
```

```text

EXIT 0
```

### Proof worktree status

```sh
git status --short --branch
```

```text
## worker/heat-duhamel-hessian-time-holder

EXIT 0
```

## Exact statement and compiled-module probes

The statement was probed before implementation. The final assignment uses
the statement copied from the frozen task without changing its quantifiers.
The `.olean` was generated from the final verified source with:

```sh
LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/HeatDuhamelHessianTimeHolder.olean Poincare/Global/HeatDuhamelHessianTimeHolder.lean
```

```text

EXIT 0
```

### statement

```lean
import Poincare.Global.HeatDuhamelHessianSpatialHolder
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace Interval
namespace Poincare.HeatDuhamelHessianTimeHolder
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
  HeatDuhamelHessianDifferentiation HeatDuhamelHessianSpatialHolder
#check (
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖
      ≤ C * K * |t₁ - t₂| ^ (α / 2) : Prop)
end Poincare.HeatDuhamelHessianTimeHolder
```

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/statement.lean`.

```text
∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : ℝ × E → ℝ) (M K : ℝ),
                  0 ≤ M →
                    0 ≤ K →
                      ContinuousOn f (Icc 0 T ×ˢ univ) →
                        (∀ t ∈ Icc 0 T, ∀ (x : E), |f (t, x)| ≤ M) →
                          (∀ t ∈ Icc 0 T, ∀ (x y : E), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                            let u := fun t x => ∫ (s : ℝ) in 0..t, heatSolution (t - s) (fun y => f (s, y)) x;
                            ∀ t₁ ∈ Icc 0 T,
                              ∀ t₂ ∈ Icc 0 T,
                                ∀ (x : E),
                                  ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
                                    C * K * |t₁ - t₂| ^ (α / 2) : Prop

EXIT 0
```

### exact-assignment

```lean
import Poincare.Global.HeatDuhamelHessianTimeHolder
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology InnerProductSpace Interval
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  { norm_smul_le := Poincare.norm_real_smul_continuousLinearMap_two_le }
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖
      ≤ C * K * |t₁ - t₂| ^ (α / 2) := Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder
```

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/exact-assignment.lean`.

```text

EXIT 0
```

### module-audit

```lean
import Poincare.Global.HeatDuhamelHessianTimeHolder
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HeatDuhamelHessianTimeHolder
    | throwError "module missing"
  let mut count := 0
  let mut used : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx && !n.isInternal then
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      let axs ← liftCoreM (collectAxioms n)
      unless axs.size == 3 && axs.contains ``propext && axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "unexpected dependencies for {n}"
      for k in ci.type.getUsedConstants do
        used := used.insert k
      if let some v := ci.value? then
        for k in v.getUsedConstants do
          used := used.insert k
  unless count == 25 do throwError "unexpected declaration count: {count}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count} PASS"
  for n in used.toList do
    logInfo m!"USED {n}"
```

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/module-audit.lean`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=25 PASS
USED IsModuleTopology.toContinuousSMul
USED NormedCommRing.toNormedRing
USED Set.instSProd
USED PiLp.instNorm
USED Norm.norm
USED Pi.Function.module
USED InnerProductSpace.toNormedSpace
USED NormedCommRing.toSeminormedCommRing
USED NonAssocSemiring.toAddCommMonoidWithOne
USED ContinuousLinearMap.toNormedAddCommGroup
USED ContinuousLinearMap.continuousSMul
USED RingHomSurjective.ids
USED Real.instPow
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat
USED Real.instLE
USED Real
USED Set.Ioi
USED Algebra.to_smulCommClass
USED instHSMul
USED WithLp.instModuleFinite
USED Continuous
USED instHDiv
USED NonUnitalCommRing.toNonUnitalNonAssocCommRing
USED PiLp.normedSpace
USED measureSpaceOfInnerProductSpace
USED fact_one_le_two_ennreal
USED NormedRing.toRing
USED HMul.hMul
USED Real.lattice
USED IsScalarTower.right
USED NormedSpace
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_2
USED ContinuousLinearMap.topologicalAddGroup
USED IsTopologicalRing.toIsTopologicalSemiring
USED ContinuousLinearMap.topologicalSpace
USED Real.denselyNormedField
USED Real.instZero
USED ContinuousLinearMap.smulRight
USED Real.instRCLike
USED SProd.sprod
USED abs
USED CommSemiring.toSemiring
USED innerSL
USED Real.instInv
USED DistribMulAction.toDistribSMul
USED AddCommGroup.toAddCommMonoid
USED ContinuousLinearMap.distribMulAction
USED IsSemitopologicalRing.toIsSemitopologicalSemiring
USED ContinuousLinearMap.addCommGroup._proof_6
USED SeparatelyContinuousMul.to_continuousSMul
USED deriv
USED Real.instDivInvMonoid
USED ContinuousLinearMap.funLike
USED Real.instSub
USED Set.univ
USED NormedSpace.toModule
USED Pi.module
USED AddMonoid.toAddZeroClass
USED MeasureTheory.MeasureSpace.toMeasurableSpace
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_3
USED Nat.instAtLeastTwoHAddOfNat
USED IsTopologicalDivisionRing.toIsTopologicalRing
USED HasDerivAt
USED FiniteDimensional.rclike_to_real
USED HSub.hSub
USED PseudoMetricSpace.toUniformSpace
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_1
USED instTopologicalSpaceProd
USED ContinuousLinearMap.addCommMonoid
USED intervalIntegral
USED Real.instLT
USED AddCommGroup.toAddGroup
USED NormedDivisionRing.toDivisionRing
USED MeasureTheory.Integrable
USED Algebra.toSMul
USED WithLp.instAddCommGroup
USED Membership.mem
USED Real.measureSpace
USED NormedField.toField
USED Exists
USED DivisionRing.toDivisionSemiring
USED AddZeroClass.toAddZero
USED inferInstance
USED Real.semiring
USED MeasureTheory.Measure.restrict
USED instIsTopologicalRingReal
USED Set.Elem
USED SeminormedAddGroup.toContinuousENorm
USED Algebra.id
USED IsTopologicalSemiring.toIsModuleTopology
USED ContinuousLinearMap.smulCommClass
USED HDiv.hDiv
USED Function.hasSMul
USED NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
USED PiLp.innerProductSpace
USED DistribSMul.toSMulZeroClass
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_4
USED PiLp.seminormedAddCommGroup
USED Prod.mk
USED AddMonoidWithOne.toNatCast
USED Real.normedAddCommGroup
USED NonUnitalSemiring.toNonUnitalNonAssocSemiring
USED Real.instAddGroup
USED Ne
USED ContinuousLinearMap.module
USED Real.instRing
USED instOfNatNat
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat._proof_2
USED AddCommMonoidWithOne.toAddMonoidWithOne
USED LE.le
USED NormedField.toNormedDivisionRing
USED Finite.of_fintype
USED fderiv
USED Real.instAddCommGroup
USED NormedCommRing.toNonUnitalNormedCommRing
USED RingHomIsometric.ids
USED ContinuousLinearMap.addCommGroup
USED Field.toSemifield
USED Prod.fst
USED IsScalarTower.left
USED ContinuousLinearMap.toNormedSpace
USED Fin.fintype
USED PiLp.borelSpace
USED RCLike.toDenselyNormedField
USED FiniteDimensional.finiteDimensional_pi'
USED Monoid.toPow
USED Real.instAdd
USED PiLp.topologicalSpace
USED ContinuousLinearMap
USED Real.instOne
USED SubNegMonoid.toSub
USED NonUnitalNonAssocSemiring.toAddCommMonoid
USED SeminormedAddCommGroup.toSeminormedAddGroup
USED Real.instMonoid
USED AddZero.toZero
USED Poincare.heatSolution
USED instHAdd
USED IsSemitopologicalSemiring.toSeparatelyContinuousMul
USED And
USED Real.measurableSpace
USED Real.instMax
USED ContinuousLinearMap.continuousConstSMul
USED instHSub
USED Inv.inv
USED Set.Icc
USED Semifield.toDivisionSemiring
USED SeminormedAddCommGroup.toPseudoMetricSpace
USED WithLp.instSMul
USED AddGroup.toSubNegMonoid
USED HPow.hPow
USED MeasureTheory.MeasureSpace.volume
USED Real.normedCommRing
USED MeasureTheory.Measure.prod
USED Distrib.toMul
USED HAdd.hAdd
USED ContinuousLinearMap.instSMul
USED Localization.instSMulCommClassOfIsScalarTower
USED SeminormedAddCommGroup.toAddCommGroup
USED Nat.instNeZeroSucc
USED Max.max
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat
USED PseudoEMetricSpace.toUniformSpace
USED ContinuousLinearMap.hasOpNorm
USED ContinuousLinearMap.isScalarTower
USED NonAssocSemiring.toNonUnitalNonAssocSemiring
USED Ring.toAddCommGroup
USED MeasurableSpace.pi
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat._proof_1
USED NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing
USED MeasureTheory.integral
USED Nat
USED Real.instMul
USED Real.instDivisionRing
USED NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
USED LT.lt
USED Pi.addCommGroup
USED ContinuousLinearMap.instAddMonoid
USED NormedSpace.mk
USED ENNReal
USED DivInvMonoid.toDiv
USED IsTopologicalRing.toIsSemitopologicalRing
USED SeminormedCommRing.toSeminormedRing
USED DivisionSemiring.toSemiring
USED NonUnitalSeminormedRing.toSeminormedAddCommGroup
USED Real.instAddCommMonoid
USED One.toOfNat1
USED Semiring.toNonUnitalSemiring
USED NonUnitalNonAssocSemiring.toDistrib
USED Poincare.ClosedSmoothModel
USED PiLp.innerProductSpace._proof_1
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_5
USED Zero.toOfNat0
USED NormedDivisionRing.to_isTopologicalDivisionRing
USED ContinuousOn
USED HSMul.hSMul
USED NontriviallyNormedField.toNormedField
USED Module.toDistribMulAction
USED SMulZeroClass.toSMul
USED instSecondCountableTopologyReal
USED instIsTopologicalAddGroupReal
USED Real.pseudoMetricSpace
USED AddCommMonoid.toAddMonoid
USED Real.normedField
USED instTopologicalSpaceSubtype
USED Semifield.toCommSemiring
USED DenselyNormedField.toNontriviallyNormedField
USED NormedField.toNormedSpace
USED instHPow
USED SeminormedRing.toPseudoMetricSpace
USED AddMonoidWithOne.toAddMonoid
USED WithLp.instModule
USED NonUnitalNormedCommRing.toNonUnitalCommRing
USED NormedField.toNormedCommRing
USED Real.borelSpace
USED WithLp.measurableSpace
USED SubNegMonoid.toAddMonoid
USED ContinuousLinearMap.toSeminormedAddCommGroup
USED SeminormedCommRing.toNonUnitalSeminormedCommRing
USED Prod
USED SeminormedAddCommGroup.toIsTopologicalAddGroup
USED starRingEnd
USED OfNat.ofNat
USED RCLike.innerProductSpace
USED Poincare.heatKernel
USED DenselyNormedField.toNormedField
USED Fin
USED Subtype.val
USED NormedAddCommGroup.toSeminormedAddCommGroup
USED RingHom.id
USED UniformSpace.toTopologicalSpace
USED Semiring.toNonAssocSemiring
USED Ring.toSemiring
USED Eq
USED Set.instMembership
USED Prod.snd
USED DFunLike.coe
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat._proof_6
USED instOfNatAtLeastTwo
USED Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat._proof_3
USED Set.Ioo
USED ENNReal.instAddCommMonoidWithOne
USED Poincare.HeatDuhamelHessianTimeHolder.euclideanForm
USED instCountableFin
USED Real.instPreorder
USED MeasureTheory.AEStronglyMeasurable
USED MonoidWithZero.toMonoid
USED RCLike.toInnerProductSpaceReal
USED RCLike.toStarRing
USED NormedAddCommGroup
USED IsSemitopologicalSemiring.toContinuousAdd
USED Real.instCommSemiring
USED Real.norm
USED DistribMulAction.toMulAction
USED Real.instCommMonoid
USED Semiring.toMonoidWithZero
USED instHMul
USED PseudoMetricSpace.toPseudoEMetricSpace
USED ContinuousLinearMap.sub
USED PiLp.normedAddCommGroup
USED Prod.instMeasurableSpace
USED Real.instNatCast
USED Set

EXIT 0
```

## Commit sequence

Each new theorem was compiled before its separate commit. The initial
bilinear definition is committed with the first tensor-formula theorem.
The last proof commit removes redundant options and tactic-style warnings.

```text
2cd9ef78a111d237349c5c1bd4d270ac249ba6f4 Prove fixed-tensor formula for the heat kernel Hessian
ba10bf8ca7a030e5d7d3bfcf8745736f75207000 Differentiate the Gaussian Hessian in time
06f38c4d91da27807e203fa2698a432a46ea2741 Bound the unit-time Hessian time derivative by a quartic Gaussian
df10f4951e29b71a68c4b0a3e57b6968fa09195a Prove spatial continuity of the Hessian time derivative
52e7a59eca3e8094d1941b004700af70da4eae47 Prove weighted integrability of the unit-time Hessian time derivative
594605764472179feadc942fadd71c24e26e08e8 Prove parabolic dilation of the Hessian time derivative
be9e9a429f3ea875061abfc44956e6d357383fb9 Prove scaling-0 for the Hessian time derivative
226aadc3a3fc3f5cb773baa033f5d79f3d78b58a Prove scaling-1 for the Hessian time derivative
e27c8cc446b44419f4efbecec40bfea1b01c5b2d Prove scaling-2 for the Hessian time derivative
a9e81209cfa7f92a09169f51397512e59afdde66 Prove moment-scaling for the Hessian time derivative
542cbc1339603f1ec02fc64e719e463c649c4e07 Prove moment-bound for the Hessian time derivative
a6227ee40e8f9ce374532f91c1fe1afed39a7ccd Prove tail-bound for the Hessian time derivative
2852463e4b51bffd060a447546d9e35fac8c5a68 Prove before-bound for the Hessian time derivative
19bcf73666aac5e134fa909219d240cacfc9c50f Prove near-bound for the Hessian time derivative
10ef6d24914db21c852532d6b3497dd6f0c98466 Prove joint-continuity for the Hessian time derivative
283b515528a3e0533e7bf7928b4faaccaf0812e0 Prove joint integrability of the weighted kernel time derivative
237c79dbbb2bfe8f580f7d9a1e5b9aebff53d4ab Prove time-FTC for the Hessian time derivative
846e7cdb0d6393fa69824dee490880d797cbe26c Prove time-kernel-difference for the Hessian time derivative
919100b88e94bac9f0bae023049b471e2b71cc96 Integrate the far-time fourth-order kernel power
ece3b4977710ccb11792464781aaca84e355f70f Prove cancelled-time-difference for the Hessian time derivative
42d0e74a103d581e4a8ff71bdaf6141243e41e83 Prove far-bound for the Hessian time derivative
d25c59d205f7559cc1de590232f688a91b70d452 Prove assembly for the Hessian time derivative
b2537b0dd188544bcd759f4be0ad124e10581900 Remove redundant proof options and tactic-style warnings

EXIT 0
```

## Symbol search evidence

The following batched `rg` inventory covers all 176 underscore-named source
references, including named lemmas and the declarations introduced here.
Existing-source matches are preferred; new declarations resolve in the new
module. The exact compiled declaration and module probes additionally check
all elaborated names and types. Each line below is actual `rg` output.

```text
COMMAND ['rg', '-n', '--glob', '*.lean', '-f', '/private/tmp/heat-time-evidence/symbol-patterns.txt', 'Poincare', '.lake/packages/mathlib/Mathlib']
EXIT 0
SYMBOLS 176
MISSING []
Ioo_subset_Ioo
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IntegralCurve/UniformTime.lean:52:  · apply Ioo_subset_Ioo <;> linarith
abs_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean:216:      exact (abs_nonneg _).trans (fpp_bound 0)
abs_of_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:164:  ext; rw [map_apply, Real.norm_eq_abs, abs_of_nonneg]; exact le_max_right _ _
abs_sub_comm
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:121:  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v
add_le_add
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:149:      ⟨fun x => g₁ x + g₂ x, fun x => add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, ?_⟩
add_one_le_exp
Poincare/Global/HeatCauchyUniform.lean:87:    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp q)
ae_restrict_mem
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:273:    filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
all_goals
.lake/packages/mathlib/Mathlib/InformationTheory/Coding/KraftMcMillan.lean:141:  all_goals try simp at *
by_cases
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Associated.lean:191:  by_cases ha0 : a = 0
cast_ofNat
.lake/packages/mathlib/Mathlib/Algebra/Lie/Weights/Killing.lean:527:        Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, false_or] at hx
clm_apply
Poincare/Global/DeTurckFlowVariationalIdentification.lean:306:          simpa using (hDvar tau htau).clm_apply hc
comp_continuous
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:1121:    refine hf.comp_continuous (.prodMk_right _) fun y => ?_
comp_sub_left
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:473:theorem comp_sub_left {f : ℝ → E} (hf : IntervalIntegrable f volume a b) (c : ℝ)
congr_of_eventuallyEq
Poincare/CurvatureConditions.lean:116:      refine hA.congr_of_eventuallyEq ?_
conj_trivial
.lake/packages/mathlib/Mathlib/Algebra/Star/Basic.lean:355:@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _
const_mul
Poincare/CurvatureConditions.lean:328:        ((hasDerivAt_id t₀).const_mul (2 * lam * (g₀ x (Z x) w)))
contDiff_heatKernel_spatial
Poincare/Global/HeatEnvelopes.lean:164:      (contDiff_heatKernel_spatial (E := E) s).continuous.comp hsub
continuous_const
Poincare/CurvatureConditions.lean:612:        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
continuous_fst
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:595:      (continuous_fst.fst.tendsto ((a, b), (a, b)))
continuous_hessian_time_deriv
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:103:theorem continuous_hessian_time_deriv {t : ℝ} (ht : 0 < t) :
continuous_hessian_time_deriv_pos
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:337:theorem continuous_hessian_time_deriv_pos :
continuous_id
Poincare/CurvatureConditions.lean:612:        (continuous_const.sub ((continuous_const.mul continuous_id))).tendsto _
continuous_norm
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:626:  · refine Continuous.sub (continuous_norm.comp Lp.continuous_posPart)
continuous_rpow_const
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean:35:  refine (ENNReal.continuous_rpow_const.tendsto ‖f_lim a‖₊).comp ?_
continuous_snd
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:594:      (continuous_snd.fst.tendsto ((a, b), (a, b)))
continuous_sqrt
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasureExt.lean:59:    exact Continuous.tendsto continuous_sqrt 0
continuous_subtype_val
Poincare/Global/DeTurckFlowVariationalIdentification.lean:162:    exact continuous_subtype_val.comp continuous_projIcc
deriv_heatKernel_time_eq_heatKernel_mul
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:122:  rw [deriv_heatKernel_time_eq_heatKernel_mul (E := E) ht (-y),
div_const
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/Monoid.lean:507:theorem ContMDiffWithinAt.div_const (hf : CMDiffAt[s] n f x) :
div_eq_mul_inv
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/LieGroup.lean:161:  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv
div_nonneg
Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:54:  exact div_nonneg
duhamel_hessian_time_holder
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:580:theorem duhamel_hessian_time_holder :
eventually_gt_nhds
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:222:    exact ⟨hc.eventually (eventually_le_atBot _x), hb.eventually (eventually_gt_nhds hx)⟩
exp_add
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:164:  simp [circleMap, add_mul, Complex.exp_add]
far_hessian_time_difference_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:516:theorem far_hessian_time_difference_le {α T t₁ t₂ M K : ℝ}
far_time_deriv_power_integral_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:456:theorem far_time_deriv_power_integral_le {α τ t : ℝ}
fderiv_right
Poincare/Global/LocalUniformTaylorRemainder.lean:37:      (((hf x hx).fderiv_right (m := 0) (by norm_num)).continuousAt).continuousWithinAt
field_simp
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/CorrectnessTerminating.lean:79:  field_simp
filter_upwards
Poincare/CurvatureConditions.lean:99:    filter_upwards [interior_mem_nhds.mpr hv'] with y hy
finrank_euclideanSpace_fin
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:361:  have := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
hasDerivAt_heatKernel_time
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:455:    have hbase := hasDerivAt_heatKernel_time (E := E) hτpos y
hasDerivAt_hessian_time
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:37:theorem hasDerivAt_hessian_time {t : ℝ} (ht : 0 < t) (x : E) :
hasDerivAt_id
Poincare/CurvatureConditions.lean:328:        ((hasDerivAt_id t₀).const_mul (2 * lam * (g₀ x (Z x) w)))
heatKernel_nonneg
Poincare/Global/HeatCauchyFrechet.lean:57:  have hk_nonneg : 0 ≤ hk := heatKernel_nonneg (E := E) ht (x - y)
heatKernel_sq_smul
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:299:    heatKernel_sq_smul (E := E) a ha x, norm_smul,
hessian_duhamel_eq_integral
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:385:theorem hessian_duhamel_eq_integral {α T t M K : ℝ}
hessian_eq_tensor
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:22:theorem hessian_eq_tensor {t : ℝ} (ht : t ≠ 0) (x : E) :
hessian_tail_bound
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:259:theorem hessian_tail_bound {α K T t₁ t₂ : ℝ}
hessian_time_deriv_moment_bound
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:245:theorem hessian_time_deriv_moment_bound :
hessian_time_deriv_sq_smul
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:173:theorem hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
innerSL_apply_norm
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean:67:  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }
inner_smul_left
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Instances/Sphere.lean:136:  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, hw, mul_pow,
integrableOn_cancelled_hessian_time
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:202:theorem integrableOn_cancelled_hessian_time {α K T t : ℝ}
integrable_cancelled_hessian
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:97:theorem integrable_cancelled_hessian {t M : ℝ} (ht : 0 < t)
integrable_comp_smul_iff
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:174:theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
integrable_const
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:188:  · refine Integrable.add ?_ (integrable_const _)
integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
Poincare/Global/HeatCauchyUniform.lean:44:  exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) ha).const_mul A
integrable_prod_iff
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:20:* `MeasureTheory.integrable_prod_iff` states that a binary function is integrable iff both
integrable_time_weighted_hessian_deriv
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:360:theorem integrable_time_weighted_hessian_deriv {α a : ℝ}
integrable_weighted_hessian_time_deriv
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:221:theorem integrable_weighted_hessian_time_deriv {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
integrable_weighted_hessian_time_deriv_one
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:118:theorem integrable_weighted_hessian_time_deriv_one {α : ℝ}
integral_Icc_eq_integral_Ioc
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:659:theorem integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) :
integral_add_adjacent_intervals
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:365:  rw [hf.intervalIntegral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]
integral_comp_add_right
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:388:    simp_rw [integral_comp_add_right, h₀, zero_add, this (n + 1), add_comm T,
integral_comp_smul_of_nonneg
Poincare/Global/HeatSemigroupBUCPositiveGenerator.lean:320:  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
integral_comp_sub_left
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1027:theorem integral_comp_sub_left (d) : (∫ x in a..b, f (d - x)) = ∫ x in d - b..d - a, f x := by
integral_congr_ae
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:168:    integral_congr_ae (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)
integral_const
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:126:      Filter.eventually_true, integral_const, probReal_univ, smul_eq_mul, one_mul, true_and]
integral_const_mul
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:298:theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
integral_eq_sub_of_hasDerivAt
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:494:    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
integral_hessian_majorant
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:167:theorem integral_hessian_majorant {α : ℝ} (hα : 0 < α) (t A : ℝ) :
integral_integral_swap
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:532:theorem integral_integral_swap ⦃f : α → β → E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
integral_mono
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:339:lemma integral_mono {f g : α →ₛ F} (h : f ≤ᵐ[μ] g) (hf : Integrable f μ) (hg : Integrable g μ) :
integral_mono_ae
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:609:    integral_mono_ae hf1.norm.restrict (integrable_const C) (ae_restrict_of_ae hf)
integral_mul_const
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:1126:    simpa [integral_mul_const] using exists_pos_mul_lt εpos _
integral_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:325:lemma integral_nonneg {f : α →ₛ F} (hf : 0 ≤ᵐ[μ] f) :
integral_of_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:382:      rw [intervalIntegral.integral_of_le hle, setIntegral_congr_set Ioc_ae_eq_Icc]
integral_prod_left
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:131:theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α → β → E⦄
integral_prod_right
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:27:  `MeasureTheory.Integrable.integral_prod_right` states that the inner integral of the right-hand
integral_rpow
.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean:104:      rw [integral_rpow]
integral_sub
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:182:  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
intervalIntegrable_iff_integrableOn_Ioo_of_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:140:theorem intervalIntegrable_iff_integrableOn_Ioo_of_le [NoAtoms μ]
intervalIntegrable_rpow
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:160:  have hi := (intervalIntegral.intervalIntegrable_rpow'
inv_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/NeZero.lean:48:theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
inv_nonpos
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:497:          simp [abs_of_nonpos (inv_nonpos.mpr (le_of_lt hx₁))]
iteratedFDeriv_two_apply
Poincare/Global/HeatKernelPDEn.lean:71:  rw [iteratedFDeriv_two_apply]
iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination
Poincare/Global/HeatKernelHessianMoments.lean:25:    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
le_max_left
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:111:      (N' : K) ≤ (N : K) := by exact_mod_cast le_max_left _ _
le_max_right
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean:113:      _ ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
le_of_not_ge
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:67:  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩
le_rfl
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:72:  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)
le_total
.lake/packages/mathlib/Mathlib/Computability/TuringMachine/Tape.lean:245:  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
lt_of_le_of_ne
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean:267:  have : 0 < ifp_n.fr := lt_of_le_of_ne zero_le_ifp_n_fract <| ifp_n_fract_ne_zero.symm
lt_of_lt_of_le
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:189:  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)
lt_of_not_ge
.lake/packages/mathlib/Mathlib/Logic/Denumerable.lean:193:    lt_of_not_ge fun hax => h ⟨a - (x + 1), by rwa [Nat.add_right_comm, Nat.add_sub_cancel' hax]⟩
max_eq_right
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:412:  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
measurableSet_Ioo
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:172:    exact tendsto_setIntegral_of_monotone (fun k => (J k).measurableSet_Ioo)
mem_univ
Poincare/ProofProgress/OnePointTwoPointComplementTopology.lean:67:    exact Set.mem_univ z
mono_set
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:94:  exacts [disjoint_sdiff_self_left.aedisjoint, ht, hfs.mono_set diff_subset, hfs.mono_set hts]
mul_comm
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:479:    · conv_rhs => rw [mul_comm]
mul_le_mul_of_nonneg_left
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:132:      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
mul_le_mul_of_nonneg_right
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean:313:        simpa using mul_le_mul_of_nonneg_right this zero_le_of_den
mul_le_mul_of_nonpos_right
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean:113:        ⟨mul_le_mul_of_nonpos_right hk h_neg, mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg h_neg⟩
mul_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:147:        · exact Eventually.of_forall fun x => mul_nonneg (norm_nonneg _) δpos.le
mul_one
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:133:  | mul_one {a : Pre R X} : Rel (a * 1) a
mul_pow
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Torsion.lean:45:  rw [← hu, mul_pow, eq_comm, IsLeftRegular.mul_left_eq_self_iff hx, ← Units.val_pow_eq_pow_val,
mul_rpow
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/AkraBazzi.lean:334:    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
near_hessian_time_difference_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:310:theorem near_hessian_time_difference_le {α K a t₁ t₂ : ℝ}
neg_div
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean:44:  rw [neg_mul_eq_neg_mul, neg_div', neg_sub, add_comm (f b) (f a), ← sum_range_reflect]
norm_add_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/PeakFunction.lean:176:    _ ≤ ‖∫ x in s \ u, φ i x • g x ∂μ‖ + ‖∫ x in s ∩ u, φ i x • g x ∂μ‖ := norm_add_le _ _
norm_cancelled_hessian_integral_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:124:theorem norm_cancelled_hessian_integral_le {α K t : ℝ}
norm_cancelled_hessian_time_difference_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:485:theorem norm_cancelled_hessian_time_difference_le {α a b M K : ℝ}
norm_eq_abs
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:133:    _ = abs μ.real s := Real.norm_eq_abs _
norm_hessian_time_deriv_one_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:72:theorem norm_hessian_time_deriv_one_le (x : E) :
norm_hessian_time_difference_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:394:theorem norm_hessian_time_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : E) :
norm_innerSL_le
.lake/packages/mathlib/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:773:    exact norm_innerSL_le _
norm_integral_cancelled_hessian_before_le
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:274:theorem norm_integral_cancelled_hessian_before_le {α K a b t : ℝ}
norm_integral_cancelled_hessian_near_le
Poincare/Global/HeatDuhamelHessianSpatialHolder.lean:213:theorem norm_integral_cancelled_hessian_near_le {α K a t : ℝ}
norm_integral_le_integral_norm
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:308:theorem norm_integral_le_integral_norm (f : α →ₛ E) (hf : Integrable f μ) :
norm_integral_le_of_norm_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:965:theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ} (hg : Integrable g μ)
norm_mul
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_neg
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:132:      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
norm_num
Poincare/CurvatureConditions.lean:98:      (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp hZ
norm_of_nonneg
Poincare/Global/HeatCauchyFrechet.lean:70:    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nonneg, norm_neg,
norm_real_smul_continuousLinearMap_two_le
Poincare/Global/HeatDuhamelSpatialHolderHessian.lean:32:        norm_real_smul_continuousLinearMap_two_le _ _
norm_smul
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:130:      norm_smul (μ.real s) (ContinuousLinearMap.id ℝ F)
norm_smulRight_apply
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean:197:  ContinuousLinearMap.homothety_norm _ c.norm_smulRight_apply
norm_smul_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean:343:  hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg
norm_smul_of_nonneg
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:63:      simp_rw [norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * a⁻¹ by positivity)
norm_sub_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:443:          ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
norm_sub_rev
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:210:      rw [norm_sub_rev]
not_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:508:      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1, compl_setOf]; simp only [not_le]
of_forall
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:300:    · apply Filter.Eventually.of_forall fun x => _; simp
one_pow
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Basic.lean:166:    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ ↦ zero_ne_one (H.symm.trans (one_pow _))
pow_ne_zero
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Divisibility.lean:172:    apply pow_ne_zero m ha₀
pow_two
.lake/packages/mathlib/Mathlib/Algebra/DualNumber.lean:84:  simp [pow_two]
restrict_Ioo_eq_restrict_Ioc
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean:287:    rw [← restrict_Ioo_eq_restrict_Ioc]
ring_nf
.lake/packages/mathlib/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:233:      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) by rw [this]; ring_nf
rpow_le_one
.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:179:    exact (one_le_inv₀ (rpow_pos_of_pos hx _)).2 (rpow_le_one hx.le hx' P.hk.le)
rpow_le_rpow
Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:193:    Real.rpow_le_rpow hm.le (hScalarLower tau htau x) hdelta.le
rpow_le_rpow_of_exponent_le
.lake/packages/mathlib/Mathlib/NumberTheory/Transcendental/Liouville/Measure.lean:63:        rpow_le_rpow_of_exponent_le hb (one_le_two.trans ?_)
rpow_le_rpow_of_nonpos
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:573:          _ ≤ _ := rpow_le_rpow_of_nonpos (hf_pos₂ u hu.1) (hf₁ u hu).2 (le_of_lt hp)
rpow_mul
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1150:      rw [← rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one]
rpow_nonneg
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/SumTransform.lean:585:        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)
rpow_one
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:923:  simp only [eLpNorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_one, ENNReal.rpow_one,
rpow_sub
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean:594:    rw [← ENNReal.rpow_sub _ _ this ENNReal.coe_ne_top]
rpow_two
Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:72:      _ = (g.scalarAt x) ^ 2 := Real.rpow_two (g.scalarAt x)
set_option
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:315:set_option backward.privateInPublic true in
simp_rw
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Lift.lean:47:    simp_rw [show ∀ (g : G) (r : k), g • r = r by
smul_const
.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:140:@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
smul_eq_mul
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:289:    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
smul_sub
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Basic.lean:85:  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
sq_nonneg
Poincare/Global/NormalizedFlowImprovedPinchingDecay.lean:56:    (sq_nonneg (g.scalarAt x))
sq_pos_of_pos
Poincare/Global/NormalizedFlowScalarVarianceConcentration.lean:99:      g hLipschitz hNoncollapse hVarianceZero (ε ^ 2) (sq_pos_of_pos hε)]
sq_sqrt
Poincare/Global/SpeedPackage.lean:60:  exact Real.sq_sqrt
sqrt_eq_rpow
Poincare/Global/HeatDuhamelHessianDifferentiation.lean:73:  rw [h, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
sqrt_pos
Poincare/Global/HausdorffInverseChartLocalFrozenBilipschitz.lean:93:    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
sub_add_cancel
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Basic.lean:231:        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
sub_le_self
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean:78:    refine le_trans (sub_le_self _ <| NNReal.coe_nonneg _) ?_
sub_nonneg
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:341:  rw [← sub_nonneg, ← integral_sub hg hf]
sub_pos
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:634:  rw [← sub_pos, ← smul_eq_mul, ← setIntegral_const, ← integral_sub hfint this,
sub_self
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean:299:        sub_add_eq_sub_sub_swap, sub_right_comm, sub_self, zero_sub]
sub_sub_cancel
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:302:    · rw [← diff_iInter, setIntegral_diff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
sub_zero
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Unitization.lean:352:  Unitization.ext rfl (sub_zero 0).symm
subtype_mk
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:874:theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
trans_eq
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:358:      have A : μ (f ⁻¹' {f x}) = 0 := by simpa using (hμν _ |>.trans_eq this)
trans_le
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:386:  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
uIcc_of_le
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:412:  · simp only [uIcc_of_le hab, min_eq_left hab, max_eq_right hab] at *
weighted_hessian_time_deriv_integral
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:232:theorem weighted_hessian_time_deriv_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
weighted_hessian_time_deriv_integral_sq
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:204:theorem weighted_hessian_time_deriv_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
weighted_hessian_time_deriv_sq_smul
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:194:theorem weighted_hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
weighted_hessian_time_difference
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:410:theorem weighted_hessian_time_difference {α a b : ℝ}
zero_add
.lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:129:  | zero_add {a : Pre R X} : Rel (0 + a) a
zero_lt_one
.lake/packages/mathlib/Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean:386:  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
zero_rpow
.lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:559:      simp only [hx, zero_rpow (ne_of_lt hp), mul_zero,
```

## Compiler attempt history

Every focused Lean attempt and dependency probe is recorded below, including
failures. `EXIT` is the actual Lean subprocess exit code. Successful checks
with no compiler output show only that exit code. Repeated console capture
files are omitted because they duplicate the individual logs verbatim.
Probe snapshots were kept under `/private/tmp/heat-time-evidence` during the
job; their SHA-256 values identify the source used for each recorded attempt.
The final source diff and self-contained acceptance probe sources are
embedded in this report, so acceptance does not depend on temporary files.

The failures resolved during the job were tensor-type elaboration, explicit
beta reduction before rewrites, scalar denominator normalization, and a
product-integrability slice whose inferred type caused heartbeat exhaustion.
The slice succeeds after its integrand is stated explicitly. No failed
proof or unresolved estimate remains in the final module.

### tensor-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `691c4289945d8a6484d723142d8835678e7e93b1d48654e8c044b7f0dff0516e`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:18:15: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HSub (E →L[ℝ] E →L[ℝ] ℝ) (E →L⋆[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:24:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (![v, w] 0)) (![v, w] 1)
in the target expression
  (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) w =
    (((heatKernel t x / (4 * t ^ 2)) • ((innerSL ℝ) x).smulRight ((innerSL ℝ) x) -
          (heatKernel t x / (2 * t)) • innerSL ℝ)
        v)
      w

case h.h
t : ℝ
ht : t ≠ 0
x v w : E
h :
  ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) (![v, w] 0)) (![v, w] 1) =
    heatKernel t x * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
⊢ (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) w =
    (((heatKernel t x / (4 * t ^ 2)) • ((innerSL ℝ) x).smulRight ((innerSL ℝ) x) -
          (heatKernel t x / (2 * t)) • innerSL ℝ)
        v)
      w

EXIT 1
```

### tensor-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `6a3bcf07182981f4d8ca0eb9d8ef83eb95a099cc66c809ddcd54c4c7bd1b9ce7`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:18:15: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HSub (E →L[ℝ] E →L[ℝ] ℝ) (E →L⋆[ℝ] E →L[ℝ] ℝ) (E →L[ℝ] E →L[ℝ] ℝ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:25:2: error: `simp` made no progress

EXIT 1
```

### tensor-03

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `939f136b8d31c745238a07532feb8c47227f302ea93ca68f186deb3e4ed5caa3`.

```text
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:23:52: error: unsolved goals
case h.h
t : ℝ
ht : t ≠ 0
x v w : E
h :
  ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) v) w =
    heatKernel t x * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t))
⊢ heatKernel t x * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ * t⁻¹ ^ 2 * (1 / 4) + heatKernel t x * t⁻¹ * ⟪v, w⟫_ℝ * (-1 / 2) =
    heatKernel t x * ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ * t⁻¹ ^ 2 * (1 / 4) - (((heatKernel t x * t⁻¹ * (1 / 2)) • innerSL ℝ) v) w

EXIT 1
```

### tensor-04

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `7b31e0c49c1b33d0359313186faab3cdac364e2dbe05cf96e2853ff4efd41d2e`.

```text

EXIT 0
```

### tensor-04-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/tensor-04-audit.lean`.

Snapshot SHA-256: `78cd2d1df2d86a8178cb7337a8192a3fc350f33707b61bf5c72432f35177ca6d`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### derivative-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `b0c0cb1f814b9e5090ebe1903ba6ca6f6cad4e8ef2f6a379cdea0bb96c76c7f0`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:42:48: error(lean.invalidField): Invalid field `hasDerivAt`: The environment does not contain `HasFDerivAtFilter.hasDerivAt`, so it is not possible to project the field `hasDerivAt` from an expression
  hasDerivAt_heatKernel_time ht x
of type
  HasFDerivAtFilter (fun τ => heatKernel τ x)
    (ContinuousLinearMap.toSpanSingleton ℝ
      (4 * Real.pi * (-↑(Module.finrank ℝ E) / 2) * (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) / 2 - 1) *
          Real.exp (-‖x‖ ^ 2 / (4 * t)) +
        (4 * Real.pi * t) ^ (-↑(Module.finrank ℝ E) / 2) * (Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2)))))
    (𝓝 t ×ˢ pure t)
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:55:10: error: failed to synthesize
  SeminormedAddCommGroup (E →L[ℝ] ℝ)
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:57:2: error: No goals to be solved

EXIT 1
```

### derivative-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `93481a470818d672553c3af4b2fd73f862526e832895cb6bbde13a763542d53f`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:53:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:53:33: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:53:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:56:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:56:33: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:56:48: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### derivative-03-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/derivative-03-audit.lean`.

Snapshot SHA-256: `a8888c2c386f5f19f3bfefb4f084e152d872878c83c280d2bb2c50ff9e4f8f4d`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### norm-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `4d0369a6f436955ff96973a1121fee57545446d48a3291d2264fe7fc2c4f2821`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:74:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) 1
in the target expression
  ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖ ≤
    heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)

x : E
⊢ ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖ ≤
    heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)

EXIT 1
```

### norm-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `a23dd54f4412e2639d221bcb5e6d3299bb310fda652dfd1db55f0ce28048352c`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:76:35: error: Type mismatch
  norm_innerSL_le
has type
  ∀ (𝕜 : Type ?u.46376.6481) {«E» : Type ?u.46376.6480} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup «E»]
    [inst_2 : InnerProductSpace 𝕜 «E»], ‖innerSL 𝕜‖ ≤ 1
but is expected to have type
  ‖euclideanForm‖ ≤ 1
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:93:10: error: Tactic `apply` failed: could not unify the type of `mul_le_mul_of_nonneg_left ?m.630 hk`
  heatKernel 1 x * ?m.627 ≤ heatKernel 1 x * ?m.628
with the goal
  heatKernel 1 x * ‖‖x‖ ^ 2 / 8 - 5 / 4‖ ≤ heatKernel 1 x

case h₂.h₁
x : E
hI : ‖euclideanForm‖ ≤ 1
hQ : ‖((innerSL ℝ) x).smulRight ((innerSL ℝ) x)‖ = ‖x‖ ^ 2
hk : 0 ≤ heatKernel 1 x
⊢ heatKernel 1 x * ‖‖x‖ ^ 2 / 8 - 5 / 4‖ ≤ heatKernel 1 x
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:95:10: error: Type mismatch
  hI
has type
  ‖euclideanForm‖ ≤ 1
but is expected to have type
  ‖euclideanForm‖ ≤ ‖x‖ ^ 2 / 8 + 5 / 4

EXIT 1
```

### norm-03

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `fc75169c7ce4af27bbf31f199e7a4a5898fcf58536b23d9a70ee6702cbfac0c2`.

```text

EXIT 0
```

### norm-03-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/norm-03-audit.lean`.

Snapshot SHA-256: `6e7df62a68f6d1dae1d5d2102eef4300e609b0b3179dd811137c7ad788e585c6`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### continuous-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `a3fd91dfe25fe90873cd2fc2820bfb4455bd88225f7a2cc36abade5acc4ff360`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:111:11: error(lean.unknownIdentifier): Unknown identifier `continuous_heatKernel_spatial`

EXIT 1
```

### continuous-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `78521ca5872a3e044668b20462aef9591182bd7eb781549bfc8b8df57537a595`.

```text

EXIT 0
```

### continuous-02-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/continuous-02-audit.lean`.

Snapshot SHA-256: `7e1425400b6467ffb48ef398879b959ed7061bda57ce5273788e40d30dab8b46`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### integrable-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `4385ee87370a42610a50dd4fb36f50c307afd78a2a8aca5e05006b4ba4d80595`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:129:30: error: failed to prove positivity/nonnegativity/nonzeroness
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:148:68: error: unsolved goals
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2
hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16)
hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8)
hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2
⊢ -‖x‖ ^ 2 / 4 = -(‖x‖ ^ 2 / 4) ∨ (4 * Real.pi) ^ (-3 / 2) = 0
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:153:70: error: unsolved goals
case b0
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := ⋯
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2
hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16)
hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8)
hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2
hk : heatKernel 1 x = c * Real.exp (-(‖x‖ ^ 2 / 4))
⊢ 0 ≤ heatKernel 1 x * (2 * (1 + ‖x‖ ^ 2) ^ 2)

case h₁.ha
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := ⋯
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2
hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16)
hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8)
hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2
hk : heatKernel 1 x = c * Real.exp (-(‖x‖ ^ 2 / 4))
⊢ 0 ≤ heatKernel 1 x
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:155:83: error: unsolved goals
case hbc.ha
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := ⋯
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2
hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16)
hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8)
hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2
hk : heatKernel 1 x = c * Real.exp (-(‖x‖ ^ 2 / 4))
⊢ 0 ≤ heatKernel 1 x
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:149:44: warning: This simp argument is unused:
  finrank_euclideanSpace_fin

Hint: Omit it from the simp argument list.
  simp [heatKernel, c, ClosedSmoothModel,̵ ̵f̵i̵n̵r̵a̵n̵k̵_̵e̵u̵c̵l̵i̵d̵e̵a̵n̵S̵p̵a̵c̵e̵_̵f̵i̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

EXIT 1
```

### integrable-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `aebb1f5103300e392443c2e28cdd1be669fa121c8c987b1edbf8293834b73ac5`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:129:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖‖?m.193‖ * ‖?m.197‖ ^ ?m.198‖
in the target expression
  ‖((fun x => ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖) *
          (fun x => x ^ α) ∘ fun a => ‖a‖)
        x‖ ≤
    512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))

α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
⊢ ‖((fun x => ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖) *
          (fun x => x ^ α) ∘ fun a => ‖a‖)
        x‖ ≤
    512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))

EXIT 1
```

### integrable-02-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/integrable-02-audit.lean`.

Snapshot SHA-256: `645c10c3cd3d0cfc0a5ac21db3b52edc158fb6bd87c233547f52f3836c63529f`.

```text
/private/tmp/heat-time-evidence/integrable-02-audit.lean:129:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖‖?m.193‖ * ‖?m.197‖ ^ ?m.198‖
in the target expression
  ‖((fun x => ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖) *
          (fun x => x ^ α) ∘ fun a => ‖a‖)
        x‖ ≤
    512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))

α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hmajor : Integrable (fun x => 512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))) volume
x : E
⊢ ‖((fun x => ‖(fun t x => deriv (fun r => (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) r x) t) 1 x‖) *
          (fun x => x ^ α) ∘ fun a => ‖a‖)
        x‖ ≤
    512 * c * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2))
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
/private/tmp/heat-time-evidence/integrable-02-audit.lean:180:0: error: unexpected dependencies for Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one

EXIT 1
```

### integrable-03

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `557322e66cf3111862295bf527378f288d6e992a56abc8e05776176108af3f79`.

```text

EXIT 0
```

### integrable-03-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/integrable-03-audit.lean`.

Snapshot SHA-256: `0c085ec82f7a390c85fbd521231cd9432ab1d4ff21d7c22fd796d4552a601bfb`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### dilation-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `edd3f55e557257830138b6fefe9280fe8f4053fb1cf269a8a56cdc88b8c180f4`.

```text

EXIT 0
```

### dilation-01-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/dilation-01-audit.lean`.

Snapshot SHA-256: `5977b4222e05b5bbf9aa6fd9298ffc646550d8a038c297c148924265e4598778`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### scaling-0

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `c103d32402d873424bfe73da2b238d0f2cb298fbf90d89a7a2b301ea9c196686`.

```text

EXIT 0
```

### scaling-0-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/scaling-0-audit.lean`.

Snapshot SHA-256: `99fe5f81107f4f12c003aea867360fec379ad7d329fbc608a7f7305af87dc868`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### scaling-1

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `b305b01b883381655f0ca53a598c47db50d5a8340d432e19a2da0c8abd37ebf2`.

```text

EXIT 0
```

### scaling-1-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/scaling-1-audit.lean`.

Snapshot SHA-256: `28b315dc2f4c2544d9c2cf754ad39ee8dba24bb5c951b7774ecd2094c2aca46d`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### scaling-2

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `89715129381c045bac886177c1eb50939cb9d572f9688f707b176ebfffba5927`.

```text

EXIT 0
```

### scaling-2-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/scaling-2-audit.lean`.

Snapshot SHA-256: `5f39d652b805f75c58d78f3b539552d73a1f8a93645314ef8d934c42532ad298`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### moment-scaling

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `911facf670369ff558bf402cdfda9e2144fbfff7e75631abe9f41502cf3d78de`.

```text

EXIT 0
```

### moment-scaling-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/moment-scaling-audit.lean`.

Snapshot SHA-256: `5bcf71d23eb4d2cc2ce333db7ee2c6a3bef7ffea29b189a423ad581dc40a91cc`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### moment-bound

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `7ca92ec65f66b733fc3cf00f230171a92d45e4234b2ab61e0f2a4688581eaacb`.

```text

EXIT 0
```

### moment-bound-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/moment-bound-audit.lean`.

Snapshot SHA-256: `58ea771a194ab44e0dcd11667db11a3b0b0929f5b6b42741eb7afd7422429b6b`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### tail-bound

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `4434f1ab2a823d9901e3d7130a35a53336bfe478cd559c57ad59230c65b9ec4c`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### tail-bound-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/tail-bound-audit.lean`.

Snapshot SHA-256: `76941082f26c5323e9538d156c83290341801dc187e02e632527ff6e3e435a8b`.

```text
/private/tmp/heat-time-evidence/tail-bound-audit.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### before-bound

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `c2f565deba306d825a1321fbed33d2364eb1fb8f7ce78a8dbf489b5434721051`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### before-bound-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/before-bound-audit.lean`.

Snapshot SHA-256: `12127807dfa6afaa0e25e0c43c110ac4d615d5337eead869fe60b7f39062c44a`.

```text
/private/tmp/heat-time-evidence/before-bound-audit.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### near-bound

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `01fe9258f1aa418cf064dcb630643eff4c83797ae5a0f68eca2d6e85a0182e34`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### near-bound-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/near-bound-audit.lean`.

Snapshot SHA-256: `4780137cd54ea4d850903b5766ea556c1d22c281cf75e44a2d3fd96626481a84`.

```text
/private/tmp/heat-time-evidence/near-bound-audit.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### joint-continuity

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `42c06162e8818f58376ed2f7e16c6888d7efa5aa556c9199ff8af9ea78e5e12f`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### joint-continuity-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/joint-continuity-audit.lean`.

Snapshot SHA-256: `17004782f644e2e672c431ca3fcf271b65047767872dbdae415d144d349ec1fa`.

```text
/private/tmp/heat-time-evidence/joint-continuity-audit.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### time-product

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `d2b0d3cd86cee873c319944ee24dffa35a67069135ac0ea92f64e9a4722bb0c1`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:270:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:358:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

EXIT 1
```

### time-product-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `d6cd39bfe794773ef1b680444579690e2d48041932ce73181b15575f3f0548e9`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:359:86: error: unexpected token 'set_option'; expected 'lemma'
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:361:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (3000000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

EXIT 1
```

### time-product-03

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `b99d78fb8504adbe559b72a8d6a84428f0c51387641d644d8696f3b2918a98b4`.

```text
STEP G
STEP pos
STEP D
STEP continuous
STEP J
STEP product criterion
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:360:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

EXIT 1
```

### time-product-04

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `f9a8253a7dd5351d0ac1ef898c16e9ae9ca77d57bfe8d235705493848981cf09`.

```text

EXIT 0
```

### time-product-04-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/time-product-04-audit.lean`.

Snapshot SHA-256: `8d768a0bc2a7bfe0d7fed43eb967f67328a6aa5e21f3a66f3af890471e8c2fc5`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### time-FTC

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `97418b12a37a06fc8c7a7f22aca4a008e1cd693afc34d288b5fd4b69d6d3e86c`.

```text

EXIT 0
```

### time-FTC-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/time-FTC-audit.lean`.

Snapshot SHA-256: `d227f0ccc8b94379fa4311f0af179d36a4f6ebade5129d36f1ac6a1e4ce232f2`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### time-kernel-difference

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `f0bb6c8bfee76d5818da75c17fb5734bd7a29daa0bcbd7a584bbaf91ff0a2722`.

```text

EXIT 0
```

### time-kernel-difference-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/time-kernel-difference-audit.lean`.

Snapshot SHA-256: `bbc133fad6e47da95744b3a01ef06e784e58247598f88f0a06e36913bb48a88f`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### far-power

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `e594c397b3f02c06d7c7678fe7ccf6373dc64de477464177fcba2f43c6fe833c`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:472:8: error: linarith failed to find a contradiction
case h
α τ t : ℝ
hα1 : α < 1
hτ : 0 < τ
ht : τ ≤ t
hq : α / 2 - 2 + 1 < 0
hnn : 0 ≤ t ^ (α / 2 - 2 + 1)
a✝ : t ^ (α * 2⁻¹ - 2 + 1) - τ ^ (α * 2⁻¹ - 2 + 1) < -τ ^ (α * 2⁻¹ - 2 + 1)
⊢ False
failed
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:473:41: error: unsolved goals
α τ t : ℝ
hα1 : α < 1
hτ : 0 < τ
ht : τ ≤ t
hq : α / 2 - 2 + 1 < 0
⊢ α * (-2 + α)⁻¹ - (-2 + α)⁻¹ * 2 = 1

EXIT 1
```

### far-power-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `599581bd51d126f04202c9a21aa17d290a010674d39b5aaf2ac925ec9cd8f8e0`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:472:8: error: linarith failed to find a contradiction
case h
α τ t : ℝ
hα1 : α < 1
hτ : 0 < τ
ht : τ ≤ t
hq : α / 2 - 2 + 1 < 0
hnn : 0 ≤ t ^ (α / 2 - 2 + 1)
a✝ : t ^ (α * 2⁻¹ - 2 + 1) - τ ^ (α * 2⁻¹ - 2 + 1) < -τ ^ (α * 2⁻¹ - 2 + 1)
⊢ False
failed
Try this:
  [apply] ring_nf
  
  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.
    
  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:473:41: error: unsolved goals
α τ t : ℝ
hα1 : α < 1
hτ : 0 < τ
ht : τ ≤ t
hq : α / 2 - 2 + 1 < 0
⊢ α * (-2 + α)⁻¹ - (-2 + α)⁻¹ * 2 = 1

EXIT 1
```

### far-power-03

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `787bdb67d62f250e986db670369d6d7b07698279f6400fd472dfd00405136a9c`.

```text

EXIT 0
```

### far-power-03-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/far-power-03-audit.lean`.

Snapshot SHA-256: `d8e42bf1e322e12e701f70108de46a4ffba7041dbc9cbe95d207393a98d6e80a`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### cancelled-time-difference

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `88f345e5f171548cbbf97f235d8d9ba8cfd6b23dcab3ca6bcb96934f1da6dd17`.

```text

EXIT 0
```

### cancelled-time-difference-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/cancelled-time-difference-audit.lean`.

Snapshot SHA-256: `80118e3853a3d487a62b7952a4844aff8307c810a8eba0ed11015a2642fc40ac`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### far-bound

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `65373d204cb433922e9c087735511a51e7cff71f02c09b4364d8c9aed55b97da`.

```text

EXIT 0
```

### far-bound-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/far-bound-audit.lean`.

Snapshot SHA-256: `45df1fcdc0110797bca931a9e95777238de59fc9da7c693ddd6796e1c73526a3`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### assembly

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `0865304eebe52739031c7acde4cfa534fa75a874d8f0a782d9ab6b9fa6a329a2`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:636:29: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:636:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:654:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:654:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

### assembly-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/assembly-audit.lean`.

Snapshot SHA-256: `93a3c13f6c7a3102d87e4b351b7983587206b0bfeb2c1a4cded460a7d0642110`.

```text
/private/tmp/heat-time-evidence/assembly-audit.lean:636:29: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/private/tmp/heat-time-evidence/assembly-audit.lean:636:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/private/tmp/heat-time-evidence/assembly-audit.lean:654:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
/private/tmp/heat-time-evidence/assembly-audit.lean:654:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### final-clean

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `c1a434734f002d2a07db056279a9b82efd68991ee305eff543edb45a8f3c7368`.

```text

EXIT 0
```

### final-clean-audit

Command: `LEAN_NUM_THREADS=1 lake env lean /private/tmp/heat-time-evidence/final-clean-audit.lean`.

Snapshot SHA-256: `e782a7f031a7dedcc9e835f4730e6d6e1ddcf06013e98b3e361df2628cc72513`.

```text
'Poincare.HeatDuhamelHessianTimeHolder.euclideanForm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_tail_bound: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral_sq: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_integral: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_cancelled_hessian_time_difference_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_deriv_one_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hasDerivAt_hessian_time: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_difference: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_time_weighted_hessian_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_eq_tensor: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv_one: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.far_time_deriv_power_integral_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.integrable_weighted_hessian_time_deriv: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.norm_integral_cancelled_hessian_before_le: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.weighted_hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.near_hessian_time_difference_le: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.continuous_hessian_time_deriv_pos: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.instNormedSpaceRealContinuousLinearMapIdClosedSmoothModelOfNatNat__stdin: [propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.euclideanForm: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_sq_smul: [propext, Classical.choice, Quot.sound]
DECL Poincare.HeatDuhamelHessianTimeHolder.hessian_time_deriv_moment_bound: [propext, Classical.choice, Quot.sound]

EXIT 0
```

### final-build

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatDuhamelHessianTimeHolder.lean`.

Snapshot SHA-256: `see recorded build command`.

```text
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:636:29: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:636:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:654:26: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
Poincare/Global/HeatDuhamelHessianTimeHolder.lean:654:40: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

EXIT 0
```

## Final proof diff

```diff
diff --git a/Poincare/Global/HeatDuhamelHessianTimeHolder.lean b/Poincare/Global/HeatDuhamelHessianTimeHolder.lean
new file mode 100644
index 00000000..ea076a5d
--- /dev/null
+++ b/Poincare/Global/HeatDuhamelHessianTimeHolder.lean
@@ -0,0 +1,694 @@
+import Poincare.Global.HeatDuhamelHessianSpatialHolder
+set_option autoImplicit false
+set_option synthInstance.maxHeartbeats 200000
+set_option maxHeartbeats 800000
+noncomputable section
+open Set MeasureTheory
+open scoped Topology InnerProductSpace Interval
+namespace Poincare.HeatDuhamelHessianTimeHolder
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+open HeatKernelHessianMoments HeatDuhamelSpatialHolderHessian
+  HeatDuhamelHessianDifferentiation HeatDuhamelHessianSpatialHolder
+
+/-- The Euclidean inner product as a real bilinear operator. -/
+def euclideanForm : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
+
+/-- The Gaussian Hessian as a linear combination of two fixed bilinear forms. -/
+theorem hessian_eq_tensor {t : ℝ} (ht : t ≠ 0) (x : E) :
+    Hess t x = (heatKernel t x / (4 * t ^ 2)) •
+        (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) -
+      (heatKernel t x / (2 * t)) • euclideanForm := by
+  ext v w
+  have h := iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht x v w
+  simp [iteratedFDeriv_two_apply] at h
+  rw [h]
+  change heatKernel t x * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ / (4 * t ^ 2) - ⟪v, w⟫_ℝ / (2 * t)) =
+    (heatKernel t x / (4 * t ^ 2)) * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) -
+      (heatKernel t x / (2 * t)) * ⟪v, w⟫_ℝ
+  ring
+
+
+/-- The time derivative of the full Gaussian Hessian. -/
+theorem hasDerivAt_hessian_time {t : ℝ} (ht : 0 < t) (x : E) :
+    HasDerivAt (fun r : ℝ => Hess r x)
+      ((heatKernel t x * (‖x‖ ^ 2 / (16 * t ^ 4) - 7 / (8 * t ^ 3))) •
+          (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) -
+        (heatKernel t x * (‖x‖ ^ 2 / (8 * t ^ 3) - 5 / (4 * t ^ 2))) • euclideanForm) t := by
+  have hk : HasDerivAt (fun r : ℝ => heatKernel r x)
+      (heatKernel t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 3 / (2 * t))) t := by
+    have h := (hasDerivAt_heatKernel_time ht x)
+    rw [← h.deriv, deriv_heatKernel_time_eq_heatKernel_mul ht x] at h
+    simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, Nat.cast_ofNat] using h
+  have ha := hk.div (((hasDerivAt_id t).pow 2).const_mul 4)
+    (show 4 * t ^ 2 ≠ 0 by positivity)
+  have hb := hk.div ((hasDerivAt_id t).const_mul 2)
+    (show 2 * t ≠ 0 by positivity)
+  have ha' : HasDerivAt (fun r : ℝ => heatKernel r x / (4 * r ^ 2))
+      (heatKernel t x * (‖x‖ ^ 2 / (16 * t ^ 4) - 7 / (8 * t ^ 3))) t := by
+    convert ha using 1
+    dsimp
+    field_simp
+    ring
+  have hb' : HasDerivAt (fun r : ℝ => heatKernel r x / (2 * r))
+      (heatKernel t x * (‖x‖ ^ 2 / (8 * t ^ 3) - 5 / (4 * t ^ 2))) t := by
+    convert hb using 1
+    dsimp
+    field_simp
+    ring
+  apply ((ha'.smul_const (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x))).sub
+    (hb'.smul_const euclideanForm)).congr_of_eventuallyEq
+  filter_upwards [eventually_gt_nhds ht] with r hr
+  exact hessian_eq_tensor hr.ne' x
+
+
+local notation "DtHess" => fun (t : ℝ) (x : E) => deriv (fun r : ℝ => Hess r x) t
+
+/-- A quartic Gaussian envelope for the time derivative at unit time. -/
+theorem norm_hessian_time_deriv_one_le (x : E) :
+    ‖DtHess 1 x‖ ≤ heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2) := by
+  change ‖deriv (fun r : ℝ => Hess r x) 1‖ ≤ _
+  rw [(hasDerivAt_hessian_time zero_lt_one x).deriv]
+  have hI : ‖euclideanForm‖ ≤ 1 := norm_innerSL_le ℝ
+  have hQ : ‖ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)‖ = ‖x‖ ^ 2 := by
+    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
+    ring
+  have hk : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
+  calc
+    _ ≤ ‖(heatKernel 1 x * (‖x‖ ^ 2 / (16 * 1 ^ 4) - 7 / (8 * 1 ^ 3))) •
+        (ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x))‖ +
+      ‖(heatKernel 1 x * (‖x‖ ^ 2 / (8 * 1 ^ 3) - 5 / (4 * 1 ^ 2))) • euclideanForm‖ :=
+      norm_sub_le _ _
+    _ ≤ (heatKernel 1 x * (‖x‖ ^ 2 / 16 + 7 / 8)) * ‖x‖ ^ 2 +
+        (heatKernel 1 x * (‖x‖ ^ 2 / 8 + 5 / 4)) * 1 := by
+      simp only [norm_smul, norm_mul, Real.norm_of_nonneg hk, hQ, one_pow, mul_one]
+      apply add_le_add
+      · gcongr
+        exact (norm_sub_le _ _).trans_eq (by simp [Real.norm_of_nonneg (sq_nonneg ‖x‖)])
+      · calc
+          _ ≤ (heatKernel 1 x * ‖‖x‖ ^ 2 / 8 - 5 / 4‖) * 1 :=
+            mul_le_mul_of_nonneg_left hI (by positivity)
+          _ ≤ _ := by
+            rw [mul_one]
+            apply mul_le_mul_of_nonneg_left _ hk
+            exact (norm_sub_le _ _).trans_eq (by simp [Real.norm_of_nonneg (sq_nonneg ‖x‖)])
+    _ ≤ _ := by nlinarith [mul_nonneg hk (sq_nonneg (‖x‖ ^ 2))]
+
+
+/-- Spatial continuity of the actual Hessian time derivative at positive time. -/
+theorem continuous_hessian_time_deriv {t : ℝ} (ht : 0 < t) :
+    Continuous (DtHess t) := by
+  have hQ : Continuous (fun x : E =>
+      ContinuousLinearMap.smulRight (innerSL ℝ x) (innerSL ℝ x)) :=
+    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
+      euclideanForm.continuous).clm_apply euclideanForm.continuous
+  change Continuous (fun x : E => deriv (fun r : ℝ => Hess r x) t)
+  simp_rw [(hasDerivAt_hessian_time ht _).deriv]
+  exact ((((contDiff_heatKernel_spatial («E» := E) t).continuous).mul
+    (((continuous_norm.pow 2).div_const _).sub continuous_const)).smul hQ).sub
+    ((((contDiff_heatKernel_spatial («E» := E) t).continuous).mul
+      (((continuous_norm.pow 2).div_const _).sub continuous_const)).smul continuous_const)
+
+
+/-- The quartic envelope remains integrable after a fractional radial weight. -/
+theorem integrable_weighted_hessian_time_deriv_one {α : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) :
+    Integrable (fun x : E => ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
+  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
+  have hc : 0 ≤ c := by dsimp [c]; positivity
+  have hmajor := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
+    («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).const_mul (512 * c)
+  apply hmajor.mono'
+    ((continuous_hessian_time_deriv zero_lt_one).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+  refine Filter.Eventually.of_forall fun x => ?_
+  change ‖‖DtHess 1 x‖ * ‖x‖ ^ α‖ ≤ _
+  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+  have hk0 : 0 ≤ heatKernel 1 x := heatKernel_nonneg zero_lt_one x
+  have hw : ‖x‖ ^ α ≤ 1 + ‖x‖ ^ 2 := by
+    by_cases hx : ‖x‖ ≤ 1
+    · exact (Real.rpow_le_one (norm_nonneg x) hx hα).trans (by nlinarith [sq_nonneg ‖x‖])
+    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hα2
+      rw [Real.rpow_two] at h
+      linarith
+  have hbase : 1 + ‖x‖ ^ 2 ≤ 16 * Real.exp (‖x‖ ^ 2 / 16) := by
+    have h := Real.add_one_le_exp (‖x‖ ^ 2 / 16)
+    linarith
+  have hsquare : (1 + ‖x‖ ^ 2) ^ 2 ≤ 256 * Real.exp (‖x‖ ^ 2 / 8) := by
+    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖ ^ 2) hbase 2
+    have he : Real.exp (‖x‖ ^ 2 / 16) ^ 2 = Real.exp (‖x‖ ^ 2 / 8) := by
+      rw [pow_two, ← Real.exp_add]
+      congr 1
+      ring
+    simpa only [mul_pow, he, show (16 : ℝ) ^ 2 = 256 by norm_num] using h
+  have hpoly : ‖x‖ ^ 4 + ‖x‖ ^ 2 + 2 ≤ 2 * (1 + ‖x‖ ^ 2) ^ 2 := by
+    nlinarith [sq_nonneg (‖x‖ ^ 2), sq_nonneg ‖x‖]
+  have hk : heatKernel (1 : ℝ) x = c * Real.exp (-(‖x‖ ^ 2 / 4)) := by
+    simp [heatKernel, c, ClosedSmoothModel, neg_div]
+  calc
+    _ ≤ (heatKernel 1 x * (‖x‖ ^ 4 + ‖x‖ ^ 2 + 2)) * ‖x‖ ^ α :=
+      mul_le_mul_of_nonneg_right (norm_hessian_time_deriv_one_le x) (by positivity)
+    _ ≤ (heatKernel 1 x * (2 * (1 + ‖x‖ ^ 2) ^ 2)) * (1 + ‖x‖ ^ 2) := by
+      gcongr
+    _ ≤ (heatKernel 1 x * (2 * (256 * Real.exp (‖x‖ ^ 2 / 8)))) * (1 + ‖x‖ ^ 2) := by
+      gcongr
+    _ = (512 * c) * ((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) := by
+      rw [hk]
+      have he : Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8) =
+          Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) := by
+        rw [← Real.exp_add]
+        congr 1
+        ring
+      calc
+        _ = (512 * c) * ((1 + ‖x‖ ^ 2) *
+          (Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (‖x‖ ^ 2 / 8))) := by ring
+        _ = _ := by rw [he]
+
+
+/-- Parabolic dilation of the time derivative of the Gaussian Hessian. -/
+theorem hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    DtHess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • DtHess 1 x := by
+  change deriv (fun r : ℝ => Hess r (a • x)) (a ^ 2) =
+    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) • deriv (fun r : ℝ => Hess r x) 1
+  rw [(hasDerivAt_hessian_time (sq_pos_of_pos ha) (a • x)).deriv,
+    (hasDerivAt_hessian_time zero_lt_one x).deriv]
+  ext v w
+  change (heatKernel (a ^ 2) (a • x) *
+      (‖a • x‖ ^ 2 / (16 * (a ^ 2) ^ 4) - 7 / (8 * (a ^ 2) ^ 3))) *
+        (⟪a • x, v⟫_ℝ * ⟪a • x, w⟫_ℝ) -
+      (heatKernel (a ^ 2) (a • x) *
+        (‖a • x‖ ^ 2 / (8 * (a ^ 2) ^ 3) - 5 / (4 * (a ^ 2) ^ 2))) * ⟪v, w⟫_ℝ =
+    ((a ^ 3)⁻¹ * (a ^ 4)⁻¹) *
+      ((heatKernel 1 x * (‖x‖ ^ 2 / (16 * 1 ^ 4) - 7 / (8 * 1 ^ 3))) *
+        (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) -
+      (heatKernel 1 x * (‖x‖ ^ 2 / (8 * 1 ^ 3) - 5 / (4 * 1 ^ 2))) * ⟪v, w⟫_ℝ)
+  rw [heatKernel_sq_smul a ha x, norm_smul_of_nonneg ha.le]
+  simp only [inner_smul_left, conj_trivial, ClosedSmoothModel, finrank_euclideanSpace_fin]
+  field_simp
+
+/-- Pointwise parabolic dilation including the radial weight. -/
+theorem weighted_hessian_time_deriv_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
+    ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
+      ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (‖DtHess 1 x‖ * ‖x‖ ^ α) := by
+  rw [hessian_time_deriv_sq_smul a ha x,
+    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 4)⁻¹ by positivity) (DtHess 1 x),
+    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
+  ring
+
+
+/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
+theorem weighted_hessian_time_deriv_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
+    (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
+      ((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖DtHess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ x : E, ‖DtHess (a ^ 2) x‖ * ‖x‖ ^ α) =
+        ∫ x : E, ‖DtHess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * (a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
+      simp_rw [weighted_hessian_time_deriv_sq_smul a ha]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (((a ^ 4)⁻¹ * a ^ α) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α)) := by ring
+
+
+/-- Weighted Bochner integrability at every positive time. -/
+theorem integrable_weighted_hessian_time_deriv {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
+    {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) := by
+  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
+  rw [← Real.sq_sqrt ht.le]
+  apply (integrable_comp_smul_iff volume _ ha.ne').1
+  simp_rw [weighted_hessian_time_deriv_sq_smul (Real.sqrt t) ha]
+  exact (integrable_weighted_hessian_time_deriv_one hα hα2).const_mul _
+
+
+/-- Exact scaling of the weighted Hessian time-derivative moment. -/
+theorem weighted_hessian_time_deriv_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
+    (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) =
+      t ^ (α / 2 - 2) * (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α) := by
+  have h := weighted_hessian_time_deriv_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h]
+  congr 1
+  have hp : (Real.sqrt t) ^ 4 = t ^ 2 := by nlinarith [Real.sq_sqrt ht.le]
+  rw [hp, Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_two]
+  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
+  ring
+
+/-- The weighted time derivative has a positive constant uniform for all positive times. -/
+theorem hessian_time_deriv_moment_bound :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
+      Integrable (fun x : E => ‖DtHess t x‖ * ‖x‖ ^ α) ∧
+      (∫ x : E, ‖DtHess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 2) := by
+  intro α hα hα1
+  refine ⟨max 1 (∫ x : E, ‖DtHess 1 x‖ * ‖x‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t ht
+  refine ⟨integrable_weighted_hessian_time_deriv hα.le (by linarith) ht, ?_⟩
+  rw [weighted_hessian_time_deriv_integral ht, mul_comm (t ^ (α / 2 - 2))]
+  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
+
+/-- The new time interval contributes only the half-exponent Hölder tail. -/
+theorem hessian_tail_bound {α K T t₁ t₂ : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht₁ : t₁ ∈ Icc 0 T)
+    (ht₂ : t₂ ∈ Icc 0 T) (h12 : t₁ ≤ t₂) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ s in t₁..t₂, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ ≤
+      ((∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * |t₂ - t₁| ^ (α / 2) := by
+  have h := norm_integral_cancelled_hessian_near_le hα hα1 h12
+    (fun s hs => hK s ⟨ht₁.1.trans hs.1.le, hs.2.le.trans ht₂.2⟩) x
+  rw [abs_of_nonneg (sub_nonneg.mpr h12)]
+  convert h using 1
+  ring
+
+/-- An interval ending before the observation time obeys the same short-interval bound. -/
+theorem norm_integral_cancelled_hessian_before_le {α K a b t : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (hab : a ≤ b) (hbt : b ≤ t)
+    {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a b, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖∫ s in a..b, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      (K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)) * (2 / α) * (b - a) ^ (α / 2) := by
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α)
+  have hA : 0 ≤ A := mul_nonneg hK0 (integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+  have hi : IntervalIntegrable (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) volume a b := by
+    have h := ((intervalIntegral.intervalIntegrable_rpow'
+      (a := (0 : ℝ)) (b := b - a) (r := α / 2 - 1) (by linarith)).comp_sub_left b).symm
+    simp only [sub_zero, sub_sub_cancel] at h
+    exact h.const_mul A
+  have hb : ‖∫ s in Ioo a b, ∫ y : E,
+      (f (s, x - y) - f (s, x)) • Hess (t - s) y‖ ≤
+      ∫ s in Ioo a b, A * (b - s) ^ (α / 2 - 1) := by
+    apply norm_integral_le_of_norm_le
+      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi)
+    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+    exact (norm_cancelled_hessian_integral_le hα.le (by linarith)
+      (by linarith [hs.2] : 0 < t - s) (hK s hs) x).trans
+      (mul_le_mul_of_nonneg_left
+        (Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hs.2) (by linarith) (by linarith)) hA)
+  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hab,
+    ← intervalIntegral.integral_of_le hab] at hb
+  refine hb.trans_eq ?_
+  have he := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := b - a)
+    (fun s : ℝ => A * (b - s) ^ (α / 2 - 1)) a
+  simp only [zero_add, sub_add_cancel] at he
+  have hs (s : ℝ) : b - (s + a) = b - a - s := by ring
+  simp only [hs] at he
+  rw [← he, integral_hessian_majorant hα]
+
+/-- The recent part of a time increment costs twice the Hessian majorant. -/
+theorem near_hessian_time_difference_le {α K a t₁ t₂ : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (hK0 : 0 ≤ K) (ha : a ≤ t₁) (h12 : t₁ ≤ t₂)
+    (hscale : t₁ - a ≤ t₂ - t₁) {f : ℝ × E → ℝ}
+    (hK : ∀ s ∈ Ioo a t₁, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖(∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y) -
+      (∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y)‖ ≤
+      (2 * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)) * K * (t₂ - t₁) ^ (α / 2) := by
+  let A := K * (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
+  have hA : 0 ≤ A := mul_nonneg
+    (mul_nonneg hK0 (integral_nonneg (fun y =>
+      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))))
+    (div_nonneg (by norm_num) hα.le)
+  have hp : (t₁ - a) ^ (α / 2) ≤ (t₂ - t₁) ^ (α / 2) :=
+    Real.rpow_le_rpow (sub_nonneg.mpr ha) hscale (by linarith)
+  calc
+    _ ≤ ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y‖ +
+      ‖∫ s in a..t₁, ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y‖ :=
+      norm_sub_le _ _
+    _ ≤ A * (t₁ - a) ^ (α / 2) + A * (t₁ - a) ^ (α / 2) :=
+      add_le_add (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha h12 hK x)
+        (norm_integral_cancelled_hessian_before_le hα hα1 hK0 ha le_rfl hK x)
+    _ ≤ A * (t₂ - t₁) ^ (α / 2) + A * (t₂ - t₁) ^ (α / 2) :=
+      add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hp hA)
+    _ = _ := by dsimp [A]; ring
+
+/-- Dilation gives joint continuity of the full DtHessian at positive times. -/
+theorem continuous_hessian_time_deriv_pos :
+    Continuous (fun p : Ioi (0 : ℝ) × E => DtHess p.1 p.2) := by
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+    { norm_smul_le := norm_real_smul_continuousLinearMap_two_le }
+  have hunit : Continuous (DtHess 1) := continuous_hessian_time_deriv zero_lt_one
+  have ha : Continuous (fun p : Ioi (0 : ℝ) × E => Real.sqrt (p.1 : ℝ)) :=
+    Real.continuous_sqrt.comp (continuous_subtype_val.comp continuous_fst)
+  have hapos (p : Ioi (0 : ℝ) × E) : 0 < Real.sqrt (p.1 : ℝ) :=
+    Real.sqrt_pos.2 p.1.property
+  have hc : Continuous (fun p : Ioi (0 : ℝ) × E =>
+      (((Real.sqrt (p.1 : ℝ)) ^ 3)⁻¹ * ((Real.sqrt (p.1 : ℝ)) ^ 4)⁻¹) •
+        DtHess 1 ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)) :=
+    ((ha.pow 3).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')).mul
+      ((ha.pow 4).inv₀ (fun p => pow_ne_zero _ (hapos p).ne')) |>.smul
+      (hunit.comp ((ha.inv₀ (fun p => (hapos p).ne')).smul continuous_snd))
+  apply hc.congr
+  intro p
+  have h := hessian_time_deriv_sq_smul (Real.sqrt (p.1 : ℝ)) (hapos p)
+    ((Real.sqrt (p.1 : ℝ))⁻¹ • p.2)
+  simpa only [Real.sq_sqrt p.1.property.le, smul_inv_smul₀ (hapos p).ne'] using h.symm
+
+
+/-- The weighted time derivative is integrable jointly on every positive time slab. -/
+theorem integrable_time_weighted_hessian_deriv {α a : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (b : ℝ) :
+    Integrable (fun p : ℝ × E => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α)
+      ((volume.restrict (Icc a b)).prod volume) := by
+  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
+  have hpos (p : ℝ × E) : 0 < max a p.1 := ha.trans_le (le_max_left _ _)
+  have hD : Continuous (fun p : ℝ × E => DtHess (max a p.1) p.2) :=
+    continuous_hessian_time_deriv_pos.comp
+      (((continuous_const.max continuous_fst).subtype_mk hpos).prodMk continuous_snd)
+  have hg : Continuous G := hD.norm.mul
+    ((Real.continuous_rpow_const hα).comp continuous_snd.norm)
+  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
+  have hJ : 0 ≤ J := integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
+  constructor
+  · refine Filter.Eventually.of_forall ?_
+    intro r
+    change Integrable (fun y : E => ‖DtHess (max a r) y‖ * ‖y‖ ^ α) volume
+    exact integrable_weighted_hessian_time_deriv hα hα2 (ha.trans_le (le_max_left a r))
+  · have hm := hg.norm.stronglyMeasurable.integral_prod_right' (ν := volume)
+    refine (integrable_const (a ^ (α / 2 - 2) * J)).mono' hm.aestronglyMeasurable ?_
+    refine Filter.Eventually.of_forall fun r => ?_
+    have he : (∫ y : E, ‖G (r, y)‖) = ∫ y : E, G (r, y) := by
+      apply integral_congr_ae
+      exact Filter.Eventually.of_forall fun y => Real.norm_of_nonneg
+        (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _)), he]
+    change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
+    rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
+    exact mul_le_mul_of_nonneg_right
+      (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ
+
+/-- Integrating the actual time derivative bounds a kernel Hessian increment. -/
+theorem norm_hessian_time_difference_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (y : E) :
+    ‖Hess b y - Hess a y‖ ≤ ∫ r in a..b, ‖DtHess (max a r) y‖ := by
+  have hD : Continuous (fun r : ℝ => DtHess (max a r) y) :=
+    continuous_hessian_time_deriv_pos.comp
+      (((continuous_const.max continuous_id).subtype_mk
+        (fun r => ha.trans_le (le_max_left _ _))).prodMk continuous_const)
+  have hd (r : ℝ) (hr : r ∈ uIcc a b) :
+      HasDerivAt (fun t : ℝ => Hess t y) (DtHess (max a r) y) r := by
+    rw [uIcc_of_le hab] at hr
+    rw [max_eq_right hr.1]
+    exact (hasDerivAt_hessian_time (ha.trans_le hr.1) y).differentiableAt.hasDerivAt
+  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hD.intervalIntegrable a b)
+  rw [← he]
+  exact intervalIntegral.norm_integral_le_integral_norm hab
+
+/-- A weighted kernel Hessian time increment is linear away from time zero. -/
+theorem weighted_hessian_time_difference {α a b : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) :
+    Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ∧
+    (∫ y : E, ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) ≤
+      (b - a) * a ^ (α / 2 - 2) * (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) := by
+  let G : ℝ × E → ℝ := fun p => ‖DtHess (max a p.1) p.2‖ * ‖p.2‖ ^ α
+  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
+  have hJ : 0 ≤ J := integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+  have hg : Integrable G ((volume.restrict (Icc a b)).prod volume) :=
+    integrable_time_weighted_hessian_deriv hα hα2 ha b
+  have hiMajor := hg.integral_prod_right
+  have hb (y : E) : ‖Hess b y - Hess a y‖ * ‖y‖ ^ α ≤ ∫ r in Icc a b, G (r, y) := by
+    calc
+      _ ≤ (∫ r in a..b, ‖DtHess (max a r) y‖) * ‖y‖ ^ α :=
+        mul_le_mul_of_nonneg_right (norm_hessian_time_difference_le ha hab y)
+          (Real.rpow_nonneg (norm_nonneg _) _)
+      _ = _ := by
+        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
+        exact (intervalIntegral.integral_mul_const _ _).symm
+  have hH (t : ℝ) : Continuous (Hess t) :=
+    (((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
+  have hi : Integrable (fun y : E => ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) :=
+    hiMajor.mono' (((hH b).sub (hH a)).norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable
+      (Filter.Eventually.of_forall fun y => by
+        change ‖‖Hess b y - Hess a y‖ * ‖y‖ ^ α‖ ≤ _
+        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
+        exact hb y)
+  refine ⟨hi, (integral_mono hi hiMajor hb).trans ?_⟩
+  rw [← integral_integral_swap hg]
+  calc
+    (∫ r in Icc a b, ∫ y : E, G (r, y)) ≤ ∫ _r in Icc a b, a ^ (α / 2 - 2) * J := by
+      apply integral_mono_ae hg.integral_prod_left (integrable_const _)
+      refine Filter.Eventually.of_forall fun r => ?_
+      change (∫ y : E, ‖DtHess (max a r) y‖ * ‖y‖ ^ α) ≤ _
+      rw [weighted_hessian_time_deriv_integral (ha.trans_le (le_max_left _ _))]
+      exact mul_le_mul_of_nonneg_right
+        (Real.rpow_le_rpow_of_nonpos ha (le_max_left _ _) (by linarith)) hJ
+    _ = _ := by
+      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
+        intervalIntegral.integral_const, smul_eq_mul]
+      ring
+
+/-- The far-time fourth-order power integrates to the half Hölder exponent. -/
+theorem far_time_deriv_power_integral_le {α τ t : ℝ}
+    (hα1 : α < 1) (hτ : 0 < τ) (ht : τ ≤ t) :
+    τ * (∫ s in (0 : ℝ)..(t - τ), (t - s) ^ (α / 2 - 2)) ≤
+      (2 / (2 - α)) * τ ^ (α / 2) := by
+  have hq : α / 2 - 2 + 1 < 0 := by linarith
+  rw [intervalIntegral.integral_comp_sub_left
+    (fun r : ℝ => r ^ (α / 2 - 2)) t, sub_sub_cancel, sub_zero]
+  rw [integral_rpow (Or.inr ⟨by linarith, ?_⟩)]
+  · calc
+      τ * ((t ^ (α / 2 - 2 + 1) - τ ^ (α / 2 - 2 + 1)) / (α / 2 - 2 + 1)) ≤
+          τ * (-τ ^ (α / 2 - 2 + 1) / (α / 2 - 2 + 1)) := by
+        apply mul_le_mul_of_nonneg_left _ hτ.le
+        simp only [div_eq_mul_inv]
+        apply mul_le_mul_of_nonpos_right _ (inv_nonpos.mpr hq.le)
+        have hnn := Real.rpow_nonneg (hτ.le.trans ht) (α / 2 - 2 + 1)
+        simp only [div_eq_mul_inv] at hnn
+        linarith only [hnn]
+      _ = (2 / (2 - α)) * τ ^ (α / 2) := by
+        rw [show α / 2 - 2 + 1 = α / 2 - 1 by ring, Real.rpow_sub hτ, Real.rpow_one]
+        field_simp [hτ.ne', show 2 - α ≠ 0 by linarith, show α / 2 - 1 ≠ 0 by linarith]
+        ring_nf
+        all_goals
+          have hi := mul_inv_cancel₀ (show -2 + α ≠ 0 by linarith)
+          nlinarith only [hi]
+  · rw [uIcc_of_le ht]
+    intro hz
+    exact (not_le.mpr hτ) hz.1
+
+/-- Cancellation transfers the weighted kernel time increment to Hölder forcing. -/
+theorem norm_cancelled_hessian_time_difference_le {α a b M K : ℝ}
+    (hα : 0 ≤ α) (hα2 : α ≤ 2) (ha : 0 < a) (hab : a ≤ b) (hK0 : 0 ≤ K)
+    {f : E → ℝ} (hf : AEStronglyMeasurable f volume) (hM : ∀ y, ‖f y‖ ≤ M)
+    (hK : ∀ x y : E, |f x - f y| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖(∫ y : E, (f (x - y) - f x) • Hess b y) -
+      (∫ y : E, (f (x - y) - f x) • Hess a y)‖ ≤
+      ((∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * K * (b - a)) * a ^ (α / 2 - 2) := by
+  rw [← integral_sub (integrable_cancelled_hessian (ha.trans_le hab) hf hM x)
+    (integrable_cancelled_hessian ha hf hM x)]
+  simp_rw [← smul_sub]
+  have hi := (weighted_hessian_time_difference hα hα2 ha hab).1.const_mul K
+  have hb (y : E) : ‖(f (x - y) - f x) • (Hess b y - Hess a y)‖ ≤
+      K * (‖Hess b y - Hess a y‖ * ‖y‖ ^ α) := by
+    have hd : ‖f (x - y) - f x‖ ≤ K * ‖y‖ ^ α := by
+      have he : x - y - x = -y := by abel
+      simpa only [he, norm_neg, Real.norm_eq_abs] using hK (x - y) x
+    calc
+      _ ≤ ‖f (x - y) - f x‖ * ‖Hess b y - Hess a y‖ :=
+        norm_real_smul_continuousLinearMap_two_le _ _
+      _ ≤ (K * ‖y‖ ^ α) * ‖Hess b y - Hess a y‖ :=
+        mul_le_mul_of_nonneg_right hd (norm_nonneg _)
+      _ = _ := by ring
+  calc
+    _ ≤ ∫ y : E, K * (‖Hess b y - Hess a y‖ * ‖y‖ ^ α) :=
+      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
+    _ = K * (∫ y : E, ‖Hess b y - Hess a y‖ * ‖y‖ ^ α) := integral_const_mul _ _
+    _ ≤ K * ((b - a) * a ^ (α / 2 - 2) * (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α)) :=
+      mul_le_mul_of_nonneg_left (weighted_hessian_time_difference hα hα2 ha hab).2 hK0
+    _ = _ := by ring
+
+/-- The far part of the Duhamel time increment has the required half Hölder power. -/
+theorem far_hessian_time_difference_le {α T t₁ t₂ M K : ℝ}
+    (hα : 0 < α) (hα1 : α < 1) (ht₁ : t₁ ∈ Icc 0 T) (ht₂ : t₂ ∈ Icc 0 T)
+    (h12 : t₁ < t₂) (hscale : t₂ - t₁ < t₁) (hK0 : 0 ≤ K)
+    {f : ℝ × E → ℝ} (hf : ContinuousOn f (Icc 0 T ×ˢ univ))
+    (hM : ∀ s ∈ Icc 0 T, ∀ y : E, |f (s, y)| ≤ M)
+    (hK : ∀ s ∈ Icc 0 T, ∀ x y : E,
+      |f (s, x) - f (s, y)| ≤ K * ‖x - y‖ ^ α) (x : E) :
+    ‖(∫ s in (0 : ℝ)..(t₁ - (t₂ - t₁)), ∫ y : E,
+        (f (s, x - y) - f (s, x)) • Hess (t₂ - s) y) -
+      (∫ s in (0 : ℝ)..(t₁ - (t₂ - t₁)), ∫ y : E,
+        (f (s, x - y) - f (s, x)) • Hess (t₁ - s) y)‖ ≤
+      ((∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * (2 / (2 - α))) *
+        K * (t₂ - t₁) ^ (α / 2) := by
+  let a := t₁ - (t₂ - t₁)
+  let J := ∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α
+  let F := fun r s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (r - s) y
+  have ha : 0 < a := sub_pos.mpr hscale
+  have hτ : 0 < t₂ - t₁ := sub_pos.mpr h12
+  have hat : a ≤ t₁ := sub_le_self t₁ hτ.le
+  have hJ : 0 ≤ J := integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
+  have hFi (r : ℝ) (hr : r ∈ Icc 0 T) (har : a ≤ r) :
+      IntervalIntegrable (F r) volume 0 a :=
+    (intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le).mpr
+      ((integrableOn_cancelled_hessian_time hα hα1 hr hf hK x).mono_set
+        (Ioo_subset_Ioo le_rfl har))
+  have hip : IntervalIntegrable (fun r : ℝ => r ^ (α / 2 - 2)) volume (t₂ - t₁) t₁ := by
+    apply intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
+    rw [uIcc_of_le hscale.le]
+    intro hz
+    exact (not_le.mpr hτ) hz.1
+  have hiB : IntervalIntegrable
+      (fun s : ℝ => J * K * (t₂ - t₁) * (t₁ - s) ^ (α / 2 - 2)) volume 0 a := by
+    have h := (hip.comp_sub_left t₁).symm
+    simp only [sub_self] at h
+    exact h.const_mul (J * K * (t₂ - t₁))
+  have hbound : ‖∫ s in (0 : ℝ)..a, F t₂ s - F t₁ s‖ ≤
+      ∫ s in (0 : ℝ)..a, J * K * (t₂ - t₁) * (t₁ - s) ^ (α / 2 - 2) := by
+    apply intervalIntegral.norm_integral_le_of_norm_le ha.le _ hiB
+    refine Filter.Eventually.of_forall fun s hs => ?_
+    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, (hs.2.trans hat).trans ht₁.2⟩
+    have hsτ : t₂ - t₁ ≤ t₁ - s := by dsimp [a] at hs; linarith [hs.2]
+    have hlag : 0 < t₁ - s := hτ.trans_le hsτ
+    have hfc : Continuous (fun y : E => f (s, y)) :=
+      hf.comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩)
+    have hMs : ∀ y : E, ‖f (s, y)‖ ≤ M := by simpa only [Real.norm_eq_abs] using hM s hsT
+    have hd := norm_cancelled_hessian_time_difference_le hα.le (by linarith) hlag
+      (show t₁ - s ≤ t₂ - s by linarith) hK0 hfc.aestronglyMeasurable hMs (hK s hsT) x
+    have he : t₂ - s - (t₁ - s) = t₂ - t₁ := by ring
+    simpa only [he] using hd
+  change ‖(∫ s in (0 : ℝ)..a, F t₂ s) - (∫ s in (0 : ℝ)..a, F t₁ s)‖ ≤ _
+  rw [← intervalIntegral.integral_sub (hFi t₂ ht₂ (hat.trans h12.le)) (hFi t₁ ht₁ hat)]
+  refine hbound.trans ?_
+  rw [intervalIntegral.integral_const_mul]
+  calc
+    (J * K * (t₂ - t₁)) * (∫ s in (0 : ℝ)..a, (t₁ - s) ^ (α / 2 - 2)) =
+      (J * K) * ((t₂ - t₁) * (∫ s in (0 : ℝ)..a, (t₁ - s) ^ (α / 2 - 2))) := by ring
+    _ ≤ (J * K) * ((2 / (2 - α)) * (t₂ - t₁) ^ (α / 2)) :=
+      mul_le_mul_of_nonneg_left (far_time_deriv_power_integral_le hα1 hτ hscale.le)
+        (mul_nonneg hJ hK0)
+    _ = _ := by ring
+
+/-- The time Hölder estimate for the actual Duhamel Hessian, including both endpoints. -/
+theorem duhamel_hessian_time_holder :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
+  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
+  ContinuousOn f (Icc 0 T ×ˢ univ) →
+  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
+  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
+  ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
+    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖
+      ≤ C * K * |t₁ - t₂| ^ (α / 2) := by
+  intro α hα hα1
+  let B := (∫ y : E, ‖Hess 1 y‖ * ‖y‖ ^ α) * (2 / α)
+  let F := (∫ y : E, ‖DtHess 1 y‖ * ‖y‖ ^ α) * (2 / (2 - α))
+  have hB : 0 ≤ B := mul_nonneg (integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+    (div_nonneg (by norm_num) hα.le)
+  have hF : 0 ≤ F := mul_nonneg (integral_nonneg (fun y =>
+    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
+    (div_nonneg (by norm_num) (by linarith))
+  refine ⟨max 1 (3 * B + F), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro T _ _ f M K _ hK0 hf hM hK
+  let u : ℝ → E → ℝ := fun t x => ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  change ∀ t₁ ∈ Icc 0 T, ∀ t₂ ∈ Icc 0 T, ∀ x : E,
+    ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
+      max 1 (3 * B + F) * K * |t₁ - t₂| ^ (α / 2)
+  have ordered (t₁ : ℝ) (ht₁ : t₁ ∈ Icc 0 T) (t₂ : ℝ) (ht₂ : t₂ ∈ Icc 0 T)
+      (h12 : t₁ ≤ t₂) (x : E) :
+      ‖fderiv ℝ (fderiv ℝ (u t₂)) x - fderiv ℝ (fderiv ℝ (u t₁)) x‖ ≤
+        (3 * B + F) * K * (t₂ - t₁) ^ (α / 2) := by
+    by_cases he : t₁ = t₂
+    · subst t₂
+      simp [Real.zero_rpow (show α / 2 ≠ 0 by linarith)]
+    have hlt : t₁ < t₂ := lt_of_le_of_ne h12 he
+    let H := fun r s => ∫ y : E, (f (s, x - y) - f (s, x)) • Hess (r - s) y
+    have hi (r : ℝ) (hr : r ∈ Icc 0 T) (b : ℝ) (hb : 0 ≤ b) (hbr : b ≤ r) :
+        IntervalIntegrable (H r) volume 0 b :=
+      (intervalIntegrable_iff_integrableOn_Ioo_of_le hb).mpr
+        ((integrableOn_cancelled_hessian_time hα hα1 hr hf hK x).mono_set
+          (Ioo_subset_Ioo le_rfl hbr))
+    have hsplit : (∫ s in (0 : ℝ)..t₂, H t₂ s) =
+        (∫ s in (0 : ℝ)..t₁, H t₂ s) + (∫ s in t₁..t₂, H t₂ s) :=
+      (intervalIntegral.integral_add_adjacent_intervals (hi t₂ ht₂ t₁ ht₁.1 h12)
+        ((hi t₂ ht₂ t₁ ht₁.1 h12).symm.trans (hi t₂ ht₂ t₂ ht₂.1 le_rfl))).symm
+    have htail : ‖∫ s in t₁..t₂, H t₂ s‖ ≤ B * K * (t₂ - t₁) ^ (α / 2) := by
+      simpa only [abs_of_nonneg (sub_nonneg.mpr h12)] using hessian_tail_bound hα hα1 ht₁ ht₂ h12 hK x
+    have hoverlap : ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤
+        (2 * B + F) * K * (t₂ - t₁) ^ (α / 2) := by
+      by_cases hsmall : t₁ ≤ t₂ - t₁
+      · have hn := near_hessian_time_difference_le hα hα1 hK0 ht₁.1 h12
+          (by simpa using hsmall)
+          (fun s hs => hK s ⟨hs.1.le, hs.2.le.trans ht₁.2⟩) x
+        have hn' : ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤
+            (2 * B) * K * (t₂ - t₁) ^ (α / 2) := by
+          convert hn using 1
+          dsimp [B]
+          ring
+        exact hn'.trans (mul_le_mul_of_nonneg_right
+          (mul_le_mul_of_nonneg_right (by linarith : 2 * B ≤ 2 * B + F) hK0)
+          (Real.rpow_nonneg (sub_nonneg.mpr h12) _))
+      have hscale : t₂ - t₁ < t₁ := lt_of_not_ge hsmall
+      let a := t₁ - (t₂ - t₁)
+      have ha : 0 < a := sub_pos.mpr hscale
+      have hat : a ≤ t₁ := sub_le_self t₁ (sub_nonneg.mpr h12)
+      have hs (r : ℝ) (hr : r ∈ Icc 0 T) (htr : t₁ ≤ r) :
+          (∫ s in (0 : ℝ)..t₁, H r s) =
+            (∫ s in (0 : ℝ)..a, H r s) + (∫ s in a..t₁, H r s) :=
+        (intervalIntegral.integral_add_adjacent_intervals (hi r hr a ha.le (hat.trans htr))
+          ((hi r hr a ha.le (hat.trans htr)).symm.trans (hi r hr t₁ ht₁.1 htr))).symm
+      have hn : ‖(∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s)‖ ≤
+          (2 * B) * K * (t₂ - t₁) ^ (α / 2) := by
+        have h := near_hessian_time_difference_le hα hα1 hK0 hat h12
+          (by dsimp [a]; linarith)
+          (fun s hs => hK s ⟨ha.le.trans hs.1.le, hs.2.le.trans ht₁.2⟩) x
+        convert h using 1
+        dsimp [B]
+        ring
+      have hfar : ‖(∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)‖ ≤
+          F * K * (t₂ - t₁) ^ (α / 2) :=
+        far_hessian_time_difference_le hα hα1 ht₁ ht₂ hlt hscale hK0 hf hM hK x
+      rw [hs t₂ ht₂ h12, hs t₁ ht₁ le_rfl]
+      calc
+        _ = ‖((∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)) +
+            ((∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s))‖ := by congr 1; abel
+        _ ≤ ‖(∫ s in (0 : ℝ)..a, H t₂ s) - (∫ s in (0 : ℝ)..a, H t₁ s)‖ +
+            ‖(∫ s in a..t₁, H t₂ s) - (∫ s in a..t₁, H t₁ s)‖ := norm_add_le _ _
+        _ ≤ F * K * (t₂ - t₁) ^ (α / 2) + (2 * B) * K * (t₂ - t₁) ^ (α / 2) :=
+          add_le_add hfar hn
+        _ = _ := by ring
+    rw [hessian_duhamel_eq_integral hα hα1 ht₂ hf hM hK x,
+      hessian_duhamel_eq_integral hα hα1 ht₁ hf hM hK x]
+    change ‖(∫ s in (0 : ℝ)..t₂, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ ≤ _
+    rw [hsplit]
+    calc
+      _ = ‖((∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)) +
+          (∫ s in t₁..t₂, H t₂ s)‖ := by congr 1; abel
+      _ ≤ ‖(∫ s in (0 : ℝ)..t₁, H t₂ s) - (∫ s in (0 : ℝ)..t₁, H t₁ s)‖ +
+          ‖∫ s in t₁..t₂, H t₂ s‖ := norm_add_le _ _
+      _ ≤ (2 * B + F) * K * (t₂ - t₁) ^ (α / 2) + B * K * (t₂ - t₁) ^ (α / 2) :=
+        add_le_add hoverlap htail
+      _ = _ := by ring
+  intro t₁ ht₁ t₂ ht₂ x
+  have hraw : ‖fderiv ℝ (fderiv ℝ (u t₁)) x - fderiv ℝ (fderiv ℝ (u t₂)) x‖ ≤
+      (3 * B + F) * K * |t₁ - t₂| ^ (α / 2) := by
+    rcases le_total t₁ t₂ with h12 | h21
+    · rw [abs_sub_comm t₁ t₂, abs_of_nonneg (sub_nonneg.mpr h12), norm_sub_rev]
+      exact ordered t₁ ht₁ t₂ ht₂ h12 x
+    · rw [abs_of_nonneg (sub_nonneg.mpr h21)]
+      exact ordered t₂ ht₂ t₁ ht₁ h21 x
+  exact hraw.trans (mul_le_mul_of_nonneg_right
+    (mul_le_mul_of_nonneg_right (le_max_right 1 (3 * B + F)) hK0)
+    (Real.rpow_nonneg (abs_nonneg _) _))
+
+end Poincare.HeatDuhamelHessianTimeHolder
```
