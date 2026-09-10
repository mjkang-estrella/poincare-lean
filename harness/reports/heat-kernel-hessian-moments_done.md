# Heat kernel Hessian moments: completed worker proof

Date: 2026-09-10. Base: `094313e6835e844993f59534cb6d68a496f138fb`. Proof head: `ad58be1454636f45f32b5a4198ec1aa5bf770ee6`.
Branch: `worker/heat-kernel-hessian-moments`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.
Mathlib: `7175569c842f9164564bd76ff8b207e7b4705522`.

The exact frozen `Poincare.HeatKernelHessianMoments.hessian_moments` theorem compiles.
The independent assignment below uses the statement extracted verbatim from
`harness/tasks/heat-kernel-hessian-moments.md`. All ten theorems and the local
normed-group instance have exactly `[propext, Classical.choice, Quot.sound]`.
The module-wide audit also checks that compiler-generated internal declarations
have no dependencies outside those three; notation metadata and some generated
simplifier proofs naturally use fewer of them.

Only the new Lean module and this report are deliverables. The branch was clean
at the recorded base. The supplied worker branch is retained, as required by the
specific contract. Existing Lean files, root imports, HANDOFF, the task, frozen
contracts, and ledgers are unchanged. The specific two-file scope takes priority
over the general HANDOFF editing instruction. This is a worker proof awaiting
independent orchestrator review, not a merge or task-acceptance decision.

## Mathematical read-back

For `E = ClosedSmoothModel 3`, the Hessian is the actual nested Frechet derivative
of the existing heat kernel. No alternative Hessian or assumed analytic estimate
is introduced. The compiled route is:

1. The existing bilinear formula proves
   `Hess (a²) (a • x) = ((a³)⁻¹ * (a²)⁻¹) • Hess 1 x` for `a > 0`.
2. For `0 ≤ α ≤ 2`, the elementary bound
   `r^α * exp(-r²/8) ≤ 8` absorbs the fractional weight. Combining it with the
   landed integrable quadratic Gaussian envelope proves unit-time weighted
   Hessian integrability. Haar dilation transfers integrability to every positive
   time.
3. The Haar Jacobian cancels the factor `(a³)⁻¹`. Taking `a = sqrt t` gives the
   exact equality
   `∫ x, ‖Hess t x‖ * ‖x‖^α = t^(α/2 - 1) * ∫ x, ‖Hess 1 x‖ * ‖x‖^α`.
   The final constant is `max 1 (∫ x, ‖Hess 1 x‖ * ‖x‖^α)`, chosen before time.
4. Taking `α = 0` gives tensor Bochner integrability. Cancellation uses the
   differentiation route, not a Gaussian second-moment assumption:
   `heatSolution t (fun _ => 1) = fun _ => 1`; the landed directional
   differentiation-under-the-integral theorem gives zero evaluated Hessian
   integrals. Continuous-linear-map evaluation commutes with the integrals,
   and translation/reflection invariance gives the full tensor integral zero.

The final theorem preserves `0 < α`, `α < 1`, `0 < t`, `t ≤ 1`, both required
integrability clauses, the specified exponent, and tensor cancellation. Several
auxiliary facts hold on the wider range `0 ≤ α ≤ 2` and all positive times; the
frozen conclusion is not altered. No K2, full Schauder estimate, or Poincare
completion is claimed.

## Verification

The focused command was run on the delivered source, not only on scratch copies.
No root build or root integration audit was run. A subsequent focused `lean -o`
export built this module alone for the independent import probe.

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
exit=0

$ LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/HeatKernelHessianMoments.olean Poincare/Global/HeatKernelHessianMoments.lean
exit=0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HeatKernelHessianMoments.lean
(no output)
exit=1

$ git diff --check
(no output)
exit=0

$ git diff --check 094313e6835e844993f59534cb6d68a496f138fb
(no output)
exit=0

$ git status --short --branch
## worker/heat-kernel-hessian-moments
exit=0

```

Source SHA-256: `ed5b32e3ee8311c21c37864278b763ccc9d7cc08c4d1227c39fb746de2e9500f`.

Exact target and declaration audit input:

```lean
import Poincare.Global.HeatKernelHessianMoments
set_option autoImplicit false
noncomputable section
open MeasureTheory
local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
example :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
    Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := Poincare.HeatKernelHessianMoments.hessian_moments

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HeatKernelHessianMoments
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"DECL {n} internal={n.isInternal} dependencies={axs}"
      for a in axs do
        if a != ``propext && a != ``Classical.choice && a != ``Quot.sound then
          throwError "unexpected internal dependency: {n}: {a}"
      if !n.isInternal then
        count := count + 1
        if axs.size != 3 || !axs.contains ``propext ||
            !axs.contains ``Classical.choice || !axs.contains ``Quot.sound then
          throwError "unexpected dependencies: {n}: {axs}"
  logInfo m!"EXACT_DECLARATION_AUDIT passed={count}"
#print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
#print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
#print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
#print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral
#print axioms Poincare.HeatKernelHessianMoments.integrable_hessian
#print axioms Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero
#print axioms Poincare.HeatKernelHessianMoments.hessian_moments

#print axioms Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-025.lean
DECL Poincare.HeatKernelHessianMoments.hessian_moments internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_5 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_3 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_5 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_2 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_2 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___unexpand_Poincare_ClosedSmoothModel_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_7 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termHess internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_1 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_4 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_6 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_4 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termE internal=true dependencies=[]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termE_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_1 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termHess_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_3 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
EXACT_DECLARATION_AUDIT passed=11
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

## Commits

Each theorem was committed after its source compiled and its dependency probe passed.

```text
44fd9d35 Prove full heat Hessian dilation in dimension three
674093ce Bound fractional radial weights by a Gaussian
6e109fd3 Prove fractional weighted Hessian integrability at unit time
b8402417 Prove pointwise weighted Hessian dilation
46398a77 Prove exact weighted Hessian integral dilation
130d7e12 Transfer weighted Hessian integrability to positive times
ea728c1f Prove exact positive-time weighted Hessian moment scaling
b05c4595 Prove Bochner integrability of the full heat Hessian
9549803e Prove cancellation of the full heat Hessian tensor integral
5673d7c8 Prove the exact K1 heat kernel Hessian moments theorem
ad58be14 Disable implicit variables and format the verified Hessian proof
```

## Symbol search evidence

The following recorded `rg` inventory consolidates the source locations used during the probes. `integral_sub_left_eq_self` is generated by `to_additive` from `integral_div_left_eq_self` in `MeasureTheory/Group/Integral.lean:162-166`; the final proof also checks the generated name directly. Named argument `E` must be escaped as `«E»` because the local notation reserves its token.

```text
$ rg -n ^.*\b(theorem|lemma|def|abbrev)\s+(?:[A-Za-z_][A-Za-z_0-9]*\.)*(?:ClosedSmoothModel|heatKernel|iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination|iteratedFDeriv_two_apply|heatKernel_sq_smul|finrank_euclideanSpace_fin|rpow_le_one|rpow_le_rpow_of_exponent_le|rpow_two|add_one_le_exp|exp_add|exp_pos|norm_of_nonneg|continuous_rpow_const|integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq|mul_bdd|contDiff_heatKernel_spatial|fderiv_right|norm_fderiv_fderiv_heatKernel_le_order_two|heatKernel_nonneg|rpow_nonneg|norm_smul_of_nonneg|mul_rpow|integral_comp_smul_of_nonneg|integral_const_mul|sqrt_pos|sq_sqrt|integrable_comp_smul_iff|sqrt_eq_rpow|rpow_mul|rpow_sub|rpow_one|integrable_norm_iff|heatSolution|heatSolution_apply|integral_heatKernel_eq_one|integral_apply|integrable_comp|heatSolution_fderiv_apply_hasFDerivAt|fderiv_const_apply|hasFDerivAt_const|integrable_smul_fderiv_fderiv_heatKernel_sub_flip|flip_apply|integral_div_left_eq_self)\b Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HeatEnvelopes.lean:46:theorem integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean:408:@[simp] lemma exp_add (a b : M) : exp (a + b) = exp a * exp b := rfl
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:49:@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:97:@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:178:theorem sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x := by rw [sq, mul_self_sqrt h]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:276:theorem sq_sqrt' : √x ^ 2 = max x 0 := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:286:theorem sqrt_pos : 0 < √x ↔ 0 < x :=
Poincare/Global/HeatKernel.lean:27:def heatKernel [FiniteDimensional ℝ E] (t : ℝ) (x : E) : ℝ :=
Poincare/Global/HeatKernel.lean:39:theorem heatKernel_nonneg [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
Poincare/Global/HeatKernel.lean:49:theorem contDiff_heatKernel_spatial [FiniteDimensional ℝ E] (t : ℝ) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean:128:theorem flip_apply (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) (m : M) (n : N) : flip f n m = f m n := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Canonical.lean:539:@[simp] lemma exp_pos : 0 < exp a := by simp [exp]
Poincare/Global/BoundedUniformContinuousHeat.lean:135:theorem heatKernel_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:135:theorem flip_apply (A : BilinForm R M) (x y : M) : flipHom A x y = A y x :=
Poincare/Global/HeatCauchyNext2.lean:66:theorem iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination
Poincare/Global/HeatCauchyNext2.lean:171:theorem norm_fderiv_fderiv_heatKernel_le_order_two {t : ℝ} (ht : 0 < t) (u : E) :
Poincare/Global/HeatCauchyNext2.lean:328:theorem integrable_smul_fderiv_fderiv_heatKernel_sub_flip
Poincare/Global/HeatCauchyNext2.lean:625:theorem heatSolution_fderiv_apply_hasFDerivAt
.lake/packages/mathlib/Mathlib/LinearAlgebra/PerfectPairing/Basic.lean:192:@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl
Poincare/Global/HeatKernelIntegral.lean:61:theorem integral_heatKernel_eq_one {t : ℝ} (ht : 0 < t) :
Poincare/Global/HeatKernelIntegral.lean:87:def heatSolution (t : ℝ) (f : E → ℝ) : E → ℝ :=
Poincare/Global/HeatKernelIntegral.lean:93:theorem heatSolution_apply (t : ℝ) (f : E → ℝ) (x : E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean:663:theorem exp_add {x y : 𝔸} : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Instances.lean:197:theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Real.lean:62:theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:156:theorem flip_apply (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:629:theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : K)‖ = r :=
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:866:lemma norm_of_nonneg' {x : K} (hx : 0 ≤ x) : ‖x‖ = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/ERealExp.lean:109:lemma exp_add (x y : EReal) : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/Data/Nat/Sqrt.lean:158:lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:412:lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:434:lemma rpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:637:lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:648:lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:204:theorem finrank_euclideanSpace_fin {n : ℕ} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:298:theorem integral_const_mul {L : Type*} [RCLike L] (r : L) (f : α → L) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:72:theorem integral_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {φ : X → H →L[𝕜] E}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:82:theorem _root_.ContinuousMultilinearMap.integral_apply {ι : Type*} [Fintype ι] {M : ι → Type*}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:138:lemma ContinuousMap.integral_apply [NormedSpace ℝ E] [CompleteSpace E] {f : X → C(Y, E)}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:146:theorem ContinuousMapZero.integral_apply {R : Type*} [NormedCommRing R] [Zero Y]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean:45:theorem norm_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CircleIntegral.lean:478:theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:807:theorem integral_const_mul [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:148:theorem rpow_one (x : ℝ) : x ^ (1 : ℝ) = x := by simp [rpow_def]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:163:theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:262:theorem rpow_sub {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:265:theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:412:theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:468:theorem rpow_two (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:476:theorem mul_rpow (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:613:theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:664:theorem rpow_le_one {x z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988:theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:71:theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:140:theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:157:theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:160:theorem rpow_sub' (h : y - z ≠ 0) (x : ℝ≥0) : x ^ (y - z) = x ^ y / x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:185:theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:195:theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:197:theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:334:@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:360:theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:560:theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:664:theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:669:theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:701:theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:841:@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:897:theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:228:theorem continuous_rpow_const {q : ℝ} (h : 0 ≤ q) : Continuous (fun x : ℝ => x ^ q) :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:422:theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : Continuous fun x : ℝ≥0 => x ^ y :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean:468:theorem continuous_rpow_const {y : ℝ} : Continuous fun a : ℝ≥0∞ => a ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:940:lemma iteratedFDeriv_two_apply (f : E → F) (z : E) (m : Fin 2 → E) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:724:theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean:750:theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 ≤ n) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:114:theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:216:theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Circle.lean:128:theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:114:theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:174:theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:230:theorem integrable_comp (g : F' → A) : Integrable (g ∘ f) ↔ Integrable g :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Basic.lean:461:theorem norm_of_nonneg' {x : ℂ} (hx : 0 ≤ x) : ‖x‖ = x := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:107:theorem exp_add : exp (x + y) = exp x * exp y := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:207:nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:280:theorem exp_pos (x : ℝ) : 0 < exp x :=
.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean:646:theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x := by
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:106:protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:381:theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ → ε} {f : α → δ}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:616:theorem integrable_norm_iff {f : α → β} (hf : AEStronglyMeasurable f μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1070:theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ)
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1190:theorem ContinuousLinearMap.integrable_comp {φ : α → H} (L : H →SL[σ] E) (φ_int : Integrable φ μ) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Integral.lean:163:theorem integral_div_left_eq_self (f : G → E) (μ : Measure G) [IsInvInvariant μ]
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:185:theorem exp_add' (dp : ℕ → A → A)
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/Basic.lean:193:theorem exp_add (hI : DividedPowers I) (ha : a ∈ I) (hb : b ∈ I) :
exit=0
```

## Compiler probe history

Every compiler probe is preserved below with actual output. Scratch sources and logs also remain under `/tmp/heat-kernel-hessian-moments`. Inputs are preserved as a first full snapshot and successive unified differences. Trailing spaces are trimmed in Markdown excerpts; unmodified compiler output remains in the scratch logs. Probes 001-006 invoked the original paths shown in their logs; subsequent probes invoked the numbered snapshots, adding dependency commands without modifying the deliverable. Failed elaborations can report compiler-inserted error terms in dependency output; none is accepted as a verified result.

### probe-001

Input:

```lean
import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Poincare.HeatKernelHessianMoments

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

/-- Dilation of the full spatial Hessian in dimension three. -/
theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Hess (a ^ 2) (a • x) = (a ^ 3)⁻¹ * (a ^ 2)⁻¹ • Hess 1 x := by
  ext v w
  have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
  simp only [iteratedFDeriv_two_apply] at hformula
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
    heatKernel_sq_smul a ha x]
  simp only [inner_smul_left, conj_trivial, Module.finrank_euclideanSpace]
  field_simp
  <;> ring

end Poincare.HeatKernelHessianMoments
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:12:22: error: Unknown identifier `Poincare.ClosedSmoothModel` at quotation precheck

Note: You can use `set_option quotPrecheck false` to disable this check.
Poincare/Global/HeatKernelHessianMoments.lean:13:37: error: elaboration function for `_private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termE` has not been implemented
  E
Poincare/Global/HeatKernelHessianMoments.lean:18:50: error: elaboration function for `_private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termE` has not been implemented
  E

exit=1
```

### probe-002

Input change from previous probe:

```diff
--- previous
+++ probe-002.lean
@@ -1,5 +1,6 @@
 import Poincare.Global.HeatCauchyNext2
 import Poincare.Global.HeatSemigroupBUCPositiveGenerator
+import Poincare.Global.CompactCoefficientEllipticity
 import Mathlib.Analysis.SpecificLimits.Normed

 noncomputable section
@@ -24,7 +25,7 @@
   simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
   rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
     heatKernel_sq_smul a ha x]
-  simp only [inner_smul_left, conj_trivial, Module.finrank_euclideanSpace]
+  simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
   field_simp
   <;> ring

```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:20:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) ?m.93

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

exit=1
```

### probe-003

Input change from previous probe:

```diff
--- previous
+++ probe-003.lean
@@ -1,6 +1,6 @@
 import Poincare.Global.HeatCauchyNext2
 import Poincare.Global.HeatSemigroupBUCPositiveGenerator
-import Poincare.Global.CompactCoefficientEllipticity
+import Poincare.Global.RiemannianContext
 import Mathlib.Analysis.SpecificLimits.Normed

 noncomputable section
@@ -17,7 +17,7 @@

 /-- Dilation of the full spatial Hessian in dimension three. -/
 theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
-    Hess (a ^ 2) (a • x) = (a ^ 3)⁻¹ * (a ^ 2)⁻¹ • Hess 1 x := by
+    Hess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • Hess 1 x := by
   ext v w
   have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
     iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:26:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ((fderiv ℝ (fderiv ℝ fun z => heatKernel (a ^ ?m.171) z) ?u) (![v, w] 0)) (![v, w] 1)
in the target expression
  ((fderiv ℝ (fderiv ℝ fun z => heatKernel (a ^ 2) z) (a • x)) v) w =
    (a ^ 3)⁻¹ * (a ^ 2)⁻¹ * ((fderiv ℝ (fderiv ℝ fun z => heatKernel 1 z) x) v) w

case h.h
a : ℝ
ha : 0 < a
x v w : E
hformula :
  ∀ (t : ℝ),
    t ≠ 0 →
      ∀ (u : E),
        ((fderiv ℝ (fderiv ℝ fun z => heatKernel t z) u) (![v, w] 0)) (![v, w] 1) =
          heatKernel t u * (⟪u, v⟫ * ⟪u, w⟫ / (4 * t ^ 2) - ⟪v, w⟫ / (2 * t))
⊢ ((fderiv ℝ (fderiv ℝ fun z => heatKernel (a ^ 2) z) (a • x)) v) w =
    (a ^ 3)⁻¹ * (a ^ 2)⁻¹ * ((fderiv ℝ (fderiv ℝ fun z => heatKernel 1 z) x) v) w

exit=1
```

### probe-004

Input change from previous probe:

```diff
--- previous
+++ probe-004.lean
@@ -21,7 +21,7 @@
   ext v w
   have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
     iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
-  simp only [iteratedFDeriv_two_apply] at hformula
+  simp [iteratedFDeriv_two_apply] at hformula
   simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
   rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
     heatKernel_sq_smul a ha x]
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:30:6: warning: 'ring' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
Poincare/Global/HeatKernelHessianMoments.lean:30:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`

exit=0
```

### probe-005

Input change from previous probe:

```diff
--- previous
+++ probe-005.lean
@@ -27,6 +27,7 @@
     heatKernel_sq_smul a ha x]
   simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
   field_simp
-  <;> ring

 end Poincare.HeatKernelHessianMoments
+
+#print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/Audit.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-006

Input change from previous probe:

```diff
--- previous
+++ probe-006.lean
@@ -28,6 +28,22 @@
   simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
   field_simp

+/-- A fractional radial weight is absorbed by a fixed Gaussian. -/
+theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
+    {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
+  have hpoly : r ^ α ≤ 1 + r ^ 2 := by
+    by_cases hr1 : r ≤ 1
+    · exact (Real.rpow_le_one hr hr1 hα).trans (by positivity)
+    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
+      rw [Real.rpow_two] at h
+      linarith
+  have hbound : 1 + r ^ 2 ≤ 8 * Real.exp (r ^ 2 / 8) := by
+    have h := Real.add_one_le_exp (r ^ 2 / 8)
+    linarith
+  calc
+    r ^ α * Real.exp (-(r ^ 2 / 8)) ≤
+        (8 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2 / 8)) :=
+      mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
+    _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp
+
 end Poincare.HeatKernelHessianMoments
-
-#print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HeatKernelHessianMoments.lean
Poincare/Global/HeatKernelHessianMoments.lean:36:51: error: not a positivity goal

exit=1
```

### probe-007

Input change from previous probe:

```diff
--- previous
+++ probe-007.lean
@@ -47,3 +47,6 @@
     _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp

 end Poincare.HeatKernelHessianMoments
+
+#print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
+#print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-007.lean
/tmp/heat-kernel-hessian-moments/probe-007.lean:36:51: error: not a positivity goal
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-008

Input change from previous probe:

```diff
--- previous
+++ probe-008.lean
@@ -33,7 +33,7 @@
     {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
   have hpoly : r ^ α ≤ 1 + r ^ 2 := by
     by_cases hr1 : r ≤ 1
-    · exact (Real.rpow_le_one hr hr1 hα).trans (by positivity)
+    · exact (Real.rpow_le_one hr hr1 hα).trans (by nlinarith [sq_nonneg r])
     · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
       rw [Real.rpow_two] at h
       linarith
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-008.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### probe-009

Input change from previous probe:

```diff
--- previous
+++ probe-009.lean
@@ -46,7 +46,50 @@
       mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
     _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp

+/-- The weighted Hessian norm is integrable at unit time. -/
+theorem integrable_weighted_hessian_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
+    Integrable (fun x : E => ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
+  have hc : 0 ≤ c := by dsimp [c]; positivity
+  have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
+    ((Real.continuous_rpow_const hα).comp continuous_norm).mul
+      (((continuous_norm.pow 2).div_const 8).neg.rexp)
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
+    (E := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+      hweight.aestronglyMeasurable
+      (Filter.Eventually.of_forall fun x => show
+        ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
+          rw [Real.norm_of_nonneg (by positivity)]
+          exact rpow_mul_gaussian_le_eight hα hα2 (norm_nonneg x))
+  have hcont : ContDiff ℝ 0 (Hess 1) :=
+    ((contDiff_heatKernel_spatial (E := E) 1).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  refine (hbound.const_mul c).mono'
+    (hcont.continuous.norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
+  refine Filter.Eventually.of_forall fun x => ?_
+  rw [Real.norm_of_nonneg (by positivity)]
+  have hH := norm_fderiv_fderiv_heatKernel_le_order_two (E := E) zero_lt_one x
+  have hK : heatKernel (1 : ℝ) x =
+      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
+    rw [← Real.exp_add]
+    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
+      Nat.cast_ofNat, mul_one]
+    congr 1
+    congr 1
+    ring
+  calc
+    ‖Hess 1 x‖ * ‖x‖ ^ α ≤
+        (heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))) * ‖x‖ ^ α :=
+      mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg x) α)
+    _ ≤ (heatKernel 1 x * (1 + ‖x‖ ^ 2)) * ‖x‖ ^ α := by
+      gcongr
+      nlinarith [sq_nonneg ‖x‖]
+    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
+        (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
+#print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-009.lean
/tmp/heat-kernel-hessian-moments/probe-009.lean:58:6: error: unexpected token ':='; expected ')', ',' or ':'
/tmp/heat-kernel-hessian-moments/probe-009.lean:58:4: error: Application type mismatch: The argument
  E
has type
  Type
of sort `Type 1` but is expected to have type
  0 < ?m.195
of sort `Prop` in the application
  integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq E
/tmp/heat-kernel-hessian-moments/probe-009.lean:51:54: error: unsolved goals
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hweight : Continuous fun x => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))
⊢ Integrable (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α) volume
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-010

Input change from previous probe:

```diff
--- previous
+++ probe-010.lean
@@ -54,8 +54,7 @@
   have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
     ((Real.continuous_rpow_const hα).comp continuous_norm).mul
       (((continuous_norm.pow 2).div_const 8).neg.rexp)
-  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
-    (E := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
       hweight.aestronglyMeasurable
       (Filter.Eventually.of_forall fun x => show
         ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-010.lean
/tmp/heat-kernel-hessian-moments/probe-010.lean:57:71: error: unexpected token ':='; expected ')', ',' or ':'
/tmp/heat-kernel-hessian-moments/probe-010.lean:57:69: error: Application type mismatch: The argument
  E
has type
  Type
of sort `Type 1` but is expected to have type
  0 < ?m.195
of sort `Prop` in the application
  integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq E
/tmp/heat-kernel-hessian-moments/probe-010.lean:51:54: error: unsolved goals
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hweight : Continuous fun x => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))
⊢ Integrable (fun x => ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α) volume
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-011

Input change from previous probe:

```diff
--- previous
+++ probe-011.lean
@@ -54,21 +54,21 @@
   have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
     ((Real.continuous_rpow_const hα).comp continuous_norm).mul
       (((continuous_norm.pow 2).div_const 8).neg.rexp)
-  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
       hweight.aestronglyMeasurable
       (Filter.Eventually.of_forall fun x => show
         ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
           rw [Real.norm_of_nonneg (by positivity)]
           exact rpow_mul_gaussian_le_eight hα hα2 (norm_nonneg x))
   have hcont : ContDiff ℝ 0 (Hess 1) :=
-    ((contDiff_heatKernel_spatial (E := E) 1).fderiv_right
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
       (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
   refine (hbound.const_mul c).mono'
     (hcont.continuous.norm.mul
       ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
   refine Filter.Eventually.of_forall fun x => ?_
   rw [Real.norm_of_nonneg (by positivity)]
-  have hH := norm_fderiv_fderiv_heatKernel_le_order_two (E := E) zero_lt_one x
+  have hH := norm_fderiv_fderiv_heatKernel_le_order_two («E» := E) zero_lt_one x
   have hK : heatKernel (1 : ℝ) x =
       c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
     rw [← Real.exp_add]
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-011.lean
/tmp/heat-kernel-hessian-moments/probe-011.lean:86:6: error: linarith failed to find a contradiction
case hbc.ha.h
α : ℝ
hα : 0 ≤ α
hα2 : α ≤ 2
c : ℝ := (4 * Real.pi) ^ (-3 / 2)
hc : 0 ≤ c
hweight : Continuous fun x => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))
hbound :
  Integrable (fun x => (1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8) * ‖x‖ ^ 2) * (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) volume
hcont : ContDiff ℝ 0 ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1)
x : E
hH : ‖fderiv ℝ (fderiv ℝ fun z => heatKernel 1 z) x‖ ≤ heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))
hK : heatKernel 1 x = c * (Real.exp (-(1 / 8) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8)))
a✝ : heatKernel 1 x < 0
⊢ False
failed
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-012

Input change from previous probe:

```diff
--- previous
+++ probe-012.lean
@@ -82,7 +82,8 @@
         (heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))) * ‖x‖ ^ α :=
       mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg x) α)
     _ ≤ (heatKernel 1 x * (1 + ‖x‖ ^ 2)) * ‖x‖ ^ α := by
-      gcongr
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
+      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
       nlinarith [sq_nonneg ‖x‖]
     _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
         (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-012.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### probe-013

Input change from previous probe:

```diff
--- previous
+++ probe-013.lean
@@ -88,8 +88,17 @@
     _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
         (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring

+/-- Pointwise parabolic dilation including the radial weight. -/
+theorem weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
+    ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
+      ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  rw [hessian_sq_smul a ha x, norm_smul_of_nonneg (by positivity),
+    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
+  ring
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
+#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-013.lean
/tmp/heat-kernel-hessian-moments/probe-013.lean:96:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ‖a • ?x‖
in the target expression
  ‖((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * (a * ‖x‖) ^ α =
    (a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α * (‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α)

a : ℝ
ha : 0 < a
α : ℝ
x : E
⊢ ‖((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • (fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * (a * ‖x‖) ^ α =
    (a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α * (‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α)
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-014

Input change from previous probe:

```diff
--- previous
+++ probe-014.lean
@@ -92,7 +92,7 @@
 theorem weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
     ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
       ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (‖Hess 1 x‖ * ‖x‖ ^ α) := by
-  rw [hessian_sq_smul a ha x, norm_smul_of_nonneg (by positivity),
+  rw [hessian_sq_smul a ha x, norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 2)⁻¹ by positivity) (Hess 1 x),
     norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
   ring

```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-014.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-015

Input change from previous probe:

```diff
--- previous
+++ probe-015.lean
@@ -96,9 +96,26 @@
     norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
   ring

+/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
+theorem weighted_hessian_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
+    (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
+      ((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Hess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
+        ∫ x : E, ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+      simp_rw [weighted_hessian_sq_smul a ha]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α)) := by ring
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
+#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-015.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### probe-016

Input change from previous probe:

```diff
--- previous
+++ probe-016.lean
@@ -112,6 +112,16 @@
       rw [integral_const_mul]
     _ = (a ^ 3)⁻¹ * (((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α)) := by ring

+/-- Weighted Bochner integrability at every positive time. -/
+theorem integrable_weighted_hessian {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
+    {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) := by
+  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
+  rw [← Real.sq_sqrt ht.le]
+  apply (integrable_comp_smul_iff volume _ ha.ne').1
+  simp_rw [weighted_hessian_sq_smul (Real.sqrt t) ha]
+  exact (integrable_weighted_hessian_one hα hα2).const_mul _
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
@@ -119,3 +129,4 @@
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
+#print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-016.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

### probe-017

Input change from previous probe:

```diff
--- previous
+++ probe-017.lean
@@ -122,6 +122,17 @@
   simp_rw [weighted_hessian_sq_smul (Real.sqrt t) ha]
   exact (integrable_weighted_hessian_one hα hα2).const_mul _

+/-- Exact positive-time scaling of the weighted Hessian integral. -/
+theorem weighted_hessian_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
+    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) =
+      t ^ (α / 2 - 1) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  have h := weighted_hessian_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h]
+  congr 1
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
+  congr 1 <;> ring
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
@@ -130,3 +141,4 @@
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
+#print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-017.lean
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
/tmp/heat-kernel-hessian-moments/probe-017.lean:128:59: error: unsolved goals
case e_a.e_a
t : ℝ
ht : 0 < t
α : ℝ
h :
  ∫ (x : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x‖ * ‖x‖ ^ α =
    t⁻¹ * √t ^ α * ∫ (x : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α
⊢ t⁻¹ = t ^ (α * (1 / 2))

case e_a.e_a
t : ℝ
ht : 0 < t
α : ℝ
h :
  ∫ (x : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x‖ * ‖x‖ ^ α =
    t⁻¹ * √t ^ α * ∫ (x : E), ‖(fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) 1 x‖ * ‖x‖ ^ α
⊢ t ^ (α * (1 / 2)) = t⁻¹
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-018

Input change from previous probe:

```diff
--- previous
+++ probe-018.lean
@@ -131,7 +131,8 @@
   rw [h]
   congr 1
   rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
-  congr 1 <;> ring
+  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
+  ring

 end Poincare.HeatKernelHessianMoments

```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-018.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-019

Input change from previous probe:

```diff
--- previous
+++ probe-019.lean
@@ -134,6 +134,15 @@
   rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
   ring

+/-- The full operator-valued Hessian is Bochner integrable. -/
+theorem integrable_hessian {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => Hess t x) := by
+  have hcont : ContDiff ℝ 0 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  apply (integrable_norm_iff hcont.continuous.aestronglyMeasurable).1
+  simpa using integrable_weighted_hessian (α := 0) (by norm_num) (by norm_num) ht
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
@@ -143,3 +152,4 @@
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral
+#print axioms Poincare.HeatKernelHessianMoments.integrable_hessian
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-019.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-020

Input change from previous probe:

```diff
--- previous
+++ probe-020.lean
@@ -143,6 +143,31 @@
   apply (integrable_norm_iff hcont.continuous.aestronglyMeasurable).1
   simpa using integrable_weighted_hessian (α := 0) (by norm_num) (by norm_num) ht

+/-- Tensor cancellation follows by twice differentiating the heat evolution of one. -/
+theorem integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
+    (∫ x : E, Hess t x) = 0 := by
+  have hmass : heatSolution t (fun _ : E => (1 : ℝ)) = fun _ => 1 := by
+    funext x
+    simpa only [heatSolution_apply, mul_one] using
+      (integral_heatKernel_eq_one («E» := E) ht)
+  ext v w
+  rw [ContinuousLinearMap.integral_apply (integrable_hessian ht),
+    ContinuousLinearMap.integral_apply
+      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht))]
+  have hder := heatSolution_fderiv_apply_hasFDerivAt ht
+    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E) w
+  simp only [hmass, fderiv_const_apply, ContinuousLinearMap.zero_apply] at hder
+  have hc := hder.unique (hasFDerivAt_const (0 : ℝ) (0 : E))
+  have hi := integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht
+    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E) w
+  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) hc
+  rw [ContinuousLinearMap.integral_apply hi] at hev
+  simp only [one_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hev ⊢
+  rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
+  exact hev
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
@@ -153,3 +178,4 @@
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral
 #print axioms Poincare.HeatKernelHessianMoments.integrable_hessian
+#print axioms Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-020.lean
/tmp/heat-kernel-hessian-moments/probe-020.lean:155:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (∫ (x : E),
      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v) ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x))
    ?v
in the target expression
  (∫ (x : E), ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) w = (0 v) w

case h.h
t : ℝ
ht : 0 < t
hmass : (heatSolution t fun x => 1) = fun x => 1
v w : E
⊢ (∫ (x : E), ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) w = (0 v) w
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-021

Input change from previous probe:

```diff
--- previous
+++ probe-021.lean
@@ -151,9 +151,10 @@
     simpa only [heatSolution_apply, mul_one] using
       (integral_heatKernel_eq_one («E» := E) ht)
   ext v w
+  have hiv : Integrable (fun x : E => Hess t x v) := by
+    exact (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht)
   rw [ContinuousLinearMap.integral_apply (integrable_hessian ht),
-    ContinuousLinearMap.integral_apply
-      ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht))]
+    ContinuousLinearMap.integral_apply hiv]
   have hder := heatSolution_fderiv_apply_hasFDerivAt ht
     (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
     (C := 1) (by intro y; simp) (0 : E) w
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-021.lean
/tmp/heat-kernel-hessian-moments/probe-021.lean:167:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (∫ (x : E), (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - x)).flip w) ?v
in the target expression
  (fun L => L v) (∫ (y : E), (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - y)).flip w) = (fun L => L v) 0

case h.h
t : ℝ
ht : 0 < t
hmass : (heatSolution t fun x => 1) = fun x => 1
v w : E
hiv : Integrable (fun x => ((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) volume
hder : HasFDerivAt (fun z => 0) (∫ (y : E), (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - y)).flip w) 0
hc : ∫ (y : E), (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - y)).flip w = 0
hi : Integrable (fun y => (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - y)).flip w) volume
hev : (fun L => L v) (∫ (y : E), (1 • fderiv ℝ (fderiv ℝ fun u => heatKernel t u) (0 - y)).flip w) = (fun L => L v) 0
⊢ ∫ (x : E), (((fun t x => fderiv ℝ (fderiv ℝ fun z => heatKernel t z) x) t x) v) w = (0 v) w
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

exit=1
```

### probe-022

Input change from previous probe:

```diff
--- previous
+++ probe-022.lean
@@ -164,6 +164,7 @@
     (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
     (C := 1) (by intro y; simp) (0 : E) w
   have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) hc
+  dsimp only at hev
   rw [ContinuousLinearMap.integral_apply hi] at hev
   simp only [one_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hev ⊢
   rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-022.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-023

Input change from previous probe:

```diff
--- previous
+++ probe-023.lean
@@ -170,6 +170,22 @@
   rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
   exact hev

+/-- Sharp weighted Hessian moments and tensor cancellation for the heat kernel. -/
+theorem hessian_moments :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
+      Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
+      (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
+      Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := by
+  intro α hα hα1
+  refine ⟨max 1 (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t ht _
+  refine ⟨integrable_weighted_hessian hα.le (by linarith) ht, ?_,
+    integrable_hessian ht, integral_hessian_eq_zero ht⟩
+  rw [weighted_hessian_integral ht, mul_comm (t ^ (α / 2 - 1))]
+  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
+
 end Poincare.HeatKernelHessianMoments

 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
@@ -181,3 +197,4 @@
 #print axioms Poincare.HeatKernelHessianMoments.weighted_hessian_integral
 #print axioms Poincare.HeatKernelHessianMoments.integrable_hessian
 #print axioms Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero
+#print axioms Poincare.HeatKernelHessianMoments.hessian_moments
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-023.lean
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_moments' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-024

Input change from previous probe:

```diff
--- previous
+++ probe-024.lean
@@ -1,193 +1,34 @@
-import Poincare.Global.HeatCauchyNext2
-import Poincare.Global.HeatSemigroupBUCPositiveGenerator
-import Poincare.Global.RiemannianContext
-import Mathlib.Analysis.SpecificLimits.Normed
-
+import Poincare.Global.HeatKernelHessianMoments
+set_option autoImplicit false
 noncomputable section
-
 open MeasureTheory
-open scoped Topology RealInnerProductSpace
-
-namespace Poincare.HeatKernelHessianMoments
-
 local notation "E" => Poincare.ClosedSmoothModel 3
 local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
 local notation "Hess" => fun (t : ℝ) (x : E) =>
   fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+example :
+  ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
+    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
+    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
+    Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := Poincare.HeatKernelHessianMoments.hessian_moments

-/-- Dilation of the full spatial Hessian in dimension three. -/
-theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
-    Hess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • Hess 1 x := by
-  ext v w
-  have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
-    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
-  simp [iteratedFDeriv_two_apply] at hformula
-  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
-  rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
-    heatKernel_sq_smul a ha x]
-  simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
-  field_simp
-
-/-- A fractional radial weight is absorbed by a fixed Gaussian. -/
-theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
-    {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
-  have hpoly : r ^ α ≤ 1 + r ^ 2 := by
-    by_cases hr1 : r ≤ 1
-    · exact (Real.rpow_le_one hr hr1 hα).trans (by nlinarith [sq_nonneg r])
-    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
-      rw [Real.rpow_two] at h
-      linarith
-  have hbound : 1 + r ^ 2 ≤ 8 * Real.exp (r ^ 2 / 8) := by
-    have h := Real.add_one_le_exp (r ^ 2 / 8)
-    linarith
-  calc
-    r ^ α * Real.exp (-(r ^ 2 / 8)) ≤
-        (8 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2 / 8)) :=
-      mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
-    _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp
-
-/-- The weighted Hessian norm is integrable at unit time. -/
-theorem integrable_weighted_hessian_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
-    Integrable (fun x : E => ‖Hess 1 x‖ * ‖x‖ ^ α) := by
-  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
-  have hc : 0 ≤ c := by dsimp [c]; positivity
-  have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
-    ((Real.continuous_rpow_const hα).comp continuous_norm).mul
-      (((continuous_norm.pow 2).div_const 8).neg.rexp)
-  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
-      hweight.aestronglyMeasurable
-      (Filter.Eventually.of_forall fun x => show
-        ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
-          rw [Real.norm_of_nonneg (by positivity)]
-          exact rpow_mul_gaussian_le_eight hα hα2 (norm_nonneg x))
-  have hcont : ContDiff ℝ 0 (Hess 1) :=
-    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
-      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
-  refine (hbound.const_mul c).mono'
-    (hcont.continuous.norm.mul
-      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
-  refine Filter.Eventually.of_forall fun x => ?_
-  rw [Real.norm_of_nonneg (by positivity)]
-  have hH := norm_fderiv_fderiv_heatKernel_le_order_two («E» := E) zero_lt_one x
-  have hK : heatKernel (1 : ℝ) x =
-      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
-    rw [← Real.exp_add]
-    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
-      Nat.cast_ofNat, mul_one]
-    congr 1
-    congr 1
-    ring
-  calc
-    ‖Hess 1 x‖ * ‖x‖ ^ α ≤
-        (heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))) * ‖x‖ ^ α :=
-      mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg x) α)
-    _ ≤ (heatKernel 1 x * (1 + ‖x‖ ^ 2)) * ‖x‖ ^ α := by
-      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
-      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
-      nlinarith [sq_nonneg ‖x‖]
-    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
-        (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring
-
-/-- Pointwise parabolic dilation including the radial weight. -/
-theorem weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
-    ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
-      ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (‖Hess 1 x‖ * ‖x‖ ^ α) := by
-  rw [hessian_sq_smul a ha x, norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 2)⁻¹ by positivity) (Hess 1 x),
-    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
-  ring
-
-/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
-theorem weighted_hessian_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
-    (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
-      ((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
-  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
-    (fun y : E => ‖Hess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
-  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
-  calc
-    (a ^ 3)⁻¹ * (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
-        ∫ x : E, ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
-      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
-    _ = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
-      simp_rw [weighted_hessian_sq_smul a ha]
-      rw [integral_const_mul]
-    _ = (a ^ 3)⁻¹ * (((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α)) := by ring
-
-/-- Weighted Bochner integrability at every positive time. -/
-theorem integrable_weighted_hessian {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
-    {t : ℝ} (ht : 0 < t) :
-    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) := by
-  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
-  rw [← Real.sq_sqrt ht.le]
-  apply (integrable_comp_smul_iff volume _ ha.ne').1
-  simp_rw [weighted_hessian_sq_smul (Real.sqrt t) ha]
-  exact (integrable_weighted_hessian_one hα hα2).const_mul _
-
-/-- Exact positive-time scaling of the weighted Hessian integral. -/
-theorem weighted_hessian_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
-    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) =
-      t ^ (α / 2 - 1) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
-  have h := weighted_hessian_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
-  rw [Real.sq_sqrt ht.le] at h
-  rw [h]
-  congr 1
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
-  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
-  ring
-
-/-- The full operator-valued Hessian is Bochner integrable. -/
-theorem integrable_hessian {t : ℝ} (ht : 0 < t) :
-    Integrable (fun x : E => Hess t x) := by
-  have hcont : ContDiff ℝ 0 (Hess t) :=
-    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
-      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
-  apply (integrable_norm_iff hcont.continuous.aestronglyMeasurable).1
-  simpa using integrable_weighted_hessian (α := 0) (by norm_num) (by norm_num) ht
-
-/-- Tensor cancellation follows by twice differentiating the heat evolution of one. -/
-theorem integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
-    (∫ x : E, Hess t x) = 0 := by
-  have hmass : heatSolution t (fun _ : E => (1 : ℝ)) = fun _ => 1 := by
-    funext x
-    simpa only [heatSolution_apply, mul_one] using
-      (integral_heatKernel_eq_one («E» := E) ht)
-  ext v w
-  have hiv : Integrable (fun x : E => Hess t x v) := by
-    exact (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht)
-  rw [ContinuousLinearMap.integral_apply (integrable_hessian ht),
-    ContinuousLinearMap.integral_apply hiv]
-  have hder := heatSolution_fderiv_apply_hasFDerivAt ht
-    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
-    (C := 1) (by intro y; simp) (0 : E) w
-  simp only [hmass, fderiv_const_apply, ContinuousLinearMap.zero_apply] at hder
-  have hc := hder.unique (hasFDerivAt_const (0 : ℝ) (0 : E))
-  have hi := integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht
-    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
-    (C := 1) (by intro y; simp) (0 : E) w
-  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) hc
-  dsimp only at hev
-  rw [ContinuousLinearMap.integral_apply hi] at hev
-  simp only [one_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hev ⊢
-  rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
-  exact hev
-
-/-- Sharp weighted Hessian moments and tensor cancellation for the heat kernel. -/
-theorem hessian_moments :
-    ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
-      Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
-      (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
-      Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := by
-  intro α hα hα1
-  refine ⟨max 1 (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α),
-    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
-  intro t ht _
-  refine ⟨integrable_weighted_hessian hα.le (by linarith) ht, ?_,
-    integrable_hessian ht, integral_hessian_eq_zero ht⟩
-  rw [weighted_hessian_integral ht, mul_comm (t ^ (α / 2 - 1))]
-  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
-
-end Poincare.HeatKernelHessianMoments
-
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.HeatKernelHessianMoments
+    | throwError "module not found"
+  let mut count := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      logInfo m!"DECL {n} internal={n.isInternal} dependencies={axs}"
+      if !n.isInternal then
+        count := count + 1
+        if axs.size != 3 || !axs.contains ``propext ||
+            !axs.contains ``Classical.choice || !axs.contains ``Quot.sound then
+          throwError "unexpected dependencies: {n}: {axs}"
+  logInfo m!"EXACT_DECLARATION_AUDIT passed={count}"
 #print axioms Poincare.HeatKernelHessianMoments.hessian_sq_smul
 #print axioms Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight
 #print axioms Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-024.lean
DECL Poincare.HeatKernelHessianMoments.hessian_moments internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_5 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_3 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_5 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_2 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_2 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___unexpand_Poincare_ClosedSmoothModel_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_7 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termHess internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_1 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_4 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_6 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_4 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termE internal=true dependencies=[]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termE_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_1 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termHess_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_3 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
EXACT_DECLARATION_AUDIT passed=11
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_moments' depends on axioms: [propext, Classical.choice, Quot.sound]

exit=0
```

### probe-025

Input change from previous probe:

```diff
--- previous
+++ probe-025.lean
@@ -23,6 +23,9 @@
     if env.getModuleIdxFor? n == some idx then
       let axs ← liftCoreM (collectAxioms n)
       logInfo m!"DECL {n} internal={n.isInternal} dependencies={axs}"
+      for a in axs do
+        if a != ``propext && a != ``Classical.choice && a != ``Quot.sound then
+          throwError "unexpected internal dependency: {n}: {a}"
       if !n.isInternal then
         count := count + 1
         if axs.size != 3 || !axs.contains ``propext ||
@@ -39,3 +42,5 @@
 #print axioms Poincare.HeatKernelHessianMoments.integrable_hessian
 #print axioms Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero
 #print axioms Poincare.HeatKernelHessianMoments.hessian_moments
+
+#print axioms Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat
```

Actual output:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/heat-kernel-hessian-moments/probe-025.lean
DECL Poincare.HeatKernelHessianMoments.hessian_moments internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_5 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_3 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_5 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_2 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_2 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___unexpand_Poincare_ClosedSmoothModel_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_7 internal=true dependencies=[propext]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termHess internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_1 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_4 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_6 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_4 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments.termE internal=true dependencies=[]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termE_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_integral internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat._proof_1 internal=true dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL _private.Poincare.Global.HeatKernelHessianMoments.0.Poincare.HeatKernelHessianMoments._aux_Poincare_Global_HeatKernelHessianMoments___macroRules__private_Poincare_Global_HeatKernelHessianMoments_0_Poincare_HeatKernelHessianMoments_termHess_1 internal=true dependencies=[]
DECL Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
DECL Poincare.HeatKernelHessianMoments.hessian_sq_smul._simp_1_3 internal=true dependencies=[propext]
DECL Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat internal=false dependencies=[propext,
 Classical.choice,
 Quot.sound]
EXACT_DECLARATION_AUDIT passed=11
'Poincare.HeatKernelHessianMoments.hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.rpow_mul_gaussian_le_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_sq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_weighted_hessian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HeatKernelHessianMoments.weighted_hessian_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integrable_hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.integral_hessian_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.hessian_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.HeatKernelHessianMoments.instNormedAddCommGroupContinuousLinearMapRealIdClosedSmoothModelOfNatNat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

exit=0
```

## Final proof diff

```diff
diff --git a/Poincare/Global/HeatKernelHessianMoments.lean b/Poincare/Global/HeatKernelHessianMoments.lean
new file mode 100644
index 00000000..52291858
--- /dev/null
+++ b/Poincare/Global/HeatKernelHessianMoments.lean
@@ -0,0 +1,193 @@
+import Poincare.Global.HeatCauchyNext2
+import Poincare.Global.HeatSemigroupBUCPositiveGenerator
+import Poincare.Global.RiemannianContext
+import Mathlib.Analysis.SpecificLimits.Normed
+
+set_option autoImplicit false
+
+noncomputable section
+
+open MeasureTheory
+open scoped Topology RealInnerProductSpace
+
+namespace Poincare.HeatKernelHessianMoments
+
+local notation "E" => Poincare.ClosedSmoothModel 3
+local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+local notation "Hess" => fun (t : ℝ) (x : E) =>
+  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x
+
+/-- Dilation of the full spatial Hessian in dimension three. -/
+theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
+    Hess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • Hess 1 x := by
+  ext v w
+  have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
+    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
+  simp [iteratedFDeriv_two_apply] at hformula
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
+  rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
+    heatKernel_sq_smul a ha x]
+  simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
+  field_simp
+
+/-- A fractional radial weight is absorbed by a fixed Gaussian. -/
+theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
+    {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
+  have hpoly : r ^ α ≤ 1 + r ^ 2 := by
+    by_cases hr1 : r ≤ 1
+    · exact (Real.rpow_le_one hr hr1 hα).trans (by nlinarith [sq_nonneg r])
+    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
+      rw [Real.rpow_two] at h
+      linarith
+  have hbound : 1 + r ^ 2 ≤ 8 * Real.exp (r ^ 2 / 8) := by
+    have h := Real.add_one_le_exp (r ^ 2 / 8)
+    linarith
+  calc
+    r ^ α * Real.exp (-(r ^ 2 / 8)) ≤
+        (8 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2 / 8)) :=
+      mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
+    _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp
+
+/-- The weighted Hessian norm is integrable at unit time. -/
+theorem integrable_weighted_hessian_one {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2) :
+    Integrable (fun x : E => ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  let c : ℝ := (4 * Real.pi) ^ (-(3 : ℝ) / 2)
+  have hc : 0 ≤ c := by dsimp [c]; positivity
+  have hweight : Continuous (fun x : E => ‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))) :=
+    ((Real.continuous_rpow_const hα).comp continuous_norm).mul
+      (((continuous_norm.pow 2).div_const 8).neg.rexp)
+  have hbound := (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq
+      («E» := E) (a := (1 / 8 : ℝ)) (by norm_num)).mul_bdd
+      hweight.aestronglyMeasurable
+      (Filter.Eventually.of_forall fun x => show
+        ‖‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8))‖ ≤ 8 from by
+          rw [Real.norm_of_nonneg (by positivity)]
+          exact rpow_mul_gaussian_le_eight hα hα2 (norm_nonneg x))
+  have hcont : ContDiff ℝ 0 (Hess 1) :=
+    ((contDiff_heatKernel_spatial («E» := E) 1).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  refine (hbound.const_mul c).mono'
+    (hcont.continuous.norm.mul
+      ((Real.continuous_rpow_const hα).comp continuous_norm)).aestronglyMeasurable ?_
+  refine Filter.Eventually.of_forall fun x => ?_
+  rw [Real.norm_of_nonneg (by positivity)]
+  have hH := norm_fderiv_fderiv_heatKernel_le_order_two («E» := E) zero_lt_one x
+  have hK : heatKernel (1 : ℝ) x =
+      c * (Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2) * Real.exp (-(‖x‖ ^ 2 / 8))) := by
+    rw [← Real.exp_add]
+    simp only [heatKernel, ClosedSmoothModel, finrank_euclideanSpace_fin,
+      Nat.cast_ofNat, mul_one]
+    congr 1
+    congr 1
+    ring
+  calc
+    ‖Hess 1 x‖ * ‖x‖ ^ α ≤
+        (heatKernel 1 x * (‖x‖ ^ 2 / (4 * 1 ^ 2) + 1 / (2 * 1))) * ‖x‖ ^ α :=
+      mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg (norm_nonneg x) α)
+    _ ≤ (heatKernel 1 x * (1 + ‖x‖ ^ 2)) * ‖x‖ ^ α := by
+      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg x) α)
+      apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg zero_lt_one x)
+      nlinarith [sq_nonneg ‖x‖]
+    _ = c * (((1 + ‖x‖ ^ 2) * Real.exp (-(1 / 8 : ℝ) * ‖x‖ ^ 2)) *
+        (‖x‖ ^ α * Real.exp (-(‖x‖ ^ 2 / 8)))) := by rw [hK]; ring
+
+/-- Pointwise parabolic dilation including the radial weight. -/
+theorem weighted_hessian_sq_smul (a : ℝ) (ha : 0 < a) (α : ℝ) (x : E) :
+    ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α =
+      ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  rw [hessian_sq_smul a ha x,
+    norm_smul_of_nonneg (show 0 ≤ (a ^ 3)⁻¹ * (a ^ 2)⁻¹ by positivity) (Hess 1 x),
+    norm_smul_of_nonneg ha.le, Real.mul_rpow ha.le (norm_nonneg x)]
+  ring
+
+/-- The Jacobian cancels the spatial normalization in the weighted integral. -/
+theorem weighted_hessian_integral_sq (a : ℝ) (ha : 0 < a) (α : ℝ) :
+    (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
+      ((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  have hchange := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
+    (fun y : E => ‖Hess (a ^ 2) y‖ * ‖y‖ ^ α) a (hR := ha.le)
+  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 ha.ne'))
+  calc
+    (a ^ 3)⁻¹ * (∫ x : E, ‖Hess (a ^ 2) x‖ * ‖x‖ ^ α) =
+        ∫ x : E, ‖Hess (a ^ 2) (a • x)‖ * ‖a • x‖ ^ α := by
+      simpa only [ClosedSmoothModel, finrank_euclideanSpace_fin, smul_eq_mul] using hchange.symm
+    _ = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+      simp_rw [weighted_hessian_sq_smul a ha]
+      rw [integral_const_mul]
+    _ = (a ^ 3)⁻¹ * (((a ^ 2)⁻¹ * a ^ α) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α)) := by ring
+
+/-- Weighted Bochner integrability at every positive time. -/
+theorem integrable_weighted_hessian {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
+    {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) := by
+  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
+  rw [← Real.sq_sqrt ht.le]
+  apply (integrable_comp_smul_iff volume _ ha.ne').1
+  simp_rw [weighted_hessian_sq_smul (Real.sqrt t) ha]
+  exact (integrable_weighted_hessian_one hα hα2).const_mul _
+
+/-- Exact positive-time scaling of the weighted Hessian integral. -/
+theorem weighted_hessian_integral {t : ℝ} (ht : 0 < t) (α : ℝ) :
+    (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) =
+      t ^ (α / 2 - 1) * (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α) := by
+  have h := weighted_hessian_integral_sq (Real.sqrt t) (Real.sqrt_pos.2 ht) α
+  rw [Real.sq_sqrt ht.le] at h
+  rw [h]
+  congr 1
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, Real.rpow_sub ht, Real.rpow_one]
+  rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
+  ring
+
+/-- The full operator-valued Hessian is Bochner integrable. -/
+theorem integrable_hessian {t : ℝ} (ht : 0 < t) :
+    Integrable (fun x : E => Hess t x) := by
+  have hcont : ContDiff ℝ 0 (Hess t) :=
+    ((contDiff_heatKernel_spatial («E» := E) t).fderiv_right
+      (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)
+  apply (integrable_norm_iff hcont.continuous.aestronglyMeasurable).1
+  simpa using integrable_weighted_hessian (α := 0) (by norm_num) (by norm_num) ht
+
+/-- Tensor cancellation follows by twice differentiating the heat evolution of one. -/
+theorem integral_hessian_eq_zero {t : ℝ} (ht : 0 < t) :
+    (∫ x : E, Hess t x) = 0 := by
+  have hmass : heatSolution t (fun _ : E => (1 : ℝ)) = fun _ => 1 := by
+    funext x
+    simpa only [heatSolution_apply, mul_one] using
+      (integral_heatKernel_eq_one («E» := E) ht)
+  ext v w
+  have hiv : Integrable (fun x : E => Hess t x v) := by
+    exact (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp (integrable_hessian ht)
+  rw [ContinuousLinearMap.integral_apply (integrable_hessian ht),
+    ContinuousLinearMap.integral_apply hiv]
+  have hder := heatSolution_fderiv_apply_hasFDerivAt ht
+    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E) w
+  simp only [hmass, fderiv_const_apply, ContinuousLinearMap.zero_apply] at hder
+  have hc := hder.unique (hasFDerivAt_const (0 : ℝ) (0 : E))
+  have hi := integrable_smul_fderiv_fderiv_heatKernel_sub_flip ht
+    (f := fun _ : E => (1 : ℝ)) aestronglyMeasurable_const
+    (C := 1) (by intro y; simp) (0 : E) w
+  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) hc
+  dsimp only at hev
+  rw [ContinuousLinearMap.integral_apply hi] at hev
+  simp only [one_smul, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply] at hev ⊢
+  rw [integral_sub_left_eq_self (fun y : E => Hess t y v w) volume (0 : E)] at hev
+  exact hev
+
+/-- Sharp weighted Hessian moments and tensor cancellation for the heat kernel. -/
+theorem hessian_moments :
+    ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
+      Integrable (fun x : E => ‖Hess t x‖ * ‖x‖ ^ α) ∧
+      (∫ x : E, ‖Hess t x‖ * ‖x‖ ^ α) ≤ C * t ^ (α / 2 - 1) ∧
+      Integrable (fun x : E => Hess t x) ∧ (∫ x : E, Hess t x) = 0 := by
+  intro α hα hα1
+  refine ⟨max 1 (∫ x : E, ‖Hess 1 x‖ * ‖x‖ ^ α),
+    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
+  intro t ht _
+  refine ⟨integrable_weighted_hessian hα.le (by linarith) ht, ?_,
+    integrable_hessian ht, integral_hessian_eq_zero ht⟩
+  rw [weighted_hessian_integral ht, mul_comm (t ^ (α / 2 - 1))]
+  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)
+
+end Poincare.HeatKernelHessianMoments
```

## Handoff

First action for the orchestrator:

```sh
git diff 094313e6835e844993f59534cb6d68a496f138fb..ad58be1454636f45f32b5a4198ec1aa5bf770ee6 -- Poincare/Global/HeatKernelHessianMoments.lean
```

Then rerun the focused Lean command and the exact target/dependency audit above in the review checkout. K2 can now be frozen against an independently accepted K1 commit; it has not been attempted here.

## Report formatting check

The first staged check found trailing spaces in quoted unified-diff context lines and compiler suggestions. Those trailing spaces were removed from the Markdown excerpts. The Lean source was unchanged.

```text
$ git diff --cached --check
harness/reports/heat-kernel-hessian-moments_done.md:419: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:429: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:457: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:460: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:540: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:565: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:607: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:668: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:712: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:914: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:924: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:977: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1006: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1024: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1061: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1073: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1114: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1127: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1142: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1144: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1148: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1150: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1206: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1208: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1244: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1255: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1298: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1325: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1493: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1511: trailing whitespace.
+
harness/reports/heat-kernel-hessian-moments_done.md:1578: trailing whitespace.
+
exit=2
```

Final staged checks after report formatting:

```text
$ git diff --cached --check
(no output)
exit=0
$ git diff --check 094313e6835e844993f59534cb6d68a496f138fb
(no output)
exit=0
```
