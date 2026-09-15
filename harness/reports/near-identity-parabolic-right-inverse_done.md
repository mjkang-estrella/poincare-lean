# Near-identity parabolic right inverse: done

Date: 2026-09-15. Worker result awaiting independent review; not merged or accepted.

- Base: `a77fdab525954b5d0e02f31e6fec1ef5745df306`.
- Branch: `worker/near-identity-parabolic-right-inverse`.
- Verified proof head: `4fbea6a4a06473047c96a720c8cca2875c91d614`.
- Task: `harness/tasks/near-identity-parabolic-right-inverse.md`, unchanged.
- Only new Lean source: `Poincare/Global/NearIdentityParabolicRightInverse.lean`.
- Existing Lean sources, root imports, and frozen contracts are unchanged.
- Work was confined to the supplied isolated worktree and the task's one source-file family.

## Result

All four task items are proved. `multiplier` is a continuous linear map for every
coefficient family, with the requested improved bound for positive exponents and
time. `errorOp_small` proves both the one-half bound and strict norm less than one
from the two quarter bounds. The corrected inverse solves the equation on the
closed cylinder, including both endpoints, and its norm is at most twice the
landed constant `DuhamelSolutionOperatorCLM.boundConstant α hα hα1`.

`exists_nearIdentity_solution` takes exactly the coefficient sup/seminorm bounds,
short-cylinder conditions, and quarter-size hypotheses and returns a genuine
zero-initial-trace derivative graph with the requested equation and norm bound.
The coefficient definition is `(if i = j then 1 else 0) + b i j p`, including the
perturbation on the diagonal. The explicit expanded-coefficient type probe passes.

The inverse and equation theorem use the weaker sufficient hypothesis
`‖errorOp b ...‖ < 1`; their norm theorem adds `‖errorOp b ...‖ ≤ 1/2`.
The existence theorem derives both hypotheses from the stated coefficient bounds.
This factors the proof without changing the requested existence conclusion.

## Commits

| Item | Commit |
| --- | --- |
| 1: multiplier linearity and estimate | `25978554` |
| 2: error operator and smallness | `c3acf139` |
| 3: corrected inverse, equation, norm | `046d3e48` |
| 4: existence with graph estimate | `67565c7e` |
| Explicit types for the strict generated-declaration gate | `4fbea6a4` |

## Final gates

- `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean`: exit 0, empty output.
- Forbidden-token `rg`: empty output, exit 1 as expected for no matches.
- Module-wide `#print axioms`: all 29 declarations, including generated proofs and
  congruence lemmas, have exactly `[propext, Classical.choice, Quot.sound]`.
- Expanded-coefficient existence type assignment: exit 0, empty output.
- `git diff --check`: exit 0, empty output.

There are 18 explicit declarations. No root build or integration audit was run;
this is a focused worker result. The full conjecture is not claimed.

## Failed probes and fixes

All recorded compiler diagnostics are retained below. Early shorthand parsing
needed escaped named arguments. A nonexistent `Units.oneSub_val` probe was
abandoned; the proof uses the verified `Units.oneSub` definition and `Units.val_inv`.
The first named-dependency wrapper failed to parse Lean's multiline output after
Lean itself exited 0; its retry normalizes whitespace and passes. One loose
`norm_nonneg _` caused instance search failure. Giving its inverse operator an
explicit type fixed it without increasing heartbeat limits. The token scan caught
a forbidden word used as an ordinary verb in a comment; the comment was rewritten.
Finally, local notation generated parser declarations with an empty dependency
list. Expanding the shorthand removed these declarations, so the literal
module-wide exact-dependency gate now passes without exclusions.

## First action for the reviewer

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean
```

Then rerun the module audit and expanded-coefficient contract probe below against
the recorded base plus the proof commits. The final diff is included verbatim.

## Probe sources

<details>
<summary>context.lean</summary>

```lean
import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.ParametrixNeumannCorrection
#print Poincare.DuhamelSolutionOperatorCLM.boundConstant
#print Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec
#print Poincare.DuhamelSolutionOperatorCLM.duhamelOperator
#print Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le
#print Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves
#print Poincare.ParabolicHolderMultiplier.forcing
#print Poincare.ParabolicHolderMultiplier.forcing_apply
#print Poincare.ParabolicHolderMultiplier.forcing_eq_sum
#print Poincare.ParabolicHolderMultiplier.norm_forcing_le
#print Poincare.ParabolicHolderMultiplier.norm_error_le
#print Poincare.ParabolicHolderMultiplier.error_small
#print Poincare.ParabolicHolderMultiplier.norm_entry_le
#print Poincare.ParabolicHolder.norm_mul_le
#print Poincare.ParabolicHolder.ext
#print Poincare.ParametrixNeumannCorrection.correctedInverse
#print Units.oneSub
#print tsum_geometric_le_of_norm_lt_one
#print ContinuousLinearMap.opNorm_le_bound
#print ContinuousLinearMap.norm_id_le
#print LinearMap.mkContinuous_norm_le
```

</details>

<details>
<summary>neumann.lean</summary>

```lean
import Poincare.Global.ParametrixNeumannCorrection
#print ContinuousLinearMap.opNorm_comp_le
#print ContinuousLinearMap.le_opNorm
#print inv_le_comm₀
#print Units.val_inv
#print Units.oneSub_val
#print ContinuousLinearMap.one_apply
#print ContinuousLinearMap.mul_apply
#print ContinuousLinearMap.sub_apply
```

</details>

<details>
<summary>statements.lean</summary>

```lean
import Poincare.Global.DuhamelSolutionOperatorCLM
import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.ParametrixNeumannCorrection
#check Poincare.ParabolicHolder.add_apply
#check Poincare.ParabolicHolder.smul_apply
#check Poincare.ParabolicHolder.supNorm_nonneg
#check Poincare.ParabolicHolder.holderSeminorm_nonneg
#check Poincare.ParabolicSolutionGraph.norm_ddu_le
#check ContinuousLinearMap.add_apply
#check ContinuousLinearMap.smul_apply
#check Finset.sum_add_distrib
#check Finset.sum_mul
#check Finset.mul_sum
#check Finset.sum_congr
#check Finset.sum_le_sum
#check norm_sum_le
#check mul_le_mul
#check mul_le_mul_of_nonneg_left
#check mul_le_mul_of_nonneg_right
#check norm_nonneg
#check mul_add
#check add_mul
#check mul_assoc
#check mul_comm
#check smul_eq_mul
#check ite_mul
#check sub_eq_iff_eq_add
#check congrArg
#check LinearMap.mkContinuous
#check ContinuousLinearMap.comp
#check Real.rpow_nonneg
#check Finset.sum_ite_eq
#check Finset.sum_ite_eq'
```

</details>

<details>
<summary>module-audit.lean</summary>

```lean
import Poincare.Global.NearIdentityParabolicRightInverse
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.NearIdentityParabolicRightInverse
    | throwError "module not found"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        throwError "Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

</details>

<details>
<summary>contract.lean</summary>

```lean
import Poincare.Global.NearIdentityParabolicRightInverse
open Set Poincare Poincare.ParabolicHolder Poincare.ParabolicSolutionGraph
open Poincare.DuhamelSolutionOperatorCLM Poincare.NearIdentityParabolicRightInverse
example {α T ε Λ : ℝ} (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4)
    (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
    ∃ G : Graph (E := ClosedSmoothModel 3) α T,
      (∀ t ∈ Icc 0 T, ∀ x : ClosedSmoothModel 3,
        G.ut (t, x) = f (t, x) + ∑ i, ∑ j,
          ((if i = j then 1 else 0) + b i j (t, x)) *
            G.ddu (t, x) (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) ∧
      ‖G‖ ≤ 2 * boundConstant α hα hα1 * ‖f‖ := by
  simpa only [coeff] using exists_nearIdentity_solution b hα hα1 hT hT1 hb hbα hε hΛ f
```

</details>

<details>
<summary>final-statements.lean</summary>

```lean
import Poincare.Global.NearIdentityParabolicRightInverse
#check Poincare.NearIdentityParabolicRightInverse.forcing_add
#check Poincare.NearIdentityParabolicRightInverse.forcing_smul
#check Poincare.NearIdentityParabolicRightInverse.forcing_bound
#check Poincare.NearIdentityParabolicRightInverse.multiplier
#check Poincare.NearIdentityParabolicRightInverse.multiplier_apply
#check Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le
#check Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant
#check Poincare.NearIdentityParabolicRightInverse.errorOp
#check Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le
#check Poincare.NearIdentityParabolicRightInverse.errorOp_small
#check Poincare.NearIdentityParabolicRightInverse.coeff
#check Poincare.NearIdentityParabolicRightInverse.coeff_sum
#check Poincare.NearIdentityParabolicRightInverse.neumann_data_eq
#check Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two
#check Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse
#check Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves
#check Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le
#check Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution
```

</details>

<details>
<summary>run.py</summary>

```python
import subprocess,sys,pathlib
root=pathlib.Path('/tmp/near-identity-evidence')
label=sys.argv[1]; cmd=sys.argv[2:]
p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
(root/(label+'.log')).write_text('$ '+' '.join(cmd)+'\n'+p.stdout+'\nEXIT '+str(p.returncode)+'\n')
print(p.stdout,end=''); print('EXIT',p.returncode)
sys.exit(p.returncode)
```

</details>

<details>
<summary>gate.py</summary>

```python
import subprocess,pathlib,sys,re
root=pathlib.Path('/tmp/near-identity-evidence'); label=sys.argv[1]
src=pathlib.Path('Poincare/Global/NearIdentityParabolicRightInverse.lean')
names=re.findall(r'^(?:@\[.*?\] )?(?:theorem|def) (\w+)',src.read_text(),re.M)
probe=root/(label+'.lean');probe.write_text(src.read_text()+'\n'+''.join('#print axioms Poincare.NearIdentityParabolicRightInverse.'+n+'\n' for n in names))
cmds=[['env','LEAN_NUM_THREADS=1','lake','env','lean',str(probe)],['rg','-n',r'\b(sorry|admit|axiom|opaque)\b|native_decide',str(src)],['git','diff','--check']]
allout=[]
for i,cmd in enumerate(cmds):
 p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 out='$ '+' '.join(cmd)+'\n'+p.stdout+'EXIT '+str(p.returncode)+'\n'; allout.append(out);print(out); (root/(label+'.log')).write_text('\n'.join(allout))
 if i==0:
  assert p.returncode==0
  ax=re.findall(r'depends on axioms: (\[.*?\])',p.stdout,re.S)
  ax=[' '.join(a.split()) for a in ax]
  assert len(ax)==len(names),(ax,names)
  assert all(a=='[propext, Classical.choice, Quot.sound]' for a in ax),ax
 else: assert p.returncode==(1 if i==1 else 0)
(root/(label+'.log')).write_text('\n'.join(allout))
```

</details>

## Actual command output

Each block is the captured stdout/stderr and exit status. Earlier failed probes
are evidence of the attempt, not final source results.

<details>
<summary>01-context.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/context.lean
def Poincare.DuhamelSolutionOperatorCLM.boundConstant : (α : ℝ) → 0 < α → α < 1 → ℝ :=
fun α hα hα1 => Classical.choose ⋯
theorem Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1),
  0 < Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 ∧
    ∀ (T : ℝ),
      0 < T →
        T ≤ 1 →
          ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
            ∃ G,
              (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                  ↑(WithLp.fst ↑G.u) p =
                    ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                ‖G‖ ≤ Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖ :=
fun α hα hα1 => Classical.choose_spec (Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound α hα hα1)
def Poincare.DuhamelSolutionOperatorCLM.duhamelOperator : (α T : ℝ) →
  0 < α → α < 1 → 0 < T → T ≤ 1 → Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T :=
fun α T hα hα1 hT hT1 =>
  (Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap α T hα hα1 hT hT1).mkContinuous
    (Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1) ⋯
theorem Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1),
  ∃ C,
    0 < C ∧
      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
        ‖Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1‖ ≤ C :=
fun α hα hα1 =>
  Exists.intro (Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1)
    ⟨(Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec α hα hα1).left, fun T hT hT1 =>
      LinearMap.mkContinuous_norm_le (Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap α T hα hα1 hT hT1)
        (LT.lt.le (Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec α hα hα1).left)
        (Poincare.DuhamelSolutionOperatorCLM.duhamelOperator._proof_1 α T hα hα1 hT hT1)⟩
theorem Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves : ∀ (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
  (hT1 : T ≤ 1) (f : Poincare.ParabolicHolder.Y α T ℝ),
  ∀ t ∈ Set.Icc 0 T,
    ∀ (x : Poincare.ClosedSmoothModel 3),
      ↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ut) (t, x) =
        ↑(WithLp.fst ↑f) (t, x) +
          ∑ i,
            ((↑(WithLp.fst ↑((Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f).ddu) (t, x))
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
              ((EuclideanSpace.basisFun (Fin 3) ℝ) i) :=
fun α T hα hα1 hT hT1 f =>
  let G := (Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1) f;
  let u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) x;
  have hu := fun t ht =>
    funext fun z =>
      Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u α T hα hα1 hT hT1 f (t, z) ⟨ht, Set.mem_univ z⟩;
  have hd := fun t ht =>
    funext fun z =>
      have h := HasFDerivAt.fderiv (G.hasFDeriv t ht z);
      Eq.symm (Eq.mp (congrArg (fun _a => fderiv ℝ _a z = ↑(WithLp.fst ↑G.du) (t, z)) (hu t ht)) h);
  have hdd := fun t ht x =>
    have h := HasFDerivAt.fderiv (G.hasFDeriv_du t ht x);
    Eq.symm (Eq.mp (congrArg (fun _a => fderiv ℝ _a x = ↑(WithLp.fst ↑G.ddu) (t, x)) (hd t ht)) h);
  have hf :=
    Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound hα (Poincare.ParabolicHolder.hasHolderBound f);
  have hfM := fun t x x_1 => Poincare.ParabolicHolder.norm_le f (t, x_1);
  have hfK := fun t ht x y =>
    id
      (Eq.mp
        (congrArg (LE.le |↑(WithLp.fst ↑f) (t, x) - ↑(WithLp.fst ↑f) (t, y)|)
          (congrArg (HMul.hMul ‖↑f‖)
            (congrFun'
              (congrArg HPow.hPow
                (Eq.trans
                  (congrArg (HAdd.hAdd ‖x - y‖)
                    (Eq.trans (congrArg Real.sqrt (Eq.trans (congrArg abs (sub_self t)) abs_zero)) Real.sqrt_zero))
                  (add_zero ‖x - y‖)))
              α)))
        (Poincare.ParabolicHolder.hasHolderBound f (t, x) ⟨ht, Set.mem_univ x⟩ (t, y) ⟨ht, Set.mem_univ y⟩));
  fun t ht x =>
  id
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ↑(WithLp.fst ↑G.ut) (t, x) =
              ↑(WithLp.fst ↑f) (t, x) +
                ∑ i, (_a ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
          (hdd t ht x)))
      (have htime :=
        (Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation α hα hα1 T hT hT1 ↑(WithLp.fst ↑f) ‖f‖ ‖f‖
              (norm_nonneg f) (norm_nonneg f) hf hfM hfK).right
          t ht x;
      have htimeG := HasDerivWithinAt.congr_of_mem htime (fun s hs => congrFun (hu s hs) x) ht;
      Eq.trans (Eq.symm (HasDerivWithinAt.derivWithin (G.hasDeriv_time t ht x) (uniqueDiffOn_Icc hT t ht)))
        (HasDerivWithinAt.derivWithin htimeG (uniqueDiffOn_Icc hT t ht))))
def Poincare.ParabolicHolderMultiplier.forcing : {α T : ℝ} →
  (Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) →
    Poincare.ParabolicSolutionGraph.Graph α T → Poincare.ParabolicHolder.Y α T ℝ :=
fun {α T} b G =>
  let y :=
    ∑ i,
      ∑ j,
        b i j *
          Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
            ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ⋯ ⋯;
  have he := ⋯;
  Poincare.ParabolicHolder.ofFunction
    (fun p =>
      ∑ i,
        ∑ j,
          ↑(WithLp.fst ↑(b i j)) p *
            ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j))
    ⋯ ⋯ ⋯
@[defeq] theorem Poincare.ParabolicHolderMultiplier.forcing_apply : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T)
  (p : ℝ × Poincare.ClosedSmoothModel 3),
  ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.forcing b G)) p =
    ∑ i,
      ∑ j,
        ↑(WithLp.fst ↑(b i j)) p *
          ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) :=
fun {α T} b G p => rfl
theorem Poincare.ParabolicHolderMultiplier.forcing_eq_sum : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T),
  Poincare.ParabolicHolderMultiplier.forcing b G =
    ∑ i,
      ∑ j,
        b i j *
          Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
            ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ⋯ ⋯ :=
fun {α T} b G =>
  Poincare.ParabolicHolder.ext fun p a =>
    of_eq_true
      (Eq.trans
        (congr
          (congrArg Eq
            (Finset.sum_congr (Eq.refl Finset.univ) fun x a =>
              Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
                Eq.refl
                  (↑(WithLp.fst ↑(b x x_1)) p *
                    ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) x))
                      ((EuclideanSpace.basisFun (Fin 3) ℝ) x_1))))
          (Eq.trans
            (Poincare.ParabolicHolderMultiplier.sum_apply Finset.univ
              (fun i =>
                ∑ j,
                  b i j *
                    Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
                      ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
                      (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)
                      (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) j))
              p)
            (Finset.sum_congr (Eq.refl Finset.univ) fun x a =>
              Eq.trans
                (Poincare.ParabolicHolderMultiplier.sum_apply Finset.univ
                  (fun i =>
                    b x i *
                      Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) x)
                        ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
                        (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) x)
                        (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i))
                  p)
                (Finset.sum_congr (Eq.refl Finset.univ) fun x_1 a =>
                  Eq.refl
                    (↑(WithLp.fst ↑(b x x_1)) p *
                      ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) x))
                        ((EuclideanSpace.basisFun (Fin 3) ℝ) x_1))))))
        (eq_self
          (∑ x,
            ∑ x_1,
              ↑(WithLp.fst ↑(b x x_1)) p *
                ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) x))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) x_1))))
theorem Poincare.ParabolicHolderMultiplier.norm_forcing_le : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T),
  0 < α →
    0 < T →
      ∀ {ε Λ : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            ‖Poincare.ParabolicHolderMultiplier.forcing b G‖ ≤ 9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖) :=
fun {α T} b G hα hT {ε Λ} hb hbα =>
  Eq.mpr
    (id
      (congrArg (fun _a => ‖_a‖ ≤ 9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖))
        (Poincare.ParabolicHolderMultiplier.forcing_eq_sum b G)))
    (Trans.trans
      (Trans.trans
        (norm_sum_le Finset.univ fun i =>
          ∑ j,
            b i j *
              Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
                ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
                (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)
                (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) j))
        (Finset.sum_le_sum fun i a =>
          LE.le.trans
            (norm_sum_le Finset.univ fun i_1 =>
              b i i_1 *
                Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) i_1)
                  (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)
                  (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i_1))
            (Finset.sum_le_sum fun j a =>
              Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le (b i j) G hα hT (hb i j) (hbα i j)
                ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
                (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)
                (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) j))))
      (Eq.mpr
        (id
          (congrFun'
            (congrArg Eq
              (Eq.trans
                (Eq.trans
                  (Finset.sum_congr (Eq.refl Finset.univ) fun x a =>
                    Eq.trans (Finset.sum_const (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖))
                      (Eq.trans
                        (Eq.trans
                          (congrFun' (congrArg HSMul.hSMul (Fintype.card_fin 3)) (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖))
                          (smul_add 3 (ε * ‖G‖) (Λ * T ^ (α / 2) * ‖G‖)))
                        (congr (congrArg HAdd.hAdd (nsmul_eq_mul 3 (ε * ‖G‖)))
                          (nsmul_eq_mul 3 (Λ * T ^ (α / 2) * ‖G‖)))))
                  (Finset.sum_const (3 * (ε * ‖G‖) + 3 * (Λ * T ^ (α / 2) * ‖G‖))))
                (Eq.trans
                  (Eq.trans
                    (congrFun' (congrArg HSMul.hSMul (Fintype.card_fin 3))
                      (3 * (ε * ‖G‖) + 3 * (Λ * T ^ (α / 2) * ‖G‖)))
                    (smul_add 3 (3 * (ε * ‖G‖)) (3 * (Λ * T ^ (α / 2) * ‖G‖))))
                  (congr (congrArg HAdd.hAdd (nsmul_eq_mul 3 (3 * (ε * ‖G‖))))
                    (nsmul_eq_mul 3 (3 * (Λ * T ^ (α / 2) * ‖G‖)))))))
            (9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖))))
        (Mathlib.Tactic.Ring.of_eq
          (Mathlib.Tactic.Ring.Common.add_congr
            (Mathlib.Tactic.Ring.Common.mul_congr
              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                      (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖G‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖G‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 3)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 3))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 3) + 0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 3) + 0))))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3) (Eq.refl 9)))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 3))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))
                (Mathlib.Tactic.Ring.Common.zero_mul (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 3) + 0))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 9) + 0))))
            (Mathlib.Tactic.Ring.Common.mul_congr
              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 3)))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.mul_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                (Eq.refl 1)))))
                        (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖G‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖G‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                (Eq.refl 1))))))
                      (Mathlib.Tactic.Ring.Common.mul_zero
                        (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                        0))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 3))))))
                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 3))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 3)) +
                        0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 3)) + 0))))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 3) (Eq.refl 9))))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 3))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
                (Mathlib.Tactic.Ring.Common.zero_mul
                  (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 3)) + 0))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0))))
            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 9))
              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
            (Mathlib.Tactic.Ring.Common.add_congr
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                  (Eq.mpr
                    (id (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                    (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.atom_pf ‖G‖ rfl
                  (Eq.mpr
                    (id
                      (congrArg (fun _a => ‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖G‖ ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 1))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                      (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a => (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.atom_pf ‖G‖ rfl
                  (Eq.mpr
                    (id
                      (congrArg (fun _a => ‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖G‖ ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                    (Mathlib.Tactic.Ring.Common.mul_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                        0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0))))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                  (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖G‖ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 9))
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0))))
              (Mathlib.Tactic.Ring.Common.zero_mul
                (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 1) +
                  (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (ε ^ Nat.rawCast 1 * (‖G‖ ^ Nat.rawCast 1 * Nat.rawCast 9) +
                  (‖G‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                    0))))))))
theorem Poincare.ParabolicHolderMultiplier.norm_error_le : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (S : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T),
  0 < α →
    0 < T →
      ∀ {ε Λ C_S : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            ‖S‖ ≤ C_S →
              ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                ‖Poincare.ParabolicHolderMultiplier.forcing b (S f)‖ ≤ 9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ :=
fun {α T} b S hα hT {ε Λ C_S} hb hbα hS f =>
  have hε := LE.le.trans (Poincare.ParabolicHolder.supNorm_nonneg (b 0 0)) (hb 0 0);
  have hΛ := LE.le.trans (Poincare.ParabolicHolder.holderSeminorm_nonneg (b 0 0)) (hbα 0 0);
  have hpow := Real.rpow_nonneg (LT.lt.le hT) (α / 2);
  have hSf := LE.le.trans (ContinuousLinearMap.le_opNorm S f) (mul_le_mul_of_nonneg_right hS (norm_nonneg f));
  Trans.trans
    (Trans.trans
      (Trans.trans (Poincare.ParabolicHolderMultiplier.norm_forcing_le b (S f) hα hT hb hbα)
        (Mathlib.Tactic.Ring.of_eq
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
            (Mathlib.Tactic.Ring.Common.add_congr
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                  (Eq.mpr
                    (id (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                    (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.atom_pf ‖S f‖ rfl
                  (Eq.mpr
                    (id
                      (congrArg (fun _a => ‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖S f‖ ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 1))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
              (Mathlib.Tactic.Ring.Common.mul_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                      (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a => (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.atom_pf ‖S f‖ rfl
                  (Eq.mpr
                    (id
                      (congrArg (fun _a => ‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖S f‖ ^ Nat.rawCast 1 * _a)
                        (Eq.symm rfl)))
                    (Eq.refl (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.add_mul
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
                    (Mathlib.Tactic.Ring.Common.mul_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                        0)))
                  (Mathlib.Tactic.Ring.Common.zero_mul (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                      0))))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                  (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                      0)))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                      0))))
              (Mathlib.Tactic.Ring.Common.zero_mul
                (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) +
                  (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1)) + 0)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 9) +
                  (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                    0)))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.mul_congr
              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                  (Eq.mpr
                    (id (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                    (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                      (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a => (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))
                  (Mathlib.Tactic.Ring.Common.mul_add
                    (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 9)
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0))))
                (Mathlib.Tactic.Ring.Common.zero_mul
                  (ε ^ Nat.rawCast 1 * Nat.rawCast 1 +
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (ε ^ Nat.rawCast 1 * Nat.rawCast 9 +
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))))
            (Mathlib.Tactic.Ring.Common.atom_pf ‖S f‖ rfl
              (Eq.mpr
                (id
                  (congrArg (fun _a => ‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖S f‖ ^ Nat.rawCast 1 * _a)
                    (Eq.symm rfl)))
                (Eq.refl (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
                (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖S f‖ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                            (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
                  (Mathlib.Tactic.Ring.Common.mul_zero
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                      0)))
                (Mathlib.Tactic.Ring.Common.zero_mul (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (‖S f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                  (‖S f‖ ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)) +
                    0)))))))
      (mul_le_mul_of_nonneg_left hSf
        (mul_nonneg
          (le_of_lt
            (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9))
              (Eq.refl (Nat.ble 1 9))))
          (add_nonneg hε (mul_nonneg hΛ (le_of_lt (Real.rpow_pos_of_pos hT (α / 2))))))))
    (Mathlib.Tactic.Ring.of_eq
      (Mathlib.Tactic.Ring.Common.mul_congr
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
          (Mathlib.Tactic.Ring.Common.add_congr
            (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
              (Eq.mpr
                (id (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.mul_congr
              (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                (Eq.mpr
                  (id (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                  (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 9)
                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0))))
            (Mathlib.Tactic.Ring.Common.zero_mul
              (ε ^ Nat.rawCast 1 * Nat.rawCast 1 +
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (ε ^ Nat.rawCast 1 * Nat.rawCast 9 +
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))))
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.atom_pf C_S rfl
            (Eq.mpr
              (id (congrArg (fun _a => C_S ^ Nat.rawCast 1 * Nat.rawCast 1 = C_S ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.atom_pf ‖f‖ rfl
            (Eq.mpr
              (id (congrArg (fun _a => ‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖f‖ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
              (Eq.refl (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖f‖ (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
              (Mathlib.Tactic.Ring.Common.mul_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
        (Mathlib.Tactic.Ring.Common.add_mul
          (Mathlib.Tactic.Ring.Common.mul_add
            (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖f‖ (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
            (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 9))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖f‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))))
              (Mathlib.Tactic.Ring.Common.mul_zero
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 9)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Λ ^ Nat.rawCast 1 *
                    ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                  0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (Λ ^ Nat.rawCast 1 *
                  ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                0)))
          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
            (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9)))
            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
              (Λ ^ Nat.rawCast 1 *
                  ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                0)))))
      (Mathlib.Tactic.Ring.Common.mul_congr
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
            (Mathlib.Tactic.Ring.Common.atom_pf C_S rfl
              (Eq.mpr
                (id (congrArg (fun _a => C_S ^ Nat.rawCast 1 * Nat.rawCast 1 = C_S ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                (Eq.refl (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))
                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0)))
              (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0))))
          (Mathlib.Tactic.Ring.Common.add_congr
            (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
              (Eq.mpr
                (id (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.mul_congr
              (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                (Eq.mpr
                  (id (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
                  (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a => (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                      (Eq.symm rfl)))
                  (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
              (Mathlib.Tactic.Ring.Common.add_mul
                (Mathlib.Tactic.Ring.Common.mul_add
                  (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                  (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
                (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
                (Mathlib.Tactic.Ring.Common.mul_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))
                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0))))
            (Mathlib.Tactic.Ring.Common.zero_mul
              (ε ^ Nat.rawCast 1 * Nat.rawCast 1 +
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1) + 0)))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9) +
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))))
        (Mathlib.Tactic.Ring.Common.atom_pf ‖f‖ rfl
          (Eq.mpr
            (id (congrArg (fun _a => ‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖f‖ ^ Nat.rawCast 1 * _a) (Eq.symm rfl)))
            (Eq.refl (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
        (Mathlib.Tactic.Ring.Common.add_mul
          (Mathlib.Tactic.Ring.Common.mul_add
            (Mathlib.Tactic.Ring.Common.mul_pf_left ε (Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖f‖ (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9))))))
            (Mathlib.Tactic.Ring.Common.mul_zero (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9)))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9)) + 0)))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_left (T ^ (α / 2)) (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.mul_pf_right ‖f‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 9)))))))
              (Mathlib.Tactic.Ring.Common.mul_zero
                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Λ ^ Nat.rawCast 1 *
                    ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                  0)))
            (Mathlib.Tactic.Ring.Common.zero_mul (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (Λ ^ Nat.rawCast 1 *
                  ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                0)))
          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
            (ε ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9)))
            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
              (Λ ^ Nat.rawCast 1 *
                  ((T ^ (α / 2)) ^ Nat.rawCast 1 * (C_S ^ Nat.rawCast 1 * (‖f‖ ^ Nat.rawCast 1 * Nat.rawCast 9))) +
                0))))))
theorem Poincare.ParabolicHolderMultiplier.error_small : ∀ {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (S : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T),
  0 < α →
    0 < T →
      ∀ {ε Λ C_S : ℝ},
        (∀ (i j : Fin 3),
            Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε) →
          (∀ (i j : Fin 3),
              Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤
                Λ) →
            ‖S‖ ≤ C_S →
              9 * C_S * ε ≤ 1 / 4 →
                9 * C_S * Λ * T ^ (α / 2) ≤ 1 / 4 →
                  ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                    ‖Poincare.ParabolicHolderMultiplier.forcing b (S f)‖ ≤ 1 / 2 * ‖f‖ :=
fun {α T} b S hα hT {ε Λ C_S} hb hbα hS hε hΛ f =>
  LE.le.trans (Poincare.ParabolicHolderMultiplier.norm_error_le b S hα hT hb hbα hS f)
    (mul_le_mul_of_nonneg_right
      (le_of_not_gt fun a =>
        Mathlib.Tactic.Linarith.lt_irrefl
          (Eq.mp
            (congrArg (fun _a => _a < 0)
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                                      (Eq.refl 9)))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 9 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf C_S rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => C_S ^ Nat.rawCast 1 * Nat.rawCast 1 = C_S ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 9))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0))))
                          (Mathlib.Tactic.Ring.Common.add_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                              (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 2))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (ε ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                              (Mathlib.Tactic.Ring.Common.mul_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg
                                        (fun _a =>
                                          (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                            (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.add_mul
                                  (Mathlib.Tactic.Ring.Common.mul_add
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2))))
                                    (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                      ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                                  (Mathlib.Tactic.Ring.Common.zero_mul
                                    ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 2)))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul
                                  ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt (ε ^ Nat.rawCast 1 * Nat.rawCast 2)
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2) + 0))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                                      (Eq.refl 18)))))
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                                          (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2) (Eq.refl 18))))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (C_S ^ Nat.rawCast 1 *
                                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 18)) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * Nat.rawCast 18))
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  (C_S ^ Nat.rawCast 1 *
                                      (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 18)) +
                                    0))))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (ε ^ Nat.rawCast 1 * Nat.rawCast 2 +
                                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 2) + 0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * Nat.rawCast 18) +
                                (C_S ^ Nat.rawCast 1 *
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 18)) +
                                  0)))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul C_S (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.neg_mul ε (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 18))
                                    (Eq.refl (Int.negOfNat 18))))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul C_S (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.neg_mul Λ (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.neg_mul (T ^ (α / 2)) (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 18))
                                        (Eq.refl (Int.negOfNat 18)))))))
                              Mathlib.Tactic.Ring.Common.neg_zero))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * (Int.negOfNat 18).rawCast) +
                                (C_S ^ Nat.rawCast 1 *
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 18).rawCast)) +
                                  0))))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 2)))
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 18))
                                    (Eq.refl (Int.negOfNat 36))))))
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                      (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 18))
                                        (Eq.refl (Int.negOfNat 36)))))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 2))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (C_S ^ Nat.rawCast 1 *
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast)) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast))
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                (C_S ^ Nat.rawCast 1 *
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast)) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 2)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast) +
                                (C_S ^ Nat.rawCast 1 *
                                    (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast)) +
                                  0)))))
                        (Mathlib.Tactic.Ring.Common.zero_mul
                          (Nat.rawCast 1 +
                            (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * (Int.negOfNat 18).rawCast) +
                              (C_S ^ Nat.rawCast 1 *
                                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 18).rawCast)) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Nat.rawCast 2 +
                            (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast) +
                              (C_S ^ Nat.rawCast 1 *
                                  (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast)) +
                                0))))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                                    (Eq.refl 9)))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 9 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf C_S rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => C_S ^ Nat.rawCast 1 * Nat.rawCast 1 = C_S ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 9))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))
                          (Mathlib.Tactic.Ring.Common.atom_pf ε rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => ε ^ Nat.rawCast 1 * Nat.rawCast 1 = ε ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (ε ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 4))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 4))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 4 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (ε ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (ε ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right ε (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                    (Eq.refl 36)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * Nat.rawCast 36) + 0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul (ε ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * Nat.rawCast 36) + 0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                (Eq.refl 1)))
                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C_S ^ Nat.rawCast 1 * (ε ^ Nat.rawCast 1 * Nat.rawCast 36) + 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 2))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero C_S (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ε (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 36))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 36))
                                (Eq.refl (Int.ofNat 0))))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (C_S ^ Nat.rawCast 1 *
                              (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * (Int.negOfNat 36).rawCast)) +
                            0)))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 9)))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9)
                                    (Eq.refl 9)))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 9 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 9 + 0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf C_S rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => C_S ^ Nat.rawCast 1 * Nat.rawCast 1 = C_S ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (C_S ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right C_S (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 9))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 9))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (C_S ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9 + 0))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.atom_pf Λ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => Λ ^ Nat.rawCast 1 * Nat.rawCast 1 = Λ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (Λ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right Λ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 9)))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (C_S ^ Nat.rawCast 1 * Nat.rawCast 9))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (C_S ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * Nat.rawCast 9) + 0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul (Λ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C_S ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * Nat.rawCast 9) + 0))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))
                        (Mathlib.Tactic.Ring.Common.atom_pf (T ^ (α / 2)) rfl
                          (Eq.mpr
                            (id
                              (congrArg
                                (fun _a =>
                                  (T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 = (T ^ (α / 2)) ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 4))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 4))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4 + 0)))
                          (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left C_S (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left Λ (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right (T ^ (α / 2)) (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 9) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 4)
                                    (Eq.refl 36))))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (C_S ^ Nat.rawCast 1 * (Λ ^ Nat.rawCast 1 * Nat.rawCast 9)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (C_S ^ Nat.rawCast 1 *
                                (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 36)) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 4 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (C_S ^ Nat.rawCast 1 *
                              (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 36)) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))
                          (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (C_S ^ Nat.rawCast 1 *
                              (Λ ^ Nat.rawCast 1 * ((T ^ (α / 2)) ^ Nat.rawCast 1 * Nat.rawCast 36)) +
                            0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero C_S (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero Λ (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (T ^ (α / 2)) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 36))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 36))
                                (Eq.refl (Int.ofNat 0)))))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
            (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le
              (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le
                (Mathlib.Tactic.Linarith.mul_neg
                  (Eq.mp
                    (congrArg (fun _a => _a < 0)
                      (Mathlib.Tactic.CancelDenoms.derive_trans
                        (Eq.trans
                          (congrFun'
                            (congrArg HSub.hSub
                              (Mathlib.Meta.NormNum.IsNNRat.to_eq
                                (Mathlib.Meta.NormNum.isNNRat_div
                                  (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                    (Eq.refl (Nat.mul 1 1)) (Eq.refl 2)))
                                Nat.cast_one (Eq.refl 2)))
                            (9 * C_S * (ε + Λ * T ^ (α / 2))))
                          (congrFun'
                            (congrArg HSub.hSub
                              (Mathlib.Meta.NormNum.IsNNRat.to_eq
                                (Mathlib.Meta.NormNum.isNNRat_div
                                  (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                    (Eq.refl (Nat.mul 1 1)) (Eq.refl 2)))
                                Nat.cast_one (Eq.refl 2)))
                            (9 * C_S * (ε + Λ * T ^ (α / 2)))))
                        (Mathlib.Tactic.CancelDenoms.sub_subst
                          (Mathlib.Tactic.CancelDenoms.div_subst rfl
                            (Mathlib.Meta.NormNum.isNat_eq_true
                              (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                (Mathlib.Meta.NormNum.isNNRat_div
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                    (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                      (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))
                                        (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                          (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                                        (Eq.refl (Nat.mul 2 1)) (Eq.refl 2))))))
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Meta.NormNum.isNat_eq_true
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2))))
                          (Mathlib.Tactic.CancelDenoms.mul_subst
                            (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                              (Mathlib.Meta.NormNum.isNat_eq_true
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))
                            (Mathlib.Tactic.CancelDenoms.add_subst rfl
                              (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                                (Mathlib.Meta.NormNum.isNat_eq_true
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))))
                            (Mathlib.Meta.NormNum.isNat_eq_true
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl 2))
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)))))))
                    (Mathlib.Tactic.Linarith.mul_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt a)
                      (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false))))
                  (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 2)) (Eq.refl false)))
                (Eq.mp
                  (congrArg (fun _a => _a ≤ 0)
                    (Mathlib.Tactic.CancelDenoms.derive_trans
                      (Eq.trans
                        (congrArg (HSub.hSub (9 * C_S * ε))
                          (Mathlib.Meta.NormNum.IsNNRat.to_eq
                            (Mathlib.Meta.NormNum.isNNRat_div
                              (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                                (Eq.refl (Nat.mul 1 1)) (Eq.refl 4)))
                            Nat.cast_one (Eq.refl 4)))
                        (congrArg (HSub.hSub (9 * C_S * ε))
                          (Mathlib.Meta.NormNum.IsNNRat.to_eq
                            (Mathlib.Meta.NormNum.isNNRat_div
                              (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                  (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                                (Eq.refl (Nat.mul 1 1)) (Eq.refl 4)))
                            Nat.cast_one (Eq.refl 4))))
                      (Mathlib.Tactic.CancelDenoms.sub_subst
                        (Mathlib.Tactic.CancelDenoms.mul_subst
                          (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                            (Mathlib.Meta.NormNum.isNat_eq_true
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))
                          rfl
                          (Mathlib.Meta.NormNum.isNat_eq_true
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl 4))
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                        (Mathlib.Tactic.CancelDenoms.div_subst rfl
                          (Mathlib.Meta.NormNum.isNat_eq_true
                            (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                              (Mathlib.Meta.NormNum.isNNRat_div
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                  (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                    (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))
                                      (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                        (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                                      (Eq.refl (Nat.mul 4 1)) (Eq.refl 4))))))
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Meta.NormNum.isNat_eq_true
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl 4))
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))))))
                  (Mathlib.Tactic.Linarith.mul_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le hε)
                    (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl false)))))
              (Eq.mp
                (congrArg (fun _a => _a ≤ 0)
                  (Mathlib.Tactic.CancelDenoms.derive_trans
                    (Eq.trans
                      (congrArg (HSub.hSub (9 * C_S * Λ * T ^ (α / 2)))
                        (Mathlib.Meta.NormNum.IsNNRat.to_eq
                          (Mathlib.Meta.NormNum.isNNRat_div
                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                              (Eq.refl (Nat.mul 1 1)) (Eq.refl 4)))
                          Nat.cast_one (Eq.refl 4)))
                      (congrArg (HSub.hSub (9 * C_S * Λ * T ^ (α / 2)))
                        (Mathlib.Meta.NormNum.IsNNRat.to_eq
                          (Mathlib.Meta.NormNum.isNNRat_div
                            (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                  (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                              (Eq.refl (Nat.mul 1 1)) (Eq.refl 4)))
                          Nat.cast_one (Eq.refl 4))))
                    (Mathlib.Tactic.CancelDenoms.sub_subst
                      (Mathlib.Tactic.CancelDenoms.mul_subst
                        (Mathlib.Tactic.CancelDenoms.mul_subst
                          (Mathlib.Tactic.CancelDenoms.mul_subst rfl rfl
                            (Mathlib.Meta.NormNum.isNat_eq_true
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))
                          rfl
                          (Mathlib.Meta.NormNum.isNat_eq_true
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                              (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl 1))
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)))
                        rfl
                        (Mathlib.Meta.NormNum.isNat_eq_true
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl 4))
                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                      (Mathlib.Tactic.CancelDenoms.div_subst rfl
                        (Mathlib.Meta.NormNum.isNat_eq_true
                          (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                            (Mathlib.Meta.NormNum.isNNRat_div
                              (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                (Mathlib.Meta.NormNum.IsNNRat.to_isNat
                                  (Mathlib.Meta.NormNum.isNNRat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                      (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))
                                    (Mathlib.Meta.NormNum.isNNRat_inv_pos
                                      (Mathlib.Meta.NormNum.IsNat.to_isNNRat
                                        (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4))))
                                    (Eq.refl (Nat.mul 4 1)) (Eq.refl 4))))))
                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Meta.NormNum.isNat_eq_true
                          (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                            (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl 4))
                          (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)))))))
                (Mathlib.Tactic.Linarith.mul_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le hΛ)
                  (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
                    (Mathlib.Meta.NormNum.isNat_ofNat ℝ (Eq.refl 4)) (Eq.refl false)))))))
      (norm_nonneg f))
theorem Poincare.ParabolicHolderMultiplier.norm_entry_le : ∀ {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1),
  ‖Poincare.ParabolicHolderMultiplier.entry H v w hv hw‖ ≤ ‖H‖ :=
fun {α T} H v w hv hw =>
  Eq.mpr
    (id
      (congrArg (fun _a => ‖Poincare.ParabolicHolderMultiplier.entry H v w hv hw‖ ≤ _a)
        (Poincare.ParabolicHolder.norm_eq H)))
    (Poincare.ParabolicHolder.norm_le_of_bounds (Poincare.ParabolicHolderMultiplier.entry H v w hv hw)
      (Poincare.ParabolicHolder.supNorm_nonneg H) (Poincare.ParabolicHolder.holderSeminorm_nonneg H)
      (fun p a =>
        LE.le.trans (Poincare.ParabolicHolderMultiplier.eval_norm_le (↑(WithLp.fst ↑H) p) hv hw)
          (Poincare.ParabolicHolder.le_supNorm H p))
      (Poincare.ParabolicHolderMultiplier.entry_holderBound H hv hw))
theorem Poincare.ParabolicHolder.norm_mul_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T ℝ), ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
fun {E} [NormedAddCommGroup E] {α T} f g =>
  have hb :=
    Poincare.ParabolicHolder.norm_le_of_bounds (f * g)
      (mul_nonneg (Poincare.ParabolicHolder.supNorm_nonneg f) (Poincare.ParabolicHolder.supNorm_nonneg g))
      (add_nonneg
        (mul_nonneg (Poincare.ParabolicHolder.supNorm_nonneg f) (Poincare.ParabolicHolder.holderSeminorm_nonneg g))
        (mul_nonneg (Poincare.ParabolicHolder.holderSeminorm_nonneg f) (Poincare.ParabolicHolder.supNorm_nonneg g)))
      (fun p a =>
        Eq.mpr
          (id
            (congrArg
              (fun _a =>
                ‖_a‖ ≤
                  Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) *
                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
              (Poincare.ParabolicHolder.mul_apply f g p)))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  _a ≤
                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) *
                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                (norm_mul (↑(WithLp.fst ↑f) p) (↑(WithLp.fst ↑g) p))))
            (mul_le_mul (Poincare.ParabolicHolder.le_supNorm f p) (Poincare.ParabolicHolder.le_supNorm g p)
              (norm_nonneg (↑(WithLp.fst ↑g) p)) (Poincare.ParabolicHolder.supNorm_nonneg f))))
      (Poincare.ParabolicHolder.product_holderBound f g);
  Eq.mpr (id (congrArg (fun _a => ‖f * g‖ ≤ _a * ‖g‖) (Poincare.ParabolicHolder.norm_eq f)))
    (Eq.mpr
      (id
        (congrArg
          (fun _a =>
            ‖f * g‖ ≤
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) +
                  Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) *
                _a)
          (Poincare.ParabolicHolder.norm_eq g)))
      (le_of_not_gt fun a =>
        Mathlib.Tactic.Linarith.lt_irrefl
          (Eq.mp
            (congrArg (fun _a => _a < 0)
              (Mathlib.Tactic.Ring.of_eq
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖f * g‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖f * g‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖f * g‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖f * g‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f))
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g))
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.atom_pf
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                              rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑f) ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑f) ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.atom_pf
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                ↑(WithLp.fst ↑g))
                              rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑g) ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑g) ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_left
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑f))
                                  (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g))
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1)))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.Common.atom_pf
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                ↑(WithLp.fst ↑f))
                              rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑f) ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑f) ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.atom_pf
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                              rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑g) ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                              ↑(WithLp.fst ↑g) ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g))
                                  (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f))
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1)))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                              Nat.rawCast 1 *
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1) +
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                0)))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                            (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.neg_mul
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1))))))
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                              (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.neg_mul
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1))))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g))
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.neg_mul
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑f))
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                    (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                      (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                      (Eq.refl (Int.negOfNat 1))))))
                              Mathlib.Tactic.Ring.Common.neg_zero)))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖f * g‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Int.negOfNat 1).rawCast) +
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Int.negOfNat 1).rawCast) +
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      (Int.negOfNat 1).rawCast) +
                                  0)))))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑f))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.atom_pf
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑g))
                            rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1 =
                                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑g) ^
                                          Nat.rawCast 1 *
                                        _a)
                                  (Eq.symm rfl)))
                              (Eq.refl
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                              (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1)))))
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_left
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f))
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g))
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g))
                                (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.mul_pf_left
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑f))
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))))
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g))
                                  (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f))
                                    (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1)))))
                                (Mathlib.Tactic.Ring.Common.mul_zero
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0))))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0)))))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖f * g‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖f * g‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖f * g‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖f * g‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖f * g‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_gt (‖f * g‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1) +
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑f) ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1) +
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                          ↑(WithLp.fst ↑g) ^
                                        Nat.rawCast 1 *
                                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                            ↑(WithLp.fst ↑f) ^
                                          Nat.rawCast 1 *
                                        Nat.rawCast 1) +
                                    0))))))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖f * g‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                          (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                          (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                            (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.ofNat 0))))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                            (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                ↑(WithLp.fst ↑g))
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.ofNat 0))))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                              (Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f))
                                (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_isNat
                                  (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.ofNat 0))))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑g) ^
                                    Nat.rawCast 1 *
                                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1) +
                                0)))))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.mul_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf
                        (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                          ↑(WithLp.fst ↑f))
                        rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 =
                                  Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑f) ^
                                      Nat.rawCast 1 *
                                    _a)
                              (Eq.symm rfl)))
                          (Eq.refl
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.atom_pf
                        (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                          ↑(WithLp.fst ↑g))
                        rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a =>
                                Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 =
                                  Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                        ↑(WithLp.fst ↑g) ^
                                      Nat.rawCast 1 *
                                    _a)
                              (Eq.symm rfl)))
                          (Eq.refl
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_right
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑g))
                            (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.mul_pf_left
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                ↑(WithLp.fst ↑f))
                              (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                  (Eq.refl 1)))))
                          (Mathlib.Tactic.Ring.Common.mul_zero
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑g) ^
                                  Nat.rawCast 1 *
                                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                      ↑(WithLp.fst ↑f) ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1) +
                              0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul
                          (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g) ^
                                Nat.rawCast 1 *
                              Nat.rawCast 1 +
                            0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑g) ^
                                Nat.rawCast 1 *
                              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                    ↑(WithLp.fst ↑f) ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul
                          (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                            ↑(WithLp.fst ↑g))
                          (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.neg_mul
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑f))
                            (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                ↑(WithLp.fst ↑g) ^
                              Nat.rawCast 1 *
                            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                                  ↑(WithLp.fst ↑f) ^
                                Nat.rawCast 1 *
                              (Int.negOfNat 1).rawCast) +
                          0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                      (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                        (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                          ↑(WithLp.fst ↑f))
                        (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0))))))
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
            (Mathlib.Tactic.Linarith.add_lt_of_neg_of_le
              (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg (Mathlib.Tactic.Linarith.sub_nonpos_of_le hb)
                (Mathlib.Tactic.Linarith.sub_neg_of_lt a))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le
                (mul_nonneg (Poincare.ParabolicHolder.holderSeminorm_nonneg f)
                  (Poincare.ParabolicHolder.holderSeminorm_nonneg g)))))))
theorem Poincare.ParabolicHolder.ext.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} {f g : Poincare.ParabolicHolder.Y α T F},
  (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p) → f = g :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} {f g} h =>
  have hval :=
    lp.ext
      (funext fun p =>
        if hp : p ∈ Poincare.ParabolicHolder.cylinder T then h p hp
        else Eq.trans (Poincare.ParabolicHolder.zero_off f hp) (Eq.symm (Poincare.ParabolicHolder.zero_off g hp)));
  Subtype.ext
    (Equiv.injective (WithLp.equiv 1 (↥(lp (fun x => F) ⊤) × ↥(lp (fun x => F) ⊤)))
      (Prod.ext hval
        (lp.ext
          (funext fun i =>
            id
              (Eq.mpr (id (congrArg (fun _a => _a = ↑(WithLp.snd ↑g) i) (Poincare.ParabolicHolder.increment_eq f i)))
                (Eq.mpr
                  (id
                    (congrArg
                      (fun _a =>
                        (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ •
                            (↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2) =
                          _a)
                      (Poincare.ParabolicHolder.increment_eq g i)))
                  (id
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (↑_a (↑i).1 - ↑_a (↑i).2) =
                              (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ •
                                (↑(WithLp.fst ↑g) (↑i).1 - ↑(WithLp.fst ↑g) (↑i).2))
                          hval))
                      (Eq.refl
                        ((Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ •
                          (↑(WithLp.fst ↑g) (↑i).1 - ↑(WithLp.fst ↑g) (↑i).2)))))))))))
def Poincare.ParametrixNeumannCorrection.correctedInverse.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : NormedAddCommGroup X] →
      [inst_1 : NormedSpace ℝ X] →
        [inst_2 : NormedAddCommGroup Y] →
          [inst_3 : NormedSpace ℝ Y] → [CompleteSpace Y] → (Y →L[ℝ] X) → (R : Y →L[ℝ] Y) → ‖R‖ < 1 → Y →L[ℝ] X :=
fun {X} {Y} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] P R
    hR =>
  P.comp ↑(Units.oneSub R hR)⁻¹
def Units.oneSub.{u_4} : {R : Type u_4} → [inst : NormedRing R] → [HasSummableGeomSeries R] → (t : R) → ‖t‖ < 1 → Rˣ :=
fun {R} [NormedRing R] [HasSummableGeomSeries R] t h =>
  { val := 1 - t, inv := ∑' (n : ℕ), t ^ n, val_inv := ⋯, inv_val := ⋯ }
theorem tsum_geometric_le_of_norm_lt_one.{u_4} : ∀ {R : Type u_4} [inst : NormedRing R] (x : R),
  ‖x‖ < 1 → ‖∑' (n : ℕ), x ^ n‖ ≤ ‖1‖ - 1 + (1 - ‖x‖)⁻¹ :=
fun {R} [inst : NormedRing R] x h =>
  if hx : Summable fun n => x ^ n then
    Eq.mpr (id (congrArg (fun _a => ‖_a‖ ≤ ‖1‖ - 1 + (1 - ‖x‖)⁻¹) (Summable.tsum_eq_zero_add hx)))
      (Eq.mpr
        (id
          (congrFun'
            (congrArg LE.le (congrArg norm (congrFun' (congrArg HAdd.hAdd (pow_zero x)) (∑' (b : ℕ), x ^ (b + 1)))))
            (‖1‖ - 1 + (1 - ‖x‖)⁻¹)))
        (le_trans (norm_add_le 1 (∑' (b : ℕ), x ^ (b + 1)))
          (have this :=
            tsum_of_norm_bounded
              (Eq.mpr
                (eq_of_heq
                  ((fun α β inst inst' e'_3 inst_1 f a a' e'_6 L =>
                      Eq.casesOn (motive := fun a_1 x => inst' = a_1 → e'_3 ≍ x → HasSum f a L ≍ HasSum f a' L) e'_3
                        (fun h =>
                          Eq.ndrec (motive := fun inst' =>
                            ∀ (e_3 : inst = inst'), e_3 ≍ Eq.refl inst → HasSum f a L ≍ HasSum f a' L)
                            (fun e_3 h =>
                              Eq.casesOn (motive := fun a_1 x => a' = a_1 → e'_6 ≍ x → HasSum f a L ≍ HasSum f a' L)
                                e'_6
                                (fun h =>
                                  Eq.ndrec (motive := fun a' =>
                                    ∀ (e_6 : a = a'), e_6 ≍ Eq.refl a → HasSum f a L ≍ HasSum f a' L)
                                    (fun e_6 h => HEq.refl (HasSum f a L)) (Eq.symm h) e'_6)
                                (Eq.refl a') (HEq.refl e'_6))
                            (Eq.symm h) e'_3)
                        (Eq.refl inst') (HEq.refl e'_3))
                    ℝ ℕ Real.instAddCommMonoid Real.instAddCommGroup.toAddCommMonoid (Eq.refl Real.instAddCommMonoid)
                    PseudoMetricSpace.toUniformSpace.toTopologicalSpace (fun b => ‖x‖ ^ (b + 1)) ((1 - ‖x‖)⁻¹ - 1)
                    ((1 - ‖x‖)⁻¹ - ∑ i ∈ Finset.range 1, ‖x‖ ^ i)
                    (eq_of_heq
                      ((fun α β γ self a a_1 a' e'_6 =>
                          Eq.casesOn (motive := fun a_2 x => a' = a_2 → e'_6 ≍ x → a - a_1 ≍ a - a') e'_6
                            (fun h =>
                              Eq.ndrec (motive := fun a' => ∀ (e_6 : a_1 = a'), e_6 ≍ Eq.refl a_1 → a - a_1 ≍ a - a')
                                (fun e_6 h => HEq.refl (a - a_1)) (Eq.symm h) e'_6)
                            (Eq.refl a') (HEq.refl e'_6))
                        ℝ ℝ ℝ instHSub (1 - ‖x‖)⁻¹ 1 (∑ i ∈ Finset.range 1, ‖x‖ ^ i)
                        (of_eq_true
                          (Eq.trans (congrArg (Eq 1) (Eq.trans (Finset.sum_singleton (HPow.hPow ‖x‖) 0) (pow_zero ‖x‖)))
                            (eq_self 1)))))))
                ((hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)))
              fun b => norm_pow_le' x (Nat.succ_pos b);
          le_of_not_gt fun a =>
            Mathlib.Tactic.Linarith.lt_irrefl
              (Eq.mp
                (congrArg (fun _a => _a < 0)
                  (Mathlib.Tactic.Ring.of_eq
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.atom_pf ‖∑' (b : ℕ), x ^ (b + 1)‖ rfl
                            (Eq.mpr
                              (id
                                (congrArg
                                  (fun _a =>
                                    ‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                      ‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right ‖∑' (b : ℕ), x ^ (b + 1)‖ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.inv_congr
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg
                                        (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul ‖x‖ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                              (Mathlib.Tactic.Ring.Common.atom_pf'
                                (Eq.refl (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1 =
                                          (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl
                                    ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1)))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1)))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.sub_pf
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1))))
                              Mathlib.Tactic.Ring.Common.neg_zero)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0)))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 1)))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul
                                (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1)))))
                              Mathlib.Tactic.Ring.Common.neg_zero))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    (Int.negOfNat 1).rawCast +
                                  0))))))
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.sub_congr
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf ‖1‖ rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => ‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖1‖ ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Tactic.Ring.Common.mul_pf_right ‖1‖ (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                        (Eq.refl 1))))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                    (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                            (Mathlib.Tactic.Ring.Common.mul_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.add_mul
                                (Mathlib.Tactic.Ring.Common.mul_add
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1)))
                                  (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                                (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                            (Mathlib.Tactic.Ring.Common.sub_pf
                              (Mathlib.Tactic.Ring.Common.neg_add
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1))))
                                Mathlib.Tactic.Ring.Common.neg_zero)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.inv_congr
                              (Mathlib.Tactic.Ring.Common.sub_congr
                                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                                (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                                  (Eq.mpr
                                    (id
                                      (congrArg
                                        (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                        (Eq.symm rfl)))
                                    (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                                (Mathlib.Tactic.Ring.Common.sub_pf
                                  (Mathlib.Tactic.Ring.Common.neg_add
                                    (Mathlib.Tactic.Ring.Common.neg_mul ‖x‖ (Nat.rawCast 1)
                                      (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                        (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                          (Eq.refl (Int.negOfNat 1)))))
                                    Mathlib.Tactic.Ring.Common.neg_zero)
                                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                      (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                              (Mathlib.Tactic.Ring.Common.atom_pf'
                                (Eq.refl (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹) rfl
                                (Eq.mpr
                                  (id
                                    (congrArg
                                      (fun _a =>
                                        (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            Nat.rawCast 1 =
                                          (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                              Nat.rawCast 1 *
                                            _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl
                                    ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1)))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right
                                  (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹
                                  (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                        Nat.rawCast 1 *
                                      Nat.rawCast 1 +
                                    0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 1).rawCast
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                  Nat.rawCast 1 *
                                Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                        (Mathlib.Tactic.Ring.Common.add_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf ‖1‖ rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => ‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖1‖ ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖1‖ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf ‖∑' (b : ℕ), x ^ (b + 1)‖ rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      ‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                        ‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖∑' (b : ℕ), x ^ (b + 1)‖ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                  (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul
                                (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                            (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul ‖∑' (b : ℕ), x ^ (b + 1)‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Tactic.Ring.Common.neg_mul ‖1‖ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                  (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                    (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                    (Eq.refl (Int.negOfNat 1)))))
                              Mathlib.Tactic.Ring.Common.neg_zero))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 1).rawCast
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt
                              (‖∑' (b : ℕ), x ^ (b + 1)‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖1‖ (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                        (Eq.refl (Int.ofNat 0)))))
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖∑' (b : ℕ), x ^ (b + 1)‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                              (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
                  (Eq.mp
                    (congrArg (fun _a => _a ≤ 0)
                      (Mathlib.Tactic.Linarith.without_one_mul
                        (Mathlib.Tactic.CancelDenoms.sub_subst rfl (Mathlib.Tactic.CancelDenoms.sub_subst rfl rfl))))
                    (Mathlib.Tactic.Linarith.sub_nonpos_of_le this))
                  (Eq.mp
                    (congrArg (fun _a => _a < 0)
                      (Mathlib.Tactic.Linarith.without_one_mul
                        (Mathlib.Tactic.CancelDenoms.sub_subst
                          (Mathlib.Tactic.CancelDenoms.add_subst (Mathlib.Tactic.CancelDenoms.sub_subst rfl rfl) rfl)
                          (Mathlib.Tactic.CancelDenoms.add_subst rfl rfl))))
                    (Mathlib.Tactic.Linarith.sub_neg_of_lt a)))))))
  else
    Eq.mpr
      (id
        (congrFun' (congrArg LE.le (Eq.trans (congrArg norm (tsum_eq_zero_of_not_summable hx)) norm_zero))
          (‖1‖ - 1 + (1 - ‖x‖)⁻¹)))
      (Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim
        (fun a =>
          of_eq_true
            (Eq.trans
              (congrArg (LE.le 0)
                (Eq.trans
                  (congr
                    (congrArg HAdd.hAdd
                      (Eq.trans (congrFun' (congrArg HSub.hSub (norm_of_subsingleton 1)) 1) (zero_sub 1)))
                    (Eq.trans
                      (congrArg Inv.inv (Eq.trans (congrArg (HSub.hSub 1) (norm_of_subsingleton x)) (sub_zero 1)))
                      inv_one))
                  (neg_add_cancel 1)))
              (Std.le_refl._simp_1 0)))
        fun a =>
        have this := one_le_norm_one R;
        have this_1 :=
          inv_nonneg.mpr
            (le_of_not_gt fun a =>
              Mathlib.Tactic.Linarith.lt_irrefl
                (Eq.mp
                  (congrArg (fun _a => _a < 0)
                    (Mathlib.Tactic.Ring.of_eq
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                            (Eq.mpr
                              (id
                                (congrArg (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                  (Eq.symm rfl)))
                              (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.sub_pf
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1))))
                              Mathlib.Tactic.Ring.Common.neg_zero)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.sub_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.sub_pf
                              (Mathlib.Tactic.Ring.Common.neg_add
                                (Mathlib.Tactic.Ring.Common.neg_mul ‖x‖ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                    (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                      (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                      (Eq.refl (Int.negOfNat 1)))))
                                Mathlib.Tactic.Ring.Common.neg_zero)
                              (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                  (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                          (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                          (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.ofNat 0))))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖x‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0))))
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
                  (Mathlib.Tactic.Linarith.add_neg (Mathlib.Tactic.Linarith.sub_neg_of_lt h)
                    (Mathlib.Tactic.Linarith.sub_neg_of_lt a))));
        le_of_not_gt fun a =>
          Mathlib.Tactic.Linarith.lt_irrefl
            (Eq.mp
              (congrArg (fun _a => _a < 0)
                (Mathlib.Tactic.Ring.of_eq
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖1‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖1‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul ‖1‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            Mathlib.Tactic.Ring.Common.neg_zero)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (‖1‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                      (Mathlib.Tactic.Ring.Common.sub_congr
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                          (Mathlib.Tactic.Ring.Common.add_mul (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.zero_mul 0) (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.inv_congr
                            (Mathlib.Tactic.Ring.Common.sub_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.sub_pf
                                (Mathlib.Tactic.Ring.Common.neg_add
                                  (Mathlib.Tactic.Ring.Common.neg_mul ‖x‖ (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Eq.refl (Int.negOfNat 1)))))
                                  Mathlib.Tactic.Ring.Common.neg_zero)
                                (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                    (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                            (Mathlib.Tactic.Ring.Common.atom_pf'
                              (Eq.refl (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹) rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1)))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.sub_pf
                          (Mathlib.Tactic.Ring.Common.neg_add
                            (Mathlib.Tactic.Ring.Common.neg_mul
                              (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1)))))
                            Mathlib.Tactic.Ring.Common.neg_zero)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^ Nat.rawCast 1 *
                                (Int.negOfNat 1).rawCast +
                              0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖1‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^ Nat.rawCast 1 *
                                (Int.negOfNat 1).rawCast +
                              0)))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.sub_congr
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.atom_pf ‖1‖ rfl
                              (Eq.mpr
                                (id
                                  (congrArg (fun _a => ‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖1‖ ^ Nat.rawCast 1 * _a)
                                    (Eq.symm rfl)))
                                (Eq.refl (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Tactic.Ring.Common.mul_pf_right ‖1‖ (Nat.rawCast 1)
                                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                      (Eq.refl 1))))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.mul_congr
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                            (Mathlib.Tactic.Ring.Common.add_mul
                              (Mathlib.Tactic.Ring.Common.mul_add
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1)))
                                (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                                (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                              (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.sub_pf
                            (Mathlib.Tactic.Ring.Common.neg_add
                              (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Eq.refl (Int.negOfNat 1))))
                              Mathlib.Tactic.Ring.Common.neg_zero)
                            (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Int.negOfNat 1).rawCast
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                        (Mathlib.Tactic.Ring.Common.mul_congr
                          (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                          (Mathlib.Tactic.Ring.Common.inv_congr
                            (Mathlib.Tactic.Ring.Common.sub_congr
                              (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                              (Mathlib.Tactic.Ring.Common.atom_pf ‖x‖ rfl
                                (Eq.mpr
                                  (id
                                    (congrArg (fun _a => ‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖x‖ ^ Nat.rawCast 1 * _a)
                                      (Eq.symm rfl)))
                                  (Eq.refl (‖x‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                              (Mathlib.Tactic.Ring.Common.sub_pf
                                (Mathlib.Tactic.Ring.Common.neg_add
                                  (Mathlib.Tactic.Ring.Common.neg_mul ‖x‖ (Nat.rawCast 1)
                                    (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                                      (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                        (Eq.refl (Int.negOfNat 1)))))
                                  Mathlib.Tactic.Ring.Common.neg_zero)
                                (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                                  (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                    (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                            (Mathlib.Tactic.Ring.Common.atom_pf'
                              (Eq.refl (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹) rfl
                              (Eq.mpr
                                (id
                                  (congrArg
                                    (fun _a =>
                                      (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                            Nat.rawCast 1 *
                                          Nat.rawCast 1 =
                                        (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                            Nat.rawCast 1 *
                                          _a)
                                    (Eq.symm rfl)))
                                (Eq.refl
                                  ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1)))))
                          (Mathlib.Tactic.Ring.Common.add_mul
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pf_right
                                (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                                    (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                      Nat.rawCast 1 *
                                    Nat.rawCast 1 +
                                  0)))
                            (Mathlib.Tactic.Ring.Common.zero_mul
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Int.negOfNat 1).rawCast
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0)))))
                      (Mathlib.Tactic.Ring.Common.mul_congr
                        (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one))
                        (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                        (Mathlib.Tactic.Ring.Common.add_mul (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.zero_mul 0) (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))
                      (Mathlib.Tactic.Ring.Common.sub_pf Mathlib.Tactic.Ring.Common.neg_zero
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          ((Int.negOfNat 1).rawCast +
                            (‖1‖ ^ Nat.rawCast 1 * Nat.rawCast 1 +
                              ((Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ ^
                                    Nat.rawCast 1 *
                                  Nat.rawCast 1 +
                                0))))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                        (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖1‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_isNat
                            (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                              (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.ofNat 0)))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                          (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero
                            (Nat.rawCast 1 + (‖x‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))⁻¹ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_isNat
                              (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.ofNat 0)))))
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
                  (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
              (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
                (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                  (Eq.mp
                    (congrArg (fun _a => _a ≤ 0)
                      (Mathlib.Tactic.Linarith.without_one_mul (Mathlib.Tactic.CancelDenoms.sub_subst rfl rfl)))
                    (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1)))
                (Eq.mp
                  (congrArg (fun _a => _a < 0)
                    (Mathlib.Tactic.Linarith.without_one_mul
                      (Mathlib.Tactic.CancelDenoms.sub_subst
                        (Mathlib.Tactic.CancelDenoms.add_subst (Mathlib.Tactic.CancelDenoms.sub_subst rfl rfl) rfl)
                        rfl)))
                  (Mathlib.Tactic.Linarith.sub_neg_of_lt a)))))
theorem ContinuousLinearMap.opNorm_le_bound.{u_1, u_2, u_4, u_5} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
  {F : Type u_5} [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F]
  [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →SL[σ₁₂] F) {M : ℝ},
  0 ≤ M → (∀ (x : E), ‖f x‖ ≤ M * ‖x‖) → ‖f‖ ≤ M :=
fun {𝕜} {𝕜₂} {E} {F} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂} f {M} hMp hM =>
  csInf_le ContinuousLinearMap.bounds_bddBelow ⟨hMp, hM⟩
theorem ContinuousLinearMap.norm_id_le.{u_1, u_4} : ∀ {𝕜 : Type u_1} {E : Type u_4} [inst : SeminormedAddCommGroup E]
  [inst_1 : NontriviallyNormedField 𝕜] [inst_2 : NormedSpace 𝕜 E], ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 :=
fun {𝕜} {E} [SeminormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] =>
  ContinuousLinearMap.opNorm_le_bound (ContinuousLinearMap.id 𝕜 E) zero_le_one fun x =>
    of_eq_true (Eq.trans (congrArg (LE.le ‖x‖) (one_mul ‖x‖)) (Std.le_refl._simp_1 ‖x‖))
theorem LinearMap.mkContinuous_norm_le.{u_1, u_2, u_4, u_5} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
  {F : Type u_5} [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F]
  [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {C : ℝ},
  0 ≤ C → ∀ (h : ∀ (x : E), ‖f x‖ ≤ C * ‖x‖), ‖f.mkContinuous C h‖ ≤ C :=
fun {𝕜} {𝕜₂} {E} {F} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂} f {C} hC h =>
  ContinuousLinearMap.opNorm_le_bound (f.mkContinuous C h) hC h

EXIT 0
```

</details>

<details>
<summary>02-item1.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean
Poincare/Global/NearIdentityParabolicRightInverse.lean:14:31: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearIdentityParabolicRightInverse.lean:14:20: error(lean.unknownIdentifier): Unknown identifier `α`
Poincare/Global/NearIdentityParabolicRightInverse.lean:14:22: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/NearIdentityParabolicRightInverse.lean:15:35: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearIdentityParabolicRightInverse.lean:15:20: error(lean.unknownIdentifier): Unknown identifier `α`
Poincare/Global/NearIdentityParabolicRightInverse.lean:15:22: error(lean.unknownIdentifier): Unknown identifier `T`
Poincare/Global/NearIdentityParabolicRightInverse.lean:20:47: error: unexpected token ')'; expected term
Poincare/Global/NearIdentityParabolicRightInverse.lean:29:48: error: unexpected token ')'; expected term
Poincare/Global/NearIdentityParabolicRightInverse.lean:43:49: error: unexpected token ')'; expected term
Poincare/Global/NearIdentityParabolicRightInverse.lean:58:42: error: unexpected token ')'; expected term
Poincare/Global/NearIdentityParabolicRightInverse.lean:64:60: error: unexpected token ')'; expected term
Poincare/Global/NearIdentityParabolicRightInverse.lean:68:54: error: unexpected token ')'; expected term

EXIT 1
```

</details>

<details>
<summary>03-item1.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean
Poincare/Global/NearIdentityParabolicRightInverse.lean:16:27: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearIdentityParabolicRightInverse.lean:17:31: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/NearIdentityParabolicRightInverse.lean:20:41: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:20:52: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:29:42: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:29:59: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:43:43: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:43:52: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:58:36: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:58:42: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:61:37: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:64:54: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:64:63: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termX₀` has not been implemented
  X₀
Poincare/Global/NearIdentityParabolicRightInverse.lean:68:48: error: elaboration function for `_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse.termY₀` has not been implemented
  Y₀

EXIT 1
```

</details>

<details>
<summary>04-item1.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>06-item1-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/06-item1-gate.lean
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT 0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean
EXIT 1

$ git diff --check
EXIT 0
```

</details>

<details>
<summary>07-item2.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>08-neumann.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/neumann.lean
theorem ContinuousLinearMap.opNorm_comp_le.{u_1, u_2, u_3, u_4, u_5, u_7} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2}
  {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_5} {G : Type u_7} [inst : SeminormedAddCommGroup E]
  [inst_1 : SeminormedAddCommGroup F] [inst_2 : SeminormedAddCommGroup G] [inst_3 : NontriviallyNormedField 𝕜]
  [inst_4 : NontriviallyNormedField 𝕜₂] [inst_5 : NontriviallyNormedField 𝕜₃] [inst_6 : NormedSpace 𝕜 E]
  [inst_7 : NormedSpace 𝕜₂ F] [inst_8 : NormedSpace 𝕜₃ G] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [inst_9 : RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] (h : F →SL[σ₂₃] G)
  (f : E →SL[σ₁₂] F), ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
fun {𝕜} {𝕜₂} {𝕜₃} {E} {F} {G} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] {σ₁₂} {σ₂₃} {σ₁₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂]
    [RingHomIsometric σ₂₃] h f =>
  csInf_le ContinuousLinearMap.bounds_bddBelow
    ⟨mul_nonneg (norm_nonneg h) (norm_nonneg f), fun x =>
      Eq.mpr (id (congrArg (fun _a => ‖(h.comp f) x‖ ≤ _a) (mul_assoc ‖h‖ ‖f‖ ‖x‖)))
        (ContinuousLinearMap.le_opNorm_of_le h (ContinuousLinearMap.le_opNorm f x))⟩
theorem ContinuousLinearMap.le_opNorm.{u_1, u_2, u_4, u_5} : ∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}
  {F : Type u_5} [inst : SeminormedAddCommGroup E] [inst_1 : SeminormedAddCommGroup F]
  [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : NontriviallyNormedField 𝕜₂] [inst_4 : NormedSpace 𝕜 E]
  [inst_5 : NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) (x : E), ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
fun {𝕜} {𝕜₂} {E} {F} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂} [RingHomIsometric σ₁₂] f x =>
  (ContinuousLinearMap.isLeast_opNorm f).left.right x
theorem inv_le_comm₀.{u_3} : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀]
  [MulPosReflectLT G₀] {a b : G₀}, 0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻¹ ≤ a) :=
fun {G₀} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] [MulPosReflectLT G₀] {a b} ha hb =>
  Eq.mpr (id (congrArg (fun _a => _a ↔ b⁻¹ ≤ a) (Eq.symm (propext (inv_le_inv₀ hb (inv_pos.mpr ha))))))
    (Eq.mpr (id (congrArg (fun _a => b⁻¹ ≤ _a ↔ b⁻¹ ≤ a) (inv_inv a))) Iff.rfl)
theorem Units.val_inv.{u} : ∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * self.inv = 1 :=
fun α [Monoid α] self => self.3
/tmp/near-identity-evidence/neumann.lean:6:7: error(lean.unknownIdentifier): Unknown constant `Units.oneSub_val`
@[defeq] theorem ContinuousLinearMap.one_apply.{u_1, u_4} : ∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4}
  [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁] [inst_3 : Module R₁ M₁] (x : M₁), 1 x = x :=
fun {R₁} [Semiring R₁] {M₁} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁] x => rfl
@[defeq] theorem ContinuousLinearMap.mul_apply.{u_1, u_4} : ∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4}
  [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁] [inst_3 : Module R₁ M₁] (f g : M₁ →L[R₁] M₁) (x : M₁),
  (f * g) x = f (g x) :=
fun {R₁} [Semiring R₁] {M₁} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁] f g x => rfl
@[defeq] theorem ContinuousLinearMap.sub_apply.{u_1, u_2, u_4, u_5} : ∀ {R : Type u_1} [inst : Ring R] {R₂ : Type u_2}
  [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M] [inst_3 : AddCommGroup M] {M₂ : Type u_5}
  [inst_4 : TopologicalSpace M₂] [inst_5 : AddCommGroup M₂] [inst_6 : Module R M] [inst_7 : Module R₂ M₂]
  {σ₁₂ : R →+* R₂} [inst_8 : IsTopologicalAddGroup M₂] (f g : M →SL[σ₁₂] M₂) (x : M), (f - g) x = f x - g x :=
fun {R} [Ring R] {R₂} [Ring R₂] {M} [TopologicalSpace M] [AddCommGroup M] {M₂} [TopologicalSpace M₂] [AddCommGroup M₂]
    [Module R M] [Module R₂ M₂] {σ₁₂} [IsTopologicalAddGroup M₂] f g x =>
  rfl

EXIT 1
```

</details>

<details>
<summary>09-item2-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/09-item2-gate.lean
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT 0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean
EXIT 1

$ git diff --check
EXIT 0
```

</details>

<details>
<summary>10-item3.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean
Poincare/Global/NearIdentityParabolicRightInverse.lean:185:42: error: failed to synthesize
  SeminormedAddGroup (Y α T ℝ →L[ℝ] Y α T ℝ)
(deterministic) timeout at `typeclass`, maximum number of heartbeats (20000) has been reached

Note: Use `set_option synthInstance.maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

EXIT 1
```

</details>

<details>
<summary>11-item3.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean
Poincare/Global/NearIdentityParabolicRightInverse.lean:187:41: error: Application type mismatch: The argument
  norm_nonneg ?m.117
has type
  0 ≤ @norm ?m.115 SeminormedAddGroup.toNorm ?m.117
but is expected to have type
  0 ≤ @norm (Y α T ℝ →L[ℝ] Y α T ℝ) ContinuousLinearMap.hasOpNorm ↑(Units.oneSub (errorOp b hα hα1 hT hT1) hR)⁻¹
in the application
  mul_le_mul (duhamel_norm_le_boundConstant hα hα1 hT hT1) (neumann_norm_le_two (errorOp b hα hα1 hT hT1) hR hhalf)
    (norm_nonneg ?m.117)

EXIT 1
```

</details>

<details>
<summary>12-item3-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/12-item3-gate.lean
/tmp/near-identity-evidence/12-item3-gate.lean:187:41: error: Application type mismatch: The argument
  norm_nonneg ?m.117
has type
  0 ≤ @norm ?m.115 SeminormedAddGroup.toNorm ?m.117
but is expected to have type
  0 ≤ @norm (Y α T ℝ →L[ℝ] Y α T ℝ) ContinuousLinearMap.hasOpNorm ↑(Units.oneSub (errorOp b hα hα1 hT hT1) hR)⁻¹
in the application
  mul_le_mul (duhamel_norm_le_boundConstant hα hα1 hT hT1) (neumann_norm_le_two (errorOp b hα hα1 hT hT1) hR hhalf)
    (norm_nonneg ?m.117)
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_data_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
EXIT 1
```

</details>

<details>
<summary>13-item3.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>14-statements.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/statements.lean
Poincare.ParabolicHolder.add_apply.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f g : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E) :
  ↑(WithLp.fst ↑(f + g)) p = ↑(WithLp.fst ↑f) p + ↑(WithLp.fst ↑g) p
Poincare.ParabolicHolder.smul_apply.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (c : ℝ) (f : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E) :
  ↑(WithLp.fst ↑(c • f)) p = c • ↑(WithLp.fst ↑f) p
Poincare.ParabolicHolder.supNorm_nonneg.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F) :
  0 ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)
Poincare.ParabolicHolder.holderSeminorm_nonneg.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F) :
  0 ≤ Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)
Poincare.ParabolicSolutionGraph.norm_ddu_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
  (g : Poincare.ParabolicSolutionGraph.Graph α T) : ‖g.ddu‖ ≤ ‖g‖
ContinuousLinearMap.add_apply.{u_1, u_2, u_4, u_6} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]
  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]
  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] [ContinuousAdd M₂] (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) :
  (f + g) x = f x + g x
ContinuousLinearMap.smul_apply.{u_1, u_2, u_4, u_6, u_9} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]
  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]
  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] {S₂ : Type u_9} [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂]
  [ContinuousConstSMul S₂ M₂] (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x
Finset.sum_add_distrib.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s : Finset ι} [AddCommMonoid M] {f g : ι → M} :
  ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x
Finset.sum_mul.{u_1, u_4} {ι : Type u_1} {R : Type u_4} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R)
  (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
Finset.mul_sum.{u_1, u_4} {ι : Type u_1} {R : Type u_4} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R)
  (a : R) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
Finset.sum_congr.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [AddCommMonoid M] {f g : ι → M}
  (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f g : ι → N} {s : Finset ι}
  [AddLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
norm_sum_le.{u_3, u_9} {ι : Type u_3} {E : Type u_9} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
  ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖
mul_le_mul.{u_1} {α : Type u_1} [Mul α] [Zero α] [Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b)
  (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d
mul_le_mul_of_nonneg_left.{u_1} {α : Type u_1} [Mul α] [Zero α] [Preorder α] {a b c : α} [PosMulMono α] (hbc : b ≤ c)
  (ha : 0 ≤ a) : a * b ≤ a * c
mul_le_mul_of_nonneg_right.{u_1} {α : Type u_1} [Mul α] [Zero α] [Preorder α] {a b c : α} [MulPosMono α] (hbc : b ≤ c)
  (ha : 0 ≤ a) : b * a ≤ c * a
norm_nonneg.{u_5} {E : Type u_5} [SeminormedAddGroup E] (a : E) : 0 ≤ ‖a‖
mul_add.{v} {R : Type v} [Mul R] [Add R] [LeftDistribClass R] (a b c : R) : a * (b + c) = a * b + a * c
add_mul.{v} {R : Type v} [Mul R] [Add R] [RightDistribClass R] (a b c : R) : (a + b) * c = a * c + b * c
mul_assoc.{u_1} {G : Type u_1} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a
smul_eq_mul.{u_9} {α : Type u_9} [Mul α] (a b : α) : a • b = a * b
ite_mul.{u_2} {α : Type u_2} (P : Prop) [Decidable P] [Mul α] (a b c : α) :
  (if P then a else b) * c = if P then a * c else b * c
sub_eq_iff_eq_add.{u_3} {G : Type u_3} [AddGroup G] {a b c : G} : a - b = c ↔ a = c + b
congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂
LinearMap.mkContinuous.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_3} {F : Type u_4} [Ring 𝕜]
  [Ring 𝕜₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂}
  (f : E →ₛₗ[σ] F) (C : ℝ) (h : ∀ (x : E), ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F
ContinuousLinearMap.comp.{u_1, u_2, u_3, u_4, u_6, u_7} {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type u_3} [Semiring R₁]
  [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type u_4}
  [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type u_7}
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃
Real.rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y
Finset.sum_ite_eq.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M] [DecidableEq ι] (s : Finset ι) (a : ι)
  (b : ι → M) : (∑ x ∈ s, if a = x then b x else 0) = if a ∈ s then b a else 0
Finset.sum_ite_eq'.{u_1, u_3} {ι : Type u_1} {M : Type u_3} [AddCommMonoid M] [DecidableEq ι] (s : Finset ι) (a : ι)
  (b : ι → M) : (∑ x ∈ s, if x = a then b x else 0) = if a ∈ s then b a else 0

EXIT 0
```

</details>

<details>
<summary>15-item3-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/15-item3-gate.lean
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_data_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT 0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean
EXIT 1

$ git diff --check
EXIT 0
```

</details>

<details>
<summary>16-item4.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>17-item4-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/17-item4-gate.lean
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_data_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT 0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean
190:/-- Small Hölder perturbations admit a zero-trace solution with a uniform graph bound. -/
EXIT 0
```

</details>

<details>
<summary>18-item4-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/18-item4-gate.lean
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_data_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXIT 0

$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean
EXIT 1

$ git diff --check
EXIT 0
```

</details>

<details>
<summary>19-compile.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/NearIdentityParabolicRightInverse.olean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>20-module-audit.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/module-audit.lean
'Poincare.DuhamelSolutionOperatorCLM.boundConstant.congr_simp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse._aux_Poincare_Global_NearIdentityParabolicRightInverse___macroRules__private_Poincare_Global_NearIdentityParabolicRightInverse_0_Poincare_NearIdentityParabolicRightInverse_termX₀_1' does not depend on any axioms
/tmp/near-identity-evidence/module-audit.lean:3:0: error: Unexpected foundational dependencies for _private.Poincare.Global.NearIdentityParabolicRightInverse.0.Poincare.NearIdentityParabolicRightInverse._aux_Poincare_Global_NearIdentityParabolicRightInverse___macroRules__private_Poincare_Global_NearIdentityParabolicRightInverse_0_Poincare_NearIdentityParabolicRightInverse_termX₀_1: []

EXIT 1
```

</details>

<details>
<summary>21-final-statements.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/final-statements.lean
Poincare.NearIdentityParabolicRightInverse.forcing_add {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G H : Poincare.ParabolicSolutionGraph.Graph α T) :
  Poincare.ParabolicHolderMultiplier.forcing b (G + H) =
    Poincare.ParabolicHolderMultiplier.forcing b G + Poincare.ParabolicHolderMultiplier.forcing b H
Poincare.NearIdentityParabolicRightInverse.forcing_smul {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (c : ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T) :
  Poincare.ParabolicHolderMultiplier.forcing b (c • G) = c • Poincare.ParabolicHolderMultiplier.forcing b G
Poincare.NearIdentityParabolicRightInverse.forcing_bound {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T) :
  ‖Poincare.ParabolicHolderMultiplier.forcing b G‖ ≤ (∑ i, ∑ j, ‖b i j‖) * ‖G‖
Poincare.NearIdentityParabolicRightInverse.multiplier {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) :
  Poincare.ParabolicSolutionGraph.Graph α T →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ
Poincare.NearIdentityParabolicRightInverse.multiplier_apply {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (G : Poincare.ParabolicSolutionGraph.Graph α T) :
  (Poincare.NearIdentityParabolicRightInverse.multiplier b) G = Poincare.ParabolicHolderMultiplier.forcing b G
Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ) :
  ‖Poincare.NearIdentityParabolicRightInverse.multiplier b‖ ≤ 9 * (ε + Λ * T ^ (α / 2))
Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant {α T : ℝ} (hα : 0 < α) (hα1 : α < 1)
  (hT : 0 < T) (hT1 : T ≤ 1) :
  ‖Poincare.DuhamelSolutionOperatorCLM.duhamelOperator α T hα hα1 hT hT1‖ ≤
    Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1
Poincare.NearIdentityParabolicRightInverse.errorOp {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
  Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ
Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ) :
  ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ ≤
    9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * (ε + Λ * T ^ (α / 2))
Poincare.NearIdentityParabolicRightInverse.errorOp_small {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ)
  (hε : 9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ε ≤ 1 / 4)
  (hΛ : 9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4) :
  ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ ≤ 1 / 2 ∧
    ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ < 1
Poincare.NearIdentityParabolicRightInverse.coeff {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (i j : Fin 3) (p : ℝ × Poincare.ClosedSmoothModel 3) : ℝ
Poincare.NearIdentityParabolicRightInverse.coeff_sum {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × Poincare.ClosedSmoothModel 3) :
  ∑ i,
      ∑ j,
        Poincare.NearIdentityParabolicRightInverse.coeff b i j p *
          ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j) =
    ∑ i, ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) +
      ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.forcing b G)) p
Poincare.NearIdentityParabolicRightInverse.neumann_data_eq {α T : ℝ}
  (R : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ) (hR : ‖R‖ < 1)
  (f : Poincare.ParabolicHolder.Y α T ℝ) : ↑(Units.oneSub R hR)⁻¹ f = f + R (↑(Units.oneSub R hR)⁻¹ f)
Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two {α T : ℝ}
  (R : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicHolder.Y α T ℝ) (hR : ‖R‖ < 1) (hhalf : ‖R‖ ≤ 1 / 2) :
  ‖↑(Units.oneSub R hR)⁻¹‖ ≤ 2
Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (hR : ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ < 1) :
  Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T
Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (hR : ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ < 1) (f : Poincare.ParabolicHolder.Y α T ℝ)
  (t : ℝ) :
  t ∈ Set.Icc 0 T →
    ∀ (x : Poincare.ClosedSmoothModel 3),
      ↑(WithLp.fst ↑((Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse b hα hα1 hT hT1 hR) f).ut) (t, x) =
        ↑(WithLp.fst ↑f) (t, x) +
          ∑ i,
            ∑ j,
              Poincare.NearIdentityParabolicRightInverse.coeff b i j (t, x) *
                ((↑(WithLp.fst
                          ↑((Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse b hα hα1 hT hT1 hR) f).ddu)
                      (t, x))
                    ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                  ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
  (hR : ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ < 1)
  (hhalf : ‖Poincare.NearIdentityParabolicRightInverse.errorOp b hα hα1 hT hT1‖ ≤ 1 / 2) :
  ‖Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse b hα hα1 hT hT1 hR‖ ≤
    2 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1
Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution {α T : ℝ}
  (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ)
  (hε : 9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ε ≤ 1 / 4)
  (hΛ : 9 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4)
  (f : Poincare.ParabolicHolder.Y α T ℝ) :
  ∃ G,
    (∀ t ∈ Set.Icc 0 T,
        ∀ (x : Poincare.ClosedSmoothModel 3),
          ↑(WithLp.fst ↑G.ut) (t, x) =
            ↑(WithLp.fst ↑f) (t, x) +
              ∑ i,
                ∑ j,
                  Poincare.NearIdentityParabolicRightInverse.coeff b i j (t, x) *
                    ((↑(WithLp.fst ↑G.ddu) (t, x)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                      ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) ∧
      ‖G‖ ≤ 2 * Poincare.DuhamelSolutionOperatorCLM.boundConstant α hα hα1 * ‖f‖

EXIT 0
```

</details>

<details>
<summary>22-no-syntax-declarations.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/NearIdentityParabolicRightInverse.olean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>23-final-compile.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/NearIdentityParabolicRightInverse.olean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>24-symbol-followup.log</summary>

```text
$ rg -n congrArg|sub_eq_iff_eq_add|div_eq_iff_eq_mul|def Units.oneSub /Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean .lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean
.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean:763:theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]
.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean:943:theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]
.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean:946:theorem div_eq_iff_comm : a / b = c ↔ a / c = b := by rw [div_eq_iff_eq_mul', div_eq_iff_eq_mul]
.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean:987:  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean:1000:  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:130:  ⟨mul_left_cancel, congrArg _⟩
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:155:  ⟨mul_right_cancel, congrArg (· * a)⟩
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:1052:    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean:333:def Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
/Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean:423:theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
/Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean:1838:  congrArg f h ▸ noConfusion_of_Nat.aux (f a)
/Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean:2123:  m.rec rfl (fun _ ih => congrArg pred ih)
/Users/mjkang/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/src/lean/Init/Prelude.lean:3540:        (fun h' => h (congrArg (fun s => Array.toList (ByteArray.data (String.toByteArray s))) h')))

EXIT 0
```

</details>

<details>
<summary>25-final-compile.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean -o .lake/build/lib/lean/Poincare/Global/NearIdentityParabolicRightInverse.olean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>26-final-module-audit.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/module-audit.lean
'Poincare.DuhamelSolutionOperatorCLM.boundConstant.congr_simp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_data_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp.congr_simp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.multiplier_norm_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.exists_nearIdentity_solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse_solves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.forcing_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.neumann_norm_le_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.nearIdentityInverse._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.duhamel_norm_le_boundConstant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.NearIdentityParabolicRightInverse.errorOp._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
EXACT_MODULE_AUDIT declarations=29; every declaration has exactly the required three dependencies

EXIT 0
```

</details>

<details>
<summary>27-exact-contract.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean /tmp/near-identity-evidence/contract.lean

EXIT 0
```

</details>

<details>
<summary>28-final-source-gate.log</summary>

```text
$ env LEAN_NUM_THREADS=1 lake env lean Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 0
```

</details>

<details>
<summary>29-final-forbidden.log</summary>

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/NearIdentityParabolicRightInverse.lean

EXIT 1
```

</details>

<details>
<summary>30-final-whitespace.log</summary>

```text
$ git diff --check

EXIT 0
```

</details>

<details>
<summary>31-final-declarations.log</summary>

```text
$ rg -n ^(@\[.*\] )?(theorem|def)  Poincare/Global/NearIdentityParabolicRightInverse.lean
15:theorem forcing_add (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
27:theorem forcing_smul (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (c : ℝ)
44:theorem forcing_bound (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
60:def multiplier (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) :
68:@[simp] theorem multiplier_apply (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
73:theorem multiplier_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
86:theorem duhamel_norm_le_boundConstant (hα : 0 < α) (hα1 : α < 1)
92:def errorOp (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (hα : 0 < α) (hα1 : α < 1)
98:theorem errorOp_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
113:theorem errorOp_small (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
124:def coeff (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (i j : Fin 3) (p : ℝ ×
129:theorem coeff_sum (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
139:theorem neumann_data_eq (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)
154:theorem neumann_norm_le_two (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
168:def nearIdentityInverse (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
176:theorem nearIdentityInverse_solves (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
201:theorem nearIdentityInverse_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
217:theorem exists_nearIdentity_solution (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)

EXIT 0
```

</details>

<details>
<summary>32-proof-diff.log</summary>

```text
$ git diff a77fdab525954b5d0e02f31e6fec1ef5745df306 -- Poincare/Global/NearIdentityParabolicRightInverse.lean
diff --git a/Poincare/Global/NearIdentityParabolicRightInverse.lean b/Poincare/Global/NearIdentityParabolicRightInverse.lean
new file mode 100644
index 00000000..f7f646cc
--- /dev/null
+++ b/Poincare/Global/NearIdentityParabolicRightInverse.lean
@@ -0,0 +1,238 @@
+import Poincare.Global.DuhamelSolutionOperatorCLM
+import Poincare.Global.ParabolicHolderMultiplier
+import Poincare.Global.ParametrixNeumannCorrection
+
+noncomputable section
+
+namespace Poincare.NearIdentityParabolicRightInverse
+
+open Set ParabolicHolder ParabolicSolutionGraph ParabolicHolderMultiplier
+open DuhamelSolutionOperatorCLM
+
+variable {α T : ℝ}
+
+/-- The coefficient forcing is additive in the derivative graph. -/
+theorem forcing_add (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (G H : Graph (E := ClosedSmoothModel 3) α T) :
+    forcing b (G + H) = forcing b G + forcing b H := by
+  apply ParabolicHolder.ext
+  intro p _
+  change (∑ i, ∑ j, b i j p * (G.ddu p + H.ddu p)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
+  simp only [ContinuousLinearMap.add_apply, mul_add, Finset.sum_add_distrib,
+    ParabolicHolder.add_apply, forcing_apply]
+
+/-- The coefficient forcing respects real scalar multiplication. -/
+theorem forcing_smul (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (c : ℝ)
+    (G : Graph (E := ClosedSmoothModel 3) α T) :
+    forcing b (c • G) = c • forcing b G := by
+  apply ParabolicHolder.ext
+  intro p _
+  change (∑ i, ∑ j, b i j p * (c • G.ddu p)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
+  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ParabolicHolder.smul_apply,
+    forcing_apply, Finset.mul_sum]
+  apply Finset.sum_congr rfl
+  intro i _
+  apply Finset.sum_congr rfl
+  intro j _
+  ring
+
+/-- A bound valid without restrictions on the cylinder or exponent. -/
+theorem forcing_bound (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (G : Graph (E := ClosedSmoothModel 3) α T) :
+    ‖forcing b G‖ ≤ (∑ i, ∑ j, ‖b i j‖) * ‖G‖ := by
+  rw [forcing_eq_sum, Finset.sum_mul]
+  apply (norm_sum_le _ _).trans
+  apply Finset.sum_le_sum
+  intro i _
+  rw [Finset.sum_mul]
+  apply (norm_sum_le _ _).trans
+  apply Finset.sum_le_sum
+  intro j _
+  exact (ParabolicHolder.norm_mul_le _ _).trans
+    (mul_le_mul_of_nonneg_left
+      ((norm_entry_le G.ddu _ _ _ _).trans (norm_ddu_le G)) (norm_nonneg _))
+
+/-- The bounded multiplier on genuine derivative graphs. -/
+def multiplier (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) :
+    Graph (E := ClosedSmoothModel 3) α T →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ :=
+  ({ toFun := forcing b
+     map_add' := forcing_add b
+     map_smul' := forcing_smul b } : Graph (E := ClosedSmoothModel 3) α T →ₗ[ℝ] Y (E := ClosedSmoothModel
+         3) α T ℝ).mkContinuous
+    (∑ i, ∑ j, ‖b i j‖) (forcing_bound b)
+
+@[simp] theorem multiplier_apply (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (G : Graph (E := ClosedSmoothModel 3) α T) :
+    multiplier b G = forcing b G := rfl
+
+/-- The split estimate gives the small short-cylinder operator bound. -/
+theorem multiplier_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
+    ‖multiplier b‖ ≤ 9 * (ε + Λ * T ^ (α / 2)) := by
+  have hε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
+  have hΛ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
+  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+  intro G
+  simpa only [multiplier_apply, mul_add, add_mul, mul_assoc] using
+    norm_forcing_le b G hα hT hb hbα
+
+/-- The landed choice gives a specific uniform solution-operator constant. -/
+theorem duhamel_norm_le_boundConstant (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ boundConstant α hα hα1 :=
+  LinearMap.mkContinuous_norm_le _ (boundConstant_spec α hα hα1).1.le _
+
+/-- The coefficient perturbation following the constant-coefficient inverse. -/
+def errorOp (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) :
+    Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ :=
+  (multiplier b).comp (duhamelOperator α T hα hα1 hT hT1)
+
+/-- The operator error retains the short-time factor. -/
+theorem errorOp_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
+    ‖errorOp b hα hα1 hT hT1‖ ≤
+      9 * boundConstant α hα hα1 * (ε + Λ * T ^ (α / 2)) := by
+  have hε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
+  have hΛ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
+  have hC := (boundConstant_spec α hα hα1).1
+  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
+  intro f
+  exact norm_error_le b _ hα hT hb hbα
+    (duhamel_norm_le_boundConstant hα hα1 hT hT1) f
+
+/-- Two quarter-size contributions bound the error by one half. -/
+theorem errorOp_small (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
+    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
+    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4) :
+    ‖errorOp b hα hα1 hT hT1‖ ≤ 1 / 2 ∧ ‖errorOp b hα hα1 hT hT1‖ < 1 := by
+  have h := errorOp_norm_le b hα hα1 hT hT1 hb hbα
+  constructor <;> nlinarith only [h, hε, hΛ]
+
+/-- Identity plus the Hölder coefficient perturbation. -/
+def coeff (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ) (i j : Fin 3) (p : ℝ ×
+    ClosedSmoothModel 3) : ℝ :=
+  (if i = j then 1 else 0) + b i j p
+
+/-- Splitting the coefficient sum gives the Laplacian and perturbation forcing. -/
+theorem coeff_sum (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (G : Graph (E := ClosedSmoothModel 3) α T) (p : ℝ × ClosedSmoothModel 3) :
+    (∑ i, ∑ j, coeff b i j p * G.ddu p (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j)) =
+      (∑ i, G.ddu p (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)) + forcing b G p := by
+  classical
+  simp [coeff, add_mul, Finset.sum_add_distrib, ite_mul, forcing_apply]
+
+/-- The inverse of one minus the error solves the corrected forcing equation. -/
+theorem neumann_data_eq (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hR : ‖R‖ < 1) (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
+    (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T
+        ℝ) f =
+      f + R ((↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E :=
+          ClosedSmoothModel 3) α T ℝ) f) := by
+  have he := congrArg (fun A : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T
+      ℝ => A f) (Units.oneSub R hR).val_inv
+  change (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel
+      3) α T ℝ) f -
+    R ((↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3)
+        α T ℝ) f) = f at he
+  exact sub_eq_iff_eq_add.mp he
+
+/-- The geometric-series estimate gives a factor of two for half-size errors. -/
+theorem neumann_norm_le_two (R : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
+    T ℝ) (hR : ‖R‖ < 1)
+    (hhalf : ‖R‖ ≤ 1 / 2) :
+    ‖(↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α
+        T ℝ)‖ ≤ 2 := by
+  change ‖∑' n : ℕ, R ^ n‖ ≤ 2
+  have hs := tsum_geometric_le_of_norm_lt_one R hR
+  have h1 : ‖(1 : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ)‖ ≤ 1 :=
+      ContinuousLinearMap.norm_id_le
+  have hi : (1 - ‖R‖)⁻¹ ≤ (2 : ℝ) :=
+    (inv_le_comm₀ (by linarith) (by norm_num)).2 (by norm_num; linarith)
+  linarith
+
+/-- Correct the constant-coefficient inverse by the convergent Neumann series. -/
+def nearIdentityInverse (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Graph (E :=
+        ClosedSmoothModel 3) α T :=
+  ParametrixNeumannCorrection.correctedInverse
+    (duhamelOperator α T hα hα1 hT hT1) (errorOp b hα hα1 hT hT1) hR
+
+/-- The corrected graph solves the variable-coefficient equation at both endpoints too. -/
+theorem nearIdentityInverse_solves (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1) (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
+    ∀ t ∈ Icc 0 T, ∀ x : ClosedSmoothModel 3,
+      (nearIdentityInverse b hα hα1 hT hT1 hR f).ut (t, x) =
+        f (t, x) + ∑ i, ∑ j, coeff b i j (t, x) *
+          (nearIdentityInverse b hα hα1 hT hT1 hR f).ddu (t, x)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
+  let R := errorOp b hα hα1 hT hT1
+  let g := (↑((Units.oneSub R hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T ℝ →L[ℝ] Y (E := ClosedSmoothModel
+      3) α T ℝ) f
+  intro t ht x
+  have hg := congrArg (fun v : Y (E := ClosedSmoothModel 3) α T ℝ => v (t, x)) (neumann_data_eq R hR f)
+  change g (t, x) = f (t, x) +
+    forcing b (duhamelOperator α T hα hα1 hT hT1 g) (t, x) at hg
+  change (duhamelOperator α T hα hα1 hT hT1 g).ut (t, x) =
+    f (t, x) + ∑ i, ∑ j, coeff b i j (t, x) *
+      (duhamelOperator α T hα hα1 hT hT1 g).ddu (t, x)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j)
+  rw [duhamelOperator_solves α T hα hα1 hT hT1 g t ht x, coeff_sum, hg]
+  ring
+
+/-- The corrected solution operator has uniform norm at most twice the heat constant. -/
+theorem nearIdentityInverse_norm_le (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (hR : ‖errorOp b hα hα1 hT hT1‖ < 1)
+    (hhalf : ‖errorOp b hα hα1 hT hT1‖ ≤ 1 / 2) :
+    ‖nearIdentityInverse b hα hα1 hT hT1 hR‖ ≤ 2 * boundConstant α hα hα1 := by
+  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
+  calc
+    _ ≤ boundConstant α hα hα1 * 2 :=
+      mul_le_mul (duhamel_norm_le_boundConstant hα hα1 hT hT1)
+        (neumann_norm_le_two _ hR hhalf)
+        (norm_nonneg (↑((Units.oneSub (errorOp b hα hα1 hT hT1) hR)⁻¹) : Y (E := ClosedSmoothModel 3) α T
+            ℝ →L[ℝ] Y (E := ClosedSmoothModel 3) α T ℝ))
+        (boundConstant_spec α hα hα1).1.le
+    _ = _ := mul_comm _ _
+
+/-- Small Hölder perturbations have a zero-trace solution with a uniform graph bound. -/
+theorem exists_nearIdentity_solution (b : Fin 3 → Fin 3 → Y (E := ClosedSmoothModel 3) α T ℝ)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) {ε Λ : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
+    (hε : 9 * boundConstant α hα hα1 * ε ≤ 1 / 4)
+    (hΛ : 9 * boundConstant α hα hα1 * Λ * T ^ (α / 2) ≤ 1 / 4)
+    (f : Y (E := ClosedSmoothModel 3) α T ℝ) :
+    ∃ G : Graph (E := ClosedSmoothModel 3) α T,
+      (∀ t ∈ Icc 0 T, ∀ x : ClosedSmoothModel 3,
+        G.ut (t, x) = f (t, x) +
+          ∑ i, ∑ j, coeff b i j (t, x) * G.ddu (t, x)
+        (EuclideanSpace.basisFun (Fin 3) ℝ i)
+        (EuclideanSpace.basisFun (Fin 3) ℝ j)) ∧
+      ‖G‖ ≤ 2 * boundConstant α hα hα1 * ‖f‖ := by
+  obtain ⟨hhalf, hR⟩ := errorOp_small b hα hα1 hT hT1 hb hbα hε hΛ
+  refine ⟨nearIdentityInverse b hα hα1 hT hT1 hR f,
+    nearIdentityInverse_solves b hα hα1 hT hT1 hR f, ?_⟩
+  exact ((nearIdentityInverse b hα hα1 hT hT1 hR).le_opNorm f).trans
+    (mul_le_mul_of_nonneg_right
+      (nearIdentityInverse_norm_le b hα hα1 hT hT1 hR hhalf) (norm_nonneg f))
+
+end Poincare.NearIdentityParabolicRightInverse

EXIT 0
```

</details>

<details>
<summary>33-proof-commits.log</summary>

```text
$ git log --format=fuller a77fdab525954b5d0e02f31e6fec1ef5745df306..HEAD
commit 4fbea6a4a06473047c96a720c8cca2875c91d614
Author:     Myeongjin Kang <mj.kang@hey.com>
AuthorDate: Tue Sep 15 10:19:35 2026 -0700
Commit:     Myeongjin Kang <mj.kang@hey.com>
CommitDate: Tue Sep 15 10:19:35 2026 -0700

    Use explicit types for exact module-wide dependency audit

commit 67565c7e31f97bfc30c04b7fa9ef833df4687c93
Author:     Myeongjin Kang <mj.kang@hey.com>
AuthorDate: Tue Sep 15 10:16:20 2026 -0700
Commit:     Myeongjin Kang <mj.kang@hey.com>
CommitDate: Tue Sep 15 10:16:20 2026 -0700

    Prove existence of near-identity parabolic solutions

commit 046d3e485deae971478cf6548994688929576bfb
Author:     Myeongjin Kang <mj.kang@hey.com>
AuthorDate: Tue Sep 15 10:15:04 2026 -0700
Commit:     Myeongjin Kang <mj.kang@hey.com>
CommitDate: Tue Sep 15 10:15:04 2026 -0700

    Prove Neumann corrected parabolic inverse and its norm bound

commit c3acf139278f34cfb74cf131076d6ebbe86e8613
Author:     Myeongjin Kang <mj.kang@hey.com>
AuthorDate: Tue Sep 15 10:12:59 2026 -0700
Commit:     Myeongjin Kang <mj.kang@hey.com>
CommitDate: Tue Sep 15 10:12:59 2026 -0700

    Bound the parabolic error operator below one

commit 25978554267be6cd080d350a240f1f74ad98f383
Author:     Myeongjin Kang <mj.kang@hey.com>
AuthorDate: Tue Sep 15 10:11:20 2026 -0700
Commit:     Myeongjin Kang <mj.kang@hey.com>
CommitDate: Tue Sep 15 10:11:20 2026 -0700

    Prove bounded linear parabolic coefficient multiplier

EXIT 0
```

</details>

<details>
<summary>project-symbols.log</summary>

```text
Poincare/Global/ParametrixNeumannCorrection.lean:22:def correctedInverse (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y) (hR : ‖R‖ < 1) : Y →L[ℝ] X :=
Poincare/Global/DuhamelSolutionOperatorCLM.lean:49:def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
Poincare/Global/DuhamelSolutionOperatorCLM.lean:53:theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
Poincare/Global/DuhamelSolutionOperatorCLM.lean:133:def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
Poincare/Global/DuhamelSolutionOperatorCLM.lean:157:theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
Poincare/Global/ParabolicSolutionGraph.lean:113:theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
Poincare/Global/ParabolicHolderMultiplier.lean:95:theorem norm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
Poincare/Global/ParabolicHolderMultiplier.lean:154:def forcing (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (G : Graph («E» := E) α T) :
Poincare/Global/ParabolicHolderMultiplier.lean:168:@[simp] theorem forcing_apply (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderMultiplier.lean:173:theorem forcing_eq_sum (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderMultiplier.lean:203:theorem norm_forcing_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderMultiplier.lean:224:theorem norm_error_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderMultiplier.lean:245:theorem error_small (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderSpace.lean:217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
Poincare/Global/ParabolicHolderSpace.lean:327:theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
Poincare/Global/ParabolicHolderSpace.lean:331:theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
Poincare/Global/ParabolicHolderSpace.lean:390:theorem norm_mul_le (f g : Y (E := E) α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
```

</details>

<details>
<summary>verified-symbol-locations.log</summary>

```text
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) add_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:60:theorem add_apply (g₁ g₂ : PolynomialModule R M) (a : ℕ) : (g₁ + g₂) a = g₁ a + g₂ a :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:306:theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:803:theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:184:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:120:theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:834:theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
Poincare/Global/ParabolicHolderSpace.lean:208:@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:105:theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:328:theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:199:@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:328:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:182:theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:303:theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:254:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:777:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:291:theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:285:@[simp] lemma add_apply (ψ φ : AddChar A M) (a : A) : (ψ + φ) a = ψ a * φ a := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:72:theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (p + q) n = p n + q n := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:206:theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:138:lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:115:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:214:theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Finsupp.lean:56:lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:393:theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:289:@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:173:theorem add_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:156:theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:607:theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:199:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:234:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:111:theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:229:theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:130:theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:457:theorem add_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q + Q') x = Q x + Q' x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:282:theorem add_apply : (f + f') v = f v + f' v :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:431:theorem add_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:189:theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:140:lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:488:theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:161:theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:179:theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:208:theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:417:theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:199:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:125:theorem add_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:305:theorem add_apply (v w : VectorMeasure α M) (i : Set α) : (v + w) i = v i + w i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:70:theorem add_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ + m₂) s = m₁ s + m₂ s :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean:215:@[simp] lemma add_apply (f g : StieltjesFunction R) (x : R) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Probability/Kernel/Defs.lean:99:@[simp] lemma add_apply (κ η : Kernel α β) (a : α) : (κ + η) a = κ a + η a := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:884:theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) comp(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Computability/PartrecBasis.lean:98:theorem comp' {n m f g} (hf : @Partrec' m f) (hg : @Vec n m g) : Partrec' fun v => f (g v) :=
.lake/packages/mathlib/Mathlib/Computability/PartrecBasis.lean:101:theorem comp₁ {n} (f : ℕ →. ℕ) {g : List.Vector ℕ n → ℕ} (hf : @Partrec' 1 fun v => f v.head)
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean:178:def comp (hnp : β →*₀ γ) (hmn : α →*₀ β) : α →*₀ γ where
.lake/packages/mathlib/Mathlib/Algebra/Quandle.lean:344:def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ where
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:122:def comp (f : B →⋆* C) (g : A →⋆* B) : A →⋆* C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:180:def comp (f : B →⋆ₙₐ[R] C) (g : A →⋆ₙₐ[R] B) : A →⋆ₙₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:415:def comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:163:def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:296:def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:247:def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:352:def comp {K : Type*} [Add K] {c : K} (g : H →+c[b, c] K) (f : G →+c[a, b] H) :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean:514:protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
.lake/packages/mathlib/Mathlib/Computability/Primrec/Basic.lean:216:theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:655:theorem comp' {n m f g} (hf : @Primrec' m f) (hg : @Vec n m g) : Primrec' fun v => f (g v) :=
.lake/packages/mathlib/Mathlib/Computability/Primrec/List.lean:658:theorem comp₁ (f : ℕ → ℕ) (hf : @Primrec' 1 fun v => f v.head) {n g} (hg : @Primrec' n g) :
.lake/packages/mathlib/Mathlib/Algebra/Vertex/HVertexOperator.lean:138:def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:426:def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:762:def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
.lake/packages/mathlib/Mathlib/Logic/Function/CompTypeclasses.lean:54:theorem comp {M N P : Type*}
.lake/packages/mathlib/Mathlib/Computability/Partrec.lean:420:nonrec theorem comp {f : β →. σ} {g : α → β} (hf : Partrec f) (hg : Computable g) :
.lake/packages/mathlib/Mathlib/Computability/Partrec.lean:445:nonrec theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} (hf : Partrec₂ f) (hg : Computable g)
.lake/packages/mathlib/Mathlib/Algebra/Ring/CompTypeclasses.lean:177:theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:212:def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:541:def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/Homotopy.lean:209:def comp {C₁ C₂ C₃ : HomologicalComplex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
.lake/packages/mathlib/Mathlib/Logic/Function/Conjugate.lean:170:theorem comp {f' : β → γ} {gc : γ → γ → γ} (hf' : Semiconj₂ f' gb gc) (hf : Semiconj₂ f ga gb) :
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomologicalComplex.lean:237:def comp (A B C : HomologicalComplex V c) (φ : Hom A B) (ψ : Hom B C) : Hom A C where
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:175:def comp (g f : CentroidHom α) : CentroidHom α :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:220:def comp {n₁ n₂ n₁₂ : ℤ} (z₁ : Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:305:def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Eval/Defs.lean:373:def comp (p q : R[X]) : R[X] :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/LeftHomology.lean:311:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/SnakeLemma.lean:446:def comp (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Monic.lean:119:lemma comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Homology.lean:266:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.HomologyData}
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/RightHomology.lean:406:def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:130:noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
.lake/packages/mathlib/Mathlib/Control/Traversable/Basic.lean:162:def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:211:def comp (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) : IntertwiningMap ρ τ where
.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Preadditive.lean:492:def comp (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂) :
.lake/packages/mathlib/Mathlib/Data/Matrix/Composition.lean:37:def comp : Matrix I J (Matrix K L R) ≃ Matrix (I × K) (J × L) R where
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:486:def comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Invariant.lean:182:protected lemma comp {p : Submodule R M} {g : End R M}
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:252:lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
Poincare/Global/SemilinearHeatBUCLocalDataOperations.lean:148:def comp {N M : BUC → BUC}
.lake/packages/mathlib/Mathlib/Dynamics/PeriodicPts/Defs.lean:136:theorem comp {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:807:theorem comp (hf' : LeftInvOn f' f s) (hg' : LeftInvOn g' g t) (hf : MapsTo f s t) :
.lake/packages/mathlib/Mathlib/Data/Set/Function.lean:866:theorem comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g p) (g'pt : MapsTo g' p t) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/Basic.lean:148:def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/Basic.lean:153:def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:114:def comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m where
.lake/packages/mathlib/Mathlib/Data/PFunctor/Multivariate/Basic.lean:121:def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
.lake/packages/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean:99:protected theorem comp {g : β → γ} {f : α → β} (hg : MeasurePreserving g μb μc)
.lake/packages/mathlib/Mathlib/Data/Rel.lean:148:def comp (R : SetRel α β) (S : SetRel β γ) : SetRel α γ := {(a, c) | ∃ b, a ~[R] b ∧ b ~[S] c}
.lake/packages/mathlib/Mathlib/Dynamics/FixedPoints/Basic.lean:37:protected theorem comp (hf : IsFixedPt f x) (hg : IsFixedPt g x) : IsFixedPt (f ∘ g) x :=
.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean:169:lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:231:protected def comp (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
.lake/packages/mathlib/Mathlib/Probability/Process/Adapted.lean:207:protected theorem comp {t : ι → Ω → ι} [TopologicalSpace ι] [BorelSpace ι] [PseudoMetrizableSpace ι]
.lake/packages/mathlib/Mathlib/SetTheory/Ordinal/FundamentalSequence.lean:87:protected theorem comp (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:277:def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
.lake/packages/mathlib/Mathlib/Probability/Kernel/Composition/Comp.lean:50:noncomputable def comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:332:def comp (g : E₂ →ₛₗᵢ[σ₂₃] E₃) (f : E →ₛₗᵢ[σ₁₂] E₂) : E →ₛₗᵢ[σ₁₃] E₃ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:149:theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Conformal.lean:79:theorem comp (hg : IsConformalMap g) (hf : IsConformalMap f) : IsConformalMap (g.comp f) := by
.lake/packages/mathlib/Mathlib/Data/QPF/Univariate/Basic.lean:459:def comp : QPF (Functor.Comp F₂ F₁) where
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiffMap.lean:83:def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
.lake/packages/mathlib/Mathlib/Data/TypeVec.lean:75:def comp (g : β ⟹ γ) (f : α ⟹ β)
.lake/packages/mathlib/Mathlib/Data/PFun.lean:476:def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:222:def comp (g : P₂ →ᵃⁱ[𝕜] P₃) (f : P →ᵃⁱ[𝕜] P₂) : P →ᵃⁱ[𝕜] P₃ :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:287:def comp.smul (g : N → M) (n : N) (a : α) : α := g n • a
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:297:abbrev comp (g : N → M) : SMul N α where smul := SMul.comp.smul g
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Presheaf.lean:191:def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Presheaf C) :
.lake/packages/mathlib/Mathlib/Probability/IdentDistrib.lean:109:protected theorem comp {u : γ → δ} (h : IdentDistrib f g μ ν) (hu : Measurable u) :
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Stalks.lean:210:theorem comp (ℱ : X.Presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/PresheafedSpace.lean:102:def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:129:def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/Stalks.lean:120:theorem comp {X Y Z : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/CompTypeclasses.lean:87:theorem comp {φ : M →* N} {ψ : N →* P} :
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:136:def comp (g : Copy B C) (f : Copy A B) : Copy A C := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:136:def comp (f : Q →ᴬ[R] Q₂) (g : P →ᴬ[R] Q) : P →ᴬ[R] Q₂ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:167:def comp (f : β →*₀o γ) (g : α →*₀o β) : α →*₀o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:243:protected def comp (f : β →+*o γ) (g : α →+*o β) : α →+*o γ :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:363:def comp (f : β →*o γ) (g : α →*o β) : α →*o γ :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:420:abbrev comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Maps.lean:530:abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:281:def comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:348:theorem comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) :
.lake/packages/mathlib/Mathlib/Topology/Homotopy/TopCat/Basic.lean:74:abbrev comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:583:def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ) where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/ContinuousInverse.lean:141:lemma comp {g : F →L[R] G} (hg : g.HasLeftInverse) (hf : f.HasLeftInverse) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/ContinuousInverse.lean:306:lemma comp {g : F →L[R] G} (hg : g.HasRightInverse) (hf : f.HasRightInverse) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ContinuousMapZero.lean:82:def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:370:def comp (G : β → γ) {C : ℝ≥0} (H : LipschitzWith C G) (f : α →ᵇ β) : α →ᵇ γ :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Basic.lean:113:def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:562:def comp (f : C_c(γ, δ)) (g : β →co γ) : C_c(β, δ) where
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean:139:def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean:78:protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Prefunctor.lean:75:def comp {U : Type*} [Quiver U] {V : Type*} [Quiver V] {W : Type*} [Quiver W]
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Path.lean:88:def comp {a b : V} : ∀ {c}, Path a b → Path b c → Path a c
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean:114:theorem comp {Kg : ℝ≥0} {g : β → γ} (hg : AntilipschitzWith Kg g) {Kf : ℝ≥0} {f : α → β}
.lake/packages/mathlib/Mathlib/Topology/Category/TopPair.lean:192:def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:555:protected def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:721:theorem comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
.lake/packages/mathlib/Mathlib/Algebra/LieRinehartAlgebra/Defs.lean:118:protected def comp (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (g : L₂ →ₗ⁅σ₂₃⁆ L₃) : L₁ →ₗ⁅σ₂₃.comp σ₁₂⁆ L₃ where
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:327:def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:345:def comp (g : B →A[R] C) (f : A →A[R] B) : A →A[R] C :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:106:theorem comp {Cg rg : ℝ≥0} {g : Y → Z} {t : Set Y} (hg : HolderOnWith Cg rg g t) {Cf rf : ℝ≥0}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Holder.lean:259:theorem comp {Cg rg : ℝ≥0} {g : Y → Z} (hg : HolderWith Cg rg g) {Cf rf : ℝ≥0} {f : X → Y}
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/ReflQuiver.lean:101:def comp {U : Type*} [ReflQuiver U] {V : Type*} [ReflQuiver V] {W : Type*} [ReflQuiver W]
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:121:theorem comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Dilation.lean:288:def comp (g : β →ᵈ γ) (f : α →ᵈ β) : α →ᵈ γ where
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:108:protected theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) :
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:118:theorem comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/DiffContOnCl.lean:56:theorem comp {g : G → E} {t : Set G} (hf : DiffContOnCl 𝕜 f s) (hg : DiffContOnCl 𝕜 g t)
.lake/packages/mathlib/Mathlib/Topology/Hom/Open.lean:120:def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:152:def comp (g : B →ₜ* C) (f : A →ₜ* B) : A →ₜ* C :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Hom.lean:116:def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M := B.compl₁₂ l r
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:228:protected theorem comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f)
.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean:328:protected theorem comp {g : β → γ} {t : Set β} {Kg : ℝ≥0} (hg : LipschitzOnWith Kg g t)
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Isometry.lean:101:def comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) : B₁ →bᵢ B₃ where
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:453:def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
.lake/packages/mathlib/Mathlib/Topology/Spectral/Hom.lean:159:def comp (f : SpectralMap β γ) (g : SpectralMap α β) : SpectralMap α γ :=
.lake/packages/mathlib/Mathlib/Topology/Maps/OpenQuotient.lean:49:theorem comp {g : Y → Z} (hg : IsOpenQuotientMap g) (hf : IsOpenQuotientMap f) :
.lake/packages/mathlib/Mathlib/Topology/IsLocalHomeomorph.lean:153:protected theorem comp (hg : IsLocalHomeomorphOn g t) (hf : IsLocalHomeomorphOn f s)
.lake/packages/mathlib/Mathlib/Topology/IsLocalHomeomorph.lean:242:protected theorem comp (hg : IsLocalHomeomorph g) (hf : IsLocalHomeomorph f) :
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:200:protected lemma comp (hg : IsEmbedding g) (hf : IsEmbedding f) : IsEmbedding (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Maps/Basic.lean:282:protected lemma comp (hg : IsCoinducing g) (hf : IsCoinducing f) : IsCoinducing (g.comp f) where
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:687:def comp {ρ : R →+* T} [RingHomCompTriple σ τ ρ] (g : F →ₛₗ.[τ] G) (f : E →ₛₗ.[σ] F)
.lake/packages/mathlib/Mathlib/Topology/Homeomorph/Defs.lean:488:lemma comp {g : Y → Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) : IsHomeomorph (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Basic.lean:143:def comp (f : β →Co γ) (g : α →Co β) : ContinuousOrderHom α γ :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:165:def comp (g : PseudoEpimorphism β γ) (f : PseudoEpimorphism α β) : PseudoEpimorphism α γ :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:277:def comp (g : EsakiaHom β γ) (f : EsakiaHom α β) : EsakiaHom α γ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Hom.lean:109:def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Hom.lean:320:def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:194:theorem comp {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiffHolder/Pointwise.lean:200:theorem comp₂_of_differentiableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
.lake/packages/mathlib/Mathlib/Topology/Bornology/Hom.lean:140:def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:158:lemma comp {v : Filter κ} {ns : κ → ι} (hg : TendstoInMeasure μ f l g)
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:576:def comp (Q : QuadraticMap R N P) (f : M →ₗ[R] N) : QuadraticMap R M P where
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:288:def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean:94:def comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) : Q₁ →qᵢ Q₃ where
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:334:def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:458:def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/ElementaryMaps.lean:184:def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
.lake/packages/mathlib/Mathlib/ModelTheory/LanguageMap.lean:112:def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean:300:theorem comp₂_left (hf : HasCompactMulSupport f)
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:471:def comp (g : F →SWOT[σ₂₃] G) (f : E →SWOT[σ₁₂] F) : E →SWOT[σ₁₃] G :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:370:def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:327:def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:415:def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:94:theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Conformal/NormedSpace.lean:127:theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:82:theorem comp (hg : MeasurableEmbedding g) (hf : MeasurableEmbedding f) :
.lake/packages/mathlib/Mathlib/Order/Filter/TendstoCofinite.lean:72:lemma comp [TendstoCofinite g] [TendstoCofinite f] : TendstoCofinite (g ∘ f) :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:305:def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:410:def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:109:lemma comp (h : EventuallyConst f l) (g : β → γ) : EventuallyConst (g ∘ f) l := h.map g
.lake/packages/mathlib/Mathlib/Order/Filter/EventuallyConst.lean:122:lemma comp₂ {g : α → γ} (hf : EventuallyConst f l) (op : β → γ → δ) (hg : EventuallyConst g l) :
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:227:def comp (f : SupHom β γ) (g : SupHom α β) : SupHom α γ where
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:420:def comp (f : LatticeHom β γ) (g : LatticeHom α β) : LatticeHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:276:def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ where
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:405:def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:233:def comp (f : TopHom β γ) (g : TopHom α β) :
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:417:def comp (f : BoundedOrderHom β γ) (g : BoundedOrderHom α β) : BoundedOrderHom α γ :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean:109:def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c) (g : SimplexCategory.Hom a b) :
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:264:def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:419:def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:328:def comp (g : β →o γ) (f : α →o β) : α →o γ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/SmallShiftedHom.lean:150:noncomputable def comp {a b c : M} [HasSmallLocalizedShiftedHom.{w} W M X Y]
.lake/packages/mathlib/Mathlib/Order/OmegaCompletePartialOrder.lean:604:def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/SmallHom.lean:155:noncomputable def comp {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y]
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:144:protected def comp (g : s →r t) (f : r →r s) : r →r t :=
.lake/packages/mathlib/Mathlib/Order/IsNormal.lean:104:theorem comp (hg : IsNormal g) (hf : IsNormal f) : IsNormal (g ∘ f) := by
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/RelativeMorphism.lean:133:def comp (f' : RelativeMorphism B C ψ) {φψ : (A : SSet) ⟶ (C : SSet)}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/LocalizerMorphism.lean:71:def comp (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃) :
.lake/packages/mathlib/Mathlib/Order/Booleanisation.lean:55:@[match_pattern] def comp : α → Booleanisation α := Sum.inr
.lake/packages/mathlib/Mathlib/Order/OrdContinuous.lean:80:theorem comp (hg : LeftOrdContinuous g) (hf : LeftOrdContinuous f) : LeftOrdContinuous (g ∘ f) :=
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/DPMorphism.lean:90:theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
.lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/DPMorphism.lean:223:protected def comp (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Basic.lean:435:noncomputable def comp : Presentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:261:noncomputable def comp : PreSubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Presentation/Submersive.lean:539:noncomputable def comp : SubmersivePresentation R T (ι' ⊕ ι) (σ' ⊕ σ) where
.lake/packages/mathlib/Mathlib/RingTheory/Extension/Generators.lean:218:def comp [Algebra S T] [IsScalarTower R S T]
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Pointed.lean:73:def comp {X Y Z : Pointed.{u}} (f : Pointed.Hom X Y) (g : Pointed.Hom Y Z) : Pointed.Hom X Z :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Bipointed.lean:70:def comp {X Y Z : Bipointed.{u}} (f : Bipointed.Hom X Y) (g : Bipointed.Hom Y Z) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Pairwise.lean:84:def comp : ∀ {o₁ o₂ o₃ : Pairwise ι} (_ : Hom o₁ o₂) (_ : Hom o₂ o₃), Hom o₁ o₃
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/Composition.lean:62:lemma comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:285:def comp₀ [W.HasLeftCalculusOfFractions] {X Y Z : C}
.lake/packages/mathlib/Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:292:lemma comp₀_rel [W.HasLeftCalculusOfFractions]
.lake/packages/mathlib/Mathlib/CategoryTheory/Join/Basic.lean:79:def comp : ∀ {x y z : C ⋆ D}, Hom x y → Hom y z → Hom x z
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FunctorHom.lean:79:def comp {M : C ⥤ D} (f : HomObj F G A) (g : HomObj G M A) : HomObj F M A where
.lake/packages/mathlib/Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean:178:def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:82:def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:270:def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1
.lake/packages/mathlib/Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean:114:def comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:253:def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:780:def comp [κ : MonoidHom.CompTriple φ ψ χ]
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:92:def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
.lake/packages/mathlib/Mathlib/CategoryTheory/DifferentialObject.lean:72:def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/CategoryTheory/Types/Basic.lean:272:theorem comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/FullyFaithful.lean:222:def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
.lake/packages/mathlib/Mathlib/RingTheory/AlgebraicIndependent/Defs.lean:87:theorem comp (f : ι' → ι) (hf : Function.Injective f) : AlgebraicIndependent R (x ∘ f) := by
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:118:theorem comp [FormallyEtale R A] [FormallyEtale A B] :
.lake/packages/mathlib/Mathlib/RingTheory/Etale/Basic.lean:239:theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Basic.lean:117:def comp (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/ShiftedHom.lean:40:noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Basic.lean:576:def comp : F ⋙ H ⊣ I ⋙ G :=
.lake/packages/mathlib/Mathlib/CategoryTheory/WithTerminal/Basic.lean:88:def comp : ∀ {X Y Z : WithTerminal C}, Hom X Y → Hom Y Z → Hom X Z
.lake/packages/mathlib/Mathlib/CategoryTheory/WithTerminal/Basic.lean:493:def comp : ∀ {X Y Z : WithInitial C}, Hom X Y → Hom Y Z → Hom X Z
.lake/packages/mathlib/Mathlib/CategoryTheory/Shift/SingleFunctors.lean:131:def comp (α : Hom F G) (β : Hom G H) : Hom F H where
.lake/packages/mathlib/Mathlib/CategoryTheory/Linear/Basic.lean:194:def comp (X Y Z : C) : (X ⟶ Y) →ₗ[S] (Y ⟶ Z) →ₗ[S] X ⟶ Z where
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean:408:theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
.lake/packages/mathlib/Mathlib/RingTheory/Smooth/Basic.lean:567:theorem comp [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B] : Smooth R B where
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean:81:def comp {𝒵 : BasedCategory.{v₄, u₄} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴 ⥤ᵇ 𝒵) : 𝒳 ⥤ᵇ 𝒵 where
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean:175:def comp {F G H : 𝒳 ⥤ᵇ 𝒴} (α : BasedNatTrans F G) (β : BasedNatTrans G H) : BasedNatTrans F H where
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/AlgHom.lean:175:@[simps!] def comp (g : ℬ →ₐᵍ[R] 𝒞) (f : 𝒜 →ₐᵍ[R] ℬ) : 𝒜 →ₐᵍ[R] 𝒞 :=
.lake/packages/mathlib/Mathlib/RingTheory/FinitePresentation.lean:438:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
.lake/packages/mathlib/Mathlib/RingTheory/FinitePresentation.lean:536:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation)
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/RingHom.lean:202:def comp (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) : 𝒜 →+*ᵍ 𝒞 where
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Smooth.lean:103:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.comp f).Smooth := by
.lake/packages/mathlib/Mathlib/Tactic/CategoryTheory/Bicategory/Datatypes.lean:425:def comp? (e : Expr) : BicategoryM (Option (Mor₁ × Mor₁)) := do
.lake/packages/mathlib/Mathlib/Tactic/CategoryTheory/Monoidal/Datatypes.lean:419:def comp? (e : Expr) : MonoidalM (Option (Mor₁ × Mor₁)) := do
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:468:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite := by
.lake/packages/mathlib/Mathlib/RingTheory/Finiteness/Basic.lean:495:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/EssFiniteType.lean:23:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.EssFiniteType) (hg : g.EssFiniteType) :
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Factorization.lean:94:def comp : MorphismProperty C := fun _ _ f => Nonempty (MapFactorizationData W₁ W₂ f)
.lake/packages/mathlib/Mathlib/RingTheory/PolynomialLaw/Basic.lean:267:def comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : M →ₚₗ[R] P where
.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:251:theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FiniteType) (hf : f.FiniteType) :
.lake/packages/mathlib/Mathlib/RingTheory/FiniteType.lean:297:theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FiniteType) (hf : f.FiniteType) :
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean:250:@[simps!] def comp (φ₁ : B →ₐc[R] C) (φ₂ : A →ₐc[R] B) : A →ₐc[R] C :=
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/OpenImmersion.lean:91:lemma comp (hf : f.IsStandardOpenImmersion) (hg : g.IsStandardOpenImmersion) :
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Flat.lean:45:lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
.lake/packages/mathlib/Mathlib/RingTheory/RingHom/Unramified.lean:48:lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyUnramified)
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Hom.lean:215:@[simps!] def comp (φ₁ : B →ₗc[R] C) (φ₂ : A →ₗc[R] B) : A →ₗc[R] C :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monad/Algebra.lean:77:def comp {P Q R : Algebra T} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
.lake/packages/mathlib/Mathlib/CategoryTheory/Monad/Algebra.lean:288:def comp {P Q R : Coalgebra G} (f : Hom P Q) (g : Hom Q R) : Hom P R where f := f.f ≫ g.f
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:216:theorem comp [FormallyUnramified R A] [FormallyUnramified A B] :
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:391:theorem comp [Algebra A B] [IsScalarTower R A B] [Unramified R A] [Unramified A B] :
.lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Basic.lean:317:def comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [EnrichedCategory V C]
.lake/packages/mathlib/Mathlib/CategoryTheory/Sigma/Basic.lean:46:def comp : ∀ {X Y Z : Σ i, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
.lake/packages/mathlib/Mathlib/CategoryTheory/Action/Basic.lean:109:def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
.lake/packages/mathlib/Mathlib/CategoryTheory/Quotient.lean:152:def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg ↦
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Grp.lean:161:lemma comp' {A₁ A₂ A₃ : Grp C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Adjunction/Basic.lean:159:def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mon.lean:553:def comp {M N O : Mon C} (f : Hom M N) (g : Hom N O) : Hom M O where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Comon_.lean:171:def comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where
.lake/packages/mathlib/Mathlib/CategoryTheory/Square.lean:104:def comp {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃) : Hom sq₁ sq₃ where
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/Categorical/CatCospanTransform.lean:85:def comp
.lake/packages/mathlib/Mathlib/CategoryTheory/Grothendieck.lean:111:def comp {X Y Z : Grothendieck F} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mod.lean:175:def comp {M N O : Mod D A} (f : Hom M N) (g : Hom N O) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean:81:lemma comp₂_iso_hom {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/LocallyGroupoid.lean:85:lemma comp₂_iso_inv {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Bimod.lean:124:def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictlyUnitary.lean:162:def comp (F : StrictlyUnitaryLaxFunctor B C)
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictlyUnitary.lean:351:def comp (F : StrictlyUnitaryPseudofunctor B C)
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Prelax.lean:92:def comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxFunctorStruct B D where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Prelax.lean:146:def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Lax.lean:168:def comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Pseudofunctor.lean:154:def comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/Oplax.lean:172:def comp (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D) : B ⥤ᵒᵖᴸ D where
.lake/packages/mathlib/Mathlib/CategoryTheory/Bicategory/Functor/StrictPseudofunctor.lean:134:def comp (F : StrictPseudofunctor B C)
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:382:def comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y ⊗ (ihom y).obj z ⟶ (ihom x).obj z :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) le_opNorm(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:239:theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:212:theorem le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.1.le_opNorm m
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:380:theorem le_opNorm (f : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:207:theorem le_opNorm (x : V₁) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := by
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:348:theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Bilinear.lean:49:theorem mul_apply' (a b : A) : mul R A a b = a * b :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:653:theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:933:@[simp] theorem mul_apply (f g : R ≃⋆ₐ[S] R) (x : R) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:67:lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:438:lemma mul_apply [DecidableEq M] (x y : R[M]) (m : M) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Basic.lean:83:lemma mul_apply (x y : R) : mul x y = x * y := rfl
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:310:theorem mul_apply (f g : CentroidHom α) (a : α) : (f * g) a = f (g a) :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Aut.lean:80:theorem mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:298:theorem mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:307:theorem mul_apply' [Fintype m] [Mul α] [AddCommMonoid α] {M : Matrix l m α} {N : Matrix m n α}
Poincare/Global/ParabolicHolderSpace.lean:387:@[simp] theorem mul_apply (f g : Y (E := E) α T ℝ) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean:59:theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Basic.lean:110:@[simp] lemma mul_apply (f : M ≃ₗ[R] M) (g : M ≃ₗ[R] M) (x : M) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Data/Finsupp/Pointwise.lean:50:theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:457:@[simp] lemma mul_apply (f g : IntertwiningMap ρ ρ) (v : V) : (f * g) v = f (g v) := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:376:theorem mul_apply (f g : A →A[R] A) (x : A) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:45:theorem mul_apply' (x y : R) : mul 𝕜 R x y = x * y :=
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:284:@[simp] lemma mul_apply (ψ φ : AddChar A M) (a : A) : (ψ * φ) a = ψ a * φ a := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:244:theorem mul_apply (f g : A →ₜ* E) (a : A) : (f * g) a = f a * g a := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:37:lemma mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:57:lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:270:theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:224:theorem mul_apply (f g : α →*₀o β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:448:theorem mul_apply [IsOrderedMonoid β] (f g : α →*o β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:566:theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Basic.lean:93:theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Basic.lean:156:theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:101:theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:679:theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:422:theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:510:theorem mul_apply [Mul R] [BoundedMul R] [ContinuousMul R] (f g : α →ᵇ R) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:199:theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:220:lemma mul_apply [Π i, Mul (R i)] [∀ i, MulMemClass (S i) (R i)]
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:64:theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:58:theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:182:theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C₀(α, β)) : (f * g) x = f x * g x :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:586:theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:304:theorem mul_apply {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:307:theorem mul_apply' {l : Type*} [Fintype m] [Mul A] [AddCommMonoid A] {M : CStarMatrix l m A}
.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean:165:@[simp] theorem mul_apply : ⇑(A * B) = A.1 * B.1 := rfl
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:292:@[simp] lemma mul_apply (f g : F →WOT[𝕜₂] F) (x : F) : (f * g) x = f (g x) := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:234:theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:262:theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:167:theorem mul_apply (f g : Poly α) (x : α → ℕ) : (f * g) x = f x * g x := rfl
.lake/packages/mathlib/Mathlib/Dynamics/Circle/RotationNumber/TranslationNumber.lean:181:theorem mul_apply (x) : (f * g) x = f (g x) :=
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean:296:theorem mul_apply (φ ψ : A →ₐc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:145:theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:237:theorem mul_apply (n : ℕ) (f g : AdicCauchySequence I R) : (f * g) n = f n * g n :=
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Hom.lean:258:theorem mul_apply (φ ψ : A →ₗc[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:210:@[simp] lemma mul_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:71:lemma mul_apply (γ₁ γ₂ : ZeroCochain G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i := rfl
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_id_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:230:theorem norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:362:theorem norm_id_le : ‖(id V : NormedAddGroupHom V V)‖ ≤ 1 :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) one_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:287:theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:344:theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Notation/Pi/Defs.lean:46:lemma one_apply (i : ι) : (1 : ∀ i, M i) i = 1 := rfl
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:649:theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:158:theorem one_apply (a : A) : (1 : A →⋆* A) a = a :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:199:theorem one_apply (a : A) : (1 : A →⋆ₙ+* A) a = a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:399:theorem one_apply (x : L₁) : (1 : L₁ →ₗ⁅R⁆ L₁) x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:578:theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:218:theorem one_apply (a : A) : (1 : A →⋆ₙₐ[R] A) a = a :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:935:@[simp] theorem one_apply (x : R) : (1 : R ≃⋆ₐ[S] R) x = x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:209:theorem one_apply (G H : GrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:448:theorem one_apply (G H : CommGrpCat) (g : G) : ((1 : G ⟶ H) : G → H) g = 1 :=
.lake/packages/mathlib/Mathlib/Data/Matrix/Diagonal.lean:236:theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean:56:theorem one_apply (x : M) : (1 : Module.End R M) x = x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:193:@[simp] lemma one_apply (a : A) : (1 : AddChar A M) a = 1 := rfl
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:302:theorem one_apply (a : α) : (1 : CentroidHom α) a = a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:249:theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:417:theorem one_apply (a : α) : (1 : α →*o β) a = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Aut.lean:74:theorem one_apply (x : R) : (1 : R ≃+* R) x = x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:36:lemma one_apply (a : α) : (1 : r →r r) a = a := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/Group/End.lean:56:lemma one_apply (a : α) : (1 : r ↪r r) a = a := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:104:theorem one_apply (x) : (1 : Perm α) x = x :=
.lake/packages/mathlib/Mathlib/Algebra/Group/End.lean:683:theorem one_apply (m : M) : (1 : MulAut M) m = m :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:195:@[simp] lemma one_apply (a b : α) : (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0 := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean:169:@[simp] theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:268:theorem one_apply {i j} : (1 : CStarMatrix n n A) i j = if i = j then 1 else 0 := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:155:theorem one_apply (x) : (1 : Poly α) x = 1 := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:101:theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:251:lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1 := one_apply_coe hx.unit
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:293:@[simp] lemma one_apply (x : F) : (1 : F →WOT[𝕜₂] F) x = x := rfl
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:769:theorem one_apply (a : A) : (1 : A →*[M] A) a = a :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:333:theorem one_apply (x : A) : (1 : A →A[R] A) x = x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:379:@[simp] theorem one_apply (x : M₁) : (1 : M₁ →L[R₁] M₁) x = x := rfl
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Hom.lean:254:theorem one_apply (x : A) : (1 : A →ₗc[R] A) x = x :=
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean:292:theorem one_apply (x : A) : (1 : A →ₐc[R] A) x = x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:202:lemma one_apply [Π i, One (R i)] [∀ i, OneMemClass (S i) (R i)] (i : ι) :
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Algebra.lean:233:theorem one_apply (n : ℕ) : (1 : AdicCauchySequence I R) n = 1 :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:83:theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/NonabelianCohomology/H1.lean:65:lemma one_apply (i : I) : (1 : ZeroCochain G U) i = 1 := rfl
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:35:theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) opNorm_comp_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:397:theorem opNorm_comp_le (f : E →SL[σ₁₂] F) : ‖h.comp f‖ ≤ ‖h‖ * ‖f‖ :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) opNorm_le_bound(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:201:theorem opNorm_le_bound (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:206:theorem opNorm_le_bound' (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:65:theorem opNorm_le_bound₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) {C : ℝ} (h0 : 0 ≤ C)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:241:theorem opNorm_le_bound (f : E [⋀^ι]→L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:416:theorem opNorm_le_bound {f : ContinuousMultilinearMap 𝕜 E G}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:243:theorem opNorm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) smul_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Hom.lean:31:@[simp] theorem smul_apply [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Hom.lean:75:@[simp] theorem smul_apply [DistribSMul M B] (m : M) (f : A →+ B) (a : A) : (m • f) a = m • f a :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:168:theorem smul_apply [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E)
.lake/packages/mathlib/Mathlib/Algebra/Module/Hom.lean:84:theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:404:lemma smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:461:theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:528:theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:750:theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:123:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:853:theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
.lake/packages/mathlib/Mathlib/Algebra/Module/CharacterModule.lean:73:@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:626:@[simp] theorem smul_apply (α : Sˣ) (e : V ≃ₗ[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:252:theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean:123:@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:151:theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:443:theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:458:theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:649:theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:281:theorem smul_apply [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:914:theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Module.lean:56:theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:288:lemma smul_apply (a : A) (x : R[M]) (m : M) : (a • x) m = a • x m := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:75:theorem smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/SMul.lean:47:theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:478:theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:314:theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:233:theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:315:theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Module.lean:56:lemma smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:386:theorem smul_apply (a : M) (f : E →ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:222:theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:271:theorem smul_apply (r : R) (v : VectorMeasure α M) (i : Set α) : (r • v) i = r • v i := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Pi.lean:41:lemma smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i :=
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:93:theorem smul_apply (c : R) (m : OuterMeasure α) (s : Set α) : (c • m) s = c • m s :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:215:theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:162:theorem smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s a :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:493:theorem smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} :
Poincare/Global/ParabolicHolderSpace.lean:214:@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:261:theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:454:theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:153:theorem smul_apply (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:415:theorem smul_apply (a : S) (Q : QuadraticMap R M N) (x : M) : (a • Q) x = a • Q x :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:243:@[simp] lemma smul_apply {f : E →SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:226:theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:496:theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:210:theorem smul_apply (f : MultilinearMap R M₁ M₂) (c : S) (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/DomAct/Basic.lean:167:theorem smul_apply [SMul M α] (c : Mᵈᵐᵃ) (f : α → β) (a : α) : (c • f) a = f (mk.symm c • a) := rfl
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:202:@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Embedding.lean:41:theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:246:theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:255:lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:342:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Data/Finsupp/SMulWithZero.lean:59:theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Module.lean:37:theorem smul_apply [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:1328:@[simp] theorem smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:267:theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl
.lake/packages/mathlib/Mathlib/Tactic/Module.lean:159:@[simp] theorem smul_apply [Mul R] (r : R) (l : NF R M) : r • l = l.map fun (a, x) ↦ (r * a, x) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:1440:@[simp] theorem smul_apply (α : Sˣ) (e : V ≃L[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:175:theorem smul_apply (f : M [⋀^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:269:theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:214:theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:545:theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:818:lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:228:theorem smul_apply {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:717:theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:147:theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:255:theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:143:theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:230:lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] (g : G)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sub_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:205:@[simp] theorem sub_apply [Sub A] (M N : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:332:theorem sub_apply : (x - y) i = x i - y i :=
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:351:theorem sub_apply (v w : VectorMeasure α M) (i : Set α) : (v - w) i = v i - w i := rfl
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:124:theorem sub_apply [∀ i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Sub.lean:72:theorem sub_apply [IsFiniteMeasure ν] (h₁ : MeasurableSet s) (h₂ : ν ≤ μ) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:119:theorem sub_apply : (x - y) i = x i - y i :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:355:theorem sub_apply : (s - t) a = s a - t a :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:353:theorem sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:290:@[simp] lemma sub_apply {f g : E →SWOT[σ] F} (x : E) : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:411:theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:299:theorem sub_apply (f g : P →ᴬ[R] W) (x : P) : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:164:theorem sub_apply (f g : Poly α) (x : α → ℕ) : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:178:theorem sub_apply (f g : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (f - g) n = f n - g n := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:311:theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:505:theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:202:theorem sub_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:495:theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:863:theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:902:theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:250:theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:184:theorem sub_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:496:theorem sub_apply (m : ∀ i, M₁ i) : (f - f') m = f m - f' m :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:492:theorem sub_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
Poincare/Global/ParabolicHolderSpace.lean:211:@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:882:theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:589:theorem sub_apply (f g : CentroidHom α) (a : α) : (f - g) a = f a - g a :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:542:theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:88:theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:369:lemma sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a * χ (-a) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:405:lemma sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:237:theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:223:theorem sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:810:theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:297:theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:251:theorem sub_apply : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:657:theorem sub_apply {x : α} : (f - g) x = f x - g x := rfl
.lake/packages/mathlib/Mathlib/Algebra/Group/Finsupp.lean:418:lemma sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι →₀ G) (a : ι) : (g₁ - g₂) a = g₁ a - g₂ a := rfl
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:303:theorem sub_apply : (f - g) x = f x - g x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:501:theorem sub_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:332:theorem sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:541:theorem sub_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q - Q') x = Q x - Q' x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:1303:theorem sub_apply (m : ∀ i, M₁ i) : (f - g) m = f m - g m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:119:theorem sub_apply (x y : M₁) : (B₁ - D₁) x y = B₁ x y - D₁ x y :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:176:lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_sum(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:424:protected theorem mul_sum [Fintype m] (s : Finset β) (f : β → Matrix m n α) (M : Matrix l m α) :
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:439:theorem mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean:56:lemma mul_sum (s : Finset ι) (f : ι → R) (a : R) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sum_add_distrib(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean:466:theorem sum_add_distrib {ι} (f g : ι → Cardinal) : sum (f + g) = sum f + sum g := by
.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean:472:theorem sum_add_distrib' {ι} (f g : ι → Cardinal) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sum_congr(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:455:theorem sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G → k → M}
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:1359:theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sum_ite_eq(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:446:theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sum_le_sum(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Order.lean:477:theorem sum_le_sum {ι} (f g : ι → Cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
.lake/packages/mathlib/Mathlib/Data/Finsupp/Order.lean:48:lemma sum_le_sum (h : ∀ i ∈ f.support, h₁ i (f i) ≤ h₂ i (f i)) : f.sum h₁ ≤ f.sum h₂ :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sum_mul(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:420:protected theorem sum_mul [Fintype m] (s : Finset β) (f : β → Matrix l m α) (M : Matrix m n α) :
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:435:theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean:53:lemma sum_mul (s : Finset ι) (f : ι → R) (a : R) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mkContinuous(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:117:def mkContinuous₂ (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) (C : ℝ) (hC : ∀ x y, ‖f x y‖ ≤ C * ‖x‖ * ‖y‖) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:122:theorem mkContinuous₂_apply (f : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G) {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:150:def mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [⋀^ι]→L[𝕜] F :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:300:def mkContinuous (f : MultilinearMap 𝕜 E G) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mkContinuous_norm_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:483:theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:489:theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) boundConstant(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:49:def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) boundConstant_spec(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:53:theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) duhamelOperator(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:133:def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) duhamelOperator_norm_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:147:theorem duhamelOperator_norm_le :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) duhamelOperator_solves(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:157:theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) add_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:834:theorem add_apply (f g : M →ₛₗ[σ₁₂] M₂) (x : M) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:306:theorem add_apply (f g : CentroidHom α) (a : α) : (f + g) a = f a + g a :=
Poincare/Global/ParabolicHolderSpace.lean:208:@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:120:theorem add_apply [∀ i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:60:theorem add_apply (g₁ g₂ : PolynomialModule R M) (a : ℕ) : (g₁ + g₂) a = g₁ a + g₂ a :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:803:theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:184:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:105:theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:285:@[simp] lemma add_apply (ψ φ : AddChar A M) (a : A) : (ψ + φ) a = ψ a * φ a := rfl
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:206:theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:189:theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:138:lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Finsupp.lean:56:lemma add_apply (g₁ g₂ : ι →₀ M) (a : ι) : (g₁ + g₂) a = g₁ a + g₂ a := rfl
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:140:lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:161:theorem add_apply (f g : Poly α) (x : α → ℕ) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:179:theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:208:theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:417:theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:125:theorem add_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
.lake/packages/mathlib/Mathlib/Probability/Kernel/Defs.lean:99:@[simp] lemma add_apply (κ η : Kernel α β) (a : α) : (κ + η) a = κ a + η a := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:305:theorem add_apply (v w : VectorMeasure α M) (i : Set α) : (v + w) i = v i + w i := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean:215:@[simp] lemma add_apply (f g : StieltjesFunction R) (x : R) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:884:theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:70:theorem add_apply (m₁ m₂ : OuterMeasure α) (s : Set α) : (m₁ + m₂) s = m₁ s + m₂ s :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:291:theorem add_apply (f g : P →ᴬ[R] W) (x : P) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:130:theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:229:theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:431:theorem add_apply (f g : E →ₛₗ.[σ] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:214:theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:111:theorem add_apply (x y : M) : (B + D) x y = B x y + D x y :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:393:theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:282:theorem add_apply : (f + f') v = f v + f' v :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:173:theorem add_apply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E))
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:187:theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:199:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C₀(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:457:theorem add_apply (Q Q' : QuadraticMap R M N) (x : M) : (Q + Q') x = Q x + Q' x :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:234:theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:182:theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:199:@[simp] theorem add_apply [Add A] (M N : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:115:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:328:theorem add_apply : (x + y) i = x i + y i :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:488:theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:328:theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:303:theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:254:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:777:theorem add_apply (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:289:@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:72:theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (p + q) n = p n + q n := rfl
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:156:theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:607:theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:199:theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) ext(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/WithConv.lean:62:@[ext] protected theorem ext {x y : WithConv A}
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalHom.lean:195:theorem ext {f g : A →ₛₙₐ[φ] B} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Hom.lean:196:theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
.lake/packages/mathlib/Mathlib/Algebra/TrivSqZeroExt/Basic.lean:109:theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Hom.lean:135:@[ext] lemma ext ⦃f g : α →*₀ β⦄ (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Equiv.lean:112:theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Equiv.lean:59:@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Basic.lean:101:theorem ext {S T : Subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Category/Semigrp/Basic.lean:134:lemma ext {X Y : MagmaCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Category/Semigrp/Basic.lean:296:lemma ext {X Y : Semigrp} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean:131:theorem ext {S T : NonUnitalSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/AddConstMap/Basic.lean:335:@[ext] protected theorem ext {f g : G →+c[a, b] H} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Computability/Language.lean:123:theorem ext {l m : Language α} (h : ∀ (x : List α), x ∈ l ↔ x ∈ m) : l = m :=
.lake/packages/mathlib/Mathlib/Logic/Encodable/Basic.lean:468:protected theorem ext {a b : ULower α} : a.up = b.up → a = b :=
.lake/packages/mathlib/Mathlib/Algebra/Category/MonCat/Basic.lean:130:lemma ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Category/MonCat/Basic.lean:315:lemma ext {X Y : CommMonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:175:lemma ext ⦃f g : R[M]⦄ (hfg : ∀ m, f m = g m) : f = g := Finsupp.ext hfg
.lake/packages/mathlib/Mathlib/Algebra/Lie/Submodule.lean:129:theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:94:lemma ext (z₁ z₂ : Cochain F G n)
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:100:lemma ext₀ (z₁ z₂ : Cochain F G 0)
.lake/packages/mathlib/Mathlib/Logic/Embedding/Basic.lean:96:theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:410:theorem ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:571:theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Logic/Equiv/Defs.lean:124:@[ext, grind ext] theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g := DFunLike.ext f g H
.lake/packages/mathlib/Mathlib/Algebra/Vertex/VertexOperator.lean:47:theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
.lake/packages/mathlib/Mathlib/Algebra/Vertex/HVertexOperator.lean:53:theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
.lake/packages/mathlib/Mathlib/Control/Monad/Cont.lean:80:protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by
.lake/packages/mathlib/Mathlib/Control/Monad/Writer.lean:72:protected theorem ext {ω : Type u} (x x' : WriterT ω M α) (h : x.run = x'.run) : x = x' := h
.lake/packages/mathlib/Mathlib/Algebra/Lie/Weights/Basic.lean:228:@[ext] lemma ext {χ₁ χ₂ : Weight R L M} (h : ∀ x, χ₁ x = χ₂ x) : χ₁ = χ₂ := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Control/Functor.lean:86:protected theorem ext {α β} {x y : Const α β} (h : x.run = y.run) : x = y :=
.lake/packages/mathlib/Mathlib/Control/Functor.lean:149:protected theorem ext {α} {x y : Comp F G α} : x.run = y.run → x = y :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subsemiring/Defs.lean:204:theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Homology/HomologicalComplex.lean:79:theorem ext {C₁ C₂ : HomologicalComplex V c} (h_X : C₁.X = C₂.X)
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:462:protected theorem ext {e e' : PartialEquiv α β} (h : ∀ x, e x = e' x)
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:94:theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
.lake/packages/mathlib/Mathlib/Control/Traversable/Basic.lean:121:theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
.lake/packages/mathlib/Mathlib/Algebra/PresentedMonoid/Basic.lean:141:theorem ext {M : Type*} [Monoid M] (rels : FreeMonoid α → FreeMonoid α → Prop)
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean:358:def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:178:lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:53:lemma ext {f g : IntertwiningMap ρ σ} (h : f.toLinearMap = g.toLinearMap) : f = g := by
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:287:lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V → W) = ψ) : φ = ψ := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/Subalgebra.lean:181:theorem ext (L₁' L₂' : LieSubalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Equiv.lean:145:theorem ext {f g : R ≃+* S} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subring/Defs.lean:248:theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Data/PEquiv.lean:87:@[ext] theorem ext {f g : α ≃. β} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Quaternion.lean:755:theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b :=
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:82:theorem ext {f g : A →⋆* B} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Star/MonoidHom.lean:201:theorem ext {f g : A ≃⋆* B} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:111:theorem ext {f g : CentroidHom α} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:120:theorem ext {f g : A →⋆ₙ+* B} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarRingHom.lean:323:theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Data/Matrix/DMatrix.lean:41:theorem ext : (∀ i j, M i j = N i j) → M = N :=
.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:170:theorem ext {S T : NonUnitalStarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Star/Subsemiring.lean:93:theorem ext {S T : StarSubsemiring R} (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:128:theorem ext {f g : A →⋆ₙₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Star/StarAlgHom.lean:351:theorem ext {f g : A →⋆ₐ[R] B} (h : ∀ x, f x = g x) : f = g :=
Poincare/Global/ParabolicHolderSpace.lean:217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
.lake/packages/mathlib/Mathlib/Data/Vector/Basic.lean:43:theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
.lake/packages/mathlib/Mathlib/Algebra/Ring/Ext.lean:46:@[ext] theorem ext ⦃inst₁ inst₂ : Distrib R⦄
.lake/packages/mathlib/Mathlib/Algebra/Ring/Ext.lean:61:@[ext] theorem ext ⦃inst₁ inst₂ : NonUnitalNonAssocSemiring R⦄
.lake/packages/mathlib/Mathlib/Algebra/Star/Subalgebra.lean:132:theorem ext {S T : StarSubalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:226:theorem ext {f g : M →ₛₗ[σ] M₃} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:79:protected lemma ext {I J : X.IdealSheafData} (h : I.ideal = J.ideal) : I = J := by
.lake/packages/mathlib/Mathlib/Algebra/Field/Subfield/Defs.lean:178:theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/M.lean:164:theorem ext' (x y : M F) (H : ∀ i : ℕ, x.approx i = y.approx i) : x = y := by
.lake/packages/mathlib/Mathlib/Data/PFunctor/Univariate/M.lean:483:theorem ext [Inhabited (M F)] [DecidableEq F.A] (x y : M F)
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ExteriorPower.lean:47:lemma ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x) :
.lake/packages/mathlib/Mathlib/Algebra/Module/CharacterModule.lean:61:@[ext] theorem ext {c c' : CharacterModule A} (h : ∀ x, c x = c' x) : c = c' := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Data/Multiset/Count.lean:183:theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
.lake/packages/mathlib/Mathlib/Data/Multiset/Count.lean:189:theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:156:theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Ring/Hom/Defs.lean:442:theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
.lake/packages/mathlib/Mathlib/Data/Prod/TProd.lean:105:theorem ext :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/Differentials/Basic.lean:118:lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/RationalMap.lean:73:lemma ext (f g : X.PartialMap Y) (e : f.domain = g.domain)
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:224:theorem ext (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/Data/Analysis/Topology.lean:148:theorem ext' [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ}
.lake/packages/mathlib/Mathlib/Data/Analysis/Topology.lean:154:theorem ext [T : TopologicalSpace α] {σ : Type*} {F : Ctop α σ} (H₁ : ∀ a, IsOpen (F a))
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Basic.lean:714:theorem ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Scheme.lean:240:protected lemma ext {f g : X ⟶ Y} (h_base : f.base = g.base)
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Scheme.lean:250:protected lemma ext' {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom) : f = g := by
.lake/packages/mathlib/Mathlib/Algebra/SkewMonoidAlgebra/Basic.lean:212:theorem ext {p q : SkewMonoidAlgebra k G} : (∀ a, coeff p a = coeff q a) → p = q := ext_iff.2
.lake/packages/mathlib/Mathlib/Data/Finsupp/Defs.lean:118:theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/QuaternionBasis.lean:63:protected theorem ext ⦃q₁ q₂ : Basis A c₁ c₂ c₃⦄ (hi : q₁.i = q₂.i)
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Defs.lean:125:theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean:743:lemma ext {P' : MorphismProperty Scheme.{u}}
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:126:lemma ext {X Y : GrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Category/Grp/Basic.lean:343:lemma ext {X Y : CommGrpCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Data/Set/Defs.lean:77:theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:344:lemma ext {P Q : AffineTargetMorphismProperty}
.lake/packages/mathlib/Mathlib/AlgebraicGeometry/PullbackCarrier.lean:56:protected lemma ext {t₁ t₂ : Triplet f g} (ex : t₁.x = t₂.x) (ey : t₁.y = t₂.y) : t₁ = t₂ := by
.lake/packages/mathlib/Mathlib/Algebra/Module/LocalizedModule/Basic.lean:915:theorem ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean:92:theorem ext {S T : IntermediateField K L} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Basic.lean:95:@[ext] theorem ext {x y : DirectSum ι β} (w : ∀ i, x i = y i) : x = y :=
.lake/packages/mathlib/Mathlib/FieldTheory/PolynomialGaloisGroup.lean:62:theorem ext {σ τ : p.Gal} (h : ∀ x ∈ p.rootSet p.SplittingField, σ x = τ x) : σ = τ := by
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/Basic.lean:190:@[ext] lemma ext : (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y := ext_aux
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/MonoidWithZero.lean:108:theorem ext (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:159:theorem ext {f g : α →+*o β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Ring.lean:325:theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/SetTheory/ZFC/Class.lean:50:theorem ext {x y : Class.{u}} : (∀ z : ZFSet.{u}, x z ↔ y z) → x = y :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:292:theorem ext (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Hom/Monoid.lean:520:theorem ext (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Defs.lean:88:theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/StandardPart.lean:61:@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean:142:theorem ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff) : x = y :=
.lake/packages/mathlib/Mathlib/Data/Part.lean:75:theorem ext' : ∀ {o p : Part α}, (o.Dom ↔ p.Dom) → (∀ h₁ h₂, o.get h₁ = p.get h₂) → o = p
.lake/packages/mathlib/Mathlib/Data/Part.lean:107:theorem ext {o p : Part α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:100:theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
.lake/packages/mathlib/Mathlib/Algebra/Order/AbsoluteValue/Basic.lean:76:theorem ext ⦃f g : AbsoluteValue R S⦄ : (∀ x, f x = g x) → f = g :=
.lake/packages/mathlib/Mathlib/Data/SetLike/Basic.lean:52:@[ext] theorem ext {p q : MySubobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h
.lake/packages/mathlib/Mathlib/Data/SetLike/Basic.lean:166:theorem ext' (h : (p : Set B) = q) : p = q :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:173:theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g := Subtype.ext (funext h)
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean:83:theorem ext (h : ∀ f, X f = Y f) : X = Y := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Data/Quot.lean:38:theorem ext {α : Sort*} : ∀ {s t : Setoid α}, (∀ a b, s a b ↔ t a b) → s = t
.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean:555:protected theorem ext {P : Type*} [Monoid P] (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
.lake/packages/mathlib/Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:84:lemma ext {f g : E₁ →ₚ[R] E₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/Basic.lean:149:@[ext] theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
.lake/packages/mathlib/Mathlib/Data/Sym/Sym2.lean:344:theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:87:lemma ext (v₁ v₂ : InfinitePlace K) (h : ∀ k, v₁ k = v₂ k) : v₁ = v₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Truncated.lean:82:theorem ext {x y : TruncatedWittVector p n R} (h : ∀ i, x.coeff i = y.coeff i) : x = y :=
.lake/packages/mathlib/Mathlib/Data/Sym/Basic.lean:80:@[ext] theorem ext {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂) : s₁ = s₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/IsPoly.lean:170:theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/IsPoly.lean:330:theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
.lake/packages/mathlib/Mathlib/RingTheory/WittVector/Defs.lean:77:theorem ext {x y : 𝕎 R} (h : ∀ n, x.coeff n = y.coeff n) : x = y := by
.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:533:theorem ext (p q : MvPolynomial σ R) : (∀ m, coeff m p = coeff m q) → p = q :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Diffeomorph.lean:160:theorem ext {h h' : M ≃ₘ^n⟮I, I'⟯ M'} (Heq : ∀ x, h x = h' x) : h = h' :=
.lake/packages/mathlib/Mathlib/Data/NNRat/Defs.lean:89:theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
.lake/packages/mathlib/Mathlib/Data/List/AList.lean:64:theorem ext : ∀ {s t : AList β}, s.entries = t.entries → s = t
.lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/SmoothSection.lean:320:theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/Data/PFun.lean:101:theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) :
.lake/packages/mathlib/Mathlib/Data/PFun.lean:106:theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:145:theorem ext {φ ψ : MvPowerSeries σ R} (h : ∀ n : σ →₀ ℕ, coeff n φ = coeff n ψ) : φ = ψ :=
.lake/packages/mathlib/Mathlib/Algebra/Group/AddChar.lean:101:@[ext] lemma ext (f g : AddChar A M) (h : ∀ x : A, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Data/Seq/Defs.lean:101:protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
.lake/packages/mathlib/Mathlib/Data/Stream/Init.lean:37:protected theorem ext {s₁ s₂ : Stream' α} : (∀ n, get s₁ n = get s₂ n) → s₁ = s₂ :=
.lake/packages/mathlib/Mathlib/Data/Finmap.lean:155:theorem ext : ∀ {s t : Finmap β}, s.entries = t.entries → s = t
.lake/packages/mathlib/Mathlib/Data/ULift.lean:129:theorem ext (x y : ULift α) (h : x.down = y.down) : x = y :=
.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean:65:@[ext] lemma ext {a b : Additive α} (hab : a.toMul = b.toMul) : a = b := hab
.lake/packages/mathlib/Mathlib/Algebra/Group/TypeTags/Basic.lean:97:@[ext] lemma ext {a b : Multiplicative α} (hab : a.toAdd = b.toAdd) : a = b := hab
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:120:theorem ext' {χ χ' : MulChar R R'} (h : ∀ a, χ a = χ' a) : χ = χ' := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/NumberTheory/MulChar/Basic.lean:133:theorem ext {χ χ' : MulChar R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' := by
.lake/packages/mathlib/Mathlib/Data/FunLike/Equiv.lean:33:@[ext] theorem ext {f g : MyIso A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Defs.lean:182:theorem ext {S T : NonUnitalSubsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Data/FunLike/Embedding.lean:36:@[ext] theorem ext {f g : MyEmbedding A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubring/Defs.lean:189:theorem ext {S T : NonUnitalSubring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Subsemigroup/Defs.lean:138:theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Data/FunLike/Basic.lean:38:@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/Data/FunLike/Basic.lean:185:theorem ext' {f g : F} (h : (f : ∀ a : α, β a) = (g : ∀ a : α, β a)) : f = g :=
.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean:59:theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Basic.lean:111:lemma ext {I J : TwoSidedIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
.lake/packages/mathlib/Mathlib/RingTheory/Perfection.lean:227:theorem ext {f g : Perfection R p} (h : ∀ n, coeff R p n f = coeff R p n g) : f = g :=
.lake/packages/mathlib/Mathlib/NumberTheory/LucasLehmer.lean:242:theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
.lake/packages/mathlib/Mathlib/Data/Semiquot.lean:51:theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/ContMDiffMap.lean:73:theorem ext (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/RingTheory/PowerSeries/Basic.lean:91:theorem ext {φ ψ : R⟦X⟧} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Pointed.lean:124:@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Saturation.lean:115:lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Saturation.lean:128:lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:88:theorem ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h
.lake/packages/mathlib/Mathlib/Algebra/Group/Equiv/Defs.lean:183:theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Defs.lean:192:theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Defs.lean:428:theorem ext {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:350:theorem ext ⦃f g : (A ⊗[R] B) →ₐ[S] C⦄
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:360:theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
.lake/packages/mathlib/Mathlib/RingTheory/FractionalIdeal/Basic.lean:182:theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/Basic.lean:193:lemma ext {x y : SimplexCategoryGenRel} (h : x.len = y.len) : x = y := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Hom/Defs.lean:948:theorem ext {f g : Monoid.End M} (h : ∀ x : M, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Defs.lean:71:theorem ext {I J : Ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
.lake/packages/mathlib/Mathlib/RingTheory/IsAdjoinRoot.lean:143:theorem ext (h' : IsAdjoinRoot S f) (eq : h.root = h'.root) : h = h' :=
.lake/packages/mathlib/Mathlib/Data/Finset/Defs.lean:149:theorem ext {s₁ s₂ : Finset α} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) : s₁ = s₂ :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean:85:theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
.lake/packages/mathlib/Mathlib/RingTheory/Grassmannian.lean:80:@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Defs.lean:119:theorem ext {u v : αˣ} (huv : u.val = v.val) : u = v := val_injective huv
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Hom.lean:171:theorem ext {φ₁ φ₂ : A →ₗc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/Coalgebra/Equiv.lean:154:theorem ext (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/NumberTheory/Pell.lean:132:theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:107:theorem ext {f g : Poly α} : (∀ x, f x = g x) → f = g := DFunLike.ext _ _
.lake/packages/mathlib/Mathlib/NumberTheory/Dioph.lean:254:theorem ext (d : Dioph S) (H : ∀ v, v ∈ S ↔ v ∈ S') : Dioph S' := by rwa [← Set.ext H]
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:91:theorem ext ⦃f g : ArithmeticFunction R⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:140:theorem ext {v₁ v₂ : Valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Basic.lean:1194:theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/HomotopyCat.lean:282:lemma ext {x y : V.HomotopyCategory} (h : x.as.as = y.as.as) : x = y := by
.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean:65:theorem ext (A B : ValuationSubring K) (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := SetLike.ext h
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean:75:lemma ext {e e' : Edge x₀ x₁} (h : e.edge = e'.edge) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/CompStruct.lean:192:lemma ext {h h' : CompStruct e₀₁ e₁₂ e₀₂} (eq : h.simplex = h'.simplex) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean:77:lemma ext {n d : ℕ} (x y : Δ[n] _⦋d⦌) (h : ∀ (i : Fin (d + 1)), x i = y i) : x = y :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicIntegers.lean:73:theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialObject/Split.lean:74:theorem ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := rfl
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialObject/Split.lean:76:theorem ext (A₁ A₂ : IndexSet Δ) (h₁ : A₁.1 = A₂.1) (h₂ : A₁.e ≫ eqToHom (by rw [h₁]) = A₂.e) :
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/PresheafedSpace.lean:130:theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/Path.lean:76:lemma ext {f g : Path X m} (hᵥ : f.vertex = g.vertex) (hₐ : f.arrow = g.arrow) :
.lake/packages/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/Path.lean:82:lemma ext' {f g : Path X (m + 1)} (h : ∀ i, f.arrow i = g.arrow i) : f = g := by
.lake/packages/mathlib/Mathlib/Geometry/RingedSpace/SheafedSpace.lean:78:theorem ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base)
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Hom.lean:199:theorem ext {φ₁ φ₂ : A →ₐc[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/Bialgebra/Equiv.lean:191:theorem ext (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:100:theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:131:theorem ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Defs.lean:135:theorem ext {c d : RingCon R} (H : ∀ x y, c x y ↔ d x y) : c = d :=
.lake/packages/mathlib/Mathlib/Topology/Sheaves/Presheaf.lean:60:lemma ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P ⟶ Q}
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/AlgHom.lean:135:theorem ext {f₁ f₂ : 𝒜 →ₐᵍ[R] ℬ} (H : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:314:lemma ext {x y : AdicCompletion I M} (h : ∀ n, x.val n = y.val n) : x = y := Subtype.ext <| funext h
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:500:theorem ext {x y : AdicCauchySequence I M} (h : ∀ n, x n = y n) : x = y :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean:315:theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean:321:theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:108:theorem ext {𝒜 : ι → σ} (x : Submonoid A)
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Homogeneous/Subsemiring.lean:65:theorem ext {R S : HomogeneousSubsemiring 𝒜}
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/Homogeneous/Subsemiring.lean:69:theorem ext' {R S : HomogeneousSubsemiring 𝒜}
.lake/packages/mathlib/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean:134:lemma ext {a₁ a₂ : FiniteAdeleRing R K} (h : ∀ v, a₁ v = a₂ v) : a₁ = a₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/GradedAlgebra/RingHom.lean:140:theorem ext ⦃f g : 𝒜 →+*ᵍ ℬ⦄ : (∀ x, f x = g x) → f = g :=
.lake/packages/mathlib/Mathlib/Probability/Process/Filtration.lean:74:protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace Ω) = g) : f = g := by
.lake/packages/mathlib/Mathlib/GroupTheory/PushoutI.lean:279:theorem ext {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:139:theorem ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
.lake/packages/mathlib/Mathlib/RingTheory/Unramified/Basic.lean:153:theorem ext' [FormallyUnramified R A] {C : Type*} [Ring C] (f : B →+* C)
.lake/packages/mathlib/Mathlib/LinearAlgebra/ConvexSpace.lean:74:theorem ext {f g : StdSimplex R M} (h : f.weights = g.weights) : f = g := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/PiTensorProduct.lean:363:theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
.lake/packages/mathlib/Mathlib/Probability/Kernel/Defs.lean:251:theorem ext (h : ∀ a, κ a = η a) : κ = η := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Basic.lean:100:theorem ext (H : ∀ x y : M, B x y = D x y) : B = D := ext₂ H
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:73:theorem ext {f g : E →ₛₗ.[σ] F} (h : f.domain = g.domain)
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:109:theorem ext' {s : Submodule R E} {f g : s →ₛₗ[σ] F} (h : f = g) : mk s f = mk s g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearForm/Isometry.lean:68:theorem ext ⦃f g : B₁ →bᵢ B₂⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/UnitaryGroup.lean:145:theorem ext (A B : unitaryGroup n α) : (∀ i j, A i j = B i j) → A = B :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:149:theorem ext {f f' : MultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basic.lean:133:theorem ext' {g h : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basic.lean:163:theorem ext {g h : M ⊗ N →ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/BilinearMap.lean:104:theorem ext₂ {f g : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (H : ∀ m n, f m n = g m n) : f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:106:theorem ext (A B : SpecialLinearGroup n R) : (∀ i j, A i j = B i j) → A = B :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra/Equiv.lean:112:theorem ext {f g : A ≃A[R] B} (h : ⇑f = ⇑g) : f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Tower.lean:102:theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:198:theorem ext {f g : X →ₑ[φ] Y} :
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Hom.lean:695:theorem ext {f g : A →ₑ*[φ] B} : (∀ x, f x = g x) → f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:126:theorem ext {f f' : M [⋀^ι]→ₗ[R] N} (H : ∀ x, f x = f' x) : f = f' :=
.lake/packages/mathlib/Mathlib/GroupTheory/MonoidLocalization/Basic.lean:434:theorem ext {f g : LocalizationMap S N} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean:37:lemma ext' {m : R} {A B : FixedDetMatrix n R m} (h : A.1 = B.1) : A = B := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean:42:lemma ext {m : R} {A B : FixedDetMatrix n R m} (h : ∀ i j, A.1 i j = B.1 i j) : A = B := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:70:theorem ext {f g : P →ᴬ[R] Q} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/SpecialLinearGroup.lean:68:theorem ext (u v : SpecialLinearGroup R V) : (∀ x, u x = v x) → u = v :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/RootSystem/Basic.lean:100:protected lemma ext [CharZero R] [IsDomain R] [IsTorsionFree R M]
.lake/packages/mathlib/Mathlib/GroupTheory/HNNExtension.lean:234:theorem ext {w w' : NormalWord d}
.lake/packages/mathlib/Mathlib/Probability/ProbabilityMassFunction/Basic.lean:56:protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:69:theorem ext : (∀ i j, M i j = N i j) → M = N :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineEquiv.lean:119:theorem ext {e e' : P₁ ≃ᵃ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/SubMulAction.lean:225:theorem ext {p q : SubMulAction R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Basis.lean:112:theorem ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι → P) = b₂) : b₁ = b₂ :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:195:theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
.lake/packages/mathlib/Mathlib/Combinatorics/Young/SemistandardTableau.lean:81:theorem ext {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : ∀ i j, T i j = T' i j) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean:87:theorem ext {n : ℕ} {s1 s2 : Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean:123:theorem ext ⦃A B : GL n R⦄ (h : ∀ i j, (A : Matrix n n R) i j = (B : Matrix n n R) i j) : A = B :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean:61:theorem ext ⦃f g : Q₁ →qᵢ Q₂⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:309:theorem ext {p q : AffineSubspace k P} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineEquiv.lean:113:theorem ext {e e' : P₁ ≃ᴬ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:173:theorem ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:177:theorem ext {c d : Con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean:133:theorem ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Algebra.lean:200:theorem ext {f g : A →A[R] B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/GroupTheory/Sylow.lean:67:theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr
.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Defs.lean:218:protected theorem ext (e' : OpenPartialHomeomorph X Y) (h : ∀ x, e x = e' x)
.lake/packages/mathlib/Mathlib/Topology/Homotopy/HomotopyGroup.lean:115:theorem ext (f g : Ω^ N X x) (H : ∀ y, f y = g y) : f = g :=
.lake/packages/mathlib/Mathlib/GroupTheory/PresentedGroup.lean:136:theorem ext {φ ψ : PresentedGroup rels →* G} (hx : ∀ (x : α), φ (.of x) = ψ (.of x)) : φ = ψ := by
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:117:theorem ext {F G : Homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
.lake/packages/mathlib/Mathlib/Topology/Homotopy/Basic.lean:408:theorem ext {F G : HomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G := DFunLike.ext F G h
.lake/packages/mathlib/Mathlib/Topology/Algebra/Ring/Basic.lean:528:theorem ext {f g : RingTopology R} (h : f.IsOpen = g.IsOpen) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:100:theorem ext {f g : C₀(α, β)} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:129:theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
.lake/packages/mathlib/Mathlib/ModelTheory/PartialEquiv.lean:179:theorem ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (∀ x : M, ∀ h : x ∈ f.dom,
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ContinuousMapZero.lean:70:lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/ModelTheory/Substructures.lean:124:theorem ext {S T : L.Substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Basic.lean:108:theorem ext {f g : α →Co β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:299:theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/ModelTheory/Basic.lean:409:theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:130:theorem ext {f g : PseudoEpimorphism α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Order/Hom/Esakia.lean:237:theorem ext {f g : EsakiaHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:98:theorem ext (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/ModelTheory/ElementaryMaps.lean:164:theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean:107:@[ext] lemma ext {f g : Copy A B} : (∀ a, f a = g a) → f = g := DFunLike.ext _ _
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Defs.lean:114:theorem ext {f g : C(X, Y)} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean:245:theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Equiv.lean:91:theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:173:theorem ext {f g : E →ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean:525:theorem ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:93:theorem ext {f g : C_c(α, β)} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CocompactMap.lean:95:theorem ext {f g : CocompactMap α β} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/FintypeCat.lean:178:theorem ext (X Y : Skeleton) : X.len = Y.len → X = Y :=
.lake/packages/mathlib/Mathlib/Topology/CWComplex/Classical/Basic.lean:636:@[ext] lemma ext {E F : Subcomplex C} (h : ∀ x, x ∈ E ↔ x ∈ F) : E = F :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:139:theorem ext {f g : A →ₜ* B} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean:358:theorem ext {f g : M ≃ₜ* N} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/SetLike.lean:43:@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Completion.lean:416:theorem ext {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
.lake/packages/mathlib/Mathlib/Topology/UniformSpace/Completion.lean:420:theorem ext' {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/PiNat.lean:993:@[ext] lemma ext {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat) : x = y := by
.lake/packages/mathlib/Mathlib/Topology/Hom/Open.lean:85:theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/OrderDual.lean:147:@[ext] lemma ext {a b : αᵒᵈ} (h : ofDual a = ofDual b) : a = b := h
.lake/packages/mathlib/Mathlib/Order/UpperLower/CompleteLattice.lean:49:theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:186:theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:263:theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/RingSeminorm.lean:106:theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/RingSeminorm.lean:249:theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/Order/BooleanSubalgebra.lean:81:lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext
.lake/packages/mathlib/Mathlib/Order/Preorder/Chain.lean:333:theorem ext : (s : Set α) = t → s = t :=
.lake/packages/mathlib/Mathlib/Order/Partition/Basic.lean:97:@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:99:theorem ext {f g : M [⋀^ι]→L[R] N} (H : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/AlgebraNorm.lean:81:theorem ext {p q : AlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/AlgebraNorm.lean:170:theorem ext {p q : MulAlgebraNorm R S} : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/DilationEquiv.lean:70:protected theorem ext {e e' : X ≃ᵈ Y} (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/Order/Sublattice.lean:86:lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:159:theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean:90:lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
.lake/packages/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean:95:lemma ext {e e' : Pretrivialization F proj} (h₁ : ∀ x, e x = e' x)
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/SingleObj.lean:48:lemma ext {x y : SingleObj α} : x = y := Unit.ext x y
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Prefunctor.lean:39:theorem ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{v₂} W] {F G : Prefunctor V W}
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/Prefunctor.lean:53:theorem ext' {V W : Type u} [Quiver V] [Quiver W] {F G : Prefunctor V W}
.lake/packages/mathlib/Mathlib/Topology/LocallyFinsupp.lean:139:lemma ext [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : ∀ a, D₁ a = D₂ a) :
.lake/packages/mathlib/Mathlib/Topology/Category/TopCat/Basic.lean:125:lemma ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Filter/Ultrafilter/Defs.lean:89:theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Category/TopCat/Monoidal.lean:130:lemma ext {x y : I.{u}} (h : homeomorph x = homeomorph y) : x = y :=
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/ReflQuiver.lean:67:theorem ext {V : Type u} [ReflQuiver.{v₁} V] {W : Type u₂} [ReflQuiver.{v₂} W]
.lake/packages/mathlib/Mathlib/Combinatorics/Quiver/ReflQuiver.lean:80:theorem ext' {V W : Type u} [ReflQuiver.{v} V] [ReflQuiver.{v} W]
.lake/packages/mathlib/Mathlib/Order/Filter/Defs.lean:96:protected theorem ext (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g := filter_eq <| Set.ext h
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Basic.lean:354:protected lemma ext {G₁ G₂ : Graph α β} (hV : V(G₁) = V(G₂))
.lake/packages/mathlib/Mathlib/Order/Filter/Basic.lean:627:protected theorem ext' {f₁ f₂ : Filter α}
.lake/packages/mathlib/Mathlib/Order/Category/Frm.lean:99:lemma ext {X Y : Frm} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/CharacterSpace.lean:76:theorem ext {φ ψ : characterSpace 𝕜 A} (h : ∀ x, φ x = ψ x) : φ = ψ :=
.lake/packages/mathlib/Mathlib/Order/Category/BoolAlg.lean:97:lemma ext {X Y : BoolAlg} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/BddOrd.lean:97:lemma ext {X Y : BddOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Spectral/Hom.lean:124:theorem ext {f g : SpectralMap α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:109:theorem ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f g : E →SLᵤ[σ, 𝔖] F}
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean:422:theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:92:theorem ext {f g : P →ᵃⁱ[𝕜] P₂} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Affine/Isometry.lean:337:theorem ext {e e' : P ≃ᵃⁱ[𝕜] P₂} (h : ∀ x, e x = e' x) : e = e' :=
.lake/packages/mathlib/Mathlib/Topology/Homeomorph/Defs.lean:104:theorem ext {h h' : X ≃ₜ Y} (H : ∀ x, h x = h' x) : h = h' :=
.lake/packages/mathlib/Mathlib/Order/Category/HeytAlg.lean:96:lemma ext {X Y : HeytAlg} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Sets/Closeds.lean:65:protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
.lake/packages/mathlib/Mathlib/Topology/Sets/Closeds.lean:346:protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
.lake/packages/mathlib/Mathlib/Topology/Sets/Compacts.lean:78:protected theorem ext {s t : Compacts α} (h : (s : Set α) = t) : s = t :=
.lake/packages/mathlib/Mathlib/Topology/Sets/Compacts.lean:331:protected theorem ext {s t : NonemptyCompacts α} (h : (s : Set α) = t) : s = t :=
.lake/packages/mathlib/Mathlib/Order/Category/Lat.lean:102:lemma ext {X Y : Lat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:92:lemma ext {A B : Algebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Endofunctor/Algebra.lean:280:lemma ext {A B : Coalgebra F} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:113:lemma ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : ∀ a b, a ≤ b → f a b = g a b) : f = g := by
.lake/packages/mathlib/Mathlib/Topology/Sets/Order.lean:58:protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
.lake/packages/mathlib/Mathlib/CategoryTheory/DifferentialObject.lean:83:theorem ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Dilation.lean:112:theorem ext {f g : α →ᵈ β} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/PartOrd.lean:92:lemma ext {X Y : PartOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Sets/Opens.lean:104:theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
.lake/packages/mathlib/Mathlib/Order/Category/LinOrd.lean:76:lemma ext {X Y : LinOrd} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/FinBddDistLat.lean:106:lemma ext {X Y : FinBddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:103:theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
.lake/packages/mathlib/Mathlib/Order/Category/BddDistLat.lean:104:lemma ext {X Y : BddDistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/PartOrdEmb.lean:97:lemma ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/Preord.lean:95:lemma ext {X Y : Preord} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Bornology/Hom.lean:91:theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:113:lemma ext {x y : Πʳ i, [R i, A i]_[𝓕]} (h : ∀ i, x i = y i) : x = y :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Elements.lean:89:theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/BddLat.lean:107:lemma ext {X Y : BddLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Group/GroupTopology.lean:75:theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Category/DistLat.lean:99:lemma ext {X Y : DistLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/OpenSubgroup.lean:105:theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:376:theorem ext {f g : lp E p} (h : (f : ∀ i, E i) = g) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/StdSimplex.lean:285:lemma ext {s t : stdSimplex S X} (h : (s : X → S) = t) : s = t := by
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:184:theorem ext {f g : SupHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/Lattice.lean:383:theorem ext {f g : LatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:233:theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/CompleteLattice.lean:370:theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:189:theorem ext {f g : TopHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/Bounded.lean:382:theorem ext {f g : BoundedOrderHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Cone/Basic.lean:83:@[ext] lemma ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h
.lake/packages/mathlib/Mathlib/CategoryTheory/Adjunction/Basic.lean:190:lemma ext {F : C ⥤ D} {G : D ⥤ C} {adj adj' : F ⊣ G}
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:251:theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/Basic.lean:733:theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Nucleus.lean:88:@[ext] lemma ext {m n : Nucleus X} (h : ∀ a, m a = n a) : m = n :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:222:theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Hom/BoundedLattice.lean:384:theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Convex/Body.lean:82:protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:108:theorem ext (H : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:125:theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/OmegaCompletePartialOrder.lean:90:@[ext] lemma ext ⦃f g : Chain α⦄ (h : ⇑f = ⇑g) : f = g := DFunLike.ext' h
.lake/packages/mathlib/Mathlib/Order/OmegaCompletePartialOrder.lean:608:protected theorem ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
.lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:175:theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:66:lemma ext {M₁ M₂ : CStarMatrix m n A} (h : ∀ i j, M₁ i j = M₂ i j) : M₁ = M₂ := ext_iff.mp h
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:195:theorem ext : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:494:theorem ext : (∀ x, p x = q x) → p = q :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Iso.lean:79:theorem ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:261:theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Heyting/Hom.lean:366:theorem ext {f g : CoheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:78:lemma ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/SemiNormedGrp.lean:282:lemma ext {M N : SemiNormedGrp₁} {f₁ f₂ : M ⟶ N} (h : ∀ (x : M), f₁ x = f₂ x) : f₁ = f₂ :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean:144:theorem ext {f g : 𝓓^{n}(Ω, F)} (h : ∀ a, f a = g a) : f = g :=
.lake/packages/mathlib/Mathlib/Order/PFilter.lean:89:theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h
.lake/packages/mathlib/Mathlib/Order/Ideal.lean:119:theorem ext {s t : Ideal P} : (s : Set P) = t → s = t :=
.lake/packages/mathlib/Mathlib/CategoryTheory/ComposableArrows/Basic.lean:208:lemma ext {F G : ComposableArrows C n} (h : ∀ i, F.obj i = G.obj i)
.lake/packages/mathlib/Mathlib/CategoryTheory/ComposableArrows/Basic.lean:239:lemma ext₀ {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0) : F = G :=
.lake/packages/mathlib/Mathlib/CategoryTheory/EqToHom.lean:236:theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:134:theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/RelIso/Basic.lean:258:theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/Sublocale.lean:73:@[ext] lemma ext (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/Cat.lean:82:lemma ext {C D : Cat.{v, u}} {F G : C ⟶ D} (h : F.toFunctor = G.toFunctor) : F = G :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Preadditive/Mat.lean:455:def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
.lake/packages/mathlib/Mathlib/Order/Completion.lean:62:@[ext] theorem ext {A B : DedekindCut α} (h : A.left = B.left) : A = B := Concept.ext h
.lake/packages/mathlib/Mathlib/Order/Completion.lean:65:theorem ext' {A B : DedekindCut α} (h : A.right = B.right) : A = B := Concept.ext' h
.lake/packages/mathlib/Mathlib/CategoryTheory/Category/RelCat.lean:60:@[ext] lemma ext (f g : X ⟶ Y) (h : f.rel = g.rel) : f = g := by cases f; cases g; congr
.lake/packages/mathlib/Mathlib/Order/Closure.lean:123:theorem ext : ∀ c₁ c₂ : ClosureOperator α, (∀ x, c₁ x = c₂ x) → c₁ = c₂ :=
.lake/packages/mathlib/Mathlib/Order/Closure.lean:340:theorem ext : ∀ l₁ l₂ : LowerAdjoint u, (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
.lake/packages/mathlib/Mathlib/Order/JordanHolder.lean:174:theorem ext {s₁ s₂ : CompositionSeries X} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ := by
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:311:protected theorem ext {A ι : Type*} {E : ι → Type*} {x y : C⋆ᵐᵒᵈ(A, Π i, E i)}
.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:105:@[ext] lemma ext {f g : r ≼i s} (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/Order/InitialSeg.lean:279:theorem ext [Std.Irrefl s] [Std.Trichotomous s] {f g : r ≺i s} (h : ∀ x, f x = g x) : f = g := by
.lake/packages/mathlib/Mathlib/Order/Concept.lean:281:theorem ext (h : c.extent = d.extent) : c = d := by
.lake/packages/mathlib/Mathlib/Order/Concept.lean:288:theorem ext' (h : c.intent = d.intent) : c = d := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:79:protected theorem ext {p q : FormalMultilinearSeries 𝕜 E F} (h : ∀ n, p n = q n) : p = q :=
.lake/packages/mathlib/Mathlib/CategoryTheory/ConcreteCategory/Basic.lean:134:@[ext] lemma ext {X Y : C} {f g : X ⟶ Y} (h : hom f = hom g) : f = g :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:533:protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
.lake/packages/mathlib/Mathlib/Analysis/Complex/Circle.lean:63:@[ext] lemma ext : (x : ℂ) = y → x = y := Subtype.ext
.lake/packages/mathlib/Mathlib/Dynamics/Circle/RotationNumber/TranslationNumber.lean:163:theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean:129:@[ext] lemma ext {f g : StieltjesFunction R} (h : ∀ x, f x = g x) : f = g := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Idempotents/Karoubi.lean:59:theorem ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/Arrow.lean:149:lemma ext {f g : Arrow T}
.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/Presheaf/Basic.lean:133:lemma ext {F : Cᵒᵖ ⥤ Type v} {η : F ⟶ A} {X : C} {s : yoneda.obj X ⟶ A}
.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/Presheaf/Basic.lean:298:lemma ext {p q : YonedaCollection F X} (h : p.fst = q.fst)
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:143:theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
.lake/packages/mathlib/Mathlib/Dynamics/Flow.lean:114:theorem ext : ∀ {ϕ₁ ϕ₂ : Flow τ α}, (∀ t x, ϕ₁ t x = ϕ₂ t x) → ϕ₁ = ϕ₂
.lake/packages/mathlib/Mathlib/CategoryTheory/Center/Basic.lean:45:lemma ext (x y : CatCenter C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/ConcreteSheafification.lean:63:theorem ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq P S) (h : ∀ I : S.Arrow, x I = y I) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean:189:theorem ext {A B : StructuredArrow S T} (f g : A ⟶ B) : f.right = g.right → f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean:572:theorem ext {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left) : f = g :=
.lake/packages/mathlib/Mathlib/Order/RelSeries.lean:70:lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean:154:lemma ext (β : BasedNatTrans F G) (h : α.toNatTrans = β.toNatTrans) : α = β := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/MayerVietorisSquare.lean:188:lemma ext {x y : P.obj (op S.X₄)}
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean:117:protected lemma ext (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean:241:protected lemma ext (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Reproducing.lean:70:lemma ext {f g : H} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean:112:protected lemma ext (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
.lake/packages/mathlib/Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean:231:protected lemma ext (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Grothendieck.lean:105:theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) : J₁ = J₂ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Grothendieck.lean:439:theorem ext (S T : J.Cover X) (h : ∀ ⦃Y⦄ (f : Y ⟶ X), S f ↔ T f) : S = T :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/TwoSquare.lean:78:lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.natTrans.app X = w'.natTrans.app X) :
.lake/packages/mathlib/Mathlib/Analysis/VonNeumannAlgebra/Basic.lean:114:theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Cones.lean:300:def ext {c c' : Cone F} (φ : c.pt ≅ c'.pt)
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:139:theorem ext {z w : K} (hre : re z = re w) (him : im z = im w) : z = w :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Sieves.lean:520:protected theorem ext {R S : Sieve X} (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) : R = S :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:224:lemma ext {A B : E →SWOT[σ] F} (h : ∀ x, A x = B x) : A = B :=
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Partition/Basic.lean:102:theorem ext (h : ∀ J, J ∈ π₁ ↔ J ∈ π₂) : π₁ = π₂ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Category.lean:61:theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/CoversTop/Basic.lean:64:lemma ext (F : Sheaf J A) {c : Cone F.1} (hc : IsLimit c) {X : A} {f g : X ⟶ c.pt}
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/Box/Basic.lean:174:theorem ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Yoneda.lean:164:def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
.lake/packages/mathlib/Mathlib/CategoryTheory/Yoneda.lean:230:def ext (X Y : C) (p : ∀ {Z : C}, (X ⟶ Z) → (Y ⟶ Z))
.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean:165:lemma ext {α β : FunSpace t₀ x₀ r L} (h : ∀ t, α t = β t) : α = β := by
.lake/packages/mathlib/Mathlib/MeasureTheory/PiSystem.lean:528:theorem ext : ∀ {d₁ d₂ : DynkinSystem α}, (∀ s : Set α, d₁.Has s ↔ d₂.Has s) → d₁ = d₂
.lake/packages/mathlib/Mathlib/CategoryTheory/Grothendieck.lean:93:theorem ext {X Y : Grothendieck F} (f g : Hom X Y) (w_base : f.base = g.base)
.lake/packages/mathlib/Mathlib/CategoryTheory/SmallObject/Iteration/Basic.lean:353:lemma ext (h : ∀ (k₁ k₂ : K) (h₁₂ : k₁ ≤ k₂) (h₂ : k₂ ≤ x),
.lake/packages/mathlib/Mathlib/CategoryTheory/MorphismProperty/Basic.lean:61:lemma ext (W W' : MorphismProperty C) (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:126:theorem ext [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)}
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean:116:def ext {c c' : Bicone F} (φ : c.pt ≅ c'.pt)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean:96:theorem ext (I J : HasZeroMorphisms C) : I = J := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Images.lean:105:theorem ext {F F' : MonoFactorisation f} (hI : F.I = F'.I)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean:108:def ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/End.lean:86:def ext {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/End.lean:150:def ext {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/WidePullbacks.lean:448:def ext {ι : Type*}
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Multiequalizer.lean:560:def ext {t s : Multifork I} (e : t.pt ≅ s.pt)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Multiequalizer.lean:929:def ext {K K' : Multicofork I}
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:143:theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Enriched/Basic.lean:323:lemma ext {C : Type u₁} {D : Type u₂} [EnrichedCategory V C]
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean:156:def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
.lake/packages/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean:374:def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
.lake/packages/mathlib/Mathlib/CategoryTheory/Pi/Basic.lean:50:lemma ext {X Y : ∀ i, C i} {f g : X ⟶ Y} (w : ∀ i, f i = g i) : f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Grp.lean:345:lemma ext {X : C} (h₁ h₂ : GrpObj X) (H : h₁.toMonObj = h₂.toMonObj) : h₁ = h₂ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Bimon_.lean:72:@[ext] lemma ext {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Endomorphism.lean:67:lemma ext {x y : End X} (h : asHom x = asHom y) : x = y := h
.lake/packages/mathlib/Mathlib/CategoryTheory/Endomorphism.lean:125:lemma ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mon.lean:140:theorem ext {X : C} (h₁ h₂ : MonObj X) (H : h₁.mul = h₂.mul) : h₁ = h₂ := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Comon_.lean:181:@[ext] lemma ext {X Y : Comon C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/AEEqFun.lean:178:theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:66:theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ H
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mod.lean:77:theorem ext {X : C} (h₁ h₂ : ModObj M X) (H : h₁.smul = h₂.smul) :
.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:247:@[ext] theorem ext {e₁ e₂ : α ≃ᵐ β} (h : (e₁ : α → β) = e₂) : e₁ = e₂ := DFunLike.ext' h
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Center.lean:93:theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean:204:theorem ext {μ₁ μ₂ : OuterMeasure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:123:theorem ext {s t : VectorMeasure α M} (h : ∀ i : Set α, MeasurableSet i → s i = t i) : s = t :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) holderSeminorm_nonneg(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderSpace.lean:331:theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_mul_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderSpace.lean:390:theorem norm_mul_le (f g : Y (E := E) α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:206:theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:98:theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
.lake/packages/mathlib/Mathlib/GroupTheory/FreeGroup/Reduce.lean:387:theorem norm_mul_le (x y : FreeGroup α) : norm (x * y) ≤ norm x + norm y :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) smul_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Hom.lean:31:@[simp] theorem smul_apply [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A) :
.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/Action/Hom.lean:75:@[simp] theorem smul_apply [DistribSMul M B] (m : M) (f : A →+ B) (a : A) : (m • f) a = m • f a :=
.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:288:lemma smul_apply (a : A) (x : R[M]) (m : M) : (a • x) m = a • x m := rfl
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:461:theorem smul_apply' (s : S) (g : (restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
.lake/packages/mathlib/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:528:theorem smul_apply (M : ModuleCat R) (g : (coextendScalars f).obj M) (s s' : S) :
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:404:lemma smul_apply (a : A) (f : IntertwiningMap ρ σ) (v : V) :
.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Module/Basic.lean:151:theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
.lake/packages/mathlib/Mathlib/Algebra/Ring/CentroidHom.lean:314:theorem smul_apply (n : M) (f : CentroidHom α) (a : α) : (n • f) a = n • f a :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Hom.lean:84:theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
Poincare/Global/ParabolicHolderSpace.lean:214:@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:750:theorem smul_apply (a : S) (f : M →ₛₗ[σ₁₂] M₂) (x : M) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:281:theorem smul_apply [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpace.lean:914:theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
.lake/packages/mathlib/Mathlib/Algebra/Module/CharacterModule.lean:73:@[simp] lemma smul_apply (c : CharacterModule A) (r : R) (a : A) : (r • c) a = c (r • a) := rfl
.lake/packages/mathlib/Mathlib/Algebra/Module/Equiv/Defs.lean:626:@[simp] theorem smul_apply (α : Sˣ) (e : V ≃ₗ[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Module.lean:56:theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Basic.lean:853:theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
.lake/packages/mathlib/Mathlib/MeasureTheory/VectorMeasure/Basic.lean:271:theorem smul_apply (r : R) (v : VectorMeasure α M) (i : Set α) : (r • v) i = r • v i := rfl
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:168:theorem smul_apply [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E)
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:162:theorem smul_apply' (m : M) (s : SummableFamily Γ R α) (a : α) : (m • s) a = m • s a :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Summable.lean:493:theorem smul_apply {x : R⟦Γ⟧} {s : SummableFamily Γ' V α} {a : α} :
.lake/packages/mathlib/Mathlib/MeasureTheory/OuterMeasure/Operations.lean:93:theorem smul_apply (c : R) (m : OuterMeasure α) (s : Set α) : (c • m) s = c • m s :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Derivation/Basic.lean:252:theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/MeasureTheory/Function/SimpleFunc.lean:478:theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
.lake/packages/mathlib/Mathlib/Algebra/Order/CauSeq/Basic.lean:315:theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean:123:@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:123:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:246:theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Pi.lean:41:lemma smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:202:@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:443:theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:458:theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Seminorm.lean:649:theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean:75:theorem smul_apply [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F]
.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean:222:theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Synonym.lean:342:theorem smul_apply : (c • x) i = c • x i :=
.lake/packages/mathlib/Mathlib/Data/Finsupp/SMulWithZero.lean:59:theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:1328:@[simp] theorem smul_apply (e : V ≃ₗᵢ[𝕜] W) (α : unitary 𝕜) (x : V) :
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:261:theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/Basic.lean:454:theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:243:@[simp] lemma smul_apply {f : E →SWOT[σ] F} (c : S) (x : E) : (c • f) x = c • (f x) := rfl
.lake/packages/mathlib/Mathlib/RingTheory/AdicCompletion/Basic.lean:496:theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean:153:theorem smul_apply (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
.lake/packages/mathlib/Mathlib/Data/DFinsupp/Module.lean:37:theorem smul_apply [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
.lake/packages/mathlib/Mathlib/Topology/Algebra/ContinuousAffineMap.lean:267:theorem smul_apply (t : S) (f : P →ᴬ[R] W) (x : P) : (t • f) x = t • f x := rfl
.lake/packages/mathlib/Mathlib/RingTheory/Derivation/Basic.lean:226:theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Equiv.lean:1440:@[simp] theorem smul_apply (α : Sˣ) (e : V ≃L[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean:175:theorem smul_apply (f : M [⋀^ι]→L[A] N) (c : R') (v : ι → M) : (c • f) v = c • f v :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/DomAct/Basic.lean:167:theorem smul_apply [SMul M α] (c : Mᵈᵐᵃ) (f : α → β) (a : α) : (c • f) a = f (mk.symm c • a) := rfl
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:269:theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/Embedding.lean:41:theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/UniformConvergenceCLM.lean:228:theorem smul_apply {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean:147:theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean:230:lemma smul_apply {G : Type*} [Π i, SMul G (R i)] [∀ i, SMulMemClass (S i) G (R i)] (g : G)
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/ZeroAtInfty.lean:214:theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:545:theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Algebra.lean:818:lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean:717:theorem smul_apply (c : 𝕜) (f : α →ᵇ β) (x : α) : (c • f) x = c • f x := rfl
.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/SMul.lean:47:theorem smul_apply (g : G) (b : Basis ι R M) (i : ι) : (g • b) i = g • b i := rfl
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean:255:theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean:233:theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean:210:theorem smul_apply (f : MultilinearMap R M₁ M₂) (c : S) (m : ∀ i, M₁ i) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/LinearPMap.lean:386:theorem smul_apply (a : M) (f : E →ₛₗ.[σ] F) (x : (a • f).domain) : (a • f) x = a • f x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Module.lean:56:lemma smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
.lake/packages/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean:415:theorem smul_apply (a : S) (Q : QuadraticMap R M N) (x : M) : (a • Q) x = a • Q x :=
.lake/packages/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean:215:theorem smul_apply (c : S) (m : ι → M) : (c • f) m = c • f m :=
.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Algebra.lean:143:theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean:255:lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
.lake/packages/mathlib/Mathlib/Tactic/Module.lean:159:@[simp] theorem smul_apply [Mul R] (r : R) (l : NF R M) : r • l = l.map fun (a, x) ↦ (r * a, x) :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) supNorm_nonneg(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderSpace.lean:327:theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
.lake/packages/mathlib/Mathlib/Analysis/Polynomial/Norm.lean:66:lemma supNorm_nonneg : 0 ≤ p.supNorm := by
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) error_small(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:245:theorem error_small (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) forcing(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:154:def forcing (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (G : Graph («E» := E) α T) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) forcing_apply(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:168:@[simp] theorem forcing_apply (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) forcing_eq_sum(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:173:theorem forcing_eq_sum (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_entry_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:95:theorem norm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_error_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:224:theorem norm_error_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_forcing_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicHolderMultiplier.lean:203:theorem norm_forcing_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_ddu_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParabolicSolutionGraph.lean:113:theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) correctedInverse(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
Poincare/Global/ParametrixNeumannCorrection.lean:22:def correctedInverse (P : Y →L[ℝ] X) (R : Y →L[ℝ] Y) (hR : ‖R‖ < 1) : Y →L[ℝ] X :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) rpow_nonneg(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:163:theorem rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:412:lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) oneSub(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
EXIT 1
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) oneSub_val(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
EXIT 1
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) val_inv(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Star/SelfAdjoint.lean:457:theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
.lake/packages/mathlib/Mathlib/RingTheory/HopfAlgebra/GroupLike.lean:62:@[simp] lemma val_inv (a : GroupLike R A) : ↑(a⁻¹) = (antipode R a : A) := rfl
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) add_mul(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:357:protected theorem add_mul [Fintype m] (L M : Matrix l m α) (N : Matrix m n α) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:331:protected theorem add_mul {l : Type*} [Fintype m] [NonUnitalNonAssocSemiring A]
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:282:protected theorem add_mul (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
.lake/packages/mathlib/Mathlib/Tactic/Ring/Common.lean:681:theorem add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : c₁ + c₂ = d) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) congrArg(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
EXIT 1
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) inv_le_comm₀(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean:1228:lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) ite_mul(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Notation/Defs.lean:112:lemma ite_mul (a b c : α) : (if P then a else b) * c = if P then a * c else b * c := dite_mul ..
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_add(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:352:protected theorem mul_add [Fintype n] (L : Matrix m n α) (M N : Matrix n o α) :
.lake/packages/mathlib/Mathlib/Tactic/Ring/Common.lean:660:theorem mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : c₁ + 0 + c₂ = d) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:278:protected theorem mul_add (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:327:protected theorem mul_add {o : Type*} [Fintype n] [NonUnitalNonAssocSemiring A]
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_assoc(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:482:protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Ring.lean:233:private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
.lake/packages/mathlib/Mathlib/Data/Holor.lean:157:theorem mul_assoc [Semigroup α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:191:theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean:595:private theorem mul_assoc' [NonUnitalSemiring R] (x y z : R⟦Γ⟧) : x * y * z = x * (y * z) := by
.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorPower/Basic.lean:169:theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
.lake/packages/mathlib/Mathlib/RingTheory/MvPowerSeries/Basic.lean:286:protected theorem mul_assoc (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : φ₁ * φ₂ * φ₃ = φ₁ * (φ₂ * φ₃) := by
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:128:protected lemma mul_assoc (x y z : ⨂[R] i, A i) : mul (mul x y) z = mul x (mul y z) := by
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:309:protected theorem mul_assoc : I * J * K = I * (J * K) :=
.lake/packages/mathlib/Mathlib/GroupTheory/OreLocalization/Basic.lean:399:protected theorem mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) :=
.lake/packages/mathlib/Mathlib/RingTheory/TensorProduct/Basic.lean:234:protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
.lake/packages/mathlib/Mathlib/GroupTheory/EckmannHilton.lean:82:theorem mul_assoc : Std.Associative m₂ :=
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_comm(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean:789:protected theorem mul_comm : M * N = N * M :=
.lake/packages/mathlib/Mathlib/Algebra/DirectSum/Ring.lean:309:private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
.lake/packages/mathlib/Mathlib/Data/EReal/Basic.lean:188:protected theorem mul_comm (x y : EReal) : x * y = y * x := by
.lake/packages/mathlib/Mathlib/Algebra/Symmetrized.lean:289:theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:224:lemma mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Defs.lean:258:theorem mul_comm : ∀ a b : G, a * b = b * a := CommMagma.mul_comm
.lake/packages/mathlib/Mathlib/Data/Num/ZNum.lean:434:private theorem mul_comm : ∀ (a b : ZNum), a * b = b * a := by transfer
.lake/packages/mathlib/Mathlib/Tactic/Translate/ToAdditive.lean:40:theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y
.lake/packages/mathlib/Mathlib/Tactic/Translate/ToAdditive.lean:58:theorem mul_comm' {α} [CommSemigroup α] (x y : α) : x * y = y * x := CommSemigroup.mul_comm
.lake/packages/mathlib/Mathlib/GroupTheory/EckmannHilton.lean:75:theorem mul_comm : Std.Commutative m₂ :=
.lake/packages/mathlib/Mathlib/RingTheory/PiTensorProduct.lean:245:protected lemma mul_comm (x y : ⨂[R] i, A i) : mul x y = mul y x := by
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Operations.lean:566:protected theorem mul_comm : I * J = J * I :=
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mon.lean:1204:lemma mul_comm' [IsCommMonObj M] : (β_ M M).inv ≫ μ = μ := by simp [← cancel_epi (β_ M M).hom]
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_le_mul(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Ring/Submonoid/Pointwise.lean:176:@[mono, gcongr] lemma mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q := smul_le_smul hmp hnq
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:74:theorem mul_le_mul [MulZeroClass α] [Preorder α] [PosMulMono α] [MulPosMono α]
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:87:theorem mul_le_mul' [Mul α] [Preorder α] [MulLeftMono α]
.lake/packages/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:208:theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_le_mul_of_nonneg_left(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/StandardPart.lean:185:private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:226:theorem mul_le_mul_of_nonneg_left [PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c :=
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:66:theorem mul_le_mul_of_nonneg_left [Mul α] [Zero α] [Preorder α] [PosMulMono α]
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) mul_le_mul_of_nonneg_right(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:230:theorem mul_le_mul_of_nonneg_right [MulPosMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : b * a ≤ c * a :=
.lake/packages/mathlib/Mathlib/Tactic/GCongr/Core.lean:70:theorem mul_le_mul_of_nonneg_right [Mul α] [Zero α] [Preorder α] [MulPosMono α]
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_nonneg(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/FiniteExtension.lean:75:protected theorem norm_nonneg (x : L) : 0 ≤ B.norm x := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:468:theorem norm_nonneg' (f : lp E p) : 0 ≤ ‖f‖ := by
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:182:protected lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self (A := A)]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:124:theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:125:theorem norm_nonneg (x : L) : 0 ≤ v.norm x := by simp only [norm, NNReal.zero_le_coe]
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:34:protected theorem norm_nonneg (z : ℂ) : 0 ≤ ‖z‖ :=
.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:421:protected theorem norm_nonneg (x : mixedSpace K) :
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/Basic.lean:461:theorem norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
.lake/packages/mathlib/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:138:theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicNumbers.lean:256:theorem norm_nonneg (f : PadicSeq p) : 0 ≤ f.norm := by
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) norm_sum_le(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:829:theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) smul_eq_mul(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Defs.lean:401:theorem smul_eq_mul (x y : R) : x • y = x * y :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Units.lean:95:lemma smul_eq_mul {M} [CommMonoid M] (u₁ u₂ : Mˣ) :
.lake/packages/mathlib/Mathlib/Algebra/Group/Action/Defs.lean:73:lemma smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b := rfl
.lake/packages/mathlib/Mathlib/Tactic/Ring/Basic.lean:352:lemma smul_eq_mul {α : Type*} [Mul α] {a a' : α} (h : a = a') (b : α) : a • b = a' * b := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Monoidal/Mod.lean:68:@[simp] lemma smul_eq_mul (M : C) [MonObj M] : γ[M,M] = μ[M] := rfl
EXIT 0
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) sub_eq_iff_eq_add(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
EXIT 1
$ rg -n -m 2 \b(?:theorem|lemma|def|abbrev|structure) tsum_geometric_le_of_norm_lt_one(?:\s|\.|\b) Poincare/Global .lake/packages/mathlib/Mathlib --glob *.lean
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean:293:theorem tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
EXIT 0
```

</details>

## Delivery whitespace check

The first staged check reported an extra blank line at the end of this report;
the final newline was normalized before the documentation commit.

```text
$ git diff --cached --check
harness/reports/near-identity-parabolic-right-inverse_done.md:6367: new blank line at EOF.
EXIT 2
```
