# Duhamel solution operator CLM: done

Date: 2026-09-15. Branch: `worker/duhamel-solution-operator-clm`.
Base: `2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df`. Verified proof head: `baa4386568376ddd91224b0750902a628a14f914`.

## Result

The exact requested continuous linear operator and all three theorems compile:
`duhamelOperator`, `duhamelOperator_u`, `duhamelOperator_norm_le`, and
`duhamelOperator_solves`, in `Poincare.DuhamelSolutionOperatorCLM`.
The equation uses the same sum over the three coordinate basis vectors as
`MovingLimitLeibniz.duhamel_solves_heat_equation` and includes both endpoints.
The norm constant depends only on α, uniformly over `0 < T ≤ 1`.

`ParabolicSolutionGraph.Graph.ext_of_u` is proved for every real normed space
and positive T. No additional extensionality hypothesis is required.
The graph derivative fields determine the spatial derivatives; uniqueness of
`derivWithin` on `Icc 0 T` determines the time derivative. The carrier's existing
extensionality theorem handles its zero extension outside the cylinder.

The construction selects the constant and graph from the landed existence
estimate. Integral additivity uses positive-time convolution integrability and
the landed time-integrability theorem. Scalar linearity follows by pulling the
scalar through both integrals. Graph uniqueness gives the linear map, and
`LinearMap.mkContinuous` with the landed norm estimate gives the operator.
The heat equation follows by identifying the stored derivatives with actual
Fréchet derivatives and transferring the landed time derivative on the interval.

## Acceptance evidence

- Exact module command exits 0, with no output on the final source.
- Forbidden-token scan is empty; ripgrep exits 1, meaning no matches.
- All 12 new declarations have exactly `[propext, Classical.choice, Quot.sound]`.
- Explicit type-assignment probes for all four deliverables exit 0.
- `git diff --check` exits 0, including the full proof diff from the base.
- Each verified item was committed separately. The commits appear in the log below.
- No existing Lean module, root import, or frozen task file was changed.

This is a worker result awaiting independent orchestration review. It is not
merged or accepted. No full build or root integration audit was run.

## Resolved probes

`HasDerivWithinAt.unique`, `MeasureTheory.convolution_add`, and
`MeasureTheory.convolution_add_distrib` do not exist in this pinned Mathlib.
The used names are `HasDerivWithinAt.derivWithin`, `uniqueDiffOn_Icc`, and
`MeasureTheory.ConvolutionExistsAt.distrib_add`, verified by source searches and
Lean output below. A named-argument parse failure caused by local notation `E`
was fixed with the landed spelling `«E»`. An initial scalar-integral simplifier
attempt left the nested-integral equality shown in the compiler output; the
final proof explicitly moves the scalar with `mul_left_comm` before applying
both integral scalar rules. The final source has no remaining goals or warnings.

## Handoff

First action for the reviewer:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
```

Then rerun the dependency and exact-type probes below, inspect the base-to-head
diff, and decide acceptance. `HANDOFF.md` receives a dated worker-result entry.

## Probe sources

The dependency gate copies the final module into `/private/tmp/dclm_check.lean`
and appends `#print axioms` for each declaration. The exact-type probe similarly
copies the final module and appends the type assignments below. Neither probe
relies on a stale olean of the new module.

### dclm_probe.lean

```lean
import Poincare.Global.DuhamelSolutionOperatorBound
set_option pp.proofs false
#print Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound
#print Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound
#print Poincare.ParabolicHolder.ext
#print Poincare.ParabolicHolder.hasHolderBound
#print Poincare.ParabolicHolder.norm_le
#print Poincare.ParabolicSolutionGraph.Graph
#check HasDerivWithinAt.unique
#check uniqueDiffOn_Icc
#print Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation
#print Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time
#print Poincare.heatSolution
```

### dclm_probe2.lean

```lean
import Poincare.Global.DuhamelSolutionOperatorBound
set_option pp.proofs false
#print Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous
#print Poincare.heatSolution_apply
#print Poincare.ParabolicHolder.add_apply
#print Poincare.ParabolicHolder.smul_apply
#print Poincare.ParabolicSolutionGraph.graphEquiv
#check MeasureTheory.convolution_add
#check MeasureTheory.convolution_add_distrib
#check MeasureTheory.convolution_smul
#check HasDerivWithinAt.derivWithin
#check HasDerivWithinAt.congr_of_mem
#check LinearMap.mkContinuous
#check LinearMap.mkContinuous_norm_le
```

### dclm_probe3.lean

```lean
import Poincare.Global.DuhamelSolutionOperatorBound
#check MeasureTheory.ConvolutionExistsAt.distrib_add
#check intervalIntegral.integral_congr_ae_restrict
#check intervalIntegral.integral_smul
#check intervalIntegral.integral_const_mul
#check HasFDerivAt.fderiv
```

### dclm_contract_suffix.txt

```lean

namespace DuhamelContractProbe
open Poincare Poincare.DuhamelSolutionOperatorCLM
local notation "E" => ClosedSmoothModel 3
example (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ParabolicHolder.Y («E» := E) α T ℝ →L[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T :=
  duhamelOperator α T hα hα1 hT hT1
example (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : ParabolicHolder.Y («E» := E) α T ℝ) :
    ∀ p ∈ ParabolicHolder.cylinder T,
      (duhamelOperator α T hα hα1 hT hT1 f).u p =
        ∫ s in (0 : ℝ)..p.1, heatSolution (p.1 - s) (fun y => f (s,y)) p.2 :=
  duhamelOperator_u α T hα hα1 hT hT1 f
example : ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1), ∃ C : ℝ, 0 < C ∧
    ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1), ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ C :=
  duhamelOperator_norm_le
example (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : ParabolicHolder.Y («E» := E) α T ℝ) :
    ∀ t ∈ Icc 0 T, ∀ x : E,
      (duhamelOperator α T hα hα1 hT hT1 f).ut (t,x) = f (t,x) +
      ∑ i : Fin 3, (duhamelOperator α T hα hα1 hT hT1 f).ddu (t,x)
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
  duhamelOperator_solves α T hα hα1 hT hT1 f
end DuhamelContractProbe
```

### Gate runner

```python
import pathlib,subprocess,re,sys
p=pathlib.Path('Poincare/Global/DuhamelSolutionOperatorCLM.lean')
s=p.read_text()
names=[]
for x in re.findall(r'^(?:def|theorem) (\S+)',s,re.M):
 names.append(('Poincare.ParabolicSolutionGraph.' if x=='Graph.ext_of_u' else 'Poincare.DuhamelSolutionOperatorCLM.')+x)
pathlib.Path('/private/tmp/dclm_check.lean').write_text(s+'\n'+'\n'.join('#print axioms '+n for n in names)+'\n')
commands=['LEAN_NUM_THREADS=1 lake env lean '+str(p),'LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean',r"rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' "+str(p),'git diff --check']
for i,c in enumerate(commands):
 r=subprocess.run(c,shell=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 out='$ '+c+'\n'+r.stdout+'\nexit '+str(r.returncode)+'\n'
 with open('/private/tmp/dclm_evidence.log','a') as f:f.write(out)
 print(out,flush=True)
 if r.returncode != (1 if i==2 else 0):sys.exit(1)
 if i==1 and (r.stdout.count('[propext, Classical.choice, Quot.sound]')!=len(names)):sys.exit('dependency mismatch')
```

## Actual command output

```text
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_probe.lean
theorem Poincare.DuhamelSolutionOperatorBound.exists_solution_graph_bound : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∃ C,
        0 < C ∧
          ∀ (T : ℝ),
            0 < T →
              T ≤ 1 →
                ∀ (f : Poincare.ParabolicHolder.Y α T ℝ),
                  ∃ G,
                    (∀ p ∈ Poincare.ParabolicHolder.cylinder T,
                        ↑(WithLp.fst ↑G.u) p =
                          ∫ (s : ℝ) in 0..p.1, Poincare.heatSolution (p.1 - s) (fun y => ↑(WithLp.fst ↑f) (s, y)) p.2) ∧
                      ‖G‖ ≤ C * ‖f‖ :=
⋯
theorem Poincare.DuhamelSolutionOperatorBound.continuousOn_of_hasHolderBound.{u_1} : ∀ {F : Type u_1}
  [inst : NormedAddCommGroup F] {α T K : ℝ},
  0 < α →
    ∀ {g : ℝ × Poincare.ClosedSmoothModel 3 → F},
      Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) g K →
        ContinuousOn g (Poincare.ParabolicHolder.cylinder T) :=
⋯
theorem Poincare.ParabolicHolder.ext.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} {f g : Poincare.ParabolicHolder.Y α T F},
  (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p) → f = g :=
⋯
theorem Poincare.ParabolicHolder.hasHolderBound.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ‖f‖ :=
⋯
theorem Poincare.ParabolicHolder.norm_le.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F)
  (p : ℝ × E), ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖ :=
⋯
structure Poincare.ParabolicSolutionGraph.Graph.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (α T : ℝ) : Type u_1
number of parameters: 5
fields:
  Poincare.ParabolicSolutionGraph.Graph.u : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.ut : Poincare.ParabolicHolder.Y α T ℝ
  Poincare.ParabolicSolutionGraph.Graph.du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)
  Poincare.ParabolicSolutionGraph.Graph.zero_trace : ∀ (x : E), ↑(WithLp.fst ↑self.u) (0, x) = 0
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.u) (t, z)) (↑(WithLp.fst ↑self.du) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.du) (t, z)) (↑(WithLp.fst ↑self.ddu) (t, x)) x
  Poincare.ParabolicSolutionGraph.Graph.hasDeriv_time : ∀ t ∈ Set.Icc 0 T,
      ∀ (x : E),
        HasDerivWithinAt (fun s => ↑(WithLp.fst ↑self.u) (s, x)) (↑(WithLp.fst ↑self.ut) (t, x)) (Set.Icc 0 T) t
constructor:
  Poincare.ParabolicSolutionGraph.Graph.mk.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
    (u ut : Poincare.ParabolicHolder.Y α T ℝ) (du : Poincare.ParabolicHolder.Y α T (E →L[ℝ] ℝ))
    (ddu : Poincare.ParabolicHolder.Y α T (E →L[ℝ] E →L[ℝ] ℝ)) (zero_trace : ∀ (x : E), ↑(WithLp.fst ↑u) (0, x) = 0)
    (hasFDeriv :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑u) (t, z)) (↑(WithLp.fst ↑du) (t, x)) x)
    (hasFDeriv_du :
      ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑du) (t, z)) (↑(WithLp.fst ↑ddu) (t, x)) x)
    (hasDeriv_time :
      ∀ t ∈ Set.Icc 0 T,
        ∀ (x : E), HasDerivWithinAt (fun s => ↑(WithLp.fst ↑u) (s, x)) (↑(WithLp.fst ↑ut) (t, x)) (Set.Icc 0 T) t) :
    Poincare.ParabolicSolutionGraph.Graph α T
/private/tmp/dclm_probe.lean:9:7: error(lean.unknownIdentifier): Unknown constant `HasDerivWithinAt.unique`
uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Set.Icc a b)
theorem Poincare.MovingLimitLeibniz.duhamel_solves_heat_equation : ∀ (α : ℝ),
  0 < α →
    α < 1 →
      ∀ (T : ℝ),
        0 < T →
          T ≤ 1 →
            ∀ (f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ) (M K : ℝ),
              0 ≤ M →
                0 ≤ K →
                  ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
                    (∀ t ∈ Set.Icc 0 T, ∀ (x : Poincare.ClosedSmoothModel 3), |f (t, x)| ≤ M) →
                      (∀ t ∈ Set.Icc 0 T,
                          ∀ (x y : Poincare.ClosedSmoothModel 3), |f (t, x) - f (t, y)| ≤ K * ‖x - y‖ ^ α) →
                        have u := fun t x => ∫ (s : ℝ) in 0..t, Poincare.heatSolution (t - s) (fun y => f (s, y)) x;
                        (∀ (x : Poincare.ClosedSmoothModel 3), u 0 x = 0) ∧
                          ∀ t ∈ Set.Icc 0 T,
                            ∀ (x : Poincare.ClosedSmoothModel 3),
                              HasDerivWithinAt (fun r => u r x)
                                (f (t, x) +
                                  ∑ i,
                                    ((fderiv ℝ (fderiv ℝ (u t)) x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                      ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
                                (Set.Icc 0 T) t :=
⋯
theorem Poincare.HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time : ∀ {T t M : ℝ},
  t ∈ Set.Icc 0 T →
    ∀ {f : ℝ × Poincare.ClosedSmoothModel 3 → ℝ},
      ContinuousOn f (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc 0 T, ∀ (y : Poincare.ClosedSmoothModel 3), |f (s, y)| ≤ M) →
          ∀ (x : Poincare.ClosedSmoothModel 3),
            IntervalIntegrable (fun s => Poincare.heatSolution (t - s) (fun y => f (s, y)) x) MeasureTheory.volume 0
              t :=
⋯
def Poincare.heatSolution.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : InnerProductSpace ℝ E] →
      [FiniteDimensional ℝ E] → [inst_3 : MeasurableSpace E] → [BorelSpace E] → ℝ → (E → ℝ) → E → ℝ :=
fun {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] t f =>
  MeasureTheory.convolution (fun x => Poincare.heatKernel t x) f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

exit 1
$ rg -n 'HasDerivWithinAt.*unique|unique.*HasDerivWithinAt|mkContinuous_norm_le|theorem.*integrable.*mul.*data|theorem integrable_heatKernel' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean Poincare/Global/HeatKernelIntegral.lean Poincare/Global/HeatCauchyTheorem.lean; sed -n '380,400p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean; sed -n '80,110p' Poincare/Global/HeatKernelIntegral.lean; sed -n '35,65p' Poincare/Global/VectorHeatCauchy.lean
Poincare/Global/HeatCauchyTheorem.lean:107:theorem integrable_heatKernelFirstSpatialEnvelope {t : ℝ} (ht : 0 < t) (A : ℝ) (x : E) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:483:theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:489:theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
  HasFDerivAt.hasFDerivAtFilter h hL

theorem HasDerivAt.hasDerivWithinAt (h : HasDerivAt f f' x) : HasDerivWithinAt f f' s x :=
  HasFDerivAt.hasFDerivWithinAt h

theorem HasDerivWithinAt.differentiableWithinAt (h : HasDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  HasFDerivWithinAt.differentiableWithinAt h

theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  HasFDerivAt.differentiableAt h

@[simp]
theorem hasDerivWithinAt_univ : HasDerivWithinAt f f' univ x ↔ HasDerivAt f f' x :=
  hasFDerivWithinAt_univ

theorem HasDerivAt.unique (h₀ : HasDerivAt f f₀' x) (h₁ : HasDerivAt f f₁' x) : f₀' = f₁' :=
  toSpanSingleton_inj.mp <| h₀.hasFDerivAt.unique h₁

theorem hasDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasDerivWithinAt f f' (s ∩ t) x ↔ HasDerivWithinAt f f' s x :=
    field_simp [ht.ne']
  rw [hscale]
  rw [← Real.rpow_add hbase]
  ring_nf
  simp

/-- Heat evolution as convolution with the positive-time heat kernel. -/
def heatSolution (t : ℝ) (f : E → ℝ) : E → ℝ :=
  MeasureTheory.convolution (fun x : E => heatKernel (E := E) t x) f
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

/-- The defining integral formula for `heatSolution`. -/
@[simp]
theorem heatSolution_apply (t : ℝ) (f : E → ℝ) (x : E) :
    heatSolution (E := E) t f x =
      ∫ y : E, heatKernel (E := E) t y * f (x - y) := by
  simp [heatSolution, MeasureTheory.convolution_lsmul, smul_eq_mul]

/--
The heat-kernel convolution integrand is integrable at every point for bounded
continuous real-valued initial data.
-/
theorem heatKernel_convolutionExistsAt_of_bounded_continuous {t : ℝ} (ht : 0 < t)
    {f : E → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (x : E) :
    ConvolutionExistsAt (fun y : E => heatKernel (E := E) t y) f x
      (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  rw [ConvolutionExistsAt]
  have hshift_meas : AEStronglyMeasurable (fun y : E => f (x - y)) volume := by
    exact (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hshift_mem : MemLp (fun y : E => f (x - y)) ⊤ volume := by
    exact memLp_top_of_bound hshift_meas C

omit [FiniteDimensional ℝ F] in
/-- A bounded strongly measurable vector field has an integrable positive-time
heat-convolution integrand. -/
theorem integrable_heatKernel_smul_vectorData
    {t C : ℝ} (ht : 0 < t) {f : E → F}
    (hf : AEStronglyMeasurable f volume) (hC : ∀ y, ‖f y‖ ≤ C)
    (x : E) :
    Integrable (fun y : E ↦ heatKernel (E := E) t (x - y) • f y) volume := by
  have hker : Integrable (fun y : E ↦ heatKernel (E := E) t (x - y)) :=
    heatKernel_integrable_sub_left (E := E) ht x
  have hmeas : AEStronglyMeasurable
      (fun y : E ↦ heatKernel (E := E) t (x - y) • f y) volume := by
    have hkcont : Continuous (fun y : E ↦ heatKernel (E := E) t (x - y)) :=
      (contDiff_heatKernel_spatial (E := E) t).continuous.comp
        (continuous_const.sub continuous_id)
    exact hkcont.aestronglyMeasurable.smul hf
  refine (hker.const_mul C).mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hk_nonneg : 0 ≤ heatKernel (E := E) t (x - y) :=
    heatKernel_nonneg (E := E) ht (x - y)
  calc
    ‖heatKernel (E := E) t (x - y) • f y‖
        = heatKernel (E := E) t (x - y) * ‖f y‖ := by
          rw [norm_smul, Real.norm_of_nonneg hk_nonneg]
    _ ≤ heatKernel (E := E) t (x - y) * C :=
      mul_le_mul_of_nonneg_left (hC y) hk_nonneg
    _ = C * heatKernel (E := E) t (x - y) := by ring

/-- Continuous linear coordinates commute with the Bochner heat convolution. -/

exit 0
$ rg -n 'theorem HasDerivWithinAt.derivWithin|theorem.*convolution_add|theorem.*convolution_smul|def mkContinuous' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Convolution.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean; rg -n 'theorem.*congr_of_mem|theorem HasFDerivAt.fderiv' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:440:theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:441:theorem HasDerivWithinAt.derivWithin (h : HasDerivWithinAt f f' s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:569:theorem HasDerivWithinAt.congr_of_mem (h : HasDerivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:409:protected theorem HasFDerivAt.fderiv

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 0
$ sed -n '408,448p' .lake/packages/mathlib/Mathlib/Analysis/Convolution.lean; sed -n '465,492p' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean; rg -n '^theorem|^def|^instance' Poincare/Global/ParabolicSolutionGraph.lean
/-- The convolution of two functions with respect to a bilinear operation `L` and the volume. -/
scoped[Convolution]
  notation:67 f " ⋆[" L:67 "] " g:66 => convolution f g L MeasureSpace.volume

/-- The convolution of two real-valued functions with respect to volume. -/
scoped[Convolution]
  notation:67 f " ⋆ " g:66 =>
    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureSpace.volume

open scoped Convolution

theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl

section Group

variable {L} [AddGroup G]

theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]

theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]

@[simp]
theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]

@[simp]
  rfl

end RestrictScalars

lemma norm_pi_le_of_le {ι : Type*} [Fintype ι]
    {M : ι → Type*} [∀ i, SeminormedAddCommGroup (M i)] [∀ i, NormedSpace 𝕜 (M i)] {C : ℝ}
    {L : (i : ι) → (E →L[𝕜] M i)} (hL : ∀ i, ‖L i‖ ≤ C) (hC : 0 ≤ C) :
    ‖pi L‖ ≤ C := by
  refine opNorm_le_bound _ hC (fun x ↦ ?_)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i ↦ ?_)
  exact (L i).le_of_opNorm_le (hL i) _

end ContinuousLinearMap

namespace LinearMap

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem mkContinuous_norm_le (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC h

/-- If a continuous linear map is constructed from a linear map via the constructor `mkContinuous`,
then its norm is bounded by the bound or zero if bound is negative. -/
theorem mkContinuous_norm_le' (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    ‖f.mkContinuous C h‖ ≤ max C 0 :=
  ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => (h x).trans <| by
    gcongr; apply le_max_left
38:def graphSubmodule (α T : ℝ) : Submodule ℝ (Ambient (E := E) α T) where
66:def graphEquiv : Graph (E := E) α T ≃ ↥(graphSubmodule (E := E) α T) where
74:instance instNormedAddCommGroup : NormedAddCommGroup (Graph (E := E) α T) :=
77:instance instModule : Module ℝ (Graph (E := E) α T) := graphEquiv.module ℝ
79:instance instNormedSpace : NormedSpace ℝ (Graph (E := E) α T) := by
83:theorem norm_eq (g : Graph (E := E) α T) :
89:theorem norm_u_le (g : Graph (E := E) α T) : ‖g.u‖ ≤ ‖g‖ := by
97:theorem norm_ut_le (g : Graph (E := E) α T) : ‖g.ut‖ ≤ ‖g‖ := by
105:theorem norm_du_le (g : Graph (E := E) α T) : ‖g.du‖ ≤ ‖g‖ := by
113:theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
121:theorem sup_u_le (g : Graph (E := E) α T) (p : ℝ × E) :
125:theorem holder_u_le (g : Graph (E := E) α T) {p q : ℝ × E}
132:theorem sup_ut_le (g : Graph (E := E) α T) (p : ℝ × E) :
136:theorem holder_ut_le (g : Graph (E := E) α T) {p q : ℝ × E}
143:theorem sup_du_le (g : Graph (E := E) α T) (p : ℝ × E) :
147:theorem holder_du_le (g : Graph (E := E) α T) {p q : ℝ × E}
154:theorem sup_ddu_le (g : Graph (E := E) α T) (p : ℝ × E) :
158:theorem holder_ddu_le (g : Graph (E := E) α T) {p q : ℝ × E}
165:theorem time_bound (g : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T)
174:def ofDerivatives
211:theorem holder_tendstoUniformly {v : ℕ → Y (E := E) α T F} {w : Y (E := E) α T F}
222:theorem closed_time_derivative {f d : ℕ → ℝ → ℝ} {g e : ℝ → ℝ} {s : Set ℝ}
262:theorem isClosed_graphSubmodule :
297:instance instCompleteSpace : CompleteSpace (Graph (E := E) α T) := by

exit 0
$ rg -n 'convolution_add|add.*convolution|integral_add|integral_smul|integral_congr_ae_restrict' .lake/packages/mathlib/Mathlib/Analysis/Convolution.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean | head -35
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:438:  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:441:  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:456:  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:466:  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:774:  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:764:nonrec theorem integral_add (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:766:  simp only [intervalIntegral_eq_integral_uIoc, integral_add hf.def' hg.def', smul_add]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:783:  simpa only [sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:787:general rings assuming integrability, see `IntervalIntegrable.integral_smul`. -/
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:789:nonrec theorem integral_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:792:  simp only [intervalIntegral, integral_smul, smul_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:794:theorem _root_.IntervalIntegrable.integral_smul
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:798:  simp only [intervalIntegral, smul_sub, hf.1.integral_smul, hf.2.integral_smul]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:801:nonrec theorem integral_smul_const [CompleteSpace E]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:804:  simp only [intervalIntegral_eq_integral_uIoc, integral_smul_const, smul_assoc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:809:  integral_smul r f
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:830:nonrec theorem integral_smul_measure (c : ℝ≥0∞) :
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:832:  simp only [intervalIntegral, Measure.restrict_smul, integral_smul_measure, smul_sub]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:894:  simp_rw [integral_smul_measure, intervalIntegral, A.setIntegral_map,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1056:theorem integral_add_adjacent_intervals_cancel (hab : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1068:theorem integral_add_adjacent_intervals (hab : IntervalIntegrable f μ a b)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1071:  rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1080:    rw [Finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1097:  sub_eq_of_eq_add' <| Eq.symm <| integral_add_adjacent_intervals hac (hac.symm.trans hab)
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1103:  rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1104:    integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1220:theorem integral_congr_ae_restrict {a b : ℝ} {f g : ℝ → E} {μ : Measure ℝ}
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1229:  integral_congr_ae_restrict (ae_restrict_le_codiscreteWithin measurableSet_uIoc hf)

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_probe2.lean
theorem Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous.{u_1} : ∀ {E : Type u_1}
  [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]
  [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E] {t : ℝ},
  0 < t →
    ∀ {f : E → ℝ},
      Continuous f →
        ∀ {C : ℝ},
          (∀ (x : E), ‖f x‖ ≤ C) →
            ∀ (x : E),
              MeasureTheory.ConvolutionExistsAt (fun y => Poincare.heatKernel t y) f x (ContinuousLinearMap.lsmul ℝ ℝ)
                MeasureTheory.volume :=
⋯
theorem Poincare.heatSolution_apply.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] [inst_3 : MeasurableSpace E] [inst_4 : BorelSpace E]
  (t : ℝ) (f : E → ℝ) (x : E), Poincare.heatSolution t f x = ∫ (y : E), Poincare.heatKernel t y * f (x - y) :=
⋯
@[defeq] theorem Poincare.ParabolicHolder.add_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E),
  ↑(WithLp.fst ↑(f + g)) p = ↑(WithLp.fst ↑f) p + ↑(WithLp.fst ↑g) p :=
⋯
@[defeq] theorem Poincare.ParabolicHolder.smul_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (c : ℝ)
  (f : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E), ↑(WithLp.fst ↑(c • f)) p = c • ↑(WithLp.fst ↑f) p :=
⋯
def Poincare.ParabolicSolutionGraph.graphEquiv.{u_1} : {E : Type u_1} →
  [inst : NormedAddCommGroup E] →
    [inst_1 : NormedSpace ℝ E] →
      {α T : ℝ} → Poincare.ParabolicSolutionGraph.Graph α T ≃ ↥(Poincare.ParabolicSolutionGraph.graphSubmodule α T) :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} =>
  { toFun := fun g => ⟨WithLp.toLp 1 (WithLp.toLp 1 (g.u, g.ut), WithLp.toLp 1 (g.du, g.ddu)), ⋯⟩,
    invFun := fun v =>
      { u := (WithLp.fst ↑v).fst, ut := (WithLp.fst ↑v).snd, du := (WithLp.snd ↑v).fst, ddu := (WithLp.snd ↑v).snd,
        zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ },
    left_inv := ⋯, right_inv := ⋯ }
/private/tmp/dclm_probe2.lean:8:7: error(lean.unknownIdentifier): Unknown identifier `MeasureTheory.convolution_add`
/private/tmp/dclm_probe2.lean:9:7: error(lean.unknownIdentifier): Unknown identifier `MeasureTheory.convolution_add_distrib`
MeasureTheory.convolution_smul.{u𝕜, uG, uE, uE', uF} {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'}
  {F : Type uF} [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F] {f : G → E} {g : G → E'}
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] {L : E →L[𝕜] E' →L[𝕜] F}
  [MeasurableSpace G] {μ : MeasureTheory.Measure G} [NormedSpace ℝ F] [AddGroup G] [SMulCommClass ℝ 𝕜 F] {y : 𝕜} :
  MeasureTheory.convolution f (y • g) L μ = y • MeasureTheory.convolution f g L μ
HasDerivWithinAt.derivWithin.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} {x : 𝕜} {s : Set 𝕜} (h : HasDerivWithinAt f f' s x)
  (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
HasDerivWithinAt.congr_of_mem.{u, v} {𝕜 : Type u} [NontriviallyNormedField 𝕜] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f f₁ : 𝕜 → F} {f' : F} {x : 𝕜} {s : Set 𝕜} (h : HasDerivWithinAt f f' s x)
  (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasDerivWithinAt f₁ f' s x
LinearMap.mkContinuous.{u_1, u_2, u_3, u_4} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_3} {F : Type u_4} [Ring 𝕜]
  [Ring 𝕜₂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module 𝕜 E] [Module 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂}
  (f : E →ₛₗ[σ] F) (C : ℝ) (h : ∀ (x : E), ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F
LinearMap.mkContinuous_norm_le.{u_1, u_2, u_4, u_5} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type u_5}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {C : ℝ} (hC : 0 ≤ C)
  (h : ∀ (x : E), ‖f x‖ ≤ C * ‖x‖) : ‖f.mkContinuous C h‖ ≤ C

exit 1
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:55:14: error: unexpected token ':='; expected ')', ',' or ':'

exit 1
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_probe3.lean
MeasureTheory.ConvolutionExistsAt.distrib_add.{u𝕜, uG, uE, uE', uF} {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE}
  {E' : Type uE'} {F : Type uF} [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F] {f : G → E}
  {g g' : G → E'} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F]
  {L : E →L[𝕜] E' →L[𝕜] F} [MeasurableSpace G] {μ : MeasureTheory.Measure G} [NormedSpace ℝ F] [AddGroup G] {x : G}
  (hfg : MeasureTheory.ConvolutionExistsAt f g x L μ) (hfg' : MeasureTheory.ConvolutionExistsAt f g' x L μ) :
  MeasureTheory.convolution f (g + g') L μ x =
    MeasureTheory.convolution f g L μ x + MeasureTheory.convolution f g' L μ x
intervalIntegral.integral_congr_ae_restrict.{u_5} {E : Type u_5} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
  {f g : ℝ → E} {μ : MeasureTheory.Measure ℝ} (h : f =ᵐ[μ.restrict (Set.uIoc a b)] g) :
  ∫ (x : ℝ) in a..b, f x ∂μ = ∫ (x : ℝ) in a..b, g x ∂μ
intervalIntegral.integral_smul.{u_2, u_5} {𝕜 : Type u_2} {E : Type u_5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {μ : MeasureTheory.Measure ℝ} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  (r : 𝕜) (f : ℝ → E) : ∫ (x : ℝ) in a..b, r • f x ∂μ = r • ∫ (x : ℝ) in a..b, f x ∂μ
intervalIntegral.integral_const_mul.{u_2} {𝕜 : Type u_2} {a b : ℝ} {μ : MeasureTheory.Measure ℝ} [NormedDivisionRing 𝕜]
  [NormedAlgebra ℝ 𝕜] (r : 𝕜) (f : ℝ → 𝕜) : ∫ (x : ℝ) in a..b, r * f x ∂μ = r * ∫ (x : ℝ) in a..b, f x ∂μ
HasFDerivAt.fderiv.{u_1, u_2, u_3} {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [AddCommGroup E]
  [Module 𝕜 E] [TopologicalSpace E] {F : Type u_3} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {f : E → F}
  {f' : E →L[𝕜] F} {x : E} [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
  (h : HasFDerivAt f f' x) : fderiv 𝕜 f x = f'

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:101:72: error: unsolved goals
α T t c : ℝ
f : Y α T ℝ
x : E
⊢ ∫ (s : ℝ) in 0..t, ∫ (y : E), heatKernel (t - s) y * (c * ↑(WithLp.fst ↑f) (s, x - y)) =
    c * ∫ (s : ℝ) in 0..t, ∫ (y : E), heatKernel (t - s) y * ↑(WithLp.fst ↑f) (s, x - y)
Poincare/Global/DuhamelSolutionOperatorCLM.lean:103:4: warning: This simp argument is unused:
  ← mul_assoc

Hint: Omit it from the simp argument list.
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul, ←̵ ̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵mul_comm _ c, mul_assoc,
  ̲  ̲ ̲ ̲integral_const_mul, intervalIntegral.integral_const_mul]

Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:103:17: warning: This simp argument is unused:
  mul_comm _ c

Hint: Omit it from the simp argument list.
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul,
  ̵  ̵ ̵ ̵← mul_assoc, mul_c̵o̵m̵m̵ ̵_̵ ̵c̵,̵ ̵m̵u̵l̵_̵assoc,
  ̲  ̲ ̲ ̲integral_const_mul,
  ̵  ̵ ̵ ̵intervalIntegral.integral_const_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:103:31: warning: This simp argument is unused:
  mul_assoc

Hint: Omit it from the simp argument list.
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul,
  ̵  ̵ ̵ ̵← mul_assoc, mul_comm _ c,
  ̲ m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵  ̲ ̲integral_const_mul,
  ̵  ̵ ̵ ̵intervalIntegral.integral_const_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:103:42: warning: This simp argument is unused:
  integral_const_mul

Hint: Omit it from the simp argument list.
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul, ← mul_assoc, mul_comm _ c,
  ̲  ̲ ̲ ̲mul_assoc, i̵n̵t̵e̵g̵r̵a̵l̵_̵c̵o̵n̵s̵t̵_̵m̵u̵l̵,̵intervalIntegral.integral_const_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:104:4: warning: This simp argument is unused:
  intervalIntegral.integral_const_mul

Hint: Omit it from the simp argument list.
  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul, ← mul_assoc, mul_comm _ c,
  ̲  ̲ ̲ ̲mul_assoc, i̵n̵t̵e̵g̵r̵a̵l̵_̵c̵o̵n̵s̵t̵_̵m̵u̵l̵,̵
  ̵ ̵ ̵ ̵ ̵i̵n̵t̵e̵r̵v̵a̵l̵I̵n̵t̵e̵g̵r̵a̵l̵.̵i̵n̵t̵e̵g̵r̵a̵l̵_̵c̵o̵n̵s̵t̵_̵m̵u̵l̵]̵i̲n̲t̲e̲g̲r̲a̲l̲_̲c̲o̲n̲s̲t̲_̲m̲u̲l̲]̲

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`

exit 1
$ rg -n 'theorem integral_const_mul|theorem.*fderiv|theorem uniqueDiffOn_Icc|theorem HasFDerivAt.unique' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Real.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean | head -20
.lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Real.lean:99:theorem uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/TangentCone/Real.lean:116:theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:174:theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:234:theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:373:theorem fderivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:377:theorem fderivWithin_zero_of_notMem_closure (h : x ∉ closure s) :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:381:theorem fderivWithin_zero_of_not_uniqueDiffWithinAt {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:409:protected theorem HasFDerivAt.fderiv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:415:theorem fderiv_eq
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:420:protected theorem HasFDerivWithinAt.fderivWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:476:protected theorem DifferentiableAt.fderivWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:500:theorem fderivWithin_of_mem_nhdsWithin
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:506:theorem fderivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:512:theorem fderivWithin_inter (ht : t ∈ 𝓝 x) : fderivWithin 𝕜 f (s ∩ t) x = fderivWithin 𝕜 f s x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:516:theorem fderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:519:theorem fderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:522:theorem fderivWithin_eq_fderiv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:529:theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} : fderiv 𝕜 f x ∈ s ↔
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:533:theorem fderivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:720:theorem fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] : fderiv 𝕜 id x = .id 𝕜 E :=

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Poincare/Global/DuhamelSolutionOperatorCLM.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
/private/tmp/dclm_check.lean:54:44: warning: unused variable `hT`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
/private/tmp/dclm_check.lean:54:58: warning: unused variable `hT1`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_check.lean
'Poincare.ParabolicSolutionGraph.Graph.ext_of_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.boundConstant_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelGraph_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamel_integral_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.DuhamelSolutionOperatorCLM.duhamelOperator_solves' depends on axioms: [propext, Classical.choice, Quot.sound]

exit 0
$ rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/DuhamelSolutionOperatorCLM.lean

exit 1
$ git diff --check

exit 0
$ LEAN_NUM_THREADS=1 lake env lean /private/tmp/dclm_contract.lean

exit 0
$ git log --oneline 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df..HEAD
baa43865 Prove the Duhamel operator solves the heat equation on the closed interval
c4e0c657 Prove uniform short-time operator norm bound
584d0219 Identify the operator value with the Duhamel integral
71340a51 Construct the continuous linear Duhamel solution operator
8cf06351 Package Duhamel graph selection as a linear map
79e0e1ed Prove scalar linearity of the Duhamel integral
f8b5a0ad Prove additivity of the Duhamel integral for Holder data
1ed70147 Select Duhamel solution graph with integral and norm specifications
f095c511 Select exponent-only Duhamel bound with its existence estimate
9c9ae692 Prove solution graph uniqueness from values on positive time intervals

exit 0
$ git diff --check 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df HEAD

exit 0
```

## Verified proof diff

```diff
diff --git a/Poincare/Global/DuhamelSolutionOperatorCLM.lean b/Poincare/Global/DuhamelSolutionOperatorCLM.lean
new file mode 100644
index 00000000..dfc0a375
--- /dev/null
+++ b/Poincare/Global/DuhamelSolutionOperatorCLM.lean
@@ -0,0 +1,197 @@
+import Poincare.Global.DuhamelSolutionOperatorBound
+
+noncomputable section
+
+open Set MeasureTheory
+open scoped Interval
+
+namespace Poincare.ParabolicSolutionGraph
+
+/-- Values determine all derivatives, including at both time endpoints. -/
+theorem Graph.ext_of_u {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+    {α T : ℝ} (hT : 0 < T) {G H : Graph (E := E) α T} (hu : G.u = H.u) : G = H := by
+  have hd : G.du = H.du := by
+    apply ParabolicHolder.ext
+    intro p hp
+    have h := G.hasFDeriv p.1 hp.1 p.2
+    rw [hu] at h
+    exact h.unique (H.hasFDeriv p.1 hp.1 p.2)
+  have hdd : G.ddu = H.ddu := by
+    apply ParabolicHolder.ext
+    intro p hp
+    have h := G.hasFDeriv_du p.1 hp.1 p.2
+    rw [hd] at h
+    exact h.unique (H.hasFDeriv_du p.1 hp.1 p.2)
+  have ht : G.ut = H.ut := by
+    apply ParabolicHolder.ext
+    intro p hp
+    have h := G.hasDeriv_time p.1 hp.1 p.2
+    rw [hu] at h
+    exact (h.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)).symm.trans
+      ((H.hasDeriv_time p.1 hp.1 p.2).derivWithin (uniqueDiffOn_Icc hT p.1 hp.1))
+  cases G
+  cases H
+  cases hu
+  cases ht
+  cases hd
+  cases hdd
+  rfl
+
+end Poincare.ParabolicSolutionGraph
+
+namespace Poincare.DuhamelSolutionOperatorCLM
+
+local notation "E" => ClosedSmoothModel 3
+
+open ParabolicHolder DuhamelSolutionOperatorBound
+
+/-- A short-time bound depending only on the exponent. -/
+def boundConstant (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : ℝ :=
+  Classical.choose (exists_solution_graph_bound α hα hα1)
+
+/-- The chosen constant retains the complete landed existence estimate. -/
+theorem boundConstant_spec (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
+    0 < boundConstant α hα hα1 ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ f : Y («E» := E) α T ℝ, ∃ G : ParabolicSolutionGraph.Graph («E» := E) α T,
+      (∀ p ∈ cylinder T, G.u p =
+        ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
+      ‖G‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
+  Classical.choose_spec (exists_solution_graph_bound α hα hα1)
+
+/-- The unique graph selected by the landed existence theorem. -/
+def duhamelGraph (α T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
+    (f : Y («E» := E) α T ℝ) : ParabolicSolutionGraph.Graph («E» := E) α T :=
+  Classical.choose ((boundConstant_spec α hα hα1).2 T hT hT1 f)
+
+/-- The selected graph has the integral values and the uniform norm estimate. -/
+theorem duhamelGraph_spec (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
+    (∀ p ∈ cylinder T, (duhamelGraph α T hα hα1 hT hT1 f).u p =
+      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2) ∧
+    ‖duhamelGraph α T hα hα1 hT hT1 f‖ ≤ boundConstant α hα hα1 * ‖f‖ :=
+  Classical.choose_spec ((boundConstant_spec α hα hα1).2 T hT hT1 f)
+
+/-- The Duhamel integral is additive for parabolic Hölder data. -/
+theorem duhamel_integral_add {α T t : ℝ} (hα : 0 < α) (ht : t ∈ Icc 0 T)
+    (f g : Y («E» := E) α T ℝ) (x : E) :
+    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (f+g) (s,y)) x) =
+      (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x) +
+      ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => g (s,y)) x := by
+  have hc (v : Y («E» := E) α T ℝ) : ContinuousOn v (cylinder T) :=
+    continuousOn_of_hasHolderBound hα (hasHolderBound v)
+  have hi (v : Y («E» := E) α T ℝ) :=
+    HeatDuhamelHessianDifferentiation.intervalIntegrable_heatSolution_time ht (hc v)
+      (fun s _ y => ParabolicHolder.norm_le v (s,y)) x
+  rw [← intervalIntegral.integral_add (hi f) (hi g)]
+  apply intervalIntegral.integral_congr_ae_restrict
+  rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
+  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
+  have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
+  have he (v : Y («E» := E) α T ℝ) :=
+    heatKernel_convolutionExistsAt_of_bounded_continuous (sub_pos.mpr hs.2)
+      ((hc v).comp_continuous (continuous_const.prodMk continuous_id)
+        (fun y => ⟨hsT, mem_univ y⟩))
+      (fun y => ParabolicHolder.norm_le v (s,y)) x
+  exact (he f).distrib_add (he g)
+
+/-- Scalar multiplication commutes with the Duhamel integral. -/
+theorem duhamel_integral_smul {α T t : ℝ} (c : ℝ)
+    (f : Y («E» := E) α T ℝ) (x : E) :
+    (∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => (c • f) (s,y)) x) =
+      c • ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x := by
+  simp only [ParabolicHolder.smul_apply, heatSolution_apply, smul_eq_mul]
+  simp_rw [mul_left_comm (heatKernel _ _) c, integral_const_mul,
+    intervalIntegral.integral_const_mul]
+
+/-- Integral linearity and graph uniqueness give a linear solution map. -/
+def duhamelLinearMap (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) :
+    Y («E» := E) α T ℝ →ₗ[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T where
+  toFun := duhamelGraph α T hα hα1 hT hT1
+  map_add' f g := by
+    apply ParabolicSolutionGraph.Graph.ext_of_u hT
+    apply ParabolicHolder.ext
+    intro p hp
+    change (duhamelGraph α T hα hα1 hT hT1 (f+g)).u p =
+      (duhamelGraph α T hα hα1 hT hT1 f).u p +
+      (duhamelGraph α T hα hα1 hT hT1 g).u p
+    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (f+g)).1 p hp,
+      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp,
+      (duhamelGraph_spec α T hα hα1 hT hT1 g).1 p hp]
+    exact duhamel_integral_add hα hp.1 f g p.2
+  map_smul' c f := by
+    apply ParabolicSolutionGraph.Graph.ext_of_u hT
+    apply ParabolicHolder.ext
+    intro p hp
+    change (duhamelGraph α T hα hα1 hT hT1 (c • f)).u p =
+      c • (duhamelGraph α T hα hα1 hT hT1 f).u p
+    rw [(duhamelGraph_spec α T hα hα1 hT hT1 (c • f)).1 p hp,
+      (duhamelGraph_spec α T hα hα1 hT hT1 f).1 p hp]
+    exact duhamel_integral_smul c f p.2
+
+/-- The bounded constant-coefficient inverse in continuous linear form. -/
+def duhamelOperator (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) :
+    Y («E» := E) α T ℝ →L[ℝ] ParabolicSolutionGraph.Graph («E» := E) α T :=
+  (duhamelLinearMap α T hα hα1 hT hT1).mkContinuous (boundConstant α hα hα1)
+    (fun f => (duhamelGraph_spec α T hα hα1 hT hT1 f).2)
+
+/-- The operator's value component is the Duhamel integral on the cylinder. -/
+theorem duhamelOperator_u (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
+    ∀ p ∈ cylinder T, (duhamelOperator α T hα hα1 hT hT1 f).u p =
+      ∫ s in (0 : ℝ)..p.1, heatSolution (p.1-s) (fun y => f (s,y)) p.2 :=
+  (duhamelGraph_spec α T hα hα1 hT hT1 f).1
+
+/-- The operator norms are uniformly bounded for all short positive intervals. -/
+theorem duhamelOperator_norm_le :
+    ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1), ∃ C : ℝ, 0 < C ∧
+      ∀ (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1),
+        ‖duhamelOperator α T hα hα1 hT hT1‖ ≤ C := by
+  intro α hα hα1
+  refine ⟨boundConstant α hα hα1, (boundConstant_spec α hα hα1).1, ?_⟩
+  intro T hT hT1
+  exact LinearMap.mkContinuous_norm_le _ (boundConstant_spec α hα hα1).1.le _
+
+/-- The graph satisfies the inhomogeneous heat equation, including both endpoints. -/
+theorem duhamelOperator_solves (α T : ℝ) (hα : 0 < α) (hα1 : α < 1)
+    (hT : 0 < T) (hT1 : T ≤ 1) (f : Y («E» := E) α T ℝ) :
+    ∀ t ∈ Icc 0 T, ∀ x : E,
+      (duhamelOperator α T hα hα1 hT hT1 f).ut (t,x) = f (t,x) +
+        ∑ i : Fin 3, (duhamelOperator α T hα hα1 hT hT1 f).ddu (t,x)
+          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
+  let G := duhamelOperator α T hα hα1 hT hT1 f
+  let u : ℝ → E → ℝ := fun t x =>
+    ∫ s in (0 : ℝ)..t, heatSolution (t-s) (fun y => f (s,y)) x
+  have hu (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.u (t,z)) = u t := by
+    funext z
+    exact duhamelOperator_u α T hα hα1 hT hT1 f (t,z) ⟨ht, mem_univ z⟩
+  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : (fun z : E => G.du (t,z)) = fderiv ℝ (u t) := by
+    funext z
+    have h := (G.hasFDeriv t ht z).fderiv
+    rw [hu t ht] at h
+    exact h.symm
+  have hdd (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) :
+      G.ddu (t,x) = fderiv ℝ (fderiv ℝ (u t)) x := by
+    have h := (G.hasFDeriv_du t ht x).fderiv
+    rw [hd t ht] at h
+    exact h.symm
+  have hf : ContinuousOn f (cylinder T) :=
+    continuousOn_of_hasHolderBound hα (hasHolderBound f)
+  have hfM : ∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ ‖f‖ :=
+    fun t _ x => ParabolicHolder.norm_le f (t,x)
+  have hfK : ∀ t ∈ Icc 0 T, ∀ x y : E,
+      |f (t,x)-f (t,y)| ≤ ‖f‖ * ‖x-y‖^α := by
+    intro t ht x y
+    simpa [parabolicDist, Real.norm_eq_abs] using
+      hasHolderBound f (t,x) ⟨ht, mem_univ x⟩ (t,y) ⟨ht, mem_univ y⟩
+  intro t ht x
+  change G.ut (t,x) = f (t,x) + ∑ i : Fin 3, G.ddu (t,x) _ _
+  rw [hdd t ht x]
+  have htime := (MovingLimitLeibniz.duhamel_solves_heat_equation α hα hα1 T hT hT1
+    f ‖f‖ ‖f‖ (norm_nonneg f) (norm_nonneg f) hf hfM hfK).2 t ht x
+  have htimeG := htime.congr_of_mem (fun s hs => congrFun (hu s hs) x) ht
+  exact ((G.hasDeriv_time t ht x).derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
+    (htimeG.derivWithin (uniqueDiffOn_Icc hT t ht))
+
+end Poincare.DuhamelSolutionOperatorCLM
```
