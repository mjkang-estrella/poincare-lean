# Parabolic Hölder multiplier estimate: done

Date: 2026-09-15. Worker result awaiting independent review.

- Base: `2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df`.
- Branch: `worker/parabolic-holder-multiplier-estimate`.
- Proof head: `430f5bfb5d2b042356f9ae7bc703bafda1a3fc2a`.
- New Lean module: `Poincare/Global/ParabolicHolderMultiplier.lean`.
- Toolchain: `leanprover/lean4:v4.30.0-rc2`.

## Result and separate commits

All four requested items are proved. The namespace is
`Poincare.ParabolicHolderMultiplier`; `E` is `ClosedSmoothModel 3`, and the
coordinate vectors are `EuclideanSpace.basisFun (Fin 3) ℝ`.

| Item | Commit | Main declarations |
| --- | --- | --- |
| 1. Zero-trace interpolation | `ec6fc68b` | `du_zero_trace`, `ddu_zero_trace`, `ddu_time_bound`, `supNorm_ddu_le` |
| 2. Coordinate entries and split product bound | `5c2624ca` | `entry`, `entry_apply`, `supNorm_entry_le`, `norm_entry_le`, `norm_mul_split` |
| 3. Nine-entry multiplier estimate | `fb41a775` | `forcing`, `forcing_apply`, `forcing_eq_sum`, `norm_mul_ddu_entry_le`, `norm_forcing_le` |
| 4. Elementwise error smallness | `430f5bfb` | `norm_error_le`, `error_small` |

Item 1 uses uniqueness of the actual Fréchet derivative at time zero twice.
The Hölder comparison with `(0,x)` gives
`‖G.ddu (t,x)‖ ≤ ‖G.ddu‖ * t^(α/2)`. Taking the supremum gives
`supNorm (cylinder T) G.ddu ≤ T^(α/2) * ‖G‖` for `0 < α` and `0 < T`.
The pointwise comparison itself needs no sign restriction on `α`; positivity
is used when comparing `t^(α/2)` with `T^(α/2)`.

Item 2 constructs the entry with `ofFunction`. It bounds its sup norm and
Hölder seminorm separately. The product proof expands the increment as
`b(p)(h(p)-h(q)) + (b(p)-b(q))h(q)` and combines its two bounds with the
sup-product bound. Its conclusion is exactly
`‖b*h‖ ≤ supNorm b * ‖h‖ + holderSeminorm b * supNorm h`.

Item 3 constructs `forcing b G` with `ofFunction` and proves its value is
exactly `∑ i j, b i j p * G.ddu p (e i) (e j)`, including off-cylinder
values. The sum of the nine entry bounds yields
`‖forcing b G‖ ≤ 9 * (ε * ‖G‖ + Λ * T^(α/2) * ‖G‖)`.
The nonnegativity of `ε` and `Λ` follows from their assumed bounds on the
coefficient norms, so no extra sign hypotheses are imposed.

Item 4 uses a supplied continuous linear solution map `S` and `‖S‖ ≤ C_S`.
It proves the exact permitted elementwise form
`‖forcing b (S f)‖ ≤ 9*C_S*(ε + Λ*T^(α/2))*‖f‖`, then the one-half bound
under the two quarter-size hypotheses. Packaging the error as a continuous
linear map remains the separately scoped task. No PDE existence, localization,
cutoff estimate, or full conjecture completion is claimed here.

## Gates

Each item passed the focused source, named-dependency, forbidden-token, and
whitespace checks before its separate commit. The final environment inventory
found 46 declarations: 19 explicit declarations, 26 generated proof
constants, and `entry.congr_simp`. All 46 passed `#print axioms` with exactly
`[propext, Classical.choice, Quot.sound]`.

- `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean`: exit 0, empty output.
- `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderMultiplier.lean`: empty output, exit 1 as expected for no matches.
- All named and generated declaration dependency probes: exit 0, exact required list.
- `git diff --check`: exit 0, empty output.
- Base-to-proof-head whitespace and file-scope check: only the single new Lean module.

No existing Lean file, root import, or frozen task file was changed. The dated
handoff and this report accompany the proof. Root integration and acceptance
belong to the orchestrator.

## Failed probes and their resolutions

The full diagnostic outputs are retained below.

1. The local notation `E` shadowed the named argument token in `(E := E)`.
   Quoting the argument name as `(«E» := E)` resolved the parser error.
2. The entry support proof needed `dsimp only` before rewriting `zero_off`
   beneath the applied lambda.
3. The empty finite-sum case left `0 p = 0`; reduction closed it with `rfl`.
   Dot notation on the local notation `e` was replaced by the verified name
   `OrthonormalBasis.norm_eq_one e`.

No mathematical target resisted, and none was weakened.

## First reviewer action

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

Then compare the module against the base and independently reproduce the
46-declaration dependency check. The probes below copy the source into a
temporary Lean file and append commands, so they cannot accidentally use an
older cached version of the new module.

## Probe construction

The landed-statement probe was run before the first proof check:

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.RiemannianContext
#print Poincare.ParabolicHolder.Y
#print Poincare.ParabolicHolder.parabolicDist
#print Poincare.ParabolicHolder.cylinder
#print Poincare.ParabolicHolder.HasHolderBound
#print Poincare.ParabolicHolder.ofFunction
#print Poincare.ParabolicHolder.ofFunction_apply
#print Poincare.ParabolicHolder.norm_eq
#print Poincare.ParabolicHolder.norm_le
#print Poincare.ParabolicHolder.holder_le
#print Poincare.ParabolicHolder.norm_le_of_bounds
#print Poincare.ParabolicHolder.supNorm
#print Poincare.ParabolicHolder.supNorm_eq
#print Poincare.ParabolicHolder.holderSeminorm
#print Poincare.ParabolicHolder.holderSeminorm_eq
#print Poincare.ParabolicHolder.norm_eq_parts
#print Poincare.ParabolicHolder.supNorm_nonneg
#print Poincare.ParabolicHolder.holderSeminorm_nonneg
#print Poincare.ParabolicHolder.le_supNorm
#print Poincare.ParabolicHolder.hasHolderBound_seminorm
#print Poincare.ParabolicHolder.zero_off
#print Poincare.ParabolicHolder.mul_apply
#print Poincare.ParabolicHolder.product_holderBound
#print Poincare.ParabolicHolder.bounded
#print Poincare.ParabolicHolder.hasHolderBound
#print Poincare.ParabolicHolder.add_apply
#print Poincare.ParabolicHolder.zero_apply
#print Poincare.ParabolicSolutionGraph.Graph
#print Poincare.ParabolicSolutionGraph.Graph.zero_trace
#print Poincare.ParabolicSolutionGraph.Graph.hasFDeriv
#print Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du
#print Poincare.ParabolicSolutionGraph.norm_ddu_le
```

The stage gate generator used for each item:

```python
import pathlib,re,subprocess,sys
p=pathlib.Path('Poincare/Global/ParabolicHolderMultiplier.lean')
names=re.findall(r'^(?:@\[.*\] )?(?:theorem|def) (\w+)',p.read_text(),re.M)
a=pathlib.Path('/private/tmp/PHMAxioms.lean')
a.write_text(p.read_text()+'\n'+''.join('#print axioms Poincare.ParabolicHolderMultiplier.'+n+'\n' for n in names))
commands=[('LEAN_NUM_THREADS=1 lake env lean '+str(p),0),('LEAN_NUM_THREADS=1 lake env lean '+str(a),0),("rg -n '\\b(sorry|admit|axiom|opaque)\\b|native_decide' "+str(p),1),('git diff --check',0)]
for cmd,expected in commands:
 r=subprocess.run(['python3','/private/tmp/phm_run.py',cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 print(r.stdout,flush=True)
 if r.returncode != expected: sys.exit(1)
 if 'PHMAxioms' in cmd:
  found=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",r.stdout)
  if len(found)!=len(names) or any(v!='propext, Classical.choice, Quot.sound' for _,v in found):
   print('DEPENDENCY MISMATCH',found);sys.exit(1)
print('PASS:',len(names),'declarations; all four gates passed')
```

For the final inventory, the source copy was followed by:

```lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "Poincare.ParabolicHolderMultiplier." then
      logInfo m!"DECL {n}"
```

The all-declaration probe appended one `#print axioms` command for every inventory name. The statement probe appended `#check` for each explicit declaration. The name-lookup input was:

```text
ClosedSmoothModel
Graph
Y
HasHolderBound
zero_trace
hasFDeriv
hasFDeriv_du
unique
hasFDerivAt_const
holder_le
cylinder
mem_univ
sqrt_eq_rpow
rpow_mul
sub_zero
sub_self
norm_zero
zero_add
abs_of_nonneg
supNorm
csSup_le
insert_nonempty
rpow_nonneg
norm_nonneg
norm_ddu_le
rpow_le_rpow
mul_le_mul
mul_comm
le_opNorm₂
sub_apply
holderSeminorm
hasHolderBound_seminorm
ofFunction
zero_off
le_supNorm
supNorm_nonneg
norm_le_of_bounds
holderSeminorm_nonneg
mul_apply
norm_mul
norm_add_le
add_le_add
mul_nonneg
add_nonneg
sum_empty
induction_on
sum_insert
norm_eq
basisFun
norm_eq_one
norm_le
ext
norm_sum_le
sum_le_sum
le_opNorm
mul_le_mul_of_nonneg_right
mul_le_mul_of_nonneg_left
```

## Actual command outputs and proof diff

Compiler stdout and stderr were captured together. Empty output and exit statuses are recorded explicitly. Trailing whitespace in displayed output is omitted so the report passes the whitespace gate.


### 2026-09-15T09:55:40.733579

```sh
sed -n '1,42p' Poincare/Global/RiemannianContext.lean; rg -n 'theorem (le_opNorm₂|norm_eq_one)|def basisFun|theorem sub_apply' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace
```

```text
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic

/-!
# Standard Riemannian context
This module packages the project-level tier M1 context for a closed smooth
Riemannian `n`-manifold.  The intended downstream variable section is:
```lean
open scoped Manifold ContDiff Bundle
variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) ∞ M]
variable [CompactSpace M] [ConnectedSpace M]
variable (g : Poincare.ClosedSmoothRiemannianMetric n M)
```
From the single metric variable `g`, use the definitions below as local
instances when a downstream statement needs Mathlib's bundle or distance
typeclasses.
-/
noncomputable section
open Bundle Bornology
open scoped Manifold ContDiff Bundle Topology ENNReal
universe u
namespace Poincare

/-- The model vector space for a boundaryless smooth `n`-manifold. -/
abbrev ClosedSmoothModel (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n)

/-- The model-with-corners used for boundaryless smooth `n`-manifolds. -/
abbrev closedSmoothModelWithCorners (n : ℕ) :
    ModelWithCorners ℝ (ClosedSmoothModel n) (ClosedSmoothModel n) :=
  𝓡 n

/--
A smooth Riemannian metric on the tangent bundle of a smooth `n`-manifold.

This is the single non-typeclass metric variable used by the project context.
All Mathlib bundle and distance typeclasses below are derived from this data.
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:796:noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
exit_code=0
```

### 2026-09-15T09:55:53.962861

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMLanded.lean
```

```text
@[reducible] def Poincare.ParabolicHolder.Y.{u_1, u_3} : {E : Type u_1} →
  [NormedAddCommGroup E] →
    ℝ → ℝ → (F : Type u_3) → [inst : NormedAddCommGroup F] → [NormedSpace ℝ F] → Type (max u_1 u_3) :=
fun {E} [NormedAddCommGroup E] α T F [NormedAddCommGroup F] [NormedSpace ℝ F] =>
  ↥(Poincare.ParabolicHolder.holderSubmodule α T)
def Poincare.ParabolicHolder.parabolicDist.{u_1} : {E : Type u_1} → [NormedAddCommGroup E] → ℝ × E → ℝ × E → ℝ :=
fun {E} [NormedAddCommGroup E] p q => ‖p.2 - q.2‖ + √|p.1 - q.1|
def Poincare.ParabolicHolder.cylinder.{u_1} : {E : Type u_1} → ℝ → Set (ℝ × E) :=
fun {E} T => Set.Icc 0 T ×ˢ Set.univ
def Poincare.ParabolicHolder.HasHolderBound.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup E] → [NormedAddCommGroup F] → ℝ → Set (ℝ × E) → (ℝ × E → F) → ℝ → Prop :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] α S f K =>
  ∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * Poincare.ParabolicHolder.parabolicDist p q ^ α
def Poincare.ParabolicHolder.ofFunction.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} →
    [inst : NormedAddCommGroup E] →
      [inst_1 : NormedAddCommGroup F] →
        [inst_2 : NormedSpace ℝ F] →
          {α T : ℝ} →
            (f : ℝ × E → F) →
              (∀ p ∉ Poincare.ParabolicHolder.cylinder T, f p = 0) →
                (∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖f p‖ ≤ M) →
                  (∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K) →
                    Poincare.ParabolicHolder.Y α T F :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f hoff hb hh =>
  let v := ⟨f, ⋯⟩;
  let w := ⟨fun i => (Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)⁻¹ • (f (↑i).1 - f (↑i).2), ⋯⟩;
  ⟨WithLp.toLp 1 (v, w), ⋯⟩
@[defeq] theorem Poincare.ParabolicHolder.ofFunction_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : ℝ × E → F)
  (hoff : ∀ p ∉ Poincare.ParabolicHolder.cylinder T, f p = 0)
  (hb : ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖f p‖ ≤ M)
  (hh : ∃ K, Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) f K) (p : ℝ × E),
  ↑(WithLp.fst ↑(Poincare.ParabolicHolder.ofFunction f hoff hb hh)) p = f p :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f hoff hb hh p => rfl
theorem Poincare.ParabolicHolder.norm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F),
  ‖f‖ =
    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) +
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Eq.mpr
    (id
      (congrArg
        (fun _a =>
          ‖f‖ = _a + Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
        (Poincare.ParabolicHolder.supNorm_eq f)))
    (Eq.mpr (id (congrArg (fun _a => ‖f‖ = ‖WithLp.fst ↑f‖ + _a) (Poincare.ParabolicHolder.holderSeminorm_eq f)))
      (Eq.mpr
        (id (congrArg (fun _a => _a = ‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖) (Poincare.ParabolicHolder.norm_eq_parts f)))
        (Eq.refl (‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖))))
theorem Poincare.ParabolicHolder.norm_le.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F)
  (p : ℝ × E), ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f p =>
  Eq.mpr (id (congrArg (fun _a => ‖↑(WithLp.fst ↑f) p‖ ≤ _a) (Poincare.ParabolicHolder.norm_eq_parts f)))
    (LE.le.trans
      (lp.norm_apply_le_norm (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true))
        (WithLp.fst ↑f) p)
      (le_add_of_nonneg_right (norm_nonneg (WithLp.snd ↑f))))
theorem Poincare.ParabolicHolder.holder_le.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F)
  {p q : ℝ × E},
  p ∈ Poincare.ParabolicHolder.cylinder T →
    q ∈ Poincare.ParabolicHolder.cylinder T →
      ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f {p q} hp hq =>
  if h : p = q then
    Eq.ndrec (motive := fun {q} =>
      q ∈ Poincare.ParabolicHolder.cylinder T →
        ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α)
      (fun hq =>
        Eq.mpr
          (id
            (congrFun' (congrArg LE.le (Eq.trans (congrArg norm (sub_self (↑(WithLp.fst ↑f) p))) norm_zero))
              (‖f‖ * Poincare.ParabolicHolder.parabolicDist p p ^ α)))
          (mul_nonneg (norm_nonneg f) (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p p) α)))
      h hq
  else
    let i := ⟨(p, q), ⟨hp, ⟨hq, h⟩⟩⟩;
    have hi :=
      lp.norm_apply_le_norm (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true))
        (WithLp.snd ↑f) i;
    have hbound :=
      Eq.mpr (id (congrArg (fun _a => ‖WithLp.snd ↑f‖ ≤ _a) (Poincare.ParabolicHolder.norm_eq_parts f)))
        (le_add_of_nonneg_left (norm_nonneg (WithLp.fst ↑f)));
    (div_le_iff₀ (Real.rpow_pos_of_pos (Poincare.ParabolicHolder.parabolicDist_pos h) α)).mp
      (LE.le.trans (Eq.mp (congrArg (fun _a => _a ≤ ‖WithLp.snd ↑f‖) (Poincare.ParabolicHolder.increment_norm f i)) hi)
        hbound)
theorem Poincare.ParabolicHolder.norm_le_of_bounds.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F) {M K : ℝ},
  0 ≤ M →
    0 ≤ K →
      (∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M) →
        Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f)) K →
          ‖f‖ ≤ M + K :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f {M K} hM hK hb hh =>
  Eq.mpr (id (congrArg (fun _a => _a ≤ M + K) (Poincare.ParabolicHolder.norm_eq_parts f)))
    (add_le_add
      (lp.norm_le_of_forall_le hM fun p =>
        if hp : p ∈ Poincare.ParabolicHolder.cylinder T then hb p hp
        else
          id
            (Eq.mpr
              (id
                (congrFun'
                  (congrArg LE.le (Eq.trans (congrArg norm (Poincare.ParabolicHolder.zero_off f hp)) norm_zero)) M))
              hM))
      (lp.norm_le_of_forall_le hK fun i =>
        Eq.mpr (id (congrArg (fun _a => _a ≤ K) (Poincare.ParabolicHolder.increment_norm f i)))
          ((div_le_iff₀
                (Real.rpow_pos_of_pos (Poincare.ParabolicHolder.parabolicDist_pos i.property.right.right) α)).mpr
            (hh (↑i).1 i.property.left (↑i).2 i.property.right.left))))
def Poincare.ParabolicHolder.supNorm.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup F] → Set (ℝ × E) → (ℝ × E → F) → ℝ :=
fun {E} {F} [NormedAddCommGroup F] S f => sSup (insert 0 (Set.range fun p => ‖f ↑p‖))
theorem Poincare.ParabolicHolder.supNorm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) = ‖WithLp.fst ↑f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  le_antisymm
    (csSup_le (Set.insert_nonempty 0 (Set.range fun p => ‖↑(WithLp.fst ↑f) ↑p‖)) fun r a =>
      Or.casesOn a (fun h => Eq.symm h ▸ norm_nonneg (WithLp.fst ↑f)) fun h =>
        Exists.casesOn h fun p h =>
          h ▸
            lp.norm_apply_le_norm (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true))
              (WithLp.fst ↑f) ↑p)
    (have h0 :=
      le_csSup (Poincare.ParabolicHolder.supNorm_bddAbove f)
        (Set.mem_insert 0 (Set.range fun p => ‖↑(WithLp.fst ↑f) ↑p‖));
    lp.norm_le_of_forall_le h0 fun p =>
      if hp : p ∈ Poincare.ParabolicHolder.cylinder T then
        le_csSup (Poincare.ParabolicHolder.supNorm_bddAbove f) (Set.mem_insert_of_mem 0 (Set.mem_range_self ⟨p, hp⟩))
      else
        id
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  ‖_a‖ ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                (Poincare.ParabolicHolder.zero_off f hp)))
            (Eq.mpr
              (id
                (congrArg
                  (fun _a =>
                    _a ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                  norm_zero))
              h0)))
def Poincare.ParabolicHolder.holderSeminorm.{u_1, u_2} : {E : Type u_1} →
  {F : Type u_2} → [NormedAddCommGroup E] → [NormedAddCommGroup F] → ℝ → Set (ℝ × E) → (ℝ × E → F) → ℝ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] α S f =>
  sSup (insert 0 (Set.range fun i => ‖f (↑i).1 - f (↑i).2‖ / Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α))
theorem Poincare.ParabolicHolder.holderSeminorm_eq.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) = ‖WithLp.snd ↑f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  le_antisymm
    (csSup_le
      (Set.insert_nonempty 0
        (Set.range fun i =>
          ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ /
            Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α))
      fun r a =>
      Or.casesOn a (fun h => Eq.symm h ▸ norm_nonneg (WithLp.snd ↑f)) fun h =>
        Exists.casesOn h fun i h =>
          h ▸
            id
              (Eq.mpr
                (id (congrArg (fun _a => _a ≤ ‖WithLp.snd ↑f‖) (Eq.symm (Poincare.ParabolicHolder.increment_norm f i))))
                (lp.norm_apply_le_norm
                  (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true)) (WithLp.snd ↑f)
                  i)))
    (lp.norm_le_of_forall_le
      (le_csSup (Poincare.ParabolicHolder.holderSeminorm_bddAbove f)
        (Set.mem_insert 0
          (Set.range fun i =>
            ‖↑(WithLp.fst ↑f) (↑i).1 - ↑(WithLp.fst ↑f) (↑i).2‖ /
              Poincare.ParabolicHolder.parabolicDist (↑i).1 (↑i).2 ^ α)))
      fun i =>
      Eq.mpr
        (id
          (congrArg
            (fun _a =>
              _a ≤ Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
            (Poincare.ParabolicHolder.increment_norm f i)))
        (le_csSup (Poincare.ParabolicHolder.holderSeminorm_bddAbove f)
          (Set.mem_insert_of_mem 0 (Set.mem_range_self i))))
theorem Poincare.ParabolicHolder.norm_eq_parts.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F), ‖f‖ = ‖WithLp.fst ↑f‖ + ‖WithLp.snd ↑f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f => WithLp.prod_norm_eq_of_L1 ↑f
theorem Poincare.ParabolicHolder.supNorm_nonneg.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  0 ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Eq.mpr (id (congrArg (fun _a => 0 ≤ _a) (Poincare.ParabolicHolder.supNorm_eq f))) (norm_nonneg (WithLp.fst ↑f))
theorem Poincare.ParabolicHolder.holderSeminorm_nonneg.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  0 ≤ Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Eq.mpr (id (congrArg (fun _a => 0 ≤ _a) (Poincare.ParabolicHolder.holderSeminorm_eq f))) (norm_nonneg (WithLp.snd ↑f))
theorem Poincare.ParabolicHolder.le_supNorm.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F)
  (p : ℝ × E),
  ‖↑(WithLp.fst ↑f) p‖ ≤ Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f p =>
  Eq.mpr (id (congrArg (fun _a => ‖↑(WithLp.fst ↑f) p‖ ≤ _a) (Poincare.ParabolicHolder.supNorm_eq f)))
    (lp.norm_apply_le_norm (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true))
      (WithLp.fst ↑f) p)
theorem Poincare.ParabolicHolder.hasHolderBound_seminorm.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f))
    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f p hp q hq =>
  Eq.mpr
    (id
      (congrArg
        (fun _a => ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ _a * Poincare.ParabolicHolder.parabolicDist p q ^ α)
        (Poincare.ParabolicHolder.holderSeminorm_eq f)))
    (if h : p = q then
      Eq.ndrec (motive := fun q =>
        q ∈ Poincare.ParabolicHolder.cylinder T →
          ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖WithLp.snd ↑f‖ * Poincare.ParabolicHolder.parabolicDist p q ^ α)
        (fun hq =>
          Eq.mpr
            (id
              (congrFun' (congrArg LE.le (Eq.trans (congrArg norm (sub_self (↑(WithLp.fst ↑f) p))) norm_zero))
                (‖WithLp.snd ↑f‖ * Poincare.ParabolicHolder.parabolicDist p p ^ α)))
            (mul_nonneg (norm_nonneg (WithLp.snd ↑f))
              (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p p) α)))
        h hq
    else
      let i := ⟨(p, q), ⟨hp, ⟨hq, h⟩⟩⟩;
      have hi :=
        lp.norm_apply_le_norm (of_eq_true (Eq.trans (congrArg Not ENNReal.top_ne_zero._simp_1) not_false_eq_true))
          (WithLp.snd ↑f) i;
      (div_le_iff₀ (Real.rpow_pos_of_pos (Poincare.ParabolicHolder.parabolicDist_pos h) α)).mp
        (Eq.mp (congrArg (fun _a => _a ≤ ‖WithLp.snd ↑f‖) (Poincare.ParabolicHolder.increment_norm f i)) hi))
theorem Poincare.ParabolicHolder.zero_off.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F)
  {p : ℝ × E}, p ∉ Poincare.ParabolicHolder.cylinder T → ↑(WithLp.fst ↑f) p = 0 :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f {p} hp => f.property.left p hp
@[defeq] theorem Poincare.ParabolicHolder.mul_apply.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T ℝ) (p : ℝ × E),
  ↑(WithLp.fst ↑(f * g)) p = ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p :=
fun {E} [NormedAddCommGroup E] {α T} f g p => rfl
theorem Poincare.ParabolicHolder.product_holderBound.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T ℝ),
  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T)
    (fun p => ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p)
    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) *
        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) +
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) *
        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g)) :=
fun {E} [NormedAddCommGroup E] {α T} f g p hp q hq =>
  Trans.trans
    (Trans.trans
      (Trans.trans
        (Trans.trans
          ((fun {E} [Norm E] a a_1 e_a => e_a ▸ Eq.refl ‖a‖)
            (↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑f) q * ↑(WithLp.fst ↑g) q)
            (↑(WithLp.fst ↑f) p * (↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q) +
              (↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q) * ↑(WithLp.fst ↑g) q)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.sub_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑f) p) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑g) p) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) p) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) p) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑f) q) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑g) q) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) q) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.zero_mul (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1) + 0))))
                (Mathlib.Tactic.Ring.Common.sub_pf
                  (Mathlib.Tactic.Ring.Common.neg_add
                    (Mathlib.Tactic.Ring.Common.neg_mul (↑(WithLp.fst ↑f) q) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.neg_mul (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                            (Eq.refl (Int.negOfNat 1))))))
                    Mathlib.Tactic.Ring.Common.neg_zero)
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                    (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 *
                          (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                        0)))))
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑f) p) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑g) p) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              ↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                ↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑g) q) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt
                                (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) p) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) p) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) p) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                                (Mathlib.Meta.NormNum.IsInt.of_raw ((fun x => ℝ) p) (Int.negOfNat 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        (Mathlib.Tactic.Ring.Common.mul_zero (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 *
                              (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                            0)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                        (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 *
                              (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                            0))))
                    (Mathlib.Tactic.Ring.Common.zero_mul
                      (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1 +
                        (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1) +
                        (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 *
                            (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))))
                (Mathlib.Tactic.Ring.Common.mul_congr
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑f) p) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                ↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑f) q) rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a =>
                              ↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * Nat.rawCast 1 =
                                ↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul (↑(WithLp.fst ↑f) q) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt
                                (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                  (Mathlib.Tactic.Ring.Common.atom_pf (↑(WithLp.fst ↑g) q) rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a =>
                            ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1 =
                              ↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) p) (Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1) (Eq.refl 1)))))
                      (Mathlib.Tactic.Ring.Common.mul_zero (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_left (↑(WithLp.fst ↑f) q) (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.mul_pf_right (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsInt.of_raw ((fun x => ℝ) p) (Int.negOfNat 1))
                                (Mathlib.Meta.NormNum.IsNat.to_isInt
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                                (Eq.refl (Int.negOfNat 1))))))
                        (Mathlib.Tactic.Ring.Common.mul_zero
                          (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 *
                              (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                            0)))
                      (Mathlib.Tactic.Ring.Common.zero_mul (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 *
                            (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                      (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 *
                            (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                          0)))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                  (↑(WithLp.fst ↑f) p ^ Nat.rawCast 1 * (↑(WithLp.fst ↑g) p ^ Nat.rawCast 1 * Nat.rawCast 1))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (↑(WithLp.fst ↑f) p) (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero (↑(WithLp.fst ↑g) q) (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ((fun x => ℝ) p) (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ((fun x => ℝ) p) 1))
                            (Eq.refl (Int.ofNat 0))))))
                    (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                      (↑(WithLp.fst ↑f) q ^ Nat.rawCast 1 *
                          (↑(WithLp.fst ↑g) q ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast) +
                        0)))))))
          (norm_add_le (↑(WithLp.fst ↑f) p * (↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q))
            ((↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q) * ↑(WithLp.fst ↑g) q)))
        (Eq.mpr
          (id
            (congrArg
              (fun _a =>
                _a + ‖(↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q) * ↑(WithLp.fst ↑g) q‖ =
                  ‖↑(WithLp.fst ↑f) p‖ * ‖↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q‖ +
                    ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ * ‖↑(WithLp.fst ↑g) q‖)
              (norm_mul (↑(WithLp.fst ↑f) p) (↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q))))
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  ‖↑(WithLp.fst ↑f) p‖ * ‖↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q‖ + _a =
                    ‖↑(WithLp.fst ↑f) p‖ * ‖↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q‖ +
                      ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ * ‖↑(WithLp.fst ↑g) q‖)
                (norm_mul (↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q) (↑(WithLp.fst ↑g) q))))
            (Eq.refl
              (‖↑(WithLp.fst ↑f) p‖ * ‖↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q‖ +
                ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ * ‖↑(WithLp.fst ↑g) q‖)))))
      (add_le_add
        (mul_le_mul (Poincare.ParabolicHolder.le_supNorm f p)
          (Poincare.ParabolicHolder.hasHolderBound_seminorm g p hp q hq)
          (norm_nonneg (↑(WithLp.fst ↑g) p - ↑(WithLp.fst ↑g) q)) (Poincare.ParabolicHolder.supNorm_nonneg f))
        (mul_le_mul (Poincare.ParabolicHolder.hasHolderBound_seminorm f p hp q hq)
          (Poincare.ParabolicHolder.le_supNorm g q) (norm_nonneg (↑(WithLp.fst ↑g) q))
          (mul_nonneg (Poincare.ParabolicHolder.holderSeminorm_nonneg f)
            (Real.rpow_nonneg (Poincare.ParabolicHolder.parabolicDist_nonneg p q) α)))))
    (Mathlib.Tactic.Ring.of_eq
      (Mathlib.Tactic.Ring.Common.add_congr
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.atom_pf
            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) rfl
            (Eq.mpr
              (id
                (congrArg
                  (fun _a =>
                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1 =
                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                          Nat.rawCast 1 *
                        _a)
                  (Eq.symm rfl)))
              (Eq.refl
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                    Nat.rawCast 1 *
                  Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                        (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                    (Eq.symm rfl)))
                (Eq.refl ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
              (Mathlib.Tactic.Ring.Common.mul_zero
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                    Nat.rawCast 1 *
                  Nat.rawCast 1))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                  0)))
            (Mathlib.Tactic.Ring.Common.zero_mul
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                    Nat.rawCast 1 *
                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1) +
                0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                0))))
        (Mathlib.Tactic.Ring.Common.mul_congr
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                        (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                    (Eq.symm rfl)))
                (Eq.refl ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                            ↑(WithLp.fst ↑f) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.atom_pf
            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g)) rfl
            (Eq.mpr
              (id
                (congrArg
                  (fun _a =>
                    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1 =
                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        _a)
                  (Eq.symm rfl)))
              (Eq.refl
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                    Nat.rawCast 1 *
                  Nat.rawCast 1))))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_left (Poincare.ParabolicHolder.parabolicDist p q ^ α) (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_left
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
              (Mathlib.Tactic.Ring.Common.mul_zero
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                        Nat.rawCast 1 *
                      (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1)) +
                  0)))
            (Mathlib.Tactic.Ring.Common.zero_mul
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^ Nat.rawCast 1 *
                  Nat.rawCast 1 +
                0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1)) +
                0))))
        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
          (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
            (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                Nat.rawCast 1 *
              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
            ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                    Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1)) +
              0))))
      (Mathlib.Tactic.Ring.Common.mul_congr
        (Mathlib.Tactic.Ring.Common.add_congr
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                        Nat.rawCast 1 *
                      (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                            ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1 +
                  0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.mul_congr
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T)
                              ↑(WithLp.fst ↑f) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.atom_pf
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g)) rfl
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          Nat.rawCast 1 =
                        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                            Nat.rawCast 1 *
                          _a)
                    (Eq.symm rfl)))
                (Eq.refl
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))))
            (Mathlib.Tactic.Ring.Common.add_mul
              (Mathlib.Tactic.Ring.Common.mul_add
                (Mathlib.Tactic.Ring.Common.mul_pf_left
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_right
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1)))))
                (Mathlib.Tactic.Ring.Common.mul_zero
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1))
                (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                        Nat.rawCast 1 *
                      (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1) +
                    0)))
              (Mathlib.Tactic.Ring.Common.zero_mul
                (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1 +
                  0))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1) +
                  0))))
          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                  Nat.rawCast 1 *
                Nat.rawCast 1))
            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                    Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1) +
                0))))
        (Mathlib.Tactic.Ring.Common.atom_pf (Poincare.ParabolicHolder.parabolicDist p q ^ α) rfl
          (Eq.mpr
            (id
              (congrArg
                (fun _a =>
                  (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 =
                    (Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * _a)
                (Eq.symm rfl)))
            (Eq.refl ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1))))
        (Mathlib.Tactic.Ring.Common.add_mul
          (Mathlib.Tactic.Ring.Common.mul_add
            (Mathlib.Tactic.Ring.Common.mul_pf_left
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f)) (Nat.rawCast 1)
              (Mathlib.Tactic.Ring.Common.mul_pf_left
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α)
                  (Nat.rawCast 1)
                  (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                    (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                      (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
            (Mathlib.Tactic.Ring.Common.mul_zero
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                    Nat.rawCast 1 *
                  Nat.rawCast 1)))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)) +
                0)))
          (Mathlib.Tactic.Ring.Common.add_mul
            (Mathlib.Tactic.Ring.Common.mul_add
              (Mathlib.Tactic.Ring.Common.mul_pf_right (Poincare.ParabolicHolder.parabolicDist p q ^ α) (Nat.rawCast 1)
                (Mathlib.Tactic.Ring.Common.mul_pf_left
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f))
                  (Nat.rawCast 1)
                  (Mathlib.Tactic.Ring.Common.mul_pf_left
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g))
                    (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                      (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul) (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1)
                        (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1) (Eq.refl 1))))))
              (Mathlib.Tactic.Ring.Common.mul_zero
                (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                    Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                      Nat.rawCast 1 *
                    Nat.rawCast 1)))
              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                        Nat.rawCast 1 *
                      (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                          Nat.rawCast 1 *
                        Nat.rawCast 1)) +
                  0)))
            (Mathlib.Tactic.Ring.Common.zero_mul
              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))
            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1)) +
                0)))
          (Mathlib.Tactic.Ring.Common.add_pf_add_lt
            (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^ Nat.rawCast 1 *
              (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                  Nat.rawCast 1 *
                ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 * Nat.rawCast 1)))
            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
              ((Poincare.ParabolicHolder.parabolicDist p q ^ α) ^ Nat.rawCast 1 *
                  (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ^
                      Nat.rawCast 1 *
                    (Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑g) ^
                        Nat.rawCast 1 *
                      Nat.rawCast 1)) +
                0))))))
theorem Poincare.ParabolicHolder.bounded.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (f : Poincare.ParabolicHolder.Y α T F),
  ∃ M, ∀ p ∈ Poincare.ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f =>
  Exists.intro ‖f‖ fun p x => Poincare.ParabolicHolder.norm_le f p
theorem Poincare.ParabolicHolder.hasHolderBound.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f : Poincare.ParabolicHolder.Y α T F),
  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑f) ‖f‖ :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f x hp x_1 hq =>
  Poincare.ParabolicHolder.holder_le f hp hq
@[defeq] theorem Poincare.ParabolicHolder.add_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ}
  (f g : Poincare.ParabolicHolder.Y α T F) (p : ℝ × E),
  ↑(WithLp.fst ↑(f + g)) p = ↑(WithLp.fst ↑f) p + ↑(WithLp.fst ↑g) p :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} f g p => rfl
@[defeq] theorem Poincare.ParabolicHolder.zero_apply.{u_1, u_2} : ∀ {E : Type u_1} {F : Type u_2}
  [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F] {α T : ℝ} (p : ℝ × E),
  ↑(WithLp.fst ↑0) p = 0 :=
fun {E} {F} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {α T} p => rfl
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
theorem Poincare.ParabolicSolutionGraph.Graph.zero_trace.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (self : Poincare.ParabolicSolutionGraph.Graph α T) (x : E),
  ↑(WithLp.fst ↑self.u) (0, x) = 0 :=
fun E [NormedAddCommGroup E] [NormedSpace ℝ E] α T self => self.5
theorem Poincare.ParabolicSolutionGraph.Graph.hasFDeriv.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (self : Poincare.ParabolicSolutionGraph.Graph α T),
  ∀ t ∈ Set.Icc 0 T, ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.u) (t, z)) (↑(WithLp.fst ↑self.du) (t, x)) x :=
fun E [NormedAddCommGroup E] [NormedSpace ℝ E] α T self => self.6
theorem Poincare.ParabolicSolutionGraph.Graph.hasFDeriv_du.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (self : Poincare.ParabolicSolutionGraph.Graph α T),
  ∀ t ∈ Set.Icc 0 T,
    ∀ (x : E), HasFDerivAt (fun z => ↑(WithLp.fst ↑self.du) (t, z)) (↑(WithLp.fst ↑self.ddu) (t, x)) x :=
fun E [NormedAddCommGroup E] [NormedSpace ℝ E] α T self => self.7
theorem Poincare.ParabolicSolutionGraph.norm_ddu_le.{u_1} : ∀ {E : Type u_1} [inst : NormedAddCommGroup E]
  [inst_1 : NormedSpace ℝ E] {α T : ℝ} (g : Poincare.ParabolicSolutionGraph.Graph α T), ‖g.ddu‖ ≤ ‖g‖ :=
fun {E} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T} g =>
  Eq.mpr (id (congrArg (fun _a => ‖g.ddu‖ ≤ _a) (Poincare.ParabolicSolutionGraph.norm_eq g)))
    (have this := norm_nonneg g.u;
    have this_1 := norm_nonneg g.ut;
    have this_2 := norm_nonneg g.du;
    have this_3 := norm_nonneg g.ddu;
    le_of_not_gt fun a =>
      Mathlib.Tactic.Linarith.lt_irrefl
        (Eq.mp
          (congrArg (fun _a => _a < 0)
            (Mathlib.Tactic.Ring.of_eq
              (Mathlib.Tactic.Ring.Common.add_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.u‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.sub_congr
                      (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.sub_pf
                        (Mathlib.Tactic.Ring.Common.neg_add
                          (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ut‖ (Nat.rawCast 1)
                            (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                              (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                                (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                (Eq.refl (Int.negOfNat 1)))))
                          Mathlib.Tactic.Ring.Common.neg_zero)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.sub_congr
                    (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.sub_pf
                      (Mathlib.Tactic.Ring.Common.neg_add
                        (Mathlib.Tactic.Ring.Common.neg_mul ‖g.du‖ (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                            (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                              (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                              (Eq.refl (Int.negOfNat 1)))))
                        Mathlib.Tactic.Ring.Common.neg_zero)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (‖g.du‖ ^ Nat.rawCast 1 * (Int.negOfNat 1).rawCast + 0)))))
                (Mathlib.Tactic.Ring.Common.sub_congr
                  (Mathlib.Tactic.Ring.Common.add_congr
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.add_congr
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.u‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.u‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ut‖ rfl
                          (Eq.mpr
                            (id
                              (congrArg (fun _a => ‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ut‖ ^ Nat.rawCast 1 * _a)
                                (Eq.symm rfl)))
                            (Eq.refl (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.atom_pf ‖g.du‖ rfl
                        (Eq.mpr
                          (id
                            (congrArg (fun _a => ‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.du‖ ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))))
                    (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                      (Eq.mpr
                        (id
                          (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))))
                  (Mathlib.Tactic.Ring.Common.atom_pf ‖g.ddu‖ rfl
                    (Eq.mpr
                      (id
                        (congrArg (fun _a => ‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1 = ‖g.ddu‖ ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (‖g.ddu‖ ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.Common.sub_pf
                    (Mathlib.Tactic.Ring.Common.neg_add
                      (Mathlib.Tactic.Ring.Common.neg_mul ‖g.ddu‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_raw_eq
                          (Mathlib.Meta.NormNum.isInt_neg (Eq.refl Neg.neg)
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.negOfNat 1)))))
                      Mathlib.Tactic.Ring.Common.neg_zero)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.u‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.ut‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (‖g.du‖ ^ Nat.rawCast 1 * Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ddu‖ (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsInt.to_isNat
                                (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                                  (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1)) (Eq.refl (Int.ofNat 0)))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))))
                (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                  (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.u‖ (Nat.rawCast 1)
                    (Mathlib.Meta.NormNum.IsInt.to_isNat
                      (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                        (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                        (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                        (Eq.refl (Int.ofNat 0)))))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                    (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.ut‖ (Nat.rawCast 1)
                      (Mathlib.Meta.NormNum.IsInt.to_isNat
                        (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                          (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                          (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                          (Eq.refl (Int.ofNat 0)))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero
                      (Mathlib.Tactic.Ring.Common.add_overlap_pf_zero ‖g.du‖ (Nat.rawCast 1)
                        (Mathlib.Meta.NormNum.IsInt.to_isNat
                          (Mathlib.Meta.NormNum.isInt_add (Eq.refl HAdd.hAdd)
                            (Mathlib.Meta.NormNum.IsInt.of_raw ℝ (Int.negOfNat 1))
                            (Mathlib.Meta.NormNum.IsNat.to_isInt (Mathlib.Meta.NormNum.IsNat.of_raw ℝ 1))
                            (Eq.refl (Int.ofNat 0)))))
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add 0)))))
              (Mathlib.Tactic.Ring.cast_zero (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero))))
          (Mathlib.Tactic.Linarith.add_lt_of_le_of_neg
            (Mathlib.Tactic.Linarith.add_nonpos
              (Mathlib.Tactic.Linarith.add_nonpos (Mathlib.Tactic.Linarith.sub_nonpos_of_le this)
                (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_1))
              (Mathlib.Tactic.Linarith.sub_nonpos_of_le this_2))
            (Mathlib.Tactic.Linarith.sub_neg_of_lt a))))
exit_code=0
```

### 2026-09-15T09:56:25.105662

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
Poincare/Global/ParabolicHolderMultiplier.lean:17:35: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/ParabolicHolderMultiplier.lean:24:36: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/ParabolicHolderMultiplier.lean:31:36: error: unexpected token ':='; expected ')', ',' or ':'
Poincare/Global/ParabolicHolderMultiplier.lean:45:36: error: unexpected token ':='; expected ')', ',' or ':'
exit_code=1
```

### 2026-09-15T09:56:26.612381

```sh
rg -n '^(theorem|def) (du_zero_trace|ddu_zero_trace|ddu_time_bound|supNorm_ddu_le)|theorem HasFDerivAt.unique|theorem hasFDerivAt_const|theorem (sqrt_eq_rpow|rpow_mul|rpow_le_rpow)' Poincare/Global/ParabolicHolderMultiplier.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
```

```text
Poincare/Global/ParabolicHolderMultiplier.lean:17:theorem du_zero_trace (G : Graph (E := E) α T) (hT : 0 < T) (x : E) :
Poincare/Global/ParabolicHolderMultiplier.lean:24:theorem ddu_zero_trace (G : Graph (E := E) α T) (hT : 0 < T) (x : E) :
Poincare/Global/ParabolicHolderMultiplier.lean:31:theorem ddu_time_bound (G : Graph (E := E) α T) (hT : 0 < T)
Poincare/Global/ParabolicHolderMultiplier.lean:45:theorem supNorm_ddu_le (G : Graph (E := E) α T) (hα : 0 < α) (hT : 0 < T) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:412:theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:546:theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:570:theorem rpow_le_rpow_iff (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:613:theorem rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:632:theorem rpow_le_rpow_left_iff (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:645:theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:650:theorem rpow_le_rpow_left_iff_of_base_lt_one (hx0 : 0 < x) (hx1 : x < 1) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:717:theorem rpow_le_rpow_of_exponent_ge_of_imp (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyz : z ≤ y)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:729:theorem rpow_le_rpow_of_exponent_ge' (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 ≤ z) (hyz : z ≤ y) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988:theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:174:theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : HasFDerivAt f f₁' x) : f' = f₁' := by
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean:114:theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean:345:theorem hasFDerivAt_const_add_iff (c : F) : HasFDerivAt (c + f ·) f' x ↔ HasFDerivAt f f' x :=
exit_code=0
```

### 2026-09-15T09:56:37.008465

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T09:56:47.810544

```sh
rg -n 'theorem (le_opNorm₂|norm_sum_le)|norm_eq_one|theorem csSup_le|theorem sum_le_sum|theorem sub_apply' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group .lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean
```

```text
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:191:theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:199:theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:225:theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:552:theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:555:theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
.lake/packages/mathlib/Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:585:theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s ⊆ t) : sSup s ≤ sSup t := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:64:lemma Orthonormal.norm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:67:lemma Orthonormal.nnnorm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:70:  simp [h.norm_eq_one]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:72:lemma Orthonormal.enorm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:73:    ‖v i‖ₑ = 1 := by rw [← ofReal_norm]; simp [h.norm_eq_one]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:85:    · simp [h, inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:411:theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:829:theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
exit_code=0
```

### 2026-09-15T09:57:04.483546

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T09:57:07.393518

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMAxioms.lean
```

```text
'Poincare.ParabolicHolderMultiplier.du_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code=0
```

### 2026-09-15T09:57:07.425773

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=1
```

### 2026-09-15T09:57:07.467961

```sh
git diff --check
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T09:58:01.917550

```sh
rg -n 'theorem sub_apply|lemma norm_eq_one|theorem norm_mul' .lake/packages/mathlib/Mathlib/Algebra/Module .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator .lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Field/Basic.lean
```

```text
.lake/packages/mathlib/Mathlib/Analysis/Normed/Field/Basic.lean:115:lemma norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x ≠ 0 := by
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:454:lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/Defs.lean:882:theorem sub_apply (f g : M →ₛₗ[σ₁₂] N₂) (x : M) : (f - g) x = f x - g x :=
exit_code=0
```

### 2026-09-15T09:58:06.067249

```sh
git add Poincare/Global/ParabolicHolderMultiplier.lean && git commit -m "Prove zero-trace Hessian interpolation on parabolic cylinders"
```

```text
[worker/parabolic-holder-multiplier-estimate ec6fc68b] Prove zero-trace Hessian interpolation on parabolic cylinders
 1 file changed, 57 insertions(+)
 create mode 100644 Poincare/Global/ParabolicHolderMultiplier.lean
exit_code=0
```

### 2026-09-15T09:58:17.072528

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
Poincare/Global/ParabolicHolderMultiplier.lean:76:24: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑(WithLp.fst ↑H) p
in the target expression
  (fun p => ((↑(WithLp.fst ↑H) p) v) w) p = 0

α T : ℝ
H : Y α T (E →L[ℝ] E →L[ℝ] ℝ)
v w : E
hv : ‖v‖ = 1
hw : ‖w‖ = 1
p : ℝ × E
hp : p ∉ cylinder T
⊢ (fun p => ((↑(WithLp.fst ↑H) p) v) w) p = 0
exit_code=1
```

### 2026-09-15T09:58:35.849882

```sh
rg -n 'sum_induction|sum_insert|sum_le_sum|sum_const' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean .lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean; rg -n 'sub_apply' .lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean; rg -n 'theorem ext|theorem norm_le' Poincare/Global/ParabolicHolderSpace.lean
```

```text
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:108:@[to_additive (attr := gcongr) sum_le_sum]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:112:attribute [bound] sum_le_sum
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:117:add_decl_doc sum_le_sum
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:131:@[to_additive (attr := gcongr) sum_le_sum_of_subset_of_nonneg]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:242:@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:287:theorem abs_sum_le_sum_abs {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:319:    _ ≤ ∑ _b ∈ t, n := sum_le_sum hn
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:331:    _ ≤ ∑ b ∈ t, #{a ∈ s | f a = b} := sum_le_sum hn
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:388:  exact sum_le_sum fun i hi ↦ (hf i hi).card_pos
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:418:@[to_additive sum_le_sum_of_subset]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:428:@[to_additive sum_le_sum_of_ne_zero]
.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:582:  simpa only [sup_insert, Finset.sum_insert it] using ih.trans (by gcongr)
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:954:theorem sum_const_nat {m : ℕ} {f : ι → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:955:  rw [← Nat.nsmul_eq_mul, ← sum_const]
863:theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
902:theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
exit_code=0
```

### 2026-09-15T09:58:48.109998

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T09:58:53.129305

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMAxioms.lean
```

```text
'Poincare.ParabolicHolderMultiplier.du_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.eval_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_split' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code=0
```

### 2026-09-15T09:58:53.166682

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=1
```

### 2026-09-15T09:58:53.211985

```sh
git diff --check
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T09:59:35.766306

```sh
rg -n 'induction_on|sum_insert|sum_const|sum_empty' .lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean
```

```text
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:22:* `Finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `Finset α`,
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:290:  induction m using Multiset.induction_on <;> simp
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:475:theorem cons_induction_on {α : Type*} {motive : Finset α → Prop} (s : Finset α) (empty : motive ∅)
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:491:protected theorem induction_on {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (s : Finset α)
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:502:theorem induction_on' {α : Type*} {motive : Finset α → Prop} [DecidableEq α] (S : Finset α)
.lake/packages/mathlib/Mathlib/Data/Finset/Insert.lean:505:  @Finset.induction_on α (fun T => T ⊆ S → motive T) _ S (fun _ => empty)
exit_code=0
```

### 2026-09-15T09:59:43.209853

```sh
git add Poincare/Global/ParabolicHolderMultiplier.lean && git commit -m "Prove bounded Hessian entries and the split Holder product estimate"
```

```text
[worker/parabolic-holder-multiplier-estimate 5c2624ca] Prove bounded Hessian entries and the split Holder product estimate
 1 file changed, 88 insertions(+)
exit_code=0
```

### 2026-09-15T10:00:00.522609

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
Poincare/Global/ParabolicHolderMultiplier.lean:150:10: error: unsolved goals
case empty
α T : ℝ
ι : Type u_1
f : ι → Y α T ℝ
p : ℝ × E
⊢ 0 p = 0
Poincare/Global/ParabolicHolderMultiplier.lean:157:37: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:157:55: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:176:39: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:176:57: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:211:9: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:211:27: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:220:21: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
Poincare/Global/ParabolicHolderMultiplier.lean:220:39: error(lean.unknownIdentifier): Unknown identifier `«e».norm_eq_one`
exit_code=1
```

### 2026-09-15T10:00:01.633663

```sh
rg -n 'le_opNorm |getEnv|collectAxioms|constants.toList|moduleIdx' harness/gate.sh scripts/lean audit/PoincareAudit | head -65; rg -n 'theorem le_opNorm' .lake/packages/mathlib/Mathlib/Analysis/Normed/Operator
```

```text
harness/gate.sh:25:  let env ← getEnv
harness/gate.sh:31:      let axs ← liftCoreM (collectAxioms n)
audit/PoincareAudit/Guard.lean:29:      let axioms ← collectAxioms c
scripts/lean/TheoremRegistry.lean:116:    ("axioms", strings (← collectAxioms name))]
scripts/lean/TheoremRegistry.lean:166:    for (name, _) in env.constants.toList do
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:239:theorem le_opNorm : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:248:theorem le_opNorm_of_le {c : ℝ} {x} (h : ‖x‖ ≤ c) : ‖f x‖ ≤ ‖f‖ * c :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:70:theorem le_opNorm₂ [RingHomIsometric σ₁₃] (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) :
exit_code=0
```

### 2026-09-15T10:00:20.788299

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T10:00:26.713369

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMAxioms.lean
```

```text
'Poincare.ParabolicHolderMultiplier.du_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.eval_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_forcing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code=0
```

### 2026-09-15T10:00:26.752441

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=1
```

### 2026-09-15T10:00:26.794259

```sh
git diff --check
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T10:00:56.583142

```sh
rg -n 'norm_nonneg|mul_le_mul_of_nonneg_right|mul_le_mul_of_nonneg_left|mul_le_mul |add_le_add|mul_nonneg|add_nonneg' .lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean .lake/packages/mathlib/Mathlib/Algebra/Order/Group/Defs.lean .lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean | head -35
```

```text
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:146:lemma IsOrderedRing.of_mul_nonneg [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:147:    [ZeroLEOneClass R] (mul_nonneg : ∀ a b : R, 0 ≤ a → 0 ≤ b → 0 ≤ a * b) :
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:149:  mul_le_mul_of_nonneg_left a ha b c hbc := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:150:    simpa only [mul_sub, sub_nonneg] using mul_nonneg _ _ ha (sub_nonneg.2 hbc)
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:151:  mul_le_mul_of_nonneg_right a ha b c hbc := by
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:152:    simpa only [sub_mul, sub_nonneg] using mul_nonneg _ _ (sub_nonneg.2 hbc) ha
.lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Defs.lean:167:  .of_mul_pos fun _ _ ap bp ↦ (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:104:  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:123:@[to_additive (attr := simp) norm_nonneg]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:124:theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:128:attribute [bound] norm_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:129:attribute [grind .] norm_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:132:theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:159:  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:379:  ⟨fun a => .mk ‖a‖ (norm_nonneg' a)⟩
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:403:  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:409:  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:661:  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:921:  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:997:lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1007:  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1020:  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1088:    | none => return .nonnegative q(norm_nonneg' $a)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:1110:    | none => return .nonnegative q(norm_nonneg $a)
exit_code=0
```

### 2026-09-15T10:01:04.153856

```sh
git add Poincare/Global/ParabolicHolderMultiplier.lean && git commit -m "Prove the nine-entry parabolic Holder multiplier bound"
```

```text
[worker/parabolic-holder-multiplier-estimate fb41a775] Prove the nine-entry parabolic Holder multiplier bound
 1 file changed, 78 insertions(+)
exit_code=0
```

### 2026-09-15T10:01:19.479947

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T10:01:27.914394

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMAxioms.lean
```

```text
'Poincare.ParabolicHolderMultiplier.du_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.eval_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_forcing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_error_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.error_small' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code=0
```

### 2026-09-15T10:01:27.945330

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/ParabolicHolderMultiplier.lean
```

```text
(empty output)
exit_code=1
```

### 2026-09-15T10:01:27.983162

```sh
git diff --check
```

```text
(empty output)
exit_code=0
```

### 2026-09-15T10:01:52.943589

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMInventory.lean
```

```text
DECL Poincare.ParabolicHolderMultiplier.entry._proof_7
DECL Poincare.ParabolicHolderMultiplier.entry._proof_3
DECL Poincare.ParabolicHolderMultiplier.entry._proof_2
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_9
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_8
DECL Poincare.ParabolicHolderMultiplier.du_zero_trace
DECL Poincare.ParabolicHolderMultiplier.forcing_eq_sum
DECL Poincare.ParabolicHolderMultiplier.entry_apply
DECL Poincare.ParabolicHolderMultiplier.entry._proof_12
DECL Poincare.ParabolicHolderMultiplier.entry._proof_11
DECL Poincare.ParabolicHolderMultiplier.norm_mul_split
DECL Poincare.ParabolicHolderMultiplier.norm_entry_le
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_4
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_1
DECL Poincare.ParabolicHolderMultiplier.ddu_zero_trace
DECL Poincare.ParabolicHolderMultiplier.norm_forcing_le
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_5
DECL Poincare.ParabolicHolderMultiplier.entry._proof_6
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_13
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_10
DECL Poincare.ParabolicHolderMultiplier.supNorm_ddu_le
DECL Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le
DECL Poincare.ParabolicHolderMultiplier.forcing
DECL Poincare.ParabolicHolderMultiplier.supNorm_entry_le
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_7
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_3
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_2
DECL Poincare.ParabolicHolderMultiplier.eval_norm_le
DECL Poincare.ParabolicHolderMultiplier.entry._proof_9
DECL Poincare.ParabolicHolderMultiplier.entry._proof_8
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_12
DECL Poincare.ParabolicHolderMultiplier.error_small
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_11
DECL Poincare.ParabolicHolderMultiplier.entry.congr_simp
DECL Poincare.ParabolicHolderMultiplier.norm_error_le
DECL Poincare.ParabolicHolderMultiplier.ddu_time_bound
DECL Poincare.ParabolicHolderMultiplier.forcing_apply
DECL Poincare.ParabolicHolderMultiplier.sum_apply
DECL Poincare.ParabolicHolderMultiplier.entry._proof_4
DECL Poincare.ParabolicHolderMultiplier.entry._proof_1
DECL Poincare.ParabolicHolderMultiplier.forcing._proof_6
DECL Poincare.ParabolicHolderMultiplier.entry._proof_5
DECL Poincare.ParabolicHolderMultiplier.entry._proof_13
DECL Poincare.ParabolicHolderMultiplier.entry._proof_10
DECL Poincare.ParabolicHolderMultiplier.entry
DECL Poincare.ParabolicHolderMultiplier.entry_holderBound
exit_code=0
```

### 2026-09-15T10:01:54.769418

```sh
git add Poincare/Global/ParabolicHolderMultiplier.lean && git commit -m "Prove elementwise error smallness after the solution operator"
```

```text
[worker/parabolic-holder-multiplier-estimate 430f5bfb] Prove elementwise error smallness after the solution operator
 1 file changed, 35 insertions(+)
exit_code=0
```

### 2026-09-15T10:02:19.649137

```sh
while IFS= read -r symbol; do printf "%s: " "$symbol"; rg -n -w -m 1 "$symbol" Poincare/Global/ParabolicHolderSpace.lean Poincare/Global/ParabolicSolutionGraph.lean Poincare/Global/RiemannianContext.lean .lake/packages/mathlib/Mathlib | head -1; done < /private/tmp/phm_names.txt
```

```text
ClosedSmoothModel: Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
Graph: Poincare/Global/ParabolicSolutionGraph.lean:20:structure Graph (α T : ℝ) where
Y: Poincare/Global/ParabolicSolutionGraph.lean:21:  u : Y (E := E) α T ℝ
HasHolderBound: Poincare/Global/ParabolicHolderSpace.lean:49:def HasHolderBound (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) (K : ℝ) : Prop :=
zero_trace: Poincare/Global/ParabolicSolutionGraph.lean:25:  zero_trace : ∀ x : E, u (0, x) = 0
hasFDeriv: Poincare/Global/ParabolicSolutionGraph.lean:26:  hasFDeriv : ∀ t ∈ Icc 0 T, ∀ x : E,
hasFDeriv_du: Poincare/Global/ParabolicSolutionGraph.lean:28:  hasFDeriv_du : ∀ t ∈ Icc 0 T, ∀ x : E,
unique: Poincare/Global/ParabolicHolderSpace.lean:104:The support equation selects the unique extension that is zero off the cylinder. -/
hasFDerivAt_const: Poincare/Global/ParabolicSolutionGraph.lean:48:    · intro t ht x; exact hasFDerivAt_const (0 : ℝ) x
holder_le: Poincare/Global/ParabolicHolderSpace.lean:134:theorem holder_le (f : Y (E := E) α T F) {p q : ℝ × E}
cylinder: Poincare/Global/ParabolicHolderSpace.lean:12:An element is represented by a bounded function, zero off the cylinder, and
mem_univ: .lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean:710:  Set.mem_univ x
sqrt_eq_rpow: .lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:549:  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]
rpow_mul: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:281:      tendsto_card_le_div''_aux hX h₁ aux₂, ← Real.rpow_natCast, ← Real.rpow_mul hc₁,
sub_zero: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Unitization.lean:352:  Unitization.ext rfl (sub_zero 0).symm
sub_self: Poincare/Global/ParabolicHolderSpace.lean:139:    simp only [sub_self, norm_zero]
norm_zero: Poincare/Global/ParabolicHolderSpace.lean:139:    simp only [sub_self, norm_zero]
zero_add: .lake/packages/mathlib/Mathlib/Algebra/FreeAlgebra.lean:129:  | zero_add {a : Pre R X} : Rel (0 + a) a
abs_of_nonneg: .lake/packages/mathlib/Mathlib/Computability/AkraBazzi/GrowsPolynomially.lean:241:      rw [abs_of_nonneg hx]
supNorm: Poincare/Global/ParabolicHolderSpace.lean:61:def supNorm (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
csSup_le: Poincare/Global/ParabolicHolderSpace.lean:248:  · apply csSup_le (insert_nonempty _ _)
insert_nonempty: Poincare/Global/ParabolicHolderSpace.lean:248:  · apply csSup_le (insert_nonempty _ _)
rpow_nonneg: Poincare/Global/ParabolicSolutionGraph.lean:130:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
norm_nonneg: Poincare/Global/ParabolicSolutionGraph.lean:91:  have := norm_nonneg g.u
norm_ddu_le: Poincare/Global/ParabolicSolutionGraph.lean:113:theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
rpow_le_rpow: .lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:634:    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg
mul_le_mul: Poincare/Global/ParabolicHolderSpace.lean:370:      · exact mul_le_mul (le_supNorm f p) (hasHolderBound_seminorm g p hp q hq)
mul_comm: Poincare/Global/ParabolicHolderSpace.lean:123:  exact mul_comm _ _
le_opNorm₂: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean:1150:    · apply Eventually.of_forall (fun y ↦ (le_opNorm₂ L (g y) (f p y)).trans ?_)
sub_apply: Poincare/Global/ParabolicHolderSpace.lean:211:@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
holderSeminorm: Poincare/Global/ParabolicHolderSpace.lean:57:def holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
hasHolderBound_seminorm: Poincare/Global/ParabolicHolderSpace.lean:341:theorem hasHolderBound_seminorm (f : Y (E := E) α T F) :
ofFunction: Poincare/Global/ParabolicSolutionGraph.lean:199:  u := ofFunction u hu_off hu_bound hu_holder
zero_off: Poincare/Global/ParabolicHolderSpace.lean:112:theorem zero_off (f : Y (E := E) α T F) {p : ℝ × E} (hp : p ∉ cylinder T) :
le_supNorm: Poincare/Global/ParabolicHolderSpace.lean:336:theorem le_supNorm (f : Y (E := E) α T F) (p : ℝ × E) :
supNorm_nonneg: Poincare/Global/ParabolicHolderSpace.lean:327:theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
norm_le_of_bounds: Poincare/Global/ParabolicHolderSpace.lean:290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
holderSeminorm_nonneg: Poincare/Global/ParabolicHolderSpace.lean:331:theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
mul_apply: Poincare/Global/ParabolicHolderSpace.lean:387:@[simp] theorem mul_apply (f g : Y (E := E) α T ℝ) (p : ℝ × E) :
norm_mul: Poincare/Global/ParabolicHolderSpace.lean:364:    _ = ‖f p‖ * ‖g p - g q‖ + ‖f p - f q‖ * ‖g q‖ := by rw [norm_mul, norm_mul]
norm_add_le: Poincare/Global/ParabolicSolutionGraph.lean:258:      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
add_le_add: Poincare/Global/ParabolicSolutionGraph.lean:258:      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
mul_nonneg: Poincare/Global/ParabolicHolderSpace.lean:140:    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
add_nonneg: Poincare/Global/ParabolicHolderSpace.lean:33:  exact add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
sum_empty: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/SetToL1.lean:722:    simp only [setToFun_zero, Finset.sum_empty]
induction_on: .lake/packages/mathlib/Mathlib/Algebra/Algebra/Epi.lean:37:    induction x using TensorProduct.induction_on with
sum_insert: .lake/packages/mathlib/Mathlib/Algebra/Order/Ring/GeomSum.lean:190:      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (Nat.succ_pos _), sum_insert] <;>
norm_eq: Poincare/Global/ParabolicSolutionGraph.lean:83:theorem norm_eq (g : Graph (E := E) α T) :
basisFun: .lake/packages/mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean:156:  · rw [← Basis.det_mul_det _ (Pi.basisFun ℝ ι) _, abs_mul, Pi.basisFun_det_apply,
norm_eq_one: .lake/packages/mathlib/Mathlib/Algebra/QuadraticAlgebra/Basic.lean:253:alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary
norm_le: Poincare/Global/ParabolicSolutionGraph.lean:123:  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)
ext: Poincare/Global/ParabolicHolderSpace.lean:41:  · have ht : p.1 ≠ q.1 := fun ht => h (Prod.ext ht hx)
norm_sum_le: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/FinMeasAdditive.lean:483:    ‖∑ x ∈ f.range, T (f ⁻¹' {x}) x‖ ≤ ∑ x ∈ f.range, ‖T (f ⁻¹' {x}) x‖ := norm_sum_le _ _
sum_le_sum: .lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:334:        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
le_opNorm: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:604:    _ ≤ ‖integralCLM (α := α) (μ := μ)‖ * ‖f‖ := le_opNorm _ _
mul_le_mul_of_nonneg_right: Poincare/Global/ParabolicSolutionGraph.lean:129:    (mul_le_mul_of_nonneg_right (norm_u_le g)
mul_le_mul_of_nonneg_left: .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/L1.lean:132:      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
exit_code=0
```

### 2026-09-15T10:02:25.883988

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMAllAxioms.lean
```

```text
'Poincare.ParabolicHolderMultiplier.ddu_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.ddu_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.du_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.entry_holderBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.error_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.eval_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_10' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_11' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_13' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing._proof_9' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.forcing_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_error_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_forcing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.norm_mul_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_ddu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.ParabolicHolderMultiplier.supNorm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit_code=0
```

### 2026-09-15T10:02:57.590801

```sh
git log --oneline 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df..HEAD; git diff 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df..HEAD -- Poincare/Global/ParabolicHolderMultiplier.lean; git status --short --branch; cat lean-toolchain
```

```text
430f5bfb Prove elementwise error smallness after the solution operator
fb41a775 Prove the nine-entry parabolic Holder multiplier bound
5c2624ca Prove bounded Hessian entries and the split Holder product estimate
ec6fc68b Prove zero-trace Hessian interpolation on parabolic cylinders
diff --git a/Poincare/Global/ParabolicHolderMultiplier.lean b/Poincare/Global/ParabolicHolderMultiplier.lean
new file mode 100644
index 00000000..3373799f
--- /dev/null
+++ b/Poincare/Global/ParabolicHolderMultiplier.lean
@@ -0,0 +1,258 @@
+import Poincare.Global.ParabolicSolutionGraph
+import Poincare.Global.RiemannianContext
+
+noncomputable section
+
+namespace Poincare.ParabolicHolderMultiplier
+
+open Set ParabolicHolder ParabolicSolutionGraph
+
+local notation "E" => ClosedSmoothModel 3
+local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+variable {α T : ℝ}
+
+/-- The first spatial derivative of the zero initial trace vanishes. -/
+theorem du_zero_trace (G : Graph («E» := E) α T) (hT : 0 < T) (x : E) :
+    G.du (0, x) = 0 := by
+  have h := G.hasFDeriv 0 ⟨le_rfl, hT.le⟩ x
+  simp only [G.zero_trace] at h
+  exact h.unique (hasFDerivAt_const (0 : ℝ) x)
+
+/-- The spatial Hessian of the zero initial trace vanishes. -/
+theorem ddu_zero_trace (G : Graph («E» := E) α T) (hT : 0 < T) (x : E) :
+    G.ddu (0, x) = 0 := by
+  have h := G.hasFDeriv_du 0 ⟨le_rfl, hT.le⟩ x
+  simp only [du_zero_trace G hT] at h
+  exact h.unique (hasFDerivAt_const (0 : E →L[ℝ] ℝ) x)
+
+/-- Comparison with time zero gives the short-time Hessian factor. -/
+theorem ddu_time_bound (G : Graph («E» := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.ddu (t, x)‖ ≤ ‖G.ddu‖ * t ^ (α / 2) := by
+  have h := ParabolicHolder.holder_le G.ddu
+    (show (t, x) ∈ cylinder T from ⟨ht, mem_univ x⟩)
+    (show (0, x) ∈ cylinder T from ⟨⟨le_rfl, hT.le⟩, mem_univ x⟩)
+  have he : (Real.sqrt t) ^ α = t ^ (α / 2) := by
+    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1]
+    congr 1
+    ring
+  simpa only [ddu_zero_trace G hT, sub_zero, parabolicDist, sub_self,
+    norm_zero, zero_add, abs_of_nonneg ht.1, he] using h
+
+/-- The Hessian sup norm is small on a short cylinder. -/
+theorem supNorm_ddu_le (G : Graph («E» := E) α T) (hα : 0 < α) (hT : 0 < T) :
+    supNorm (cylinder T) G.ddu ≤ T ^ (α / 2) * ‖G‖ := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · exact mul_nonneg (Real.rpow_nonneg hT.le _) (norm_nonneg _)
+  · calc
+      ‖G.ddu p‖ ≤ ‖G.ddu‖ * p.val.1 ^ (α / 2) := ddu_time_bound G hT p.property.1 p.val.2
+      _ ≤ ‖G‖ * T ^ (α / 2) := mul_le_mul (norm_ddu_le G)
+        (Real.rpow_le_rpow p.property.1.1 p.property.1.2 (by linarith))
+        (Real.rpow_nonneg p.property.1.1 _) (norm_nonneg G)
+      _ = _ := mul_comm _ _
+
+/-- Evaluation on two unit vectors does not increase the bilinear operator norm. -/
+theorem eval_norm_le (A : Bilin) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
+    ‖A v w‖ ≤ ‖A‖ := by
+  simpa only [hv, hw, mul_one] using ContinuousLinearMap.le_opNorm₂ A v w
+
+/-- Bounded evaluation preserves the Hölder seminorm bound. -/
+theorem entry_holderBound (H : Y («E» := E) α T Bilin) {v w : E}
+    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
+    HasHolderBound α (cylinder T) (fun p => H p v w)
+      (holderSeminorm α (cylinder T) H) := by
+  intro p hp q hq
+  have h := eval_norm_le (H p - H q) hv hw
+  simp only [ContinuousLinearMap.sub_apply] at h
+  exact h.trans (hasHolderBound_seminorm H p hp q hq)
+
+/-- A coordinate entry is a supported bounded Hölder function. -/
+def entry (H : Y («E» := E) α T Bilin) (v w : E)
+    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : Y («E» := E) α T ℝ :=
+  ofFunction (fun p => H p v w)
+    (fun p hp => by dsimp only; rw [zero_off H hp]; simp)
+    ⟨supNorm (cylinder T) H, fun p _ =>
+      (eval_norm_le (H p) hv hw).trans (le_supNorm H p)⟩
+    ⟨_, entry_holderBound H hv hw⟩
+
+@[simp] theorem entry_apply (H : Y («E» := E) α T Bilin) (v w : E)
+    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (p : ℝ × E) :
+    entry H v w hv hw p = H p v w := rfl
+
+/-- The entry's sup norm is bounded by the tensor's sup norm. -/
+theorem supNorm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
+    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
+    supNorm (cylinder T) (entry H v w hv hw) ≤ supNorm (cylinder T) H := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · exact supNorm_nonneg H
+  · exact (eval_norm_le (H p) hv hw).trans (le_supNorm H p)
+
+/-- Unit coordinate evaluation has norm at most one on the Hölder space. -/
+theorem norm_entry_le (H : Y («E» := E) α T Bilin) (v w : E)
+    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
+    ‖entry H v w hv hw‖ ≤ ‖H‖ := by
+  rw [ParabolicHolder.norm_eq H]
+  apply norm_le_of_bounds _ (supNorm_nonneg H) (holderSeminorm_nonneg H)
+  · intro p _
+    exact (eval_norm_le (H p) hv hw).trans (le_supNorm H p)
+  · exact entry_holderBound H hv hw
+
+/-- The split product estimate retains the small sup factor on the second term. -/
+theorem norm_mul_split (b h : Y («E» := E) α T ℝ) :
+    ‖b * h‖ ≤ supNorm (cylinder T) b * ‖h‖ +
+      holderSeminorm α (cylinder T) b * supNorm (cylinder T) h := by
+  have hb : ∀ p ∈ cylinder T,
+      ‖(b * h) p‖ ≤ supNorm (cylinder T) b * supNorm (cylinder T) h := by
+    intro p _
+    rw [mul_apply, norm_mul]
+    exact mul_le_mul (le_supNorm b p) (le_supNorm h p)
+      (norm_nonneg _) (supNorm_nonneg b)
+  have hh : HasHolderBound α (cylinder T) (b * h)
+      (supNorm (cylinder T) b * holderSeminorm α (cylinder T) h +
+        holderSeminorm α (cylinder T) b * supNorm (cylinder T) h) := by
+    intro p hp q hq
+    calc
+      ‖(b * h) p - (b * h) q‖ =
+          ‖b p * (h p - h q) + (b p - b q) * h q‖ := by
+        simp only [mul_apply]
+        congr 1
+        ring
+      _ ≤ ‖b p * (h p - h q)‖ + ‖(b p - b q) * h q‖ := norm_add_le _ _
+      _ = ‖b p‖ * ‖h p - h q‖ + ‖b p - b q‖ * ‖h q‖ := by
+        rw [norm_mul, norm_mul]
+      _ ≤ supNorm (cylinder T) b *
+            (holderSeminorm α (cylinder T) h * parabolicDist p q ^ α) +
+          (holderSeminorm α (cylinder T) b * parabolicDist p q ^ α) *
+            supNorm (cylinder T) h := by
+        apply add_le_add
+        · exact mul_le_mul (le_supNorm b p) (hasHolderBound_seminorm h p hp q hq)
+            (norm_nonneg _) (supNorm_nonneg b)
+        · exact mul_le_mul (hasHolderBound_seminorm b p hp q hq) (le_supNorm h q)
+            (norm_nonneg _) (mul_nonneg (holderSeminorm_nonneg b)
+              (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
+      _ = _ := by ring
+  have hn := norm_le_of_bounds (b * h)
+    (mul_nonneg (supNorm_nonneg b) (supNorm_nonneg h))
+    (add_nonneg (mul_nonneg (supNorm_nonneg b) (holderSeminorm_nonneg h))
+      (mul_nonneg (holderSeminorm_nonneg b) (supNorm_nonneg h))) hb hh
+  rw [ParabolicHolder.norm_eq h]
+  nlinarith only [hn]
+
+/-- Evaluation commutes with finite sums in the Hölder carrier. -/
+theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Y («E» := E) α T ℝ)
+    (p : ℝ × E) : (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
+  classical
+  induction s using Finset.induction_on with
+  | empty => simp only [Finset.sum_empty]; rfl
+  | @insert a s ha ih => simp only [Finset.sum_insert ha, add_apply, ih]
+
+/-- The nine coefficient-Hessian products, constructed as a supported Hölder function. -/
+def forcing (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ) (G : Graph («E» := E) α T) :
+    Y («E» := E) α T ℝ := by
+  let y : Y («E» := E) α T ℝ := ∑ i, ∑ j,
+    b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)
+  have he (p : ℝ × E) : y p = ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j) := by
+    simp only [y, sum_apply, mul_apply, entry_apply]
+  exact ofFunction (fun p => ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j))
+    (fun p hp => by dsimp only; rw [← he p]; exact zero_off y hp)
+    ⟨‖y‖, fun p _ => by dsimp only; rw [← he p]; exact ParabolicHolder.norm_le y p⟩
+    ⟨‖y‖, fun p hp q hq => by
+      dsimp only
+      rw [← he p, ← he q]
+      exact ParabolicHolder.holder_le y hp hq⟩
+
+@[simp] theorem forcing_apply (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
+    (G : Graph («E» := E) α T) (p : ℝ × E) :
+    forcing b G p = ∑ i, ∑ j, b i j p * G.ddu p (e i) (e j) := rfl
+
+/-- The function construction agrees with the finite sum in the Hölder space. -/
+theorem forcing_eq_sum (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
+    (G : Graph («E» := E) α T) :
+    forcing b G = ∑ i, ∑ j,
+      b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j) := by
+  apply ParabolicHolder.ext
+  intro p _
+  simp only [forcing_apply, sum_apply, mul_apply, entry_apply]
+
+/-- A coefficient times one Hessian entry has the split short-cylinder bound. -/
+theorem norm_mul_ddu_entry_le (b : Y («E» := E) α T ℝ) (G : Graph («E» := E) α T)
+    (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
+    (hb : supNorm (cylinder T) b ≤ ε)
+    (hbα : holderSeminorm α (cylinder T) b ≤ Λ)
+    (v w : E) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
+    ‖b * entry G.ddu v w hv hw‖ ≤ ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖ := by
+  have hε : 0 ≤ ε := (supNorm_nonneg b).trans hb
+  have hΛ : 0 ≤ Λ := (holderSeminorm_nonneg b).trans hbα
+  have hn := (norm_entry_le G.ddu v w hv hw).trans (norm_ddu_le G)
+  have hs := (supNorm_entry_le G.ddu v w hv hw).trans (supNorm_ddu_le G hα hT)
+  calc
+    ‖b * entry G.ddu v w hv hw‖ ≤
+        supNorm (cylinder T) b * ‖entry G.ddu v w hv hw‖ +
+          holderSeminorm α (cylinder T) b * supNorm (cylinder T) (entry G.ddu v w hv hw) :=
+      norm_mul_split b _
+    _ ≤ ε * ‖G‖ + Λ * (T ^ (α / 2) * ‖G‖) :=
+      add_le_add (mul_le_mul hb hn (norm_nonneg _) hε)
+        (mul_le_mul hbα hs (supNorm_nonneg _) hΛ)
+    _ = _ := by ring
+
+/-- Summing the nine entries gives the frozen-coefficient multiplier estimate. -/
+theorem norm_forcing_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
+    (G : Graph («E» := E) α T) (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ) :
+    ‖forcing b G‖ ≤ 9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖) := by
+  rw [forcing_eq_sum]
+  calc
+    _ ≤ ∑ i, ‖∑ j, b i j * entry G.ddu (e i) (e j)
+        (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)‖ := norm_sum_le _ _
+    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
+        (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖) := by
+      apply Finset.sum_le_sum
+      intro i _
+      apply (norm_sum_le _ _).trans
+      apply Finset.sum_le_sum
+      intro j _
+      exact norm_mul_ddu_entry_le (b i j) G hα hT (hb i j) (hbα i j)
+        (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)
+    _ = _ := by simp; ring
+
+/-- Composing the multiplier with a bounded solution map gives an elementwise error bound. -/
+theorem norm_error_le (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
+    (S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
+    (hα : 0 < α) (hT : 0 < T) {ε Λ C_S : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
+    (hS : ‖S‖ ≤ C_S) (f : Y («E» := E) α T ℝ) :
+    ‖forcing b (S f)‖ ≤ 9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖ := by
+  have hε : 0 ≤ ε := (supNorm_nonneg (b 0 0)).trans (hb 0 0)
+  have hΛ : 0 ≤ Λ := (holderSeminorm_nonneg (b 0 0)).trans (hbα 0 0)
+  have hpow : 0 ≤ T ^ (α / 2) := Real.rpow_nonneg hT.le _
+  have hSf : ‖S f‖ ≤ C_S * ‖f‖ :=
+    (S.le_opNorm f).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg f))
+  calc
+    ‖forcing b (S f)‖ ≤ 9 * (ε * ‖S f‖ + Λ * T ^ (α / 2) * ‖S f‖) :=
+      norm_forcing_le b (S f) hα hT hb hbα
+    _ = 9 * (ε + Λ * T ^ (α / 2)) * ‖S f‖ := by ring
+    _ ≤ 9 * (ε + Λ * T ^ (α / 2)) * (C_S * ‖f‖) :=
+      mul_le_mul_of_nonneg_left hSf (by positivity)
+    _ = _ := by ring
+
+/-- Two quarter-size contributions give the required one-half error bound. -/
+theorem error_small (b : Fin 3 → Fin 3 → Y («E» := E) α T ℝ)
+    (S : Y («E» := E) α T ℝ →L[ℝ] Graph («E» := E) α T)
+    (hα : 0 < α) (hT : 0 < T) {ε Λ C_S : ℝ}
+    (hb : ∀ i j, supNorm (cylinder T) (b i j) ≤ ε)
+    (hbα : ∀ i j, holderSeminorm α (cylinder T) (b i j) ≤ Λ)
+    (hS : ‖S‖ ≤ C_S) (hε : 9 * C_S * ε ≤ 1 / 4)
+    (hΛ : 9 * C_S * Λ * T ^ (α / 2) ≤ 1 / 4)
+    (f : Y («E» := E) α T ℝ) :
+    ‖forcing b (S f)‖ ≤ (1 / 2) * ‖f‖ := by
+  apply (norm_error_le b S hα hT hb hbα hS f).trans
+  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
+  nlinarith only [hε, hΛ]
+
+end Poincare.ParabolicHolderMultiplier
## worker/parabolic-holder-multiplier-estimate
leanprover/lean4:v4.30.0-rc2
exit_code=0
```

### 2026-09-15T10:03:05.055511

```sh
LEAN_NUM_THREADS=1 lake env lean /private/tmp/PHMStatements.lean
```

```text
Poincare.ParabolicHolderMultiplier.du_zero_trace {α T : ℝ} (G : Poincare.ParabolicSolutionGraph.Graph α T) (hT : 0 < T)
  (x : Poincare.ClosedSmoothModel 3) : ↑(WithLp.fst ↑G.du) (0, x) = 0
Poincare.ParabolicHolderMultiplier.ddu_zero_trace {α T : ℝ} (G : Poincare.ParabolicSolutionGraph.Graph α T) (hT : 0 < T)
  (x : Poincare.ClosedSmoothModel 3) : ↑(WithLp.fst ↑G.ddu) (0, x) = 0
Poincare.ParabolicHolderMultiplier.ddu_time_bound {α T : ℝ} (G : Poincare.ParabolicSolutionGraph.Graph α T) (hT : 0 < T)
  {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : Poincare.ClosedSmoothModel 3) :
  ‖↑(WithLp.fst ↑G.ddu) (t, x)‖ ≤ ‖G.ddu‖ * t ^ (α / 2)
Poincare.ParabolicHolderMultiplier.supNorm_ddu_le {α T : ℝ} (G : Poincare.ParabolicSolutionGraph.Graph α T) (hα : 0 < α)
  (hT : 0 < T) :
  Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑G.ddu) ≤ T ^ (α / 2) * ‖G‖
Poincare.ParabolicHolderMultiplier.eval_norm_le
  (A : Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ) {v w : Poincare.ClosedSmoothModel 3}
  (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖(A v) w‖ ≤ ‖A‖
Poincare.ParabolicHolderMultiplier.entry_holderBound {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  {v w : Poincare.ClosedSmoothModel 3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
  Poincare.ParabolicHolder.HasHolderBound α (Poincare.ParabolicHolder.cylinder T) (fun p => ((↑(WithLp.fst ↑H) p) v) w)
    (Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑H))
Poincare.ParabolicHolderMultiplier.entry {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : Poincare.ParabolicHolder.Y α T ℝ
Poincare.ParabolicHolderMultiplier.entry_apply {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (p : ℝ × Poincare.ClosedSmoothModel 3) :
  ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.entry H v w hv hw)) p = ((↑(WithLp.fst ↑H) p) v) w
Poincare.ParabolicHolderMultiplier.supNorm_entry_le {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
  Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T)
      ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.entry H v w hv hw)) ≤
    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑H)
Poincare.ParabolicHolderMultiplier.norm_entry_le {α T : ℝ}
  (H : Poincare.ParabolicHolder.Y α T (Poincare.ClosedSmoothModel 3 →L[ℝ] Poincare.ClosedSmoothModel 3 →L[ℝ] ℝ))
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
  ‖Poincare.ParabolicHolderMultiplier.entry H v w hv hw‖ ≤ ‖H‖
Poincare.ParabolicHolderMultiplier.norm_mul_split {α T : ℝ} (b h : Poincare.ParabolicHolder.Y α T ℝ) :
  ‖b * h‖ ≤
    Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑b) * ‖h‖ +
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑b) *
        Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑h)
Poincare.ParabolicHolderMultiplier.sum_apply.{u_1} {α T : ℝ} {ι : Type u_1} (s : Finset ι)
  (f : ι → Poincare.ParabolicHolder.Y α T ℝ) (p : ℝ × Poincare.ClosedSmoothModel 3) :
  ↑(WithLp.fst ↑(∑ i ∈ s, f i)) p = ∑ i ∈ s, ↑(WithLp.fst ↑(f i)) p
Poincare.ParabolicHolderMultiplier.forcing {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) : Poincare.ParabolicHolder.Y α T ℝ
Poincare.ParabolicHolderMultiplier.forcing_apply {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) (p : ℝ × Poincare.ClosedSmoothModel 3) :
  ↑(WithLp.fst ↑(Poincare.ParabolicHolderMultiplier.forcing b G)) p =
    ∑ i,
      ∑ j,
        ↑(WithLp.fst ↑(b i j)) p *
          ((↑(WithLp.fst ↑G.ddu) p) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)
Poincare.ParabolicHolderMultiplier.forcing_eq_sum {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) :
  Poincare.ParabolicHolderMultiplier.forcing b G =
    ∑ i,
      ∑ j,
        b i j *
          Poincare.ParabolicHolderMultiplier.entry G.ddu ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
            ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ⋯ ⋯
Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le {α T : ℝ} (b : Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
  (hb : Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑b) ≤ ε)
  (hbα : Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑b) ≤ Λ)
  (v w : Poincare.ClosedSmoothModel 3) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
  ‖b * Poincare.ParabolicHolderMultiplier.entry G.ddu v w hv hw‖ ≤ ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖
Poincare.ParabolicHolderMultiplier.norm_forcing_le {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (G : Poincare.ParabolicSolutionGraph.Graph α T) (hα : 0 < α) (hT : 0 < T) {ε Λ : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ) :
  ‖Poincare.ParabolicHolderMultiplier.forcing b G‖ ≤ 9 * (ε * ‖G‖ + Λ * T ^ (α / 2) * ‖G‖)
Poincare.ParabolicHolderMultiplier.norm_error_le {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (S : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T) (hα : 0 < α) (hT : 0 < T)
  {ε Λ C_S : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ)
  (hS : ‖S‖ ≤ C_S) (f : Poincare.ParabolicHolder.Y α T ℝ) :
  ‖Poincare.ParabolicHolderMultiplier.forcing b (S f)‖ ≤ 9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖
Poincare.ParabolicHolderMultiplier.error_small {α T : ℝ} (b : Fin 3 → Fin 3 → Poincare.ParabolicHolder.Y α T ℝ)
  (S : Poincare.ParabolicHolder.Y α T ℝ →L[ℝ] Poincare.ParabolicSolutionGraph.Graph α T) (hα : 0 < α) (hT : 0 < T)
  {ε Λ C_S : ℝ}
  (hb :
    ∀ (i j : Fin 3), Poincare.ParabolicHolder.supNorm (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ ε)
  (hbα :
    ∀ (i j : Fin 3),
      Poincare.ParabolicHolder.holderSeminorm α (Poincare.ParabolicHolder.cylinder T) ↑(WithLp.fst ↑(b i j)) ≤ Λ)
  (hS : ‖S‖ ≤ C_S) (hε : 9 * C_S * ε ≤ 1 / 4) (hΛ : 9 * C_S * Λ * T ^ (α / 2) ≤ 1 / 4)
  (f : Poincare.ParabolicHolder.Y α T ℝ) : ‖Poincare.ParabolicHolderMultiplier.forcing b (S f)‖ ≤ 1 / 2 * ‖f‖
exit_code=0
```

### 2026-09-15T10:03:13.349567

```sh
git diff --check 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df HEAD; git diff --name-status 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df HEAD; git rev-parse HEAD
```

```text
A	Poincare/Global/ParabolicHolderMultiplier.lean
430f5bfb5d2b042356f9ae7bc703bafda1a3fc2a
exit_code=0
```

### 2026-09-15T10:04:21.210117

```sh
git diff --check; git status --short --branch; git diff --stat 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df
```

```text
## worker/parabolic-holder-multiplier-estimate
 M HANDOFF.md
?? harness/reports/parabolic-holder-multiplier-estimate_done.md
 HANDOFF.md                                     |  20 ++
 Poincare/Global/ParabolicHolderMultiplier.lean | 258 +++++++++++++++++++++++++
 2 files changed, 278 insertions(+)
exit_code=0
```

### 2026-09-15T10:04:33.916339

```sh
git diff --exit-code 2ca30baa6d45ba41d0c5fa3b95bd06f2cf3387df -- harness/tasks/parabolic-holder-multiplier-estimate.md Poincare.lean; git diff -- HANDOFF.md
```

```text
diff --git a/HANDOFF.md b/HANDOFF.md
index d866f3b0..04b8987d 100644
--- a/HANDOFF.md
+++ b/HANDOFF.md
@@ -3,6 +3,26 @@
 Snapshot date: 2026-09-08 (UTC)


+## 2026-09-15 Worker parabolic Hölder multiplier estimate proved
+
+Branch `worker/parabolic-holder-multiplier-estimate`, base `2ca30baa`, proof
+head `430f5bfb`. The single new `Global/ParabolicHolderMultiplier.lean`
+proves all four task items in separate commits: zero-trace Hessian
+interpolation, bounded coordinate entries and the split product norm bound,
+the nine-entry multiplier estimate, and elementwise one-half error smallness
+after a supplied bounded solution map. The forcing is built with `ofFunction`
+and agrees with the requested coefficient-Hessian sum.
+
+Focused compilation, the empty forbidden-token scan, and whitespace checks
+pass. All 46 explicit and generated declarations have exactly
+`[propext, Classical.choice, Quot.sound]`. Full probe output, failed
+diagnostics, statement checks, and the proof diff are preserved in
+`harness/reports/parabolic-holder-multiplier-estimate_done.md`.
+This worker result awaits independent review and is not merged or accepted.
+The continuous-linear-map packaging of the error remains separately scoped.
+
+First action: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicHolderMultiplier.lean`.
+
 ## 2026-09-11 Worker Duhamel parabolic Hölder bound proved

 Branch `worker/duhamel-parabolic-holder-seminorm`, base `ae66c744`, proof head
exit_code=0
```

### 2026-09-15T10:04:43.074191

```sh
git add HANDOFF.md harness/reports/parabolic-holder-multiplier-estimate_done.md && git diff --cached --check && git diff --cached --stat
```

```text
harness/reports/parabolic-holder-multiplier-estimate_done.md:2660: trailing whitespace.
+
harness/reports/parabolic-holder-multiplier-estimate_done.md:2661: trailing whitespace.
+
harness/reports/parabolic-holder-multiplier-estimate_done.md:2683: trailing whitespace.
+
exit_code=2
```

### 2026-09-15T10:04:58.858584

```sh
git add HANDOFF.md harness/reports/parabolic-holder-multiplier-estimate_done.md && git diff --cached --check && git diff --cached --stat
```

```text
harness/reports/parabolic-holder-multiplier-estimate_done.md:2696: trailing whitespace.
++
harness/reports/parabolic-holder-multiplier-estimate_done.md:2698: trailing whitespace.
++
harness/reports/parabolic-holder-multiplier-estimate_done.md:2700: trailing whitespace.
++
exit_code=2
```

### 2026-09-15T10:05:08.997077

```sh
git add HANDOFF.md harness/reports/parabolic-holder-multiplier-estimate_done.md && git diff --cached --check && git diff --cached --stat
```

```text
 HANDOFF.md                                         |   20 +
 .../parabolic-holder-multiplier-estimate_done.md   | 2718 ++++++++++++++++++++
 2 files changed, 2738 insertions(+)
exit_code=0
```
