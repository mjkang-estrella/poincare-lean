# Finite-atlas parabolic tensor space: done

Date: 2026-09-15. Branch: `worker/finite-atlas-parabolic-tensor-space`.
Base: `e65eaa7b4777910a508b0f037d2af8b509ca95d5`. Verified proof commit: `143cb944b7dccf64606dd1955fd8b0a8f40caeff`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

## Result

The three frozen targets are proved in `Poincare.FiniteAtlasParabolicTensorSpace`:

- `carrierClosed A ev : carrierClosedGoal A ev`.
- `carrierComplete A α T : carrierCompleteGoal A α T`.
- `carrierFields A ev : carrierFieldsGoal A ev`.

Support, symmetry, and the weighted overlap law are intersections of continuous
linear kernels. Their intersection is closed. The complete-space instance
`instCompleteSpaceTensor` uses `IsClosed.isComplete.completeSpace_coe` on the
finite product. `Y_M` and `X_M` inherit the existing submodule norm, additive
group, and real normed-space instances. The imported probe checks each instance
and checks that the subtype norm is definitionally the ambient norm.

`fieldsEquiv` preserves the entries in both directions. The module exposes
membership characterizations for all three constraints and their intersection,
entry bounds by the carrier norm, the expanded weighted transition equation,
and the support vanishing consequence. `isCompact_coordSupport` derives
compactness from the supplied compact coordinate closure and subordinate
partition, without adding Hausdorff or compact-manifold premises.

The frozen carrier definitions were copied from Appendix A. Local notations
`E`, `I`, and `e` are expanded in the final source to avoid emitted parser
helpers with an empty dependency set under the strict all-declaration gate.
The namespace is the requested namespace; one explanatory comment is omitted.
A textual comparison after precisely those substitutions passes. No field,
condition, overlap weight, Jacobian, target, or analytic premise changed.

This completes the worker gate, pending independent orchestrator review.
Reconstruction as a geometric tensor field and chart-transport estimates remain
subsequent tasks, as specified in the survey. No root import or existing Lean
file was changed. The assigned worker branch was retained. The existing
`HANDOFF.md` was updated under the repository handoff instruction; frozen task
and contract files were not edited.

## Acceptance evidence

| Check | Actual result |
| --- | --- |
| Full Appendix A replay at this base | Exit 0, empty output |
| Exact focused source gate | Exit 0, empty output |
| Imported three-target assignments and six instance checks | Exit 0 |
| Full emitted-module dependency audit | Exit 0; 120 declarations, zero failures |
| Forbidden-token grep | Exit 1, empty output, meaning no matches |
| `git diff --check` | Exit 0, empty output |
| Frozen-definition comparison after notation expansion | PASS |

The full module audit enumerates declarations by their imported module index,
including generated declarations, and runs `#print axioms` on every one. It
rejects anything other than exactly `[propext, Classical.choice, Quot.sound]`.
The complete actual output is preserved below.

Initial git status was clean at the base above. The worktree inventory and
commit were checked before relying on prose. README, HANDOFF's top section,
PROJECT_MAP, the task, survey sections 1, 2.5–2.6, 5 and Appendix A, Harness v2,
and the nearest imported carrier/chart definitions were read. No full build or
root integration audit was launched from this worker.

## Probe history

Each Lean probe below has its exact source, actual output, and captured exit
status. The initial full Appendix A invocation also emitted no output; the
recorded `appendix_replay` reruns it with an explicit exit-status capture.

- `carriers_01` proved the core carriers immediately.
- `carriers_02` exposed the distinction between an extended chart's
  `PartialEquiv` type and `OpenPartialHomeomorph`; the support proof now uses
  the landed `continuousOn_extChartAt` and `continuousOn_extChartAt_symm`.
- `carriers_03` needed an explicit definitional `change` before rewriting the
  chart image. `module_audit_01` ran before an emitted module existed and failed
  on that missing import; it is not evidence about the declarations.
- `carriers_04` passed. `module_audit_02` detected 16 emitted helpers whose
  dependency sets were proper subsets of the required set. All mathematical
  declarations already had the required set. Expanding the notation and using
  direct membership proofs removed those helpers without adding dependencies.
- `targets_01` needed `noncomputable section` for its instance-valued examples;
  the target assignments themselves elaborated. `targets_02` passes.
- `carriers_05`, `module_audit_03`, and `final_gate` pass on the final proof.

First reviewer action:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
```

## Definition comparison

```text
PASS: all frozen carrier definitions match the Appendix A prefix after expanding local notation, changing the namespace, and removing one comment.
```

## Commands and full outputs

<details>
<summary>appendix_replay</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/ReportProbe.lean
exit_code=0
```

Actual output:

```text
(empty)
```

Source SHA-256: `8448bfb0730f90741d7dea39a5b1988b7726b26041aec95849a6b11d5d980888`.

```lean
import Poincare.Global.NearIdentityParabolicRightInverse
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
import Poincare.Global.DeTurckPrincipalIdentity
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace FiniteAtlasSurvey
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

-- Statement definitions, not proofs of closedness, completeness or equivalence.
def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

-- Positive-time candidate strengthened norm functional; no norm instance claimed.
def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
  T ^ (-(1 - α / 2)) * ‖G.u‖ +
  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖

def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖

-- Coefficients are the resulting commutator coefficients, already zero-extended.
def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p

def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
  ∃ K : Jet α T →L[ℝ] Scalar α T,
    (∀ G p, K G p = firstOrderValue b c G p) ∧
    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)

structure CutoffData (α T : ℝ) where
  psi : E → ℝ
  smooth : ContDiff ℝ ∞ psi
  compact : HasCompactSupport psi
  a : Fin 3 → Fin 3 → Scalar α T
  drift : Fin 3 → Scalar α T
  b : Fin 3 → Scalar α T
  c : Scalar α T
  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
    b k (t,x) = -(∑ j : Fin 3,
      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)

def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
    ∀ G p, (C G).u p = D.psi p.2 * G.u p

structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
  S : Scalar α T →L[ℝ] Jet α T
  bound : ‖S‖ ≤ C_S
  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)

def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
  0 < α → 0 < T →
  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖

-- Actual chart coefficient agreement is separate from the frozen analytic data.
structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
  cutoff : E → ℝ
  smooth : ContDiff ℝ ∞ cutoff
  compact : HasCompactSupport cutoff
  one_on : ∀ z ∈ U, cutoff z = 1
  b : Fin 3 → Fin 3 → Scalar α T
  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))

def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
    (N : X_M A α T → Y_M A α T) : Prop :=
  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
    (G : Jet α T) (p : ℝ × E) : ℝ :=
  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
    a i j p * G.ddu p (e i) (e j)) -
    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p

def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
    (potential : Scalar α T) : Prop :=
  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
    (∀ G t, t ∈ Icc 0 T → ∀ x,
      localLinearValue D.a D.drift potential (C G) (t,x) -
        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
          firstOrderValue D.b D.c G (t,x))

def oscillationExtensionGoal : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
    ∃ b : Fin 3 → Fin 3 → Scalar α T,
      (∀ t ∈ Icc 0 T, ∀ x i j,
        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)

def frozenCLMGoal : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)

abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)

def localizedValue {T : ℝ} (F : TensorField (M := M) T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
  classical
  exact if ht : p.1 ∈ Icc 0 T then
    if p.2 ∈ (chart A i).target then
      let x := (chart A i).symm p.2
      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
    else 0
  else 0

def reconstructionGoal (α T : ℝ) : Prop :=
  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p

abbrev Jet1 := E →L[ℝ] Bilin
abbrev Jet2 := E →L[ℝ] Jet1

def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
  (∑ i : Fin 3, ∑ j : Fin 3,
    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
    DeTurckPrincipalIdentity.lowerTerm B DB G J

set_option synthInstance.maxHeartbeats 400000 in
def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (z h : Bilin × Jet1 × Jet2) : Bilin :=
  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
    (∑ i : Fin 3, ∑ j : Fin 3,
      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
end FiniteAtlasSurvey
```

</details>

<details>
<summary>carriers_01</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
exit_code=0
```

Actual output:

```text
(empty)
```

Source SHA-256: `a46c4b65a1450d90b2753235397c7a18b1ff9131fb71204db54464c2d2c167db`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × E → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, sub_eq_zero]

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  simp only [tensorSubmodule, Submodule.mem_inf, mem_supportSubmodule_iff,
    mem_symmetrySubmodule_iff, mem_overlapSubmodule_iff]

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>carriers_02</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
exit_code=1
```

Actual output:

```text
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:195:28: warning: This simp argument is unused:
  ContinuousLinearMap.sum_apply

Hint: Omit it from the simp argument list.
  simp [overlap, evalLocal,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵u̵m̵_̵a̵p̵p̵l̵y̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:228:19: error(lean.invalidField): Invalid field `continuousOn_symm`: The environment does not contain `PartialEquiv.continuousOn_symm`, so it is not possible to project the field `continuousOn_symm` from an expression
  chart A i
of type `PartialEquiv M E`
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.unknownIdentifier): Unknown constant `LE.le.image_of_continuousOn`

Note: Inferred this name from the expected resulting type of `.image_of_continuousOn`:
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.unknownIdentifier): Unknown constant `Membership.mem.image_of_continuousOn`

Note: Inferred this name from the expected resulting type of `.image_of_continuousOn`:
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.unknownIdentifier): Unknown constant `Membership.mem.image_of_continuousOn`

Note: Inferred this name from the expected resulting type of `.image_of_continuousOn`:
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.unknownIdentifier): Unknown constant `Set.Mem.image_of_continuousOn`

Note: Inferred this name from the expected resulting type of `.image_of_continuousOn`:
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.unknownIdentifier): Unknown constant `Filter.sets.image_of_continuousOn`

Note: Inferred this name from the expected resulting type of `.image_of_continuousOn`:
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:231:4: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.image_of_continuousOn`
  ?m.145 ≤ Filter.principal (tsupport ⇑(A.partition i))
is not of the form `C ...` or `... → C ...` where C is a constant
```

Source SHA-256: `087bcaca7395d7209f84b7b4a045ff433e9888da06ab541fd29466b16192fb01`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × E → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, sub_eq_zero]

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  simp only [tensorSubmodule, Submodule.mem_inf, mem_supportSubmodule_iff,
    mem_symmetrySubmodule_iff, mem_overlapSubmodule_iff]

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal, ContinuousLinearMap.sum_apply]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : E)
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((chart A i).continuousOn_symm.mono ht)
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  exact (hc.of_isClosed_subset (isClosed_tsupport _) ((A.subordinate i).trans subset_closure))
    .image_of_continuousOn ((chart A i).continuousOn.mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>carriers_03</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean -o .lake/build/lib/lean/Poincare/Global/FiniteAtlasParabolicTensorSpace.olean
exit_code=1
```

Actual output:

```text
Poincare/Global/FiniteAtlasParabolicTensorSpace.lean:229:9: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑(chart A i).symm '' ↑(chart A i) '' closure (A.region i)
in the target expression
  IsCompact (↑(extChartAt I (A.cover.anchor i)).symm '' ↑(extChartAt I (A.cover.anchor i)) '' closure (A.region i))

M : Type u
inst✝² : TopologicalSpace M
inst✝¹ : ChartedSpace E M
inst✝ : IsManifold I ∞ M
A : AtlasData M
i : Fin A.cover.chartCount
ht : ↑(chart A i) '' closure (A.region i) ⊆ (chart A i).target
h : IsCompact (↑(extChartAt I (A.cover.anchor i)).symm '' ↑(extChartAt I (A.cover.anchor i)) '' closure (A.region i))
⊢ IsCompact (closure (A.region i))
```

Source SHA-256: `58b46eeb9c1876a7de9f84dd411a2190094909c635be6825745f646575a17dfe`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × E → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, sub_eq_zero]

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  simp only [tensorSubmodule, Submodule.mem_inf, mem_supportSubmodule_iff,
    mem_symmetrySubmodule_iff, mem_overlapSubmodule_iff]

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : E)
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>module_audit_01</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/ModuleAudit.lean
exit_code=1
```

Actual output:

```text
/tmp/finite-atlas-parabolic-tensor-space/ModuleAudit.lean:1:0: error: object file '/private/tmp/poincare-workers/finite-atlas-parabolic-tensor-space/.lake/build/lib/lean/Poincare/Global/FiniteAtlasParabolicTensorSpace.olean' of module Poincare.Global.FiniteAtlasParabolicTensorSpace does not exist
```

Source SHA-256: `0a3ffcbafde71e0fa8685c03a1354ad72bf67960fffc0119378b08388e2eb2f7`.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.FiniteAtlasParabolicTensorSpace
    | throwError "module not found"
  let mut count := 0
  let mut failed := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        failed := failed + 1
        logInfo m!"Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; failures={failed}"
  unless failed == 0 do throwError "Dependency audit failed"
```

</details>

<details>
<summary>carriers_04</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean -o .lake/build/lib/lean/Poincare/Global/FiniteAtlasParabolicTensorSpace.olean
exit_code=0
```

Actual output:

```text
(empty)
```

Source SHA-256: `a6287e869debc1dcff25e5ce186721934c71d3adb6fc0068ad12fd4e9b109525`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold I ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set E :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : E) : E :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) (e a)) c

def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : E // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × E → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, sub_eq_zero]

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, Subtype.forall]

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  simp only [tensorSubmodule, Submodule.mem_inf, mem_supportSubmodule_iff,
    mem_symmetrySubmodule_iff, mem_overlapSubmodule_iff]

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : E)
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>module_audit_02</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/ModuleAudit.lean
exit_code=1
```

Actual output:

```text
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_3' depends on axioms: [propext, Quot.sound]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_3: [propext,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_9' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termI' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termI: []
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_3' depends on axioms: [propext, Quot.sound]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_3: [propext,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termI_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termI_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.recOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.symmetrySubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_supportSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isCompact_coordSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supportSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.ctorIdx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.partition_support_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_4' depends on axioms: [propext]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_4: [propext]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_3' depends on axioms: [propext, Quot.sound]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_3: [propext,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.change' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.closure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termE_1_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termE_1_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_EuclideanSpace_basisFun_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_EuclideanSpace_basisFun_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.rec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff._simp_1_2' depends on axioms: [propext, Quot.sound]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff._simp_1_2: [propext,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_4' depends on axioms: [propext]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_4: [propext]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierClosedGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlapSubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_Poincare_closedSmoothModelWithCorners_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_Poincare_closedSmoothModelWithCorners_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.coordinate_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_symmetrySubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.X_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.symmetrySubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.LocalProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierFields' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termE_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termE_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff._simp_1_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff._simp_1_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.jac' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supportSubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_Poincare_ClosedSmoothModel_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___unexpand_Poincare_ClosedSmoothModel_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Index' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.coordSupport_subset_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierFieldsGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termE_1' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace._aux_Poincare_Global_FiniteAtlasParabolicTensorSpace___macroRules__private_Poincare_Global_FiniteAtlasParabolicTensorSpace_0_Poincare_FiniteAtlasParabolicTensorSpace_termE_1: []
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.weighted_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_overlapSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_4' depends on axioms: [propext]
Unexpected foundational dependencies for Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_4: [propext]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlapSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.coordSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.tensorSubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.casesOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.subordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Y_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supported_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.tensorSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Y_M._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termE' does not depend on any axioms
Unexpected foundational dependencies for _private.Poincare.Global.FiniteAtlasParabolicTensorSpace.0.Poincare.FiniteAtlasParabolicTensorSpace.termE: []
'Poincare.FiniteAtlasParabolicTensorSpace.instCompleteSpaceTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff._simp_1_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=140; failures=16
/tmp/finite-atlas-parabolic-tensor-space/ModuleAudit.lean:3:0: error: Dependency audit failed
```

Source SHA-256: `0a3ffcbafde71e0fa8685c03a1354ad72bf67960fffc0119378b08388e2eb2f7`.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.FiniteAtlasParabolicTensorSpace
    | throwError "module not found"
  let mut count := 0
  let mut failed := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        failed := failed + 1
        logInfo m!"Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; failures={failed}"
  unless failed == 0 do throwError "Dependency audit failed"
```

</details>

<details>
<summary>targets_01</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/Targets.lean
exit_code=1
```

Actual output:

```text
/tmp/finite-atlas-parabolic-tensor-space/Targets.lean:13:0: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'WithLp.instProdNormedAddCommGroup', which is 'noncomputable'
/tmp/finite-atlas-parabolic-tensor-space/Targets.lean:14:0: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Real.normedField', which is 'noncomputable'
/tmp/finite-atlas-parabolic-tensor-space/Targets.lean:16:0: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'ParabolicSolutionGraph.instNormedAddCommGroup', which is 'noncomputable'
/tmp/finite-atlas-parabolic-tensor-space/Targets.lean:17:0: error(lean.dependsOnNoncomputable): failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Real.normedField', which is 'noncomputable'
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed.{u, u_1} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) {H : Type u_1} [inst_3 : NormedAddCommGroup H] [inst_4 : NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ), carrierClosedGoal A ev :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    {H} [NormedAddCommGroup H] [NormedSpace ℝ H] ev =>
  IsClosed.inter (IsClosed.inter (isClosed_supportSubmodule A ev) (isClosed_symmetrySubmodule A ev))
    (isClosed_overlapSubmodule A ev)
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete.{u} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) (α T : ℝ), carrierCompleteGoal A α T :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    α T =>
  ⟨inferInstance, inferInstance⟩
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierFields.{u, u_1} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) {H : Type u_1} [inst_3 : NormedAddCommGroup H] [inst_4 : NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ), carrierFieldsGoal A ev :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    {H} [NormedAddCommGroup H] [NormedSpace ℝ H] ev =>
  Nonempty.intro (fieldsEquiv A ev)
```

Source SHA-256: `6c6ba02e45bc0fe51460039788fd8d662d419bba22a7abaa1fe4af5ff649ad46`.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Poincare Poincare.FiniteAtlasParabolicTensorSpace
open scoped Manifold ContDiff
set_option autoImplicit false
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable (A : AtlasData M) {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ) (α T : ℝ)
example : carrierClosedGoal A ev := carrierClosed A ev
example : carrierCompleteGoal A α T := carrierComplete A α T
example : carrierFieldsGoal A ev := carrierFields A ev
example : NormedAddCommGroup (Y_M A α T) := inferInstance
example : NormedSpace ℝ (Y_M A α T) := inferInstance
example : CompleteSpace (Y_M A α T) := inferInstance
example : NormedAddCommGroup (X_M A α T) := inferInstance
example : NormedSpace ℝ (X_M A α T) := inferInstance
example : CompleteSpace (X_M A α T) := inferInstance
example (f : Y_M A α T) : ‖f‖ = ‖f.val‖ := rfl
example (f : X_M A α T) : ‖f‖ = ‖f.val‖ := rfl
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierFields
```

</details>

<details>
<summary>carriers_05</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean -o .lake/build/lib/lean/Poincare/Global/FiniteAtlasParabolicTensorSpace.olean
exit_code=0
```

Actual output:

```text
(empty)
```

Source SHA-256: `e4f053471b00cf19ab27a8154e5127649dccbf45ccd6a52291d0eb559648eab5`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) (closedSmoothModelWithCorners 3) M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) ((EuclideanSpace.basisFun (Fin 3) ℝ) a)) c

def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : (ClosedSmoothModel 3) // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × (ClosedSmoothModel 3)),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b t z hz
    exact h i a b t ⟨z, hz⟩
  · intro h i a b t z
    exact h i a b t z.val z.property

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b p
    exact sub_eq_zero.mp (h i a b p)
  · intro h i a b p
    exact sub_eq_zero.mpr (h i a b p)

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i j a b t x hx
    exact h i j a b t ⟨x, hx⟩
  · intro h i j a b t x
    exact h i j a b t x.val x.property

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  exact and_congr
    (and_congr (mem_supportSubmodule_iff A ev f) (mem_symmetrySubmodule_iff A ev f))
    (mem_overlapSubmodule_iff A ev f)

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : (ClosedSmoothModel 3))
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>module_audit_03</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/ModuleAudit.lean
exit_code=0
```

Actual output:

```text
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_9' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.recOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.symmetrySubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_supportSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isCompact_coordSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supportSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.noConfusionType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.ctorIdx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.partition_support_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.change' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.closure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.rec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierClosedGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlapSubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.coordinate_compact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_symmetrySubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.X_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.symmetrySubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_overlapSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.LocalProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk._flat_ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierFields' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.jac' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supportSubmodule.eq_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.entries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.sizeOf_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Index' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.rec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.region_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.casesOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.coordSupport_subset_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_tensorSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierFieldsGoal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.recOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal._proof_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.weighted_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.ctorIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.carrierCompleteGoal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.isClosed_overlapSubmodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_supportSubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Bilin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.overlapSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.coordSupport' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData._sizeOf_inst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_5' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.casesOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.subordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Y_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.supported_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields.mk.injEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.noConfusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.tensorSubmodule' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.AtlasData.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.mem_symmetrySubmodule_iff._simp_1_2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.CompatibleFields._sizeOf_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.Y_M._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.instCompleteSpaceTensor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.evalX._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.FiniteAtlasParabolicTensorSpace.fieldsEquiv._proof_1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
EXACT_MODULE_AUDIT declarations=120; failures=0
```

Source SHA-256: `0a3ffcbafde71e0fa8685c03a1354ad72bf67960fffc0119378b08388e2eb2f7`.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.FiniteAtlasParabolicTensorSpace
    | throwError "module not found"
  let mut count := 0
  let mut failed := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      count := count + 1
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        failed := failed + 1
        logInfo m!"Unexpected foundational dependencies for {n}: {axs}"
  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; failures={failed}"
  unless failed == 0 do throwError "Dependency audit failed"
```

</details>

<details>
<summary>targets_02</summary>

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/finite-atlas-parabolic-tensor-space/Targets.lean
exit_code=0
```

Actual output:

```text
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed.{u, u_1} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) {H : Type u_1} [inst_3 : NormedAddCommGroup H] [inst_4 : NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ), carrierClosedGoal A ev :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    {H} [NormedAddCommGroup H] [NormedSpace ℝ H] ev =>
  IsClosed.inter (IsClosed.inter (isClosed_supportSubmodule A ev) (isClosed_symmetrySubmodule A ev))
    (isClosed_overlapSubmodule A ev)
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete.{u} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) (α T : ℝ), carrierCompleteGoal A α T :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    α T =>
  ⟨inferInstance, inferInstance⟩
theorem Poincare.FiniteAtlasParabolicTensorSpace.carrierFields.{u, u_1} : ∀ {M : Type u} [inst : TopologicalSpace M]
  [inst_1 : ChartedSpace (ClosedSmoothModel 3) M] [inst_2 : IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  (A : AtlasData M) {H : Type u_1} [inst_3 : NormedAddCommGroup H] [inst_4 : NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ), carrierFieldsGoal A ev :=
fun {M} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] A
    {H} [NormedAddCommGroup H] [NormedSpace ℝ H] ev =>
  Nonempty.intro (fieldsEquiv A ev)
```

Source SHA-256: `3b5f39f87af535a2783c2e68469a32f2f02262439526efd3fd0a9040574be232`.

```lean
import Poincare.Global.FiniteAtlasParabolicTensorSpace
open Poincare Poincare.FiniteAtlasParabolicTensorSpace
open scoped Manifold ContDiff
noncomputable section
set_option autoImplicit false
universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable (A : AtlasData M) {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  (ev : ℝ × ClosedSmoothModel 3 → H →L[ℝ] ℝ) (α T : ℝ)
example : carrierClosedGoal A ev := carrierClosed A ev
example : carrierCompleteGoal A α T := carrierComplete A α T
example : carrierFieldsGoal A ev := carrierFields A ev
example : NormedAddCommGroup (Y_M A α T) := inferInstance
example : NormedSpace ℝ (Y_M A α T) := inferInstance
example : CompleteSpace (Y_M A α T) := inferInstance
example : NormedAddCommGroup (X_M A α T) := inferInstance
example : NormedSpace ℝ (X_M A α T) := inferInstance
example : CompleteSpace (X_M A α T) := inferInstance
example (f : Y_M A α T) : ‖f‖ = ‖f.val‖ := rfl
example (f : X_M A α T) : ‖f‖ = ‖f.val‖ := rfl
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierClosed
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierComplete
#print Poincare.FiniteAtlasParabolicTensorSpace.carrierFields
```

</details>

<details>
<summary>final_gate</summary>

```text
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
exit_code=0
```

Actual output:

```text
(empty)
```

Source SHA-256: `e4f053471b00cf19ab27a8154e5127649dccbf45ccd6a52291d0eb559648eab5`.

```lean
import Poincare.Global.ParabolicSolutionGraph
import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Poincare.FiniteAtlasParabolicTensorSpace
open Poincare
abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] where
  cover : FiniteExtendedChartCover (n := 3) (M := M)
  region : Fin cover.chartCount → Set M
  region_open : ∀ i, IsOpen (region i)
  region_cover : (⋃ i, region i) = univ
  closure_source : ∀ i, closure (region i) ⊆ (extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)).source
  coordinate_compact : ∀ i, IsCompact ((extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)) '' closure (region i))
  partition : SmoothPartitionOfUnity (Fin cover.chartCount) (closedSmoothModelWithCorners 3) M univ
  subordinate : partition.IsSubordinate region

variable (A : AtlasData M)
abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
abbrev LocalProduct (H : Type*) := Index A → H

def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
  chart A i '' tsupport (A.partition i)
def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
  chart A j ((chart A i).symm z)
def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
  (fderiv ℝ (change A i j) (chart A i x) ((EuclideanSpace.basisFun (Fin 3) ℝ) a)) c

def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
  ({ toFun := fun f => f p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)

def evalX (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Jet α T →L[ℝ] ℝ :=
  ({ toFun := fun G => G.u p
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def evalLocal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
    (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) : LocalProduct A H →L[ℝ] ℝ :=
  (ev p).comp (ContinuousLinearMap.proj (i, a, b))

def overlap (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)

def supportSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
    ⨅ (z : {z : (ClosedSmoothModel 3) // z ∉ coordSupport A i}),
    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap

def symmetrySubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × (ClosedSmoothModel 3)),
    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap

def overlapSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
    LinearMap.ker (overlap A ev i j a b t x).toLinearMap

def tensorSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))

structure CompatibleFields (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) where
  entries : LocalProduct A H
  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
    overlap A ev i j a b t x entries = 0

def carrierClosedGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
def carrierCompleteGoal (α T : ℝ) : Prop :=
  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
def carrierFieldsGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)

variable (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ)

theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
    f ∈ supportSubmodule A ev ↔
      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
  simp only [supportSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b t z hz
    exact h i a b t ⟨z, hz⟩
  · intro h i a b t z
    exact h i a b t z.val z.property

theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
    f ∈ symmetrySubmodule A ev ↔
      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
  simp only [symmetrySubmodule, Submodule.mem_iInf]
  constructor
  · intro h i a b p
    exact sub_eq_zero.mp (h i a b p)
  · intro h i a b p
    exact sub_eq_zero.mpr (h i a b p)

theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
    f ∈ overlapSubmodule A ev ↔
      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0 := by
  simp only [overlapSubmodule, Submodule.mem_iInf]
  constructor
  · intro h i j a b t x hx
    exact h i j a b t ⟨x, hx⟩
  · intro h i j a b t x
    exact h i j a b t x.val x.property

theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
    f ∈ tensorSubmodule A ev ↔
      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
        overlap A ev i j a b t x f = 0) := by
  exact and_congr
    (and_congr (mem_supportSubmodule_iff A ev f) (mem_symmetrySubmodule_iff A ev f))
    (mem_overlapSubmodule_iff A ev f)

theorem isClosed_supportSubmodule :
    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [supportSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun t => isClosed_iInter fun z =>
      (evalLocal A ev i a b (t, z)).isClosed_ker

theorem isClosed_symmetrySubmodule :
    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
  simp only [symmetrySubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun p =>
      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker

theorem isClosed_overlapSubmodule :
    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
  simp only [overlapSubmodule, Submodule.coe_iInf]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
      (overlap A ev i j a b t x).isClosed_ker

theorem carrierClosed : carrierClosedGoal A ev :=
  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
    (isClosed_overlapSubmodule A ev)

instance instCompleteSpaceTensor [CompleteSpace H] :
    CompleteSpace ↥(tensorSubmodule A ev) :=
  (carrierClosed A ev).isComplete.completeSpace_coe

theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
  ⟨inferInstance, inferInstance⟩

def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
  toFun f :=
    { entries := f.val
      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩

theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k

theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))

theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))

theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
    (t : ℝ) (x : M) (f : LocalProduct A H) :
    overlap A ev i j a b t x f =
      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f (j, c, d)) := by
  simp [overlap, evalLocal]

theorem supported_entry (f : ↥(tensorSubmodule A ev))
    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : (ClosedSmoothModel 3))
    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz

theorem weighted_transition (f : ↥(tensorSubmodule A ev))
    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
        (jac A i j x c a * jac A i j x d b) *
          ev (t, chart A j x) (f.val (j, c, d)) := by
  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
  rw [overlap_apply] at h
  exact sub_eq_zero.mp h

theorem partition_support_source (i : Fin A.cover.chartCount) :
    tsupport (A.partition i) ⊆ (chart A i).source :=
  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))

theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
    coordSupport A i ⊆ (chart A i).target :=
  image_subset_iff.mpr fun _ hx => (chart A i).map_source
    (partition_support_source A i hx)

theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
    IsCompact (coordSupport A i) := by
  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
  have hc : IsCompact (closure (A.region i)) := by
    have h := (A.coordinate_compact i).image_of_continuousOn
      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
    ((A.subordinate i).trans subset_closure)
  exact hs.image_of_continuousOn
    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))

end Poincare.FiniteAtlasParabolicTensorSpace
```

</details>

<details>
<summary>declaration_grep</summary>

```text
rg -n ^(abbrev|structure|def|theorem|instance)  Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
exit_code=0
```

Actual output:

```text
10:abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
11:abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
12:abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ
18:structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
30:abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
31:abbrev LocalProduct (H : Type*) := Index A → H
33:def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
34:def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
36:def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
38:def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
41:def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
47:def evalX (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Jet α T →L[ℝ] ℝ :=
54:def evalLocal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
58:def overlap (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
64:def supportSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
69:def symmetrySubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
73:def overlapSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
78:def tensorSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
80:abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
81:abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
83:structure CompatibleFields (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) where
90:def carrierClosedGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
92:def carrierCompleteGoal (α T : ℝ) : Prop :=
94:def carrierFieldsGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
99:theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
109:theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
119:theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
130:theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
140:theorem isClosed_supportSubmodule :
147:theorem isClosed_symmetrySubmodule :
154:theorem isClosed_overlapSubmodule :
161:theorem carrierClosed : carrierClosedGoal A ev :=
165:instance instCompleteSpaceTensor [CompleteSpace H] :
169:theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
172:def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
183:theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩
185:theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
188:theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
193:theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
198:theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
207:theorem supported_entry (f : ↥(tensorSubmodule A ev))
212:theorem weighted_transition (f : ↥(tensorSubmodule A ev))
223:theorem partition_support_source (i : Fin A.cover.chartCount) :
227:theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
232:theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
```

</details>

<details>
<summary>api_grep</summary>

```text
rg -n (structure|def|abbrev|theorem|lemma|instance) (Y|Graph|FiniteExtendedChartCover|exists_shrunk_chart_cover|norm_le|sup_u_le|isClosed_ker|mem_iInf|coe_iInf|mem_ker|sub_eq_zero|and_congr|image_subset_iff|isClosed_tsupport|completeSpace_coe|norm_le_pi_norm|isClosed_iInter|image_of_continuousOn|of_isClosed_subset|symm_image_image_of_subset_source|continuousOn_extChartAt|continuousOn_extChartAt_symm)(\s|\(|\{|\[|\x27|\b) Poincare/Global/ParabolicHolderSpace.lean Poincare/Global/ParabolicSolutionGraph.lean Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean .lake/packages/mathlib/Mathlib
exit_code=0
```

Actual output:

```text
Poincare/Global/ClosedLaplacianStokesGlobalCoefficients.lean:90:theorem exists_shrunk_chart_cover
Poincare/Global/ParabolicSolutionGraph.lean:20:structure Graph (α T : ℝ) where
Poincare/Global/ParabolicSolutionGraph.lean:121:theorem sup_u_le (g : Graph (E := E) α T) (p : ℝ × E) :
Poincare/Global/ParabolicHolderSpace.lean:105:abbrev Y (α T : ℝ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
Poincare/Global/ParabolicHolderSpace.lean:129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:54:structure FiniteExtendedChartCover where
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:170:theorem coe_iInf {ι : Sort*} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean:174:theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean:800:theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} :
.lake/packages/mathlib/Mathlib/Algebra/Algebra/NonUnitalSubalgebra.lean:804:theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} {x : A} :
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subsemiring/Basic.lean:219:theorem coe_iInf {ι : Sort*} {S : ι → Subsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subsemiring/Basic.lean:223:theorem mem_iInf {ι : Sort*} {S : ι → Subsemiring R} {x : R} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Order/AddGroupWithTop.lean:242:lemma sub_eq_zero (ha : a ≠ ⊤) : b - a = 0 ↔ b = a := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subring/Basic.lean:330:theorem coe_iInf {ι : Sort*} {S : ι → Subring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Ring/Subring/Basic.lean:334:theorem mem_iInf {ι : Sort*} {S : ι → Subring R} {x : R} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/Submodule.lean:364:theorem coe_iInf {ι} (p : ι → LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/Submodule.lean:368:theorem mem_iInf {ι} (p : ι → LieSubmodule R L M) {x} : x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
.lake/packages/mathlib/Mathlib/Algebra/Lie/Submodule.lean:889:theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:510:theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
.lake/packages/mathlib/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean:630:theorem continuousOn_extChartAt_symm (x : M) :
.lake/packages/mathlib/Mathlib/Algebra/Lie/Ideal.lean:305:theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean:244:theorem coe_iInf {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Lattice.lean:252:theorem mem_iInf {ι} (p : ι → Submodule R M) {x} : x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
.lake/packages/mathlib/Mathlib/Algebra/Module/Submodule/Ker.lean:64:theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
.lake/packages/mathlib/Mathlib/Algebra/Lie/Abelian.lean:141:protected theorem mem_ker (x : L) : x ∈ LieModule.ker R L M ↔ ∀ m : M, ⁅x, m⁆ = 0 := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Subsemigroup/Basic.lean:77:theorem mem_iInf {ι : Sort*} {S : ι → Subsemigroup M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Subsemigroup/Basic.lean:81:theorem coe_iInf {ι : Sort*} {S : ι → Subsemigroup M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Lattice.lean:252:theorem mem_iInf {ι : Sort*} {S : ι → Subgroup G} {x : G} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Lattice.lean:256:theorem coe_iInf {ι : Sort*} {S : ι → Subgroup G} : (↑(⨅ i, S i) : Set G) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Subgroup/Ker.lean:232:theorem mem_ker {f : G →* M} {x : G} : x ∈ f.ker ↔ f x = 1 :=
.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:826:theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} :
.lake/packages/mathlib/Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:830:theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalStarSubalgebra R A} {x : A} :
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:120:theorem coe_iInf {ι : Sort*} (f : ι → ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : Set M) := by
.lake/packages/mathlib/Mathlib/Geometry/Convex/Cone/Basic.lean:124:lemma mem_iInf {ι : Sort*} {f : ι → ConvexCone R M} : x ∈ iInf f ↔ ∀ i, x ∈ f i :=
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Basic.lean:87:theorem mem_iInf {ι : Sort*} {S : ι → Submonoid M} {x : M} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Algebra/Group/Submonoid/Basic.lean:91:theorem coe_iInf {ι : Sort*} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Star/Subalgebra.lean:735:theorem coe_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Star/Subalgebra.lean:739:theorem mem_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} {x : A} :
.lake/packages/mathlib/Mathlib/Algebra/Field/Subfield/Basic.lean:262:theorem coe_iInf {ι : Sort*} {S : ι → Subfield K} : (↑(⨅ i, S i) : Set K) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/Algebra/Field/Subfield/Basic.lean:266:theorem mem_iInf {ι : Sort*} {S : ι → Subfield K} {x : K} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
.lake/packages/mathlib/Mathlib/Data/Set/Image.lean:399:theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
.lake/packages/mathlib/Mathlib/NumberTheory/FLT/Three.lean:586:noncomputable def Y := (exists_cube_associated S).2.1.choose
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Compact.lean:200:theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C :=
.lake/packages/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean:88:theorem norm_le (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C := by
.lake/packages/mathlib/Mathlib/GroupTheory/Congruence/Defs.lean:347:theorem coe_iInf {ι : Sort*} (f : ι → Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
.lake/packages/mathlib/Mathlib/Topology/Basic.lean:147:theorem isClosed_iInter {f : ι → Set X} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
.lake/packages/mathlib/Mathlib/NumberTheory/ClassNumber/Finite.lean:74:theorem norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
.lake/packages/mathlib/Mathlib/ModelTheory/Substructures.lean:204:theorem mem_iInf {ι : Sort*} {S : ι → L.Substructure M} {x : M} :
.lake/packages/mathlib/Mathlib/ModelTheory/Substructures.lean:208:theorem coe_iInf {ι : Sort*} {S : ι → L.Substructure M} :
.lake/packages/mathlib/Mathlib/Data/ENNReal/Basic.lean:684:theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0) : (↑(iInf f) : ℝ≥0∞) = ⨅ a, ↑(f a) :=
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/LinearMap.lean:655:theorem isClosed_ker [T1Space M₂] (f : M₁ →SL[σ₁₂] M₂) :
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/ClosedSubmodule.lean:131:lemma coe_iInf (f : ι → ClosedSubmodule R M) : ↑(⨅ i, f i) = ⨅ i, (f i : Set M) := by
.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/ClosedSubmodule.lean:137:@[simp] lemma mem_iInf {f : ι → ClosedSubmodule R M} : x ∈ ⨅ i, f i ↔ ∀ i, x ∈ f i := by
.lake/packages/mathlib/Mathlib/GroupTheory/GroupAction/SubMulAction.lean:284:theorem mem_iInf {ι : Sort*} {p : ι → SubMulAction R M} {x : M} :
.lake/packages/mathlib/Mathlib/Order/CompleteLattice/SetLike.lean:49:@[simp] lemma mem_iInf : x ∈ ⨅ i : I, f i ↔ ∀ i : I, x ∈ f i := by simp [← mem_subtype]
.lake/packages/mathlib/Mathlib/Topology/Sets/Closeds.lean:171:theorem mem_iInf {ι} {x : α} {s : ι → Closeds α} : x ∈ iInf s ↔ ∀ i, x ∈ s i := by simp [iInf]
.lake/packages/mathlib/Mathlib/Topology/Sets/Closeds.lean:174:theorem coe_iInf {ι} (s : ι → Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
.lake/packages/mathlib/Mathlib/Order/BooleanSubalgebra.lean:212:lemma coe_iInf (f : ι → BooleanSubalgebra α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by simp [iInf]
.lake/packages/mathlib/Mathlib/Order/BooleanSubalgebra.lean:221:@[simp] lemma mem_iInf {f : ι → BooleanSubalgebra α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
.lake/packages/mathlib/Mathlib/Order/Filter/Ker.lean:30:@[simp] lemma mem_ker : a ∈ f.ker ↔ ∀ s ∈ f, a ∈ s := mem_sInter
.lake/packages/mathlib/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:802:theorem coe_iInf (s : ι → AffineSubspace k P) :
.lake/packages/mathlib/Mathlib/Data/ENat/Lattice.lean:53:@[norm_cast] lemma coe_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : ℕ∞) :=
.lake/packages/mathlib/Mathlib/Data/NNReal/Defs.lean:476:theorem coe_iInf {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, ↑(s i) := by
.lake/packages/mathlib/Mathlib/Order/Filter/Finite.lean:86:theorem mem_iInf {ι} {s : ι → Filter α} {U : Set α} :
.lake/packages/mathlib/Mathlib/Order/Filter/Finite.lean:106:theorem mem_iInf' {ι} {s : ι → Filter α} {U : Set α} :
.lake/packages/mathlib/Mathlib/Data/Rel.lean:338:lemma image_subset_iff : image R s ⊆ t ↔ s ⊆ core R t := by aesop (add simp [Set.subset_def])
.lake/packages/mathlib/Mathlib/Order/UpperLower/CompleteLattice.lean:166:theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]
.lake/packages/mathlib/Mathlib/Order/UpperLower/CompleteLattice.lean:173:theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) :
.lake/packages/mathlib/Mathlib/Order/UpperLower/CompleteLattice.lean:215:theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Finsubgraph.lean:113:lemma coe_iInf {ι : Sort*} (f : ι → G.Finsubgraph) : ⨅ i, f i = (⨅ i, f i : G.Subgraph) := by
.lake/packages/mathlib/Mathlib/Data/Finset/Image.lean:367:theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
.lake/packages/mathlib/Mathlib/Order/Sublattice.lean:176:@[simp, norm_cast] lemma coe_iInf (f : ι → Sublattice α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by
.lake/packages/mathlib/Mathlib/Order/Sublattice.lean:187:@[simp] lemma mem_iInf {f : ι → Sublattice α} : a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
.lake/packages/mathlib/Mathlib/Order/CompleteLatticeIntervals.lean:249:@[simp] theorem coe_iInf : (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α) := by
.lake/packages/mathlib/Mathlib/Order/Hom/Order.lean:91:theorem coe_iInf {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) :
.lake/packages/mathlib/Mathlib/Order/Sublocale.lean:99:@[simp, norm_cast] lemma coe_iInf (f : ι → S) : (⨅ i, f i).val = ⨅ i, (f i).val := by
.lake/packages/mathlib/Mathlib/Combinatorics/Graph/Basic.lean:91:structure Graph (α β : Type*) where
.lake/packages/mathlib/Mathlib/Logic/Equiv/PartialEquiv.lean:445:theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' e '' s = s :=
.lake/packages/mathlib/Mathlib/RepresentationTheory/Intertwining.lean:141:lemma mem_ker (f : IntertwiningMap ρ σ) (v : V) :
.lake/packages/mathlib/Mathlib/Order/Interval/Basic.lean:690:theorem coe_iInf [DecidableLE α] (f : ι → Interval α) :
.lake/packages/mathlib/Mathlib/Order/Interval/Basic.lean:694:theorem coe_iInf₂ [DecidableLE α] (f : ∀ i, κ i → Interval α) :
.lake/packages/mathlib/Mathlib/Order/CompleteSublattice.lean:106:@[simp] theorem coe_iInf {ι} (f : ι → L) : (↑(iInf f) : α) = ⨅ i, (f i : α) := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:640:theorem mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Hom.lean:664:theorem isClosed_ker {V₂ : Type*} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂) :
.lake/packages/mathlib/Mathlib/Tactic/Order/Graph/Basic.lean:40:abbrev Graph := Std.HashMap Nat (Array Edge)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean:343:lemma norm_le_pi_norm' (i : ι) : ‖f i‖ ≤ ‖f‖ :=
.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:186:theorem coe_iInf {ι : Sort*} (S : ι → IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/One.lean:112:def Y' (i : E.I₁') : C := E.Y i.2
.lake/packages/mathlib/Mathlib/CategoryTheory/Sites/Hypercover/One.lean:115:lemma Y'_apply (i : E.I₁') : E.Y' i = E.Y i.2 := rfl
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubring/Basic.lean:301:theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubring/Basic.lean:305:theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubring R} {x : R} :
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Lattice.lean:88:theorem mem_iInf {ι : Sort*} {I : ι → Ideal R} {x : R} : x ∈ iInf I ↔ ∀ i, x ∈ I i :=
.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Maps.lean:733:@[simp] theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]
.lake/packages/mathlib/Mathlib/RingTheory/Congruence/Basic.lean:150:theorem coe_iInf {ι : Sort*} (f : ι → RingCon R) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:185:theorem coe_iInf {ι : Sort*} {S : ι → NonUnitalSubsemiring R} :
.lake/packages/mathlib/Mathlib/RingTheory/NonUnitalSubsemiring/Basic.lean:190:theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubsemiring R} {x : R} :
.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Lattice.lean:100:lemma mem_iInf {ι : Type*} {I : ι → TwoSidedIdeal R} {x : R} :
.lake/packages/mathlib/Mathlib/RingTheory/TwoSidedIdeal/Kernel.lean:45:lemma mem_ker {x : R} : x ∈ ker f ↔ f x = 0 := by
```

</details>

<details>
<summary>token_gate</summary>

```text
rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
exit_code=1
```

Actual output:

```text
(empty)
```

</details>

<details>
<summary>diff_check</summary>

```text
git diff --check
exit_code=0
```

Actual output:

```text
(empty)
```

</details>

<details>
<summary>proof_commit</summary>

```text
git commit -m Prove complete compatible finite-atlas parabolic tensor carriers
exit_code=0
```

Actual output:

```text
[worker/finite-atlas-parabolic-tensor-space 143cb944] Prove complete compatible finite-atlas parabolic tensor carriers
 1 file changed, 246 insertions(+)
 create mode 100644 Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
```

</details>

## Final proof diff

```diff
diff --git a/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean b/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
new file mode 100644
index 00000000..f931e5b9
--- /dev/null
+++ b/Poincare/Global/FiniteAtlasParabolicTensorSpace.lean
@@ -0,0 +1,246 @@
+import Poincare.Global.ParabolicSolutionGraph
+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
+
+set_option autoImplicit false
+noncomputable section
+open Set
+open scoped Manifold ContDiff
+namespace Poincare.FiniteAtlasParabolicTensorSpace
+open Poincare
+abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := (ClosedSmoothModel 3)) α T ℝ
+abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := (ClosedSmoothModel 3)) α T
+abbrev Bilin := (ClosedSmoothModel 3) →L[ℝ] (ClosedSmoothModel 3) →L[ℝ] ℝ
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+
+structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M] where
+  cover : FiniteExtendedChartCover (n := 3) (M := M)
+  region : Fin cover.chartCount → Set M
+  region_open : ∀ i, IsOpen (region i)
+  region_cover : (⋃ i, region i) = univ
+  closure_source : ∀ i, closure (region i) ⊆ (extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)).source
+  coordinate_compact : ∀ i, IsCompact ((extChartAt (closedSmoothModelWithCorners 3) (cover.anchor i)) '' closure (region i))
+  partition : SmoothPartitionOfUnity (Fin cover.chartCount) (closedSmoothModelWithCorners 3) M univ
+  subordinate : partition.IsSubordinate region
+
+variable (A : AtlasData M)
+abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
+abbrev LocalProduct (H : Type*) := Index A → H
+
+def chart (i : Fin A.cover.chartCount) := extChartAt (closedSmoothModelWithCorners 3) (A.cover.anchor i)
+def coordSupport (i : Fin A.cover.chartCount) : Set (ClosedSmoothModel 3) :=
+  chart A i '' tsupport (A.partition i)
+def change (i j : Fin A.cover.chartCount) (z : (ClosedSmoothModel 3)) : (ClosedSmoothModel 3) :=
+  chart A j ((chart A i).symm z)
+def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
+  (fderiv ℝ (change A i j) (chart A i x) ((EuclideanSpace.basisFun (Fin 3) ℝ) a)) c
+
+def evalY (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Scalar α T →L[ℝ] ℝ :=
+  ({ toFun := fun f => f p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
+
+def evalX (α T : ℝ) (p : ℝ × (ClosedSmoothModel 3)) : Jet α T →L[ℝ] ℝ :=
+  ({ toFun := fun G => G.u p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)
+
+variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
+def evalLocal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
+    (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) : LocalProduct A H →L[ℝ] ℝ :=
+  (ev p).comp (ContinuousLinearMap.proj (i, a, b))
+
+def overlap (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
+    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
+  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
+    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
+      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)
+
+def supportSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
+    ⨅ (z : {z : (ClosedSmoothModel 3) // z ∉ coordSupport A i}),
+    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap
+
+def symmetrySubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × (ClosedSmoothModel 3)),
+    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap
+
+def overlapSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
+    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
+    LinearMap.ker (overlap A ev i j a b t x).toLinearMap
+
+def tensorSubmodule (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
+abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
+abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
+
+structure CompatibleFields (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) where
+  entries : LocalProduct A H
+  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
+  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
+  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
+    overlap A ev i j a b t x entries = 0
+
+def carrierClosedGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
+  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
+def carrierCompleteGoal (α T : ℝ) : Prop :=
+  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
+def carrierFieldsGoal (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ) : Prop :=
+  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)
+
+variable (ev : ℝ × (ClosedSmoothModel 3) → H →L[ℝ] ℝ)
+
+theorem mem_supportSubmodule_iff (f : LocalProduct A H) :
+    f ∈ supportSubmodule A ev ↔
+      ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0 := by
+  simp only [supportSubmodule, Submodule.mem_iInf]
+  constructor
+  · intro h i a b t z hz
+    exact h i a b t ⟨z, hz⟩
+  · intro h i a b t z
+    exact h i a b t z.val z.property
+
+theorem mem_symmetrySubmodule_iff (f : LocalProduct A H) :
+    f ∈ symmetrySubmodule A ev ↔
+      ∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f := by
+  simp only [symmetrySubmodule, Submodule.mem_iInf]
+  constructor
+  · intro h i a b p
+    exact sub_eq_zero.mp (h i a b p)
+  · intro h i a b p
+    exact sub_eq_zero.mpr (h i a b p)
+
+theorem mem_overlapSubmodule_iff (f : LocalProduct A H) :
+    f ∈ overlapSubmodule A ev ↔
+      ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
+        overlap A ev i j a b t x f = 0 := by
+  simp only [overlapSubmodule, Submodule.mem_iInf]
+  constructor
+  · intro h i j a b t x hx
+    exact h i j a b t ⟨x, hx⟩
+  · intro h i j a b t x
+    exact h i j a b t x.val x.property
+
+theorem mem_tensorSubmodule_iff (f : LocalProduct A H) :
+    f ∈ tensorSubmodule A ev ↔
+      ((∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t, z) f = 0) ∧
+       (∀ i a b p, evalLocal A ev i a b p f = evalLocal A ev i b a p f)) ∧
+      (∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
+        overlap A ev i j a b t x f = 0) := by
+  exact and_congr
+    (and_congr (mem_supportSubmodule_iff A ev f) (mem_symmetrySubmodule_iff A ev f))
+    (mem_overlapSubmodule_iff A ev f)
+
+theorem isClosed_supportSubmodule :
+    IsClosed (supportSubmodule A ev : Set (LocalProduct A H)) := by
+  simp only [supportSubmodule, Submodule.coe_iInf]
+  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
+    isClosed_iInter fun t => isClosed_iInter fun z =>
+      (evalLocal A ev i a b (t, z)).isClosed_ker
+
+theorem isClosed_symmetrySubmodule :
+    IsClosed (symmetrySubmodule A ev : Set (LocalProduct A H)) := by
+  simp only [symmetrySubmodule, Submodule.coe_iInf]
+  exact isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b =>
+    isClosed_iInter fun p =>
+      (evalLocal A ev i a b p - evalLocal A ev i b a p).isClosed_ker
+
+theorem isClosed_overlapSubmodule :
+    IsClosed (overlapSubmodule A ev : Set (LocalProduct A H)) := by
+  simp only [overlapSubmodule, Submodule.coe_iInf]
+  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun a =>
+    isClosed_iInter fun b => isClosed_iInter fun t => isClosed_iInter fun x =>
+      (overlap A ev i j a b t x).isClosed_ker
+
+theorem carrierClosed : carrierClosedGoal A ev :=
+  ((isClosed_supportSubmodule A ev).inter (isClosed_symmetrySubmodule A ev)).inter
+    (isClosed_overlapSubmodule A ev)
+
+instance instCompleteSpaceTensor [CompleteSpace H] :
+    CompleteSpace ↥(tensorSubmodule A ev) :=
+  (carrierClosed A ev).isComplete.completeSpace_coe
+
+theorem carrierComplete (α T : ℝ) : carrierCompleteGoal A α T :=
+  ⟨inferInstance, inferInstance⟩
+
+def fieldsEquiv : ↥(tensorSubmodule A ev) ≃ CompatibleFields A ev where
+  toFun f :=
+    { entries := f.val
+      supported := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1
+      symmetric := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.2
+      transition := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 }
+  invFun f := ⟨f.entries, (mem_tensorSubmodule_iff A ev f.entries).mpr
+    ⟨⟨f.supported, f.symmetric⟩, f.transition⟩⟩
+  left_inv _ := rfl
+  right_inv _ := rfl
+
+theorem carrierFields : carrierFieldsGoal A ev := ⟨fieldsEquiv A ev⟩
+
+theorem norm_entry_le (f : ↥(tensorSubmodule A ev)) (k : Index A) :
+    ‖f.val k‖ ≤ ‖f‖ := norm_le_pi_norm f.val k
+
+theorem evalY_entry_le (α T : ℝ) (f : Y_M A α T)
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
+    ‖f.val (i, a, b) p‖ ≤ ‖f‖ :=
+  (ParabolicHolder.norm_le _ p).trans (norm_entry_le A (evalY α T) f (i, a, b))
+
+theorem evalX_entry_le (α T : ℝ) (f : X_M A α T)
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × (ClosedSmoothModel 3)) :
+    ‖(f.val (i, a, b)).u p‖ ≤ ‖f‖ :=
+  (ParabolicSolutionGraph.sup_u_le _ p).trans (norm_entry_le A (evalX α T) f (i, a, b))
+
+theorem overlap_apply (i j : Fin A.cover.chartCount) (a b : Fin 3)
+    (t : ℝ) (x : M) (f : LocalProduct A H) :
+    overlap A ev i j a b t x f =
+      A.partition j x * ev (t, chart A i x) (f (i, a, b)) -
+      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
+        (jac A i j x c a * jac A i j x d b) *
+          ev (t, chart A j x) (f (j, c, d)) := by
+  simp [overlap, evalLocal]
+
+theorem supported_entry (f : ↥(tensorSubmodule A ev))
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (z : (ClosedSmoothModel 3))
+    (hz : z ∉ coordSupport A i) : ev (t, z) (f.val (i, a, b)) = 0 :=
+  ((mem_tensorSubmodule_iff A ev f.val).mp f.property).1.1 i a b t z hz
+
+theorem weighted_transition (f : ↥(tensorSubmodule A ev))
+    (i j : Fin A.cover.chartCount) (a b : Fin 3) (t : ℝ) (x : M)
+    (hx : x ∈ (chart A i).source ∩ (chart A j).source) :
+    A.partition j x * ev (t, chart A i x) (f.val (i, a, b)) =
+      A.partition i x * ∑ c : Fin 3, ∑ d : Fin 3,
+        (jac A i j x c a * jac A i j x d b) *
+          ev (t, chart A j x) (f.val (j, c, d)) := by
+  have h := ((mem_tensorSubmodule_iff A ev f.val).mp f.property).2 i j a b t x hx
+  rw [overlap_apply] at h
+  exact sub_eq_zero.mp h
+
+theorem partition_support_source (i : Fin A.cover.chartCount) :
+    tsupport (A.partition i) ⊆ (chart A i).source :=
+  (A.subordinate i).trans (subset_closure.trans (A.closure_source i))
+
+theorem coordSupport_subset_target (i : Fin A.cover.chartCount) :
+    coordSupport A i ⊆ (chart A i).target :=
+  image_subset_iff.mpr fun _ hx => (chart A i).map_source
+    (partition_support_source A i hx)
+
+theorem isCompact_coordSupport (i : Fin A.cover.chartCount) :
+    IsCompact (coordSupport A i) := by
+  have ht : chart A i '' closure (A.region i) ⊆ (chart A i).target :=
+    image_subset_iff.mpr fun _ hx => (chart A i).map_source (A.closure_source i hx)
+  have hc : IsCompact (closure (A.region i)) := by
+    have h := (A.coordinate_compact i).image_of_continuousOn
+      ((continuousOn_extChartAt_symm (A.cover.anchor i)).mono ht)
+    change IsCompact ((chart A i).symm '' (chart A i '' closure (A.region i))) at h
+    rwa [(chart A i).symm_image_image_of_subset_source (A.closure_source i)] at h
+  have hs := hc.of_isClosed_subset (isClosed_tsupport _)
+    ((A.subordinate i).trans subset_closure)
+  exact hs.image_of_continuousOn
+    ((continuousOn_extChartAt (A.cover.anchor i)).mono (partition_support_source A i))
+
+end Poincare.FiniteAtlasParabolicTensorSpace
```
