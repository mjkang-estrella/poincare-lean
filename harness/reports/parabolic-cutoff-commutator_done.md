# Parabolic cutoff commutator

Date: 2026-09-15. Result: done, pending independent orchestrator review.

Base: `e65eaa7b4777910a508b0f037d2af8b509ca95d5`. Proof head: `8048970f347fc9330ca803d2d0b2fe33382fee8f`.
Branch: `worker/parabolic-cutoff-commutator`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

## Result

All four task items are proved in the one new Lean module.

| Item | Main declarations | Verified conclusion |
| --- | --- | --- |
| 1 | `quadratic_remainder`, `finite_difference_derivative` | The quadratic remainder and `2*A/η + (η/2)*B` derivative estimate for every positive step and unit direction. |
| 2 | `gradient_bound`, `gradient_time_increment`, `interpolation_bounds`, `interpolation` | Full value and gradient Hölder norms with constants `12` and powers `1-α/2`, `(1-α)/2`. The gradient sup and time-increment constants are `3`. |
| 3 | `exists_cutoff_jet_carriers`, `cutoffGraphOfCarriers`, `cutoffLinearMapOfCarriers`, `exists_cutoffGraph_bound`, `exists_cutoff_operator` | Smooth compact cutoffs produce the actual four product jets and a bounded linear graph endomorphism. |
| 4 | `cutoff_commutator_identity`, `firstOrder_time_bound`, `commutator` | The exact coefficient identity and the first-order continuous linear operator with positive time powers and constant `24`. |

The two-family estimate is

```text
‖firstOrderForcing b c G‖ ≤
  24 * ((∑ i, ‖b i‖) * T^((1-α)/2) + ‖c‖ * T^(1-α/2)) * ‖G‖.
```

`commutator` also proves the literal common-exponent operator-norm target.
Taking `24` for the interpolation constant as well gives a common constant for both estimates.
The identity retains `a j k + a k j`, exactly as in `CutoffData.b_eq`; symmetry is not assumed.
The potential term cancels. The compact cutoff carriers are constructed from smoothness and compact support,
including the derivatives, without extra analytic hypotheses.

## Verification and scope

The initial worktree was clean at the recorded base. README, HANDOFF's top section, PROJECT_MAP,
the supplied task, survey sections 1, 2.5–2.6 and 5, Appendix A, and the actual nearby definitions/imports were read.
Appendix A was extracted unchanged under `/tmp/parabolic-cutoff-commutator/AppendixA.lean` and elaborated before editing.
Its complete source and outputs are preserved below.

The final literal-target probe reproduces Appendix A and assigns proofs to all four propositions:
`interpolationGoal`, `cutoffGraphGoal D`, `commutatorGoal`, and `cutoffIdentityGoal D potential`.
It introduces no new assumptions to these goals.

The emitted-module audit includes generated declarations outside the task namespace.
All **111** declarations have exactly `[propext, Classical.choice, Quot.sound]`.
The final focused Lean gate, token scan, target assignments, symbol checks, and whitespace gate pass.
The empty `rg` scan returns exit 1, its normal no-match result.

Only `Poincare/Global/ParabolicCutoffCommutator.lean` and this requested report are tracked deliverables.
Existing Lean modules, `Poincare.lean`, frozen contracts, HANDOFF, and ledgers were not edited.
The explicit worker branch and narrow deliverable scope take precedence over the general branch-prefix and handoff-edit instructions.
No root integration build or acceptance/merge was performed. This is a worker result, not a completion claim for the Poincaré formalization.

## Proof commits

```text
8bd2658c Prove the finite-difference derivative estimate with quadratic remainder
9deed7b6 Prove square-root gradient bounds and graph increment estimates
09f6531b Prove full lower-derivative parabolic Holder interpolation
c331098c Construct the bounded cutoff product graph with all product jets
8048970f Prove the cutoff commutator identity and positive-time operator bound
```

Each proof item was committed after focused verification. Early item 1/2 checks inspected the named declarations;
the later module-wide audit found generated arithmetic helpers with only `propext`.
Replacing the two `field_simp` uses by explicit cancellation identities removed those generated helpers.
The final strict audit covers the entire emitted module.

## Resolved proof and elaboration issues

- The quadratic remainder uses a derivative-increment mean-value bound and comparison with `B*s²/2`.
- The zero time-difference case is separate. No time derivative of `Du` is assumed.
- A scale split at `sqrt T` yields the spatial Hölder estimates; mixed increments split through `(t,y)`.
- Scalar multiplication and the two rank-one mixed terms act on genuine Hölder carriers through `bilinearY`.
- Nested continuous-linear-map norms needed explicit local normed instances in the cutoff bound.
- Only the cutoff norm estimate and expanded nine-term identity use the higher local heartbeat limit.

First orchestrator action:

```sh
DEVELOPER_DIR=/Library/Developer/CommandLineTools LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean
```

## Acceptance command outputs

### FinalGate.log

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n",
  "$ rg -n \\b(sorry|admit|axiom|opaque)\\b|native_decide Poincare/Global/ParabolicCutoffCommutator.lean\n",
  "exit: 1\n",
  "\n",
  "$ git diff --check\n",
  "exit: 0\n",
  "\n",
  "$ git diff --name-only\n",
  "exit: 0\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean\n",
  "\n",
  "Final Lean source SHA-256: 3615959ec31f85634f640f9ea4e9b197eeefbf2e09d29eb4864f5b099ad9af82\n"
]
```

### Item3Commit.log

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/ParabolicCutoffCommutator.lean
exit: 1

$ git diff --check
exit: 0

$ git add Poincare/Global/ParabolicCutoffCommutator.lean
exit: 0

$ git commit -m Construct the bounded cutoff product graph with all product jets
exit: 0
[worker/parabolic-cutoff-commutator c331098c] Construct the bounded cutoff product graph with all product jets
 1 file changed, 391 insertions(+), 3 deletions(-)

```

### Item4Commit.log

```text
$ git add Poincare/Global/ParabolicCutoffCommutator.lean
exit: 0

$ git commit -m Prove the cutoff commutator identity and positive-time operator bound
exit: 0
[worker/parabolic-cutoff-commutator 8048970f] Prove the cutoff commutator identity and positive-time operator bound
 1 file changed, 154 insertions(+)

```

### FinalStatus.log

```text
$ git status --short --branch
exit: 0
## worker/parabolic-cutoff-commutator

$ git rev-parse HEAD
exit: 0
8048970f347fc9330ca803d2d0b2fe33382fee8f

$ git diff --name-only e65eaa7b4777910a508b0f037d2af8b509ca95d5 HEAD
exit: 0
Poincare/Global/ParabolicCutoffCommutator.lean

```

Compiler output and diff blocks with trailing spaces are encoded as JSON arrays of lines. Concatenating the decoded strings recovers the exact original bytes while keeping the report whitespace-clean.

## Complete Lean probe history

Every numbered probe includes its actual output and an immutable source snapshot hash. Source changes are unified diffs against the preceding numbered snapshot; unchanged snapshots are identified explicitly. Thus the first source and the ordered diffs reproduce every submitted probe. Full snapshots also remain under the temporary evidence directory. Compiler-generated recovery terms in failed diagnostics are preserved verbatim; none occur in the delivered Lean source.

The first pre-runner Appendix A check also exited 0 with empty output; numbered run 001 repeats that identical source and records the exit explicitly.

<details>
<summary>run-001</summary>

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

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/AppendixA.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-002</summary>

Source SHA-256: `2814e54a3578d6db75935623256a71cff12c046c7d5f3c88d94700302fb432bb`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-002.lean\n",
  "@@ -1,252 +1,72 @@\n",
  "-import Poincare.Global.NearIdentityParabolicRightInverse\n",
  "-import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients\n",
  "-import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover\n",
  "-import Poincare.Global.DeTurckPrincipalIdentity\n",
  "-import Poincare.Global.CompactCoefficientEllipticity\n",
  "-import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  "-import Mathlib.Topology.MetricSpace.Contracting\n",
  "+import Poincare.Global.ParabolicHolderMultiplier\n",
  "+import Poincare.Global.DuhamelSolutionOperatorBound\n",
  "+import Mathlib.Analysis.Calculus.MeanValue\n",
  " \n",
  "-set_option autoImplicit false\n",
  " noncomputable section\n",
  "-open Set\n",
  "-open scoped Manifold ContDiff\n",
  "-namespace FiniteAtlasSurvey\n",
  "-open Poincare\n",
  "-local notation \"E\" => ClosedSmoothModel 3\n",
  "-local notation \"I\" => closedSmoothModelWithCorners 3\n",
  "-local notation \"e\" => EuclideanSpace.basisFun (Fin 3) ℝ\n",
  "-abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ\n",
  "-abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T\n",
  "-abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ\n",
  " \n",
  "-universe u\n",
  "-variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]\n",
  "-  [IsManifold I ∞ M]\n",
  "+namespace Poincare.ParabolicCutoffCommutator\n",
  " \n",
  "-structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]\n",
  "-    [IsManifold I ∞ M] where\n",
  "-  cover : FiniteExtendedChartCover (n := 3) (M := M)\n",
  "-  region : Fin cover.chartCount → Set M\n",
  "-  region_open : ∀ i, IsOpen (region i)\n",
  "-  region_cover : (⋃ i, region i) = univ\n",
  "-  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source\n",
  "-  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))\n",
  "-  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ\n",
  "-  subordinate : partition.IsSubordinate region\n",
  "+open Set ParabolicHolder ParabolicSolutionGraph\n",
  " \n",
  "-variable (A : AtlasData M)\n",
  "-abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3\n",
  "-abbrev LocalProduct (H : Type*) := Index A → H\n",
  "+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n",
  " \n",
  "-def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)\n",
  "-def coordSupport (i : Fin A.cover.chartCount) : Set E :=\n",
  "-  chart A i '' tsupport (A.partition i)\n",
  "-def change (i j : Fin A.cover.chartCount) (z : E) : E :=\n",
  "-  chart A j ((chart A i).symm z)\n",
  "-def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=\n",
  "-  (fderiv ℝ (change A i j) (chart A i x) (e a)) c\n",
  "+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/\n",
  "+theorem quadratic_remainder\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)\n",
  "+    (x v : E) (hv : ‖v‖ = 1) :\n",
  "+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by\n",
  "+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=\n",
  "+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)\n",
  "+      convex_univ (mem_univ x) (mem_univ y)\n",
  "+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))\n",
  "+      (dh (x + s • v) v) s := by\n",
  "+    simpa using (hd (x + s • v)).comp_hasDerivAt s\n",
  "+      (((hasDerivAt_id s).smul_const v).const_add x)\n",
  "+  have hdr (s : ℝ) : HasDerivAt\n",
  "+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)\n",
  "+      (dh (x + s • v) v - dh x v) s := by\n",
  "+    simpa using ((hdline s).sub_const (h x)).sub\n",
  "+      ((hasDerivAt_id s).mul_const (dh x v))\n",
  "+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by\n",
  "+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1 <;> ring\n",
  "+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary\n",
  "+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)\n",
  "+    (fun s _ => (hdr s).hasDerivWithinAt)\n",
  "+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)\n",
  "+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)\n",
  "+  · exact hr\n",
  "+  · calc\n",
  "+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl\n",
  "+      _ ≤ ‖dh (x + s • v) - dh x‖ := by\n",
  "+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v\n",
  "+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)\n",
  " \n",
  "-def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=\n",
  "-  ({ toFun := fun f => f p\n",
  "-     map_add' := fun _ _ => rfl\n",
  "-     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "-    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)\n",
  "+/-- The finite-difference estimate with an arbitrary positive step. -/\n",
  "+theorem finite_difference_derivative\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)\n",
  "+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :\n",
  "+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by\n",
  "+  have hr := quadratic_remainder hd hdd hb hη.le x v hv\n",
  "+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=\n",
  "+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])\n",
  "+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by\n",
  "+    calc\n",
  "+      |η * dh x v| = |(h (x + η • v) - h x) -\n",
  "+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf\n",
  "+      _ ≤ |h (x + η • v) - h x| +\n",
  "+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _\n",
  "+      _ ≤ _ := add_le_add hu hr\n",
  "+  rw [abs_mul, abs_of_pos hη] at ht\n",
  "+  apply (le_div_iff₀ hη).2\n",
  "+  nlinarith\n",
  " \n",
  "-def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=\n",
  "-  ({ toFun := fun G => G.u p\n",
  "-     map_add' := fun _ _ => rfl\n",
  "-     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "-    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)\n",
  "-\n",
  "-variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "-def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)\n",
  "-    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "-  (ev p).comp (ContinuousLinearMap.proj (i, a, b))\n",
  "-\n",
  "-def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)\n",
  "-    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "-  A.partition j x • evalLocal A ev i a b (t, chart A i x) -\n",
  "-    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,\n",
  "-      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)\n",
  "-\n",
  "-def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),\n",
  "-    ⨅ (z : {z : E // z ∉ coordSupport A i}),\n",
  "-    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap\n",
  "-\n",
  "-def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),\n",
  "-    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap\n",
  "-\n",
  "-def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),\n",
  "-    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),\n",
  "-    LinearMap.ker (overlap A ev i j a b t x).toLinearMap\n",
  "-\n",
  "-def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev\n",
  "-abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))\n",
  "-abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))\n",
  "-\n",
  "-structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where\n",
  "-  entries : LocalProduct A H\n",
  "-  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0\n",
  "-  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries\n",
  "-  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →\n",
  "-    overlap A ev i j a b t x entries = 0\n",
  "-\n",
  "--- Statement definitions, not proofs of closedness, completeness or equivalence.\n",
  "-def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "-  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))\n",
  "-def carrierCompleteGoal (α T : ℝ) : Prop :=\n",
  "-  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)\n",
  "-def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "-  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)\n",
  "-\n",
  "--- Positive-time candidate strengthened norm functional; no norm instance claimed.\n",
  "-def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=\n",
  "-  T ^ (-(1 - α / 2)) * ‖G.u‖ +\n",
  "-  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖\n",
  "-\n",
  "-def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,\n",
  "-    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "-    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖\n",
  "-\n",
  "--- Coefficients are the resulting commutator coefficients, already zero-extended.\n",
  "-def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)\n",
  "-    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "-  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p\n",
  "-\n",
  "-def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "-  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),\n",
  "-  ∃ K : Jet α T →L[ℝ] Scalar α T,\n",
  "-    (∀ G p, K G p = firstOrderValue b c G p) ∧\n",
  "-    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)\n",
  "-\n",
  "-structure CutoffData (α T : ℝ) where\n",
  "-  psi : E → ℝ\n",
  "-  smooth : ContDiff ℝ ∞ psi\n",
  "-  compact : HasCompactSupport psi\n",
  "-  a : Fin 3 → Fin 3 → Scalar α T\n",
  "-  drift : Fin 3 → Scalar α T\n",
  "-  b : Fin 3 → Scalar α T\n",
  "-  c : Scalar α T\n",
  "-  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,\n",
  "-    b k (t,x) = -(∑ j : Fin 3,\n",
  "-      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))\n",
  "-  c_eq : ∀ t ∈ Icc 0 T, ∀ x,\n",
  "-    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,\n",
  "-      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -\n",
  "-      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)\n",
  "-\n",
  "-def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=\n",
  "-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "-    ∀ G p, (C G).u p = D.psi p.2 * G.u p\n",
  "-\n",
  "-structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where\n",
  "-  S : Scalar α T →L[ℝ] Jet α T\n",
  "-  bound : ‖S‖ ≤ C_S\n",
  "-  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,\n",
  "-    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,\n",
  "-      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)\n",
  "-\n",
  "-def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}\n",
  "-    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=\n",
  "-  0 < α → 0 < T →\n",
  "-  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →\n",
  "-  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →\n",
  "-  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤\n",
  "-    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖\n",
  "-\n",
  "--- Actual chart coefficient agreement is separate from the frozen analytic data.\n",
  "-structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where\n",
  "-  cutoff : E → ℝ\n",
  "-  smooth : ContDiff ℝ ∞ cutoff\n",
  "-  compact : HasCompactSupport cutoff\n",
  "-  one_on : ∀ z ∈ U, cutoff z = 1\n",
  "-  b : Fin 3 → Fin 3 → Scalar α T\n",
  "-  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "-    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))\n",
  "-\n",
  "-def nonlinearGoal (α T r C_NL C_ref θ : ℝ)\n",
  "-    (N : X_M A α T → Y_M A α T) : Prop :=\n",
  "-  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →\n",
  "-    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧\n",
  "-  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))\n",
  "-def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)\n",
  "-    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)\n",
  "-    (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "-  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-    a i j p * G.ddu p (e i) (e j)) -\n",
  "-    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p\n",
  "-\n",
  "-def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)\n",
  "-    (potential : Scalar α T) : Prop :=\n",
  "-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "-    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧\n",
  "-    (∀ G t, t ∈ Icc 0 T → ∀ x,\n",
  "-      localLinearValue D.a D.drift potential (C G) (t,x) -\n",
  "-        D.psi x * localLinearValue D.a D.drift potential G (t,x) =\n",
  "-          firstOrderValue D.b D.c G (t,x))\n",
  "-\n",
  "-def oscillationExtensionGoal : Prop :=\n",
  "-  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →\n",
  "-  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →\n",
  "-  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →\n",
  "-  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →\n",
  "-  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,\n",
  "-    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →\n",
  "-  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "-    ∃ b : Fin 3 → Fin 3 → Scalar α T,\n",
  "-      (∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "-        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧\n",
  "-      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧\n",
  "-      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)\n",
  "-\n",
  "-def frozenCLMGoal : Prop :=\n",
  "-  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →\n",
  "-  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →\n",
  "-  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →\n",
  "-  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)\n",
  "-\n",
  "-abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →\n",
  "-  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ\n",
  "-\n",
  "-def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=\n",
  "-  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)\n",
  "-\n",
  "-def localizedValue {T : ℝ} (F : TensorField (M := M) T)\n",
  "-    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by\n",
  "-  classical\n",
  "-  exact if ht : p.1 ∈ Icc 0 T then\n",
  "-    if p.2 ∈ (chart A i).target then\n",
  "-      let x := (chart A i).symm p.2\n",
  "-      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))\n",
  "-    else 0\n",
  "-  else 0\n",
  "-\n",
  "-def reconstructionGoal (α T : ℝ) : Prop :=\n",
  "-  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,\n",
  "-    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p\n",
  "-\n",
  "-abbrev Jet1 := E →L[ℝ] Bilin\n",
  "-abbrev Jet2 := E →L[ℝ] Jet1\n",
  "-\n",
  "-def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)\n",
  "-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "-    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=\n",
  "-  (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +\n",
  "-    DeTurckPrincipalIdentity.lowerTerm B DB G J\n",
  "-\n",
  "-set_option synthInstance.maxHeartbeats 400000 in\n",
  "-def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)\n",
  "-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "-    (z h : Bilin × Jet1 × Jet2) : Bilin :=\n",
  "-  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +\n",
  "-    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +\n",
  "-    (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))\n",
  "-end FiniteAtlasSurvey\n",
  "+end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:35:76: error: unsolved goals\n",
  "case h.e'_9\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "h : E → ℝ\n",
  "dh : E → E →L[ℝ] ℝ\n",
  "ddh : E → E →L[ℝ] E →L[ℝ] ℝ\n",
  "B η : ℝ\n",
  "hd : ∀ (x : E), HasFDerivAt h (dh x) x\n",
  "hdd : ∀ (x : E), HasFDerivAt dh (ddh x) x\n",
  "hb : ∀ (x : E), ‖ddh x‖ ≤ B\n",
  "hη : 0 ≤ η\n",
  "x v : E\n",
  "hv : ‖v‖ = 1\n",
  "hlip : ∀ (y : E), ‖dh y - dh x‖ ≤ B * ‖y - x‖\n",
  "hdline : ∀ (s : ℝ), HasDerivAt (fun s => h (x + s • v)) ((dh (x + s • v)) v) s\n",
  "hdr : ∀ (s : ℝ), HasDerivAt (fun s => h (x + s • v) - h x - s * (dh x) v) ((dh (x + s • v)) v - (dh x) v) s\n",
  "s : ℝ\n",
  "⊢ B * s = B * id s\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:69:2: error: Tactic `apply` failed: could not unify the conclusion of `(le_div_iff₀ hη).mpr`\n",
  "  ?m.371 ≤ ?m.372 / η\n",
  "with the goal\n",
  "  |(dh x) v| ≤ 2 * A / η + η / 2 * B\n",
  "\n",
  "Note: The full type of `(le_div_iff₀ hη).mpr` is\n",
  "  ?m.371 * η ≤ ?m.372 → ?m.371 ≤ ?m.372 / η\n",
  "\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "h : E → ℝ\n",
  "dh : E → E →L[ℝ] ℝ\n",
  "ddh : E → E →L[ℝ] E →L[ℝ] ℝ\n",
  "A B η : ℝ\n",
  "hd : ∀ (x : E), HasFDerivAt h (dh x) x\n",
  "hdd : ∀ (x : E), HasFDerivAt dh (ddh x) x\n",
  "ha : ∀ (x : E), |h x| ≤ A\n",
  "hb : ∀ (x : E), ‖ddh x‖ ≤ B\n",
  "hη : 0 < η\n",
  "x v : E\n",
  "hv : ‖v‖ = 1\n",
  "hr : |h (x + η • v) - h x - η * (dh x) v| ≤ B * η ^ 2 / 2\n",
  "hu : |h (x + η • v) - h x| ≤ 2 * A\n",
  "ht : η * |(dh x) v| ≤ 2 * A + B * η ^ 2 / 2\n",
  "⊢ |(dh x) v| ≤ 2 * A / η + η / 2 * B\n"
]
```

</details>

<details>
<summary>run-003</summary>

Source SHA-256: `30c3a8c56791ed7807f1404450690e883439bd8361b5cc4f6e7f90af21ffc04e`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-003.lean\n",
  "@@ -33,7 +33,7 @@\n",
  "     simpa using ((hdline s).sub_const (h x)).sub\n",
  "       ((hasDerivAt_id s).mul_const (dh x v))\n",
  "   have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by\n",
  "-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1 <;> ring\n",
  "+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1 <;> simp only [id_eq] <;> ring\n",
  "   have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary\n",
  "     (fun s _ => (hdr s).continuousAt.continuousWithinAt)\n",
  "     (fun s _ => (hdr s).hasDerivWithinAt)\n",
  "@@ -66,7 +66,11 @@\n",
  "           |h (x + η • v) - h x - η * dh x v| := abs_sub _ _\n",
  "       _ ≤ _ := add_le_add hu hr\n",
  "   rw [abs_mul, abs_of_pos hη] at ht\n",
  "-  apply (le_div_iff₀ hη).2\n",
  "+  apply (mul_le_mul_right hη).mp\n",
  "+  have he : (2 * A / η + η / 2 * B) * η = 2 * A + B * η ^ 2 / 2 := by\n",
  "+    field_simp\n",
  "+    <;> ring\n",
  "+  rw [he]\n",
  "   nlinarith\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:36:72: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:36:94: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:69:30: error(lean.invalidField): Invalid field `mp`: The environment does not contain `Function.mp`, so it is not possible to project the field `mp` from an expression\n",
  "  mul_le_mul_right ?m.373\n",
  "of type\n",
  "  ∀ (a : ?m.367), a * ?m.371 ≤ a * ?m.372\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:69:26: error: Application type mismatch: The argument\n",
  "  hη\n",
  "has type\n",
  "  0 < η\n",
  "but is expected to have type\n",
  "  ?m.371 ≤ ?m.372\n",
  "in the application\n",
  "  mul_le_mul_right hη\n"
]
```

</details>

<details>
<summary>run-004</summary>

Source SHA-256: `9f9d47b21dd7d879d798d580de9b4bf1a33f76de5ba42b53e2517f82ea39af05`.

```diff
--- preceding snapshot
+++ run-004.lean
@@ -66,7 +66,7 @@
           |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
       _ ≤ _ := add_le_add hu hr
   rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_right hη).mp
+  apply (mul_le_mul_iff_right₀ hη).mp
   have he : (2 * A / η + η / 2 * B) * η = 2 * A + B * η ^ 2 / 2 := by
     field_simp
     <;> ring
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:36:72: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:36:94: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:73:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n",
  "  (2 * A / η + η / 2 * B) * η\n",
  "in the target expression\n",
  "  η * |(dh x) v| ≤ η * (2 * A / η + η / 2 * B)\n",
  "\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "h : E → ℝ\n",
  "dh : E → E →L[ℝ] ℝ\n",
  "ddh : E → E →L[ℝ] E →L[ℝ] ℝ\n",
  "A B η : ℝ\n",
  "hd : ∀ (x : E), HasFDerivAt h (dh x) x\n",
  "hdd : ∀ (x : E), HasFDerivAt dh (ddh x) x\n",
  "ha : ∀ (x : E), |h x| ≤ A\n",
  "hb : ∀ (x : E), ‖ddh x‖ ≤ B\n",
  "hη : 0 < η\n",
  "x v : E\n",
  "hv : ‖v‖ = 1\n",
  "hr : |h (x + η • v) - h x - η * (dh x) v| ≤ B * η ^ 2 / 2\n",
  "hu : |h (x + η • v) - h x| ≤ 2 * A\n",
  "ht : η * |(dh x) v| ≤ 2 * A + B * η ^ 2 / 2\n",
  "he : (2 * A / η + η / 2 * B) * η = 2 * A + B * η ^ 2 / 2\n",
  "⊢ η * |(dh x) v| ≤ η * (2 * A / η + η / 2 * B)\n"
]
```

</details>

<details>
<summary>run-005</summary>

Source SHA-256: `ce65cc45c6282fdcee5fe9d36282e65e87070c0c2cebfe230b775734923e331b`.

```diff
--- preceding snapshot
+++ run-005.lean
@@ -33,7 +33,9 @@
     simpa using ((hdline s).sub_const (h x)).sub
       ((hasDerivAt_id s).mul_const (dh x v))
   have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1 <;> simp only [id_eq] <;> ring
+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
+    simp only [id_eq]
+    ring
   have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
     (fun s _ => (hdr s).continuousAt.continuousWithinAt)
     (fun s _ => (hdr s).hasDerivWithinAt)
@@ -67,7 +69,7 @@
       _ ≤ _ := add_le_add hu hr
   rw [abs_mul, abs_of_pos hη] at ht
   apply (mul_le_mul_iff_right₀ hη).mp
-  have he : (2 * A / η + η / 2 * B) * η = 2 * A + B * η ^ 2 / 2 := by
+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
     field_simp
     <;> ring
   rw [he]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:74:8: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:74:8: warning: 'ring' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n"
]
```

</details>

<details>
<summary>run-006</summary>

Source SHA-256: `2b5af0b2862af15b30222285b1d6ce94596c20a14c450a4ff4ad123778dfee62`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-006.lean\n",
  "@@ -76,3 +76,6 @@\n",
  "   nlinarith\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "+\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item1Audit.lean \n",
  "exit: 0\n",
  "/tmp/parabolic-cutoff-commutator/Item1Audit.lean:74:8: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "/tmp/parabolic-cutoff-commutator/Item1Audit.lean:74:8: warning: 'ring' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n"
]
```

</details>

<details>
<summary>run-007</summary>

Source SHA-256: `1baf1ed7d127b130eb0e9f597aa07dd97583669864461d19eabd5b3382e0fe37`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-007.lean\n",
  "@@ -71,11 +71,7 @@\n",
  "   apply (mul_le_mul_iff_right₀ hη).mp\n",
  "   have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by\n",
  "     field_simp\n",
  "-    <;> ring\n",
  "   rw [he]\n",
  "   nlinarith\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "-\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-008</summary>

Source SHA-256: `c630bb5769749194585d4baf6abb7ec2e7cfc4845646c870beb753151097ed39`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-008.lean\n",
  "@@ -74,4 +74,87 @@\n",
  "   rw [he]\n",
  "   nlinarith\n",
  " \n",
  "+/-- Optimizing the step gives a square-root bound on the full derivative. -/\n",
  "+theorem derivative_norm_le_sqrt\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (hδ : 0 < δ) (hM : 0 ≤ M)\n",
  "+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)\n",
  "+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by\n",
  "+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)\n",
  "+  intro v hv\n",
  "+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv\n",
  "+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =\n",
  "+      3 * Real.sqrt δ * M := by\n",
  "+    have hs := Real.sq_sqrt hδ.le\n",
  "+    have hp := Real.sqrt_pos.mpr hδ\n",
  "+    apply (div_eq_iff (ne_of_gt hp)).mp\n",
  "+    field_simp\n",
  "+    nlinarith\n",
  "+  exact h.trans_eq he\n",
  "+\n",
  "+variable {α T : ℝ}\n",
  "+\n",
  "+/-- Time increments of the value are controlled by the stored time derivative. -/\n",
  "+theorem value_time_increment (G : Graph (E := E) α T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by\n",
  "+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le\n",
  "+    (fun r hr => G.hasDeriv_time r hr x)\n",
  "+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht\n",
  "+  simpa only [Real.norm_eq_abs, mul_comm] using h\n",
  "+\n",
  "+/-- The gradient of any derivative graph is uniformly small at short times. -/\n",
  "+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by\n",
  "+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT\n",
  "+    (norm_nonneg G) ?_ ?_ x\n",
  "+  · intro y\n",
  "+    calc\n",
  "+      |G.u (t, y)| ≤ t * ‖G.ut‖ := G.time_bound ht y\n",
  "+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le\n",
  "+  · intro y\n",
  "+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])\n",
  "+\n",
  "+/-- The supremum of the gradient has the same square-root gain. -/\n",
  "+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :\n",
  "+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by\n",
  "+  apply csSup_le (insert_nonempty _ _)\n",
  "+  rintro r (rfl | ⟨p, rfl⟩)\n",
  "+  · positivity\n",
  "+  · exact gradient_bound G hT p.property.1 p.val.2\n",
  "+\n",
  "+/-- Time differences of the gradient require no mixed time-space derivative. -/\n",
  "+theorem gradient_time_increment (G : Graph (E := E) α T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by\n",
  "+  by_cases hst : t = s\n",
  "+  · simp [hst]\n",
  "+  · apply derivative_norm_le_sqrt\n",
  "+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))\n",
  "+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))\n",
  "+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)\n",
  "+      (value_time_increment G hs ht) ?_ x\n",
  "+    intro y\n",
  "+    exact (norm_sub_le _ _).trans (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])\n",
  "+\n",
  "+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/\n",
  "+theorem gradient_space_increment (G : Graph (E := E) α T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=\n",
  "+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)\n",
  "+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)\n",
  "+\n",
  "+/-- Spatial value increments inherit the improved gradient bound. -/\n",
  "+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=\n",
  "+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)\n",
  "+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:93:4: error: Tactic `apply` failed: could not unify the conclusion of `(div_eq_iff (ne_of_gt hp)).mp`\n",
  "  ?m.202 = ?m.204 * √δ\n",
  "with the goal\n",
  "  2 * (δ * M) / √δ + √δ / 2 * (2 * M) = 3 * √δ * M\n",
  "\n",
  "Note: The full type of `(div_eq_iff (ne_of_gt hp)).mp` is\n",
  "  ?m.202 / √δ = ?m.204 → ?m.202 = ?m.204 * √δ\n",
  "\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "h✝ : E → ℝ\n",
  "dh : E → E →L[ℝ] ℝ\n",
  "ddh : E → E →L[ℝ] E →L[ℝ] ℝ\n",
  "δ M : ℝ\n",
  "hd : ∀ (x : E), HasFDerivAt h✝ (dh x) x\n",
  "hdd : ∀ (x : E), HasFDerivAt dh (ddh x) x\n",
  "hδ : 0 < δ\n",
  "hM : 0 ≤ M\n",
  "ha : ∀ (x : E), |h✝ x| ≤ δ * M\n",
  "hb : ∀ (x : E), ‖ddh x‖ ≤ 2 * M\n",
  "x v : E\n",
  "hv : ‖v‖ = 1\n",
  "h : |(dh x) v| ≤ 2 * (δ * M) / √δ + √δ / 2 * (2 * M)\n",
  "hs : √δ ^ 2 = δ\n",
  "hp : 0 < √δ\n",
  "⊢ 2 * (δ * M) / √δ + √δ / 2 * (2 * M) = 3 * √δ * M\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:117:37: error(lean.invalidField): Invalid field `time_bound`: The environment does not contain `Poincare.ParabolicSolutionGraph.Graph.time_bound`, so it is not possible to project the field `time_bound` from an expression\n",
  "  G\n",
  "of type `Graph α T`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:142:38: error: linarith failed to find a contradiction\n",
  "case h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "G : Graph α T\n",
  "s t : ℝ\n",
  "hs : s ∈ Icc 0 T\n",
  "ht : t ∈ Icc 0 T\n",
  "x : E\n",
  "hst : ¬t = s\n",
  "y : E\n",
  "a✝ : ?m.165 < ‖?m.159‖ + ‖?m.160‖\n",
  "⊢ False\n",
  "failed\n"
]
```

</details>

<details>
<summary>run-009</summary>

Source SHA-256: `f53730d8fa68f46ce86605b9744ed6ba5c874422b431d4f5822d66b7d64d7696`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-009.lean\n",
  "@@ -90,9 +90,8 @@\n",
  "       3 * Real.sqrt δ * M := by\n",
  "     have hs := Real.sq_sqrt hδ.le\n",
  "     have hp := Real.sqrt_pos.mpr hδ\n",
  "-    apply (div_eq_iff (ne_of_gt hp)).mp\n",
  "     field_simp\n",
  "-    nlinarith\n",
  "+    nlinarith [mul_eq_mul_right_iff.mpr (Or.inr hs)]\n",
  "   exact h.trans_eq he\n",
  " \n",
  " variable {α T : ℝ}\n",
  "@@ -114,7 +113,7 @@\n",
  "     (norm_nonneg G) ?_ ?_ x\n",
  "   · intro y\n",
  "     calc\n",
  "-      |G.u (t, y)| ≤ t * ‖G.ut‖ := G.time_bound ht y\n",
  "+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y\n",
  "       _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le\n",
  "   · intro y\n",
  "     exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])\n",
  "@@ -139,7 +138,8 @@\n",
  "       (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)\n",
  "       (value_time_increment G hs ht) ?_ x\n",
  "     intro y\n",
  "-    exact (norm_sub_le _ _).trans (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])\n",
  "+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans\n",
  "+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])\n",
  " \n",
  " /-- Spatial gradient increments are Lipschitz with the Hessian bound. -/\n",
  " theorem gradient_space_increment (G : Graph (E := E) α T)\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:94:48: error: Application type mismatch: The argument\n",
  "  hs\n",
  "has type\n",
  "  √δ ^ 2 = δ\n",
  "but is expected to have type\n",
  "  ?m.206 = 0\n",
  "in the application\n",
  "  Or.inr hs\n"
]
```

</details>

<details>
<summary>run-010</summary>

Source SHA-256: `18cc2957a8cad479f4e805e76eb7e0607d0f7054075fb604e1b579db928d4c2b`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-010.lean\n",
  "@@ -91,7 +91,7 @@\n",
  "     have hs := Real.sq_sqrt hδ.le\n",
  "     have hp := Real.sqrt_pos.mpr hδ\n",
  "     field_simp\n",
  "-    nlinarith [mul_eq_mul_right_iff.mpr (Or.inr hs)]\n",
  "+    nlinarith [congrArg (fun z : ℝ => z * M) hs]\n",
  "   exact h.trans_eq he\n",
  " \n",
  " variable {α T : ℝ}\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-011</summary>

Source SHA-256: `788c5bba9b3c259111ee2628db688aeab413323c8f6c2e62af36b12f08873219`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-011.lean\n",
  "@@ -158,3 +158,13 @@\n",
  "     (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "+\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/GradientAudit.lean \n",
  "exit: 0\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
]
```

</details>

<details>
<summary>run-012</summary>

Source SHA-256: `f2ea9702cec1aa984efb19d6cb2bb01ad18dde3848b573869e1d508d562d7ec0`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-012.lean\n",
  "@@ -157,14 +157,81 @@\n",
  "     (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)\n",
  "     (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)\n",
  " \n",
  "+/-- Split a power at a larger positive scale. -/\n",
  "+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (hR : 0 < R)\n",
  "+    (hrR : r ≤ R) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :\n",
  "+    r ^ b ≤ R ^ (b - a) * r ^ a := by\n",
  "+  have he : r ^ b = r ^ (b - a) * r ^ a := by\n",
  "+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]\n",
  "+    congr 1\n",
  "+    ring\n",
  "+  rw [he]\n",
  "+  exact mul_le_mul_of_nonneg_right\n",
  "+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)\n",
  "+\n",
  "+/-- Interpolate a Lipschitz bound and a bound at scale R. -/\n",
  "+theorem scale_interpolation {a L r R α : ℝ}\n",
  "+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)\n",
  "+    (hl : a ≤ L * r) (hb : a ≤ L * R) :\n",
  "+    a ≤ L * R ^ (1 - α) * r ^ α := by\n",
  "+  by_cases h : r ≤ R\n",
  "+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one\n",
  "+    rw [Real.rpow_one] at hp\n",
  "+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])\n",
  "+  · have he : R ^ (1 - α) * R ^ α = R := by\n",
  "+      rw [← Real.rpow_add hR]\n",
  "+      convert Real.rpow_one R using 2 <;> ring\n",
  "+    calc\n",
  "+      a ≤ L * R := hb\n",
  "+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]\n",
  "+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left\n",
  "+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)\n",
  "+\n",
  "+/-- The parabolic spatial scale is the square root of the time scale. -/\n",
  "+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :\n",
  "+    (Real.sqrt T) ^ p = T ^ (p / 2) := by\n",
  "+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]\n",
  "+  congr 1\n",
  "+  ring\n",
  "+\n",
  "+/-- Spatial Hölder gradient increments carry the desired positive time power. -/\n",
  "+theorem gradient_space_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    ‖G.du (t, x) - G.du (t, y)‖ ≤\n",
  "+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by\n",
  "+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)\n",
  "+    (L := 6 * ‖G‖) (norm_nonneg _ |> fun h => by positivity)\n",
  "+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le\n",
  "+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))\n",
  "+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans\n",
  "+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))\n",
  "+  rw [sqrt_rpow hT.le] at h\n",
  "+  nlinarith [h]\n",
  "+\n",
  "+/-- Spatial Hölder value increments gain one additional half power of time. -/\n",
  "+theorem value_space_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    |G.u (t, x) - G.u (t, y)| ≤\n",
  "+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by\n",
  "+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=\n",
  "+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)\n",
  "+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)\n",
  "+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)\n",
  "+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le\n",
  "+    (value_space_increment G hT ht x y)\n",
  "+    ((abs_sub _ _).trans (by\n",
  "+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)\n",
  "+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))\n",
  "+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by\n",
  "+    rw [← Real.rpow_one (Real.sqrt T), ← Real.rpow_add (Real.sqrt_pos.mpr hT)]\n",
  "+    rw [sqrt_rpow hT.le]\n",
  "+    congr 1\n",
  "+    ring\n",
  "+  calc\n",
  "+    |G.u (t,x) - G.u (t,y)| ≤ _ := h\n",
  "+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =\n",
  "+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "-\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:161:54: warning: unused variable `hR`\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedVariables false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:162:19: warning: unused variable `ha`\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedVariables false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:183:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:228:39: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n",
  "  √T ^ ?y * √T ^ ?z\n",
  "in the target expression\n",
  "  √T ^ 1 * (√T ^ 1) ^ (1 - α) = T ^ (1 - α / 2)\n",
  "\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "G : Graph α T\n",
  "hα : 0 < α\n",
  "hα1 : α < 1\n",
  "hT : 0 < T\n",
  "t : ℝ\n",
  "ht : t ∈ Icc 0 T\n",
  "x y : E\n",
  "hu : ∀ (z : E), |↑(WithLp.fst ↑G.u) (t, z)| ≤ T * ‖G‖\n",
  "h : |↑(WithLp.fst ↑G.u) (t, x) - ↑(WithLp.fst ↑G.u) (t, y)| ≤ 3 * √T * ‖G‖ * √T ^ (1 - α) * ‖x - y‖ ^ α\n",
  "⊢ √T ^ 1 * (√T ^ 1) ^ (1 - α) = T ^ (1 - α / 2)\n"
]
```

</details>

<details>
<summary>run-013</summary>

Source SHA-256: `1cc70ebe0eec0644a46a535c40b8d0b57cf822283d03e208ebc350ddea6b6c15`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-013.lean\n",
  "@@ -158,8 +158,8 @@\n",
  "     (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)\n",
  " \n",
  " /-- Split a power at a larger positive scale. -/\n",
  "-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (hR : 0 < R)\n",
  "-    (hrR : r ≤ R) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :\n",
  "+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)\n",
  "+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :\n",
  "     r ^ b ≤ R ^ (b - a) * r ^ a := by\n",
  "   have he : r ^ b = r ^ (b - a) * r ^ a := by\n",
  "     rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]\n",
  "@@ -180,7 +180,8 @@\n",
  "     exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])\n",
  "   · have he : R ^ (1 - α) * R ^ α = R := by\n",
  "       rw [← Real.rpow_add hR]\n",
  "-      convert Real.rpow_one R using 2 <;> ring\n",
  "+      convert Real.rpow_one R using 2\n",
  "+      ring\n",
  "     calc\n",
  "       a ≤ L * R := hb\n",
  "       _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]\n",
  "@@ -201,7 +202,7 @@\n",
  "     ‖G.du (t, x) - G.du (t, y)‖ ≤\n",
  "       6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by\n",
  "   have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)\n",
  "-    (L := 6 * ‖G‖) (norm_nonneg _ |> fun h => by positivity)\n",
  "+    (L := 6 * ‖G‖) (by positivity)\n",
  "     (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le\n",
  "     ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))\n",
  "     ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans\n",
  "@@ -225,7 +226,8 @@\n",
  "       have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)\n",
  "       nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))\n",
  "   have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by\n",
  "-    rw [← Real.rpow_one (Real.sqrt T), ← Real.rpow_add (Real.sqrt_pos.mpr hT)]\n",
  "+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]\n",
  "+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]\n",
  "     rw [sqrt_rpow hT.le]\n",
  "     congr 1\n",
  "     ring\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-014</summary>

Source SHA-256: `88f3d6b6f3e9391d66cd48f73eecb8f87dff4199703c482a1f687db81585a1e4`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-014.lean\n",
  "@@ -236,4 +236,113 @@\n",
  "     _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =\n",
  "         3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]\n",
  " \n",
  "+/-- The temporal Hölder gradient bound follows from the square-root increment. -/\n",
  "+theorem gradient_time_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x) - G.du (s, x)‖ ≤\n",
  "+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by\n",
  "+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩\n",
  "+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ\n",
  "+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)\n",
  "+    (show (0 : ℝ) < 1 / 2 by norm_num)\n",
  "+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp\n",
  "+  have hi := gradient_time_increment G hs ht x\n",
  "+  rw [Real.sqrt_eq_rpow] at hi\n",
  "+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]\n",
  "+\n",
  "+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/\n",
  "+theorem value_time_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    |G.u (t, x) - G.u (s, x)| ≤\n",
  "+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by\n",
  "+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩\n",
  "+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ\n",
  "+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one\n",
  "+  rw [Real.rpow_one] at hp\n",
  "+  exact (value_time_increment G hs ht x).trans (by\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])\n",
  "+\n",
  "+/-- Split a mixed increment through the point with the first time and second position. -/\n",
  "+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]\n",
  "+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)\n",
  "+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,\n",
  "+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)\n",
  "+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,\n",
  "+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :\n",
  "+    HasHolderBound α (cylinder T) f (Kx + Kt) := by\n",
  "+  intro p hp q hq\n",
  "+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=\n",
  "+    Real.rpow_le_rpow (norm_nonneg _) (by\n",
  "+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα\n",
  "+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by\n",
  "+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]\n",
  "+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by\n",
  "+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα\n",
  "+  calc\n",
  "+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=\n",
  "+      norm_sub_le_norm_sub_add_norm_sub _ _ _\n",
  "+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=\n",
  "+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)\n",
  "+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by\n",
  "+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]\n",
  "+\n",
  "+/-- Full gradient Hölder control, including mixed increments. -/\n",
  "+theorem gradient_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :\n",
  "+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by\n",
  "+  have h := holder_of_increments hα.le\n",
  "+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+    (fun t ht => gradient_space_holder G hα hα1 hT ht)\n",
  "+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)\n",
  "+  convert h using 1 <;> ring\n",
  "+\n",
  "+/-- Full value Hölder control with its stronger time power. -/\n",
  "+theorem value_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :\n",
  "+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by\n",
  "+  have h := holder_of_increments hα.le\n",
  "+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+    (fun t ht => value_space_holder G hα hα1 hT ht)\n",
  "+    (fun s hs t ht => value_time_holder G hα hα1 hT hs ht)\n",
  "+  convert h using 1 <;> ring\n",
  "+\n",
  "+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/\n",
  "+theorem interpolation_bounds (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :\n",
  "+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by\n",
  "+  constructor\n",
  "+  · have h := ParabolicHolder.norm_le_of_bounds G.u\n",
  "+      (show 0 ≤ T * ‖G‖ by positivity)\n",
  "+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+      (fun p hp => (time_bound G hp.1 p.2).trans\n",
  "+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))\n",
  "+      (value_holder G hα hα1 hT)\n",
  "+    have hp : T ≤ T ^ (1-α/2) := by\n",
  "+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1\n",
  "+      exact (Real.rpow_one T).symm\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),\n",
  "+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]\n",
  "+  · have h := ParabolicHolder.norm_le_of_bounds G.du\n",
  "+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)\n",
  "+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+      (fun p hp => gradient_bound G hT hp.1 p.2)\n",
  "+      (gradient_holder G hα hα1 hT)\n",
  "+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by\n",
  "+      rw [Real.sqrt_eq_rpow]\n",
  "+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]\n",
  "+\n",
  "+/-- A universal constant satisfies the frozen interpolation target. -/\n",
  "+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →\n",
  "+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,\n",
  "+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by\n",
  "+  intro α hα hα1\n",
  "+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:268:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicCutoffCommutator.holder_of_increments`:\n",
  "  [NormedSpace ℝ E]\n",
  "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n",
  "  omit [NormedSpace ℝ E] in theorem ...\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:300:20: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:310:22: error: Type mismatch\n",
  "  value_time_holder G hα hα1 hT hs ht\n",
  "has type\n",
  "  ∀ (x : E), |↑(WithLp.fst ↑G.u) (t, x) - ↑(WithLp.fst ↑G.u) (s, x)| ≤ T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2)\n",
  "but is expected to have type\n",
  "  ∀ (x : ?m.58), ‖?m.65 (t, x) - ?m.65 (s, x)‖ ≤ T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2)\n"
]
```

</details>

<details>
<summary>run-015</summary>

Source SHA-256: `9b39c931986f4bdd08923a45ce570821d9fb8d89d4b65b7945ecf9e8b655be69`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-015.lean\n",
  "@@ -265,6 +265,7 @@\n",
  "     nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])\n",
  " \n",
  " /-- Split a mixed increment through the point with the first time and second position. -/\n",
  "+omit [NormedSpace ℝ E] in\n",
  " theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]\n",
  "     {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)\n",
  "     (hspace : ∀ t ∈ Icc 0 T, ∀ x y,\n",
  "@@ -297,18 +298,20 @@\n",
  "     (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "     (fun t ht => gradient_space_holder G hα hα1 hT ht)\n",
  "     (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)\n",
  "-  convert h using 1 <;> ring\n",
  "+  convert h using 1\n",
  "+  ring\n",
  " \n",
  " /-- Full value Hölder control with its stronger time power. -/\n",
  " theorem value_holder (G : Graph (E := E) α T)\n",
  "     (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :\n",
  "     HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by\n",
  "-  have h := holder_of_increments hα.le\n",
  "+  have h := holder_of_increments (f := G.u) hα.le\n",
  "     (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "     (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "-    (fun t ht => value_space_holder G hα hα1 hT ht)\n",
  "-    (fun s hs t ht => value_time_holder G hα hα1 hT hs ht)\n",
  "-  convert h using 1 <;> ring\n",
  "+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)\n",
  "+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)\n",
  "+  convert h using 1\n",
  "+  ring\n",
  " \n",
  " /-- The complete lower-derivative norms gain positive powers on short cylinders. -/\n",
  " theorem interpolation_bounds (G : Graph (E := E) α T)\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:267:89: error: unexpected token 'omit'; expected 'lemma'\n"
]
```

</details>

<details>
<summary>run-016</summary>

Source SHA-256: `7fb6897087f64c728aa967684f56c63de42763e0fba2cc38808559dd2a63e6a7`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-016.lean\n",
  "@@ -349,3 +349,25 @@\n",
  "   exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "+\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.power_scale_bound\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.scale_interpolation\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.sqrt_rpow\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_space_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_time_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.holder_of_increments\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.interpolation_bounds\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.interpolation\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationAudit.lean \n",
  "exit: 1\n",
  "/tmp/parabolic-cutoff-commutator/InterpolationAudit.lean:267:89: error: unexpected token 'omit'; expected 'lemma'\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.power_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.sqrt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.holder_of_increments' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
]
```

</details>

<details>
<summary>run-017</summary>

Source SHA-256: `dca15c48b71c7c930005c95cea08ee93fd94e6818458e01064c4df049e631c43`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-017.lean\n",
  "@@ -264,8 +264,8 @@\n",
  "   exact (value_time_increment G hs ht x).trans (by\n",
  "     nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])\n",
  " \n",
  "+omit [NormedSpace ℝ E] in\n",
  " /-- Split a mixed increment through the point with the first time and second position. -/\n",
  "-omit [NormedSpace ℝ E] in\n",
  " theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]\n",
  "     {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)\n",
  "     (hspace : ∀ t ∈ Icc 0 T, ∀ x y,\n",
  "@@ -349,25 +349,3 @@\n",
  "   exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "-\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.power_scale_bound\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.scale_interpolation\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.sqrt_rpow\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_space_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_time_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.holder_of_increments\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.interpolation_bounds\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.interpolation\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-018</summary>

Source SHA-256: `927c4f387fb68316ba54300f02200065c7a89715e9674e94b46b653919d12286`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-018.lean\n",
  "@@ -349,3 +349,25 @@\n",
  "   exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "+\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.power_scale_bound\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.scale_interpolation\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.sqrt_rpow\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_space_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_time_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.holder_of_increments\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.gradient_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.value_holder\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.interpolation_bounds\n",
  "+#print axioms Poincare.ParabolicCutoffCommutator.interpolation\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationAudit.lean \n",
  "exit: 0\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.power_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.sqrt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.holder_of_increments' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
]
```

</details>

<details>
<summary>run-019</summary>

Source SHA-256: `b6138caebd2e40bdf058844e79be5cac25639fb614ea807c61142e18610fcf9d`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-019.lean\n",
  "@@ -1,3 +1,10 @@\n",
  "+import Poincare.Global.NearIdentityParabolicRightInverse\n",
  "+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients\n",
  "+import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover\n",
  "+import Poincare.Global.DeTurckPrincipalIdentity\n",
  "+import Poincare.Global.CompactCoefficientEllipticity\n",
  "+import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  "+import Mathlib.Topology.MetricSpace.Contracting\n",
  " import Poincare.Global.ParabolicHolderMultiplier\n",
  " import Poincare.Global.DuhamelSolutionOperatorBound\n",
  " import Mathlib.Analysis.Calculus.MeanValue\n",
  "@@ -350,24 +357,249 @@\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n",
  " \n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.quadratic_remainder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.finite_difference_derivative\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_bound\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.supNorm_gradient_le\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_space_increment\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.power_scale_bound\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.scale_interpolation\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.sqrt_rpow\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_space_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_space_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_time_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_time_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.holder_of_increments\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.gradient_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.value_holder\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.interpolation_bounds\n",
  "-#print axioms Poincare.ParabolicCutoffCommutator.interpolation\n",
  "+\n",
  "+set_option autoImplicit false\n",
  "+noncomputable section\n",
  "+open Set\n",
  "+open scoped Manifold ContDiff\n",
  "+namespace FiniteAtlasSurvey\n",
  "+open Poincare\n",
  "+local notation \"E\" => ClosedSmoothModel 3\n",
  "+local notation \"I\" => closedSmoothModelWithCorners 3\n",
  "+local notation \"e\" => EuclideanSpace.basisFun (Fin 3) ℝ\n",
  "+abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ\n",
  "+abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T\n",
  "+abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ\n",
  "+\n",
  "+universe u\n",
  "+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]\n",
  "+  [IsManifold I ∞ M]\n",
  "+\n",
  "+structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]\n",
  "+    [IsManifold I ∞ M] where\n",
  "+  cover : FiniteExtendedChartCover (n := 3) (M := M)\n",
  "+  region : Fin cover.chartCount → Set M\n",
  "+  region_open : ∀ i, IsOpen (region i)\n",
  "+  region_cover : (⋃ i, region i) = univ\n",
  "+  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source\n",
  "+  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))\n",
  "+  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ\n",
  "+  subordinate : partition.IsSubordinate region\n",
  "+\n",
  "+variable (A : AtlasData M)\n",
  "+abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3\n",
  "+abbrev LocalProduct (H : Type*) := Index A → H\n",
  "+\n",
  "+def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)\n",
  "+def coordSupport (i : Fin A.cover.chartCount) : Set E :=\n",
  "+  chart A i '' tsupport (A.partition i)\n",
  "+def change (i j : Fin A.cover.chartCount) (z : E) : E :=\n",
  "+  chart A j ((chart A i).symm z)\n",
  "+def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=\n",
  "+  (fderiv ℝ (change A i j) (chart A i x) (e a)) c\n",
  "+\n",
  "+def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=\n",
  "+  ({ toFun := fun f => f p\n",
  "+     map_add' := fun _ _ => rfl\n",
  "+     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "+    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)\n",
  "+\n",
  "+def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=\n",
  "+  ({ toFun := fun G => G.u p\n",
  "+     map_add' := fun _ _ => rfl\n",
  "+     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "+    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)\n",
  "+\n",
  "+variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "+def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)\n",
  "+    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "+  (ev p).comp (ContinuousLinearMap.proj (i, a, b))\n",
  "+\n",
  "+def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)\n",
  "+    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "+  A.partition j x • evalLocal A ev i a b (t, chart A i x) -\n",
  "+    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,\n",
  "+      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)\n",
  "+\n",
  "+def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),\n",
  "+    ⨅ (z : {z : E // z ∉ coordSupport A i}),\n",
  "+    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap\n",
  "+\n",
  "+def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),\n",
  "+    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap\n",
  "+\n",
  "+def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "+  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),\n",
  "+    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),\n",
  "+    LinearMap.ker (overlap A ev i j a b t x).toLinearMap\n",
  "+\n",
  "+def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "+  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev\n",
  "+abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))\n",
  "+abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))\n",
  "+\n",
  "+structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where\n",
  "+  entries : LocalProduct A H\n",
  "+  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0\n",
  "+  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries\n",
  "+  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →\n",
  "+    overlap A ev i j a b t x entries = 0\n",
  "+\n",
  "+-- Statement definitions, not proofs of closedness, completeness or equivalence.\n",
  "+def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "+  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))\n",
  "+def carrierCompleteGoal (α T : ℝ) : Prop :=\n",
  "+  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)\n",
  "+def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "+  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)\n",
  "+\n",
  "+-- Positive-time candidate strengthened norm functional; no norm instance claimed.\n",
  "+def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=\n",
  "+  T ^ (-(1 - α / 2)) * ‖G.u‖ +\n",
  "+  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖\n",
  "+\n",
  "+def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,\n",
  "+    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "+    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖\n",
  "+\n",
  "+-- Coefficients are the resulting commutator coefficients, already zero-extended.\n",
  "+def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)\n",
  "+    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "+  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p\n",
  "+\n",
  "+def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "+  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),\n",
  "+  ∃ K : Jet α T →L[ℝ] Scalar α T,\n",
  "+    (∀ G p, K G p = firstOrderValue b c G p) ∧\n",
  "+    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)\n",
  "+\n",
  "+structure CutoffData (α T : ℝ) where\n",
  "+  psi : E → ℝ\n",
  "+  smooth : ContDiff ℝ ∞ psi\n",
  "+  compact : HasCompactSupport psi\n",
  "+  a : Fin 3 → Fin 3 → Scalar α T\n",
  "+  drift : Fin 3 → Scalar α T\n",
  "+  b : Fin 3 → Scalar α T\n",
  "+  c : Scalar α T\n",
  "+  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,\n",
  "+    b k (t,x) = -(∑ j : Fin 3,\n",
  "+      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))\n",
  "+  c_eq : ∀ t ∈ Icc 0 T, ∀ x,\n",
  "+    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,\n",
  "+      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -\n",
  "+      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)\n",
  "+\n",
  "+def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=\n",
  "+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "+    ∀ G p, (C G).u p = D.psi p.2 * G.u p\n",
  "+\n",
  "+structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where\n",
  "+  S : Scalar α T →L[ℝ] Jet α T\n",
  "+  bound : ‖S‖ ≤ C_S\n",
  "+  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,\n",
  "+    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,\n",
  "+      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)\n",
  "+\n",
  "+def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}\n",
  "+    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=\n",
  "+  0 < α → 0 < T →\n",
  "+  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →\n",
  "+  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →\n",
  "+  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤\n",
  "+    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖\n",
  "+\n",
  "+-- Actual chart coefficient agreement is separate from the frozen analytic data.\n",
  "+structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where\n",
  "+  cutoff : E → ℝ\n",
  "+  smooth : ContDiff ℝ ∞ cutoff\n",
  "+  compact : HasCompactSupport cutoff\n",
  "+  one_on : ∀ z ∈ U, cutoff z = 1\n",
  "+  b : Fin 3 → Fin 3 → Scalar α T\n",
  "+  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "+    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))\n",
  "+\n",
  "+def nonlinearGoal (α T r C_NL C_ref θ : ℝ)\n",
  "+    (N : X_M A α T → Y_M A α T) : Prop :=\n",
  "+  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →\n",
  "+    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧\n",
  "+  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))\n",
  "+def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)\n",
  "+    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)\n",
  "+    (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "+  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "+    a i j p * G.ddu p (e i) (e j)) -\n",
  "+    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p\n",
  "+\n",
  "+def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)\n",
  "+    (potential : Scalar α T) : Prop :=\n",
  "+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "+    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧\n",
  "+    (∀ G t, t ∈ Icc 0 T → ∀ x,\n",
  "+      localLinearValue D.a D.drift potential (C G) (t,x) -\n",
  "+        D.psi x * localLinearValue D.a D.drift potential G (t,x) =\n",
  "+          firstOrderValue D.b D.c G (t,x))\n",
  "+\n",
  "+def oscillationExtensionGoal : Prop :=\n",
  "+  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →\n",
  "+  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →\n",
  "+  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →\n",
  "+  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →\n",
  "+  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,\n",
  "+    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →\n",
  "+  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "+    ∃ b : Fin 3 → Fin 3 → Scalar α T,\n",
  "+      (∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "+        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧\n",
  "+      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧\n",
  "+      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)\n",
  "+\n",
  "+def frozenCLMGoal : Prop :=\n",
  "+  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →\n",
  "+  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →\n",
  "+  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →\n",
  "+  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)\n",
  "+\n",
  "+abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →\n",
  "+  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ\n",
  "+\n",
  "+def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=\n",
  "+  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)\n",
  "+\n",
  "+def localizedValue {T : ℝ} (F : TensorField (M := M) T)\n",
  "+    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by\n",
  "+  classical\n",
  "+  exact if ht : p.1 ∈ Icc 0 T then\n",
  "+    if p.2 ∈ (chart A i).target then\n",
  "+      let x := (chart A i).symm p.2\n",
  "+      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))\n",
  "+    else 0\n",
  "+  else 0\n",
  "+\n",
  "+def reconstructionGoal (α T : ℝ) : Prop :=\n",
  "+  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,\n",
  "+    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p\n",
  "+\n",
  "+abbrev Jet1 := E →L[ℝ] Bilin\n",
  "+abbrev Jet2 := E →L[ℝ] Jet1\n",
  "+\n",
  "+def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)\n",
  "+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "+    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=\n",
  "+  (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "+    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +\n",
  "+    DeTurckPrincipalIdentity.lowerTerm B DB G J\n",
  "+\n",
  "+set_option synthInstance.maxHeartbeats 400000 in\n",
  "+def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)\n",
  "+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "+    (z h : Bilin × Jet1 × Jet2) : Bilin :=\n",
  "+  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +\n",
  "+    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +\n",
  "+    (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "+      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))\n",
  "+end FiniteAtlasSurvey\n",
  "+example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationTarget.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-020</summary>

Source SHA-256: `f696412764f29d1fef37e196887e83b4848e5d1c8cfd271d7a59a19268359388`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-020.lean\n",
  "@@ -1,13 +1,7 @@\n",
  "-import Poincare.Global.NearIdentityParabolicRightInverse\n",
  "-import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients\n",
  "-import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover\n",
  "-import Poincare.Global.DeTurckPrincipalIdentity\n",
  "-import Poincare.Global.CompactCoefficientEllipticity\n",
  "-import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  "-import Mathlib.Topology.MetricSpace.Contracting\n",
  " import Poincare.Global.ParabolicHolderMultiplier\n",
  " import Poincare.Global.DuhamelSolutionOperatorBound\n",
  " import Mathlib.Analysis.Calculus.MeanValue\n",
  "+import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  " \n",
  " noncomputable section\n",
  " \n",
  "@@ -355,251 +349,63 @@\n",
  "   intro α hα hα1\n",
  "   exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  " \n",
  "+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/\n",
  "+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]\n",
  "+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,\n",
  "+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by\n",
  "+  classical\n",
  "+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous\n",
  "+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)\n",
  "+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)\n",
  "+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by\n",
  "+    have h := scale_interpolation (L := 2*A+B) (R := 1)\n",
  "+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le\n",
  "+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))\n",
  "+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))\n",
  "+    simpa using h\n",
  "+  refine ⟨A + (2*A+B), by positivity, ?_⟩\n",
  "+  intro T\n",
  "+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0\n",
  "+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by\n",
  "+    intro p hp; simp [f, hp]\n",
  "+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by\n",
  "+    intro p hp; simpa [f, hp] using hA p.2\n",
  "+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by\n",
  "+    intro p hp q hq\n",
  "+    simp only [f, if_pos hp, if_pos hq]\n",
  "+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left\n",
  "+      (Real.rpow_le_rpow (norm_nonneg _) (by\n",
  "+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))\n",
  "+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩\n",
  "+  refine ⟨fY, ?_, ?_⟩\n",
  "+  · intro p hp\n",
  "+    change f p = ψ p.2\n",
  "+    simp [f, hp]\n",
  "+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder\n",
  "+\n",
  "+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/\n",
  "+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}\n",
  "+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,\n",
  "+      ∃ (f : Y (E := E) α T ℝ)\n",
  "+        (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),\n",
  "+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧\n",
  "+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧\n",
  "+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by\n",
  "+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)\n",
  "+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)\n",
  "+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1\n",
  "+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1\n",
  "+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1\n",
  "+  refine ⟨K0+K1+K2, by positivity, ?_⟩\n",
  "+  intro T\n",
  "+  obtain ⟨f, hf, hfb⟩ := h0 T\n",
  "+  obtain ⟨df, hdf, hdfb⟩ := h1 T\n",
  "+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T\n",
  "+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n",
  "-\n",
  "-\n",
  "-set_option autoImplicit false\n",
  "-noncomputable section\n",
  "-open Set\n",
  "-open scoped Manifold ContDiff\n",
  "-namespace FiniteAtlasSurvey\n",
  "-open Poincare\n",
  "-local notation \"E\" => ClosedSmoothModel 3\n",
  "-local notation \"I\" => closedSmoothModelWithCorners 3\n",
  "-local notation \"e\" => EuclideanSpace.basisFun (Fin 3) ℝ\n",
  "-abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ\n",
  "-abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T\n",
  "-abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ\n",
  "-\n",
  "-universe u\n",
  "-variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]\n",
  "-  [IsManifold I ∞ M]\n",
  "-\n",
  "-structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]\n",
  "-    [IsManifold I ∞ M] where\n",
  "-  cover : FiniteExtendedChartCover (n := 3) (M := M)\n",
  "-  region : Fin cover.chartCount → Set M\n",
  "-  region_open : ∀ i, IsOpen (region i)\n",
  "-  region_cover : (⋃ i, region i) = univ\n",
  "-  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source\n",
  "-  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))\n",
  "-  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ\n",
  "-  subordinate : partition.IsSubordinate region\n",
  "-\n",
  "-variable (A : AtlasData M)\n",
  "-abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3\n",
  "-abbrev LocalProduct (H : Type*) := Index A → H\n",
  "-\n",
  "-def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)\n",
  "-def coordSupport (i : Fin A.cover.chartCount) : Set E :=\n",
  "-  chart A i '' tsupport (A.partition i)\n",
  "-def change (i j : Fin A.cover.chartCount) (z : E) : E :=\n",
  "-  chart A j ((chart A i).symm z)\n",
  "-def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=\n",
  "-  (fderiv ℝ (change A i j) (chart A i x) (e a)) c\n",
  "-\n",
  "-def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=\n",
  "-  ({ toFun := fun f => f p\n",
  "-     map_add' := fun _ _ => rfl\n",
  "-     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "-    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)\n",
  "-\n",
  "-def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=\n",
  "-  ({ toFun := fun G => G.u p\n",
  "-     map_add' := fun _ _ => rfl\n",
  "-     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1\n",
  "-    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)\n",
  "-\n",
  "-variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "-def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)\n",
  "-    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "-  (ev p).comp (ContinuousLinearMap.proj (i, a, b))\n",
  "-\n",
  "-def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)\n",
  "-    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=\n",
  "-  A.partition j x • evalLocal A ev i a b (t, chart A i x) -\n",
  "-    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,\n",
  "-      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)\n",
  "-\n",
  "-def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),\n",
  "-    ⨅ (z : {z : E // z ∉ coordSupport A i}),\n",
  "-    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap\n",
  "-\n",
  "-def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),\n",
  "-    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap\n",
  "-\n",
  "-def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),\n",
  "-    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),\n",
  "-    LinearMap.ker (overlap A ev i j a b t x).toLinearMap\n",
  "-\n",
  "-def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=\n",
  "-  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev\n",
  "-abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))\n",
  "-abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))\n",
  "-\n",
  "-structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where\n",
  "-  entries : LocalProduct A H\n",
  "-  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0\n",
  "-  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries\n",
  "-  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →\n",
  "-    overlap A ev i j a b t x entries = 0\n",
  "-\n",
  "--- Statement definitions, not proofs of closedness, completeness or equivalence.\n",
  "-def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "-  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))\n",
  "-def carrierCompleteGoal (α T : ℝ) : Prop :=\n",
  "-  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)\n",
  "-def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=\n",
  "-  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)\n",
  "-\n",
  "--- Positive-time candidate strengthened norm functional; no norm instance claimed.\n",
  "-def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=\n",
  "-  T ^ (-(1 - α / 2)) * ‖G.u‖ +\n",
  "-  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖\n",
  "-\n",
  "-def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,\n",
  "-    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "-    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖\n",
  "-\n",
  "--- Coefficients are the resulting commutator coefficients, already zero-extended.\n",
  "-def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)\n",
  "-    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "-  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p\n",
  "-\n",
  "-def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →\n",
  "-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "-  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),\n",
  "-  ∃ K : Jet α T →L[ℝ] Scalar α T,\n",
  "-    (∀ G p, K G p = firstOrderValue b c G p) ∧\n",
  "-    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)\n",
  "-\n",
  "-structure CutoffData (α T : ℝ) where\n",
  "-  psi : E → ℝ\n",
  "-  smooth : ContDiff ℝ ∞ psi\n",
  "-  compact : HasCompactSupport psi\n",
  "-  a : Fin 3 → Fin 3 → Scalar α T\n",
  "-  drift : Fin 3 → Scalar α T\n",
  "-  b : Fin 3 → Scalar α T\n",
  "-  c : Scalar α T\n",
  "-  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,\n",
  "-    b k (t,x) = -(∑ j : Fin 3,\n",
  "-      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))\n",
  "-  c_eq : ∀ t ∈ Icc 0 T, ∀ x,\n",
  "-    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,\n",
  "-      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -\n",
  "-      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)\n",
  "-\n",
  "-def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=\n",
  "-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "-    ∀ G p, (C G).u p = D.psi p.2 * G.u p\n",
  "-\n",
  "-structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where\n",
  "-  S : Scalar α T →L[ℝ] Jet α T\n",
  "-  bound : ‖S‖ ≤ C_S\n",
  "-  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,\n",
  "-    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,\n",
  "-      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)\n",
  "-\n",
  "-def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}\n",
  "-    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=\n",
  "-  0 < α → 0 < T →\n",
  "-  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →\n",
  "-  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →\n",
  "-  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤\n",
  "-    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖\n",
  "-\n",
  "--- Actual chart coefficient agreement is separate from the frozen analytic data.\n",
  "-structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where\n",
  "-  cutoff : E → ℝ\n",
  "-  smooth : ContDiff ℝ ∞ cutoff\n",
  "-  compact : HasCompactSupport cutoff\n",
  "-  one_on : ∀ z ∈ U, cutoff z = 1\n",
  "-  b : Fin 3 → Fin 3 → Scalar α T\n",
  "-  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "-    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))\n",
  "-\n",
  "-def nonlinearGoal (α T r C_NL C_ref θ : ℝ)\n",
  "-    (N : X_M A α T → Y_M A α T) : Prop :=\n",
  "-  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →\n",
  "-    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧\n",
  "-  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))\n",
  "-def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)\n",
  "-    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)\n",
  "-    (G : Jet α T) (p : ℝ × E) : ℝ :=\n",
  "-  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-    a i j p * G.ddu p (e i) (e j)) -\n",
  "-    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p\n",
  "-\n",
  "-def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)\n",
  "-    (potential : Scalar α T) : Prop :=\n",
  "-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,\n",
  "-    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧\n",
  "-    (∀ G t, t ∈ Icc 0 T → ∀ x,\n",
  "-      localLinearValue D.a D.drift potential (C G) (t,x) -\n",
  "-        D.psi x * localLinearValue D.a D.drift potential G (t,x) =\n",
  "-          firstOrderValue D.b D.c G (t,x))\n",
  "-\n",
  "-def oscillationExtensionGoal : Prop :=\n",
  "-  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →\n",
  "-  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →\n",
  "-  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →\n",
  "-  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →\n",
  "-  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,\n",
  "-    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →\n",
  "-  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "-    ∃ b : Fin 3 → Fin 3 → Scalar α T,\n",
  "-      (∀ t ∈ Icc 0 T, ∀ x i j,\n",
  "-        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧\n",
  "-      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧\n",
  "-      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)\n",
  "-\n",
  "-def frozenCLMGoal : Prop :=\n",
  "-  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →\n",
  "-  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →\n",
  "-  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →\n",
  "-  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)\n",
  "-\n",
  "-abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →\n",
  "-  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ\n",
  "-\n",
  "-def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=\n",
  "-  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)\n",
  "-\n",
  "-def localizedValue {T : ℝ} (F : TensorField (M := M) T)\n",
  "-    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by\n",
  "-  classical\n",
  "-  exact if ht : p.1 ∈ Icc 0 T then\n",
  "-    if p.2 ∈ (chart A i).target then\n",
  "-      let x := (chart A i).symm p.2\n",
  "-      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))\n",
  "-    else 0\n",
  "-  else 0\n",
  "-\n",
  "-def reconstructionGoal (α T : ℝ) : Prop :=\n",
  "-  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,\n",
  "-    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p\n",
  "-\n",
  "-abbrev Jet1 := E →L[ℝ] Bilin\n",
  "-abbrev Jet2 := E →L[ℝ] Jet1\n",
  "-\n",
  "-def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)\n",
  "-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "-    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=\n",
  "-  (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +\n",
  "-    DeTurckPrincipalIdentity.lowerTerm B DB G J\n",
  "-\n",
  "-set_option synthInstance.maxHeartbeats 400000 in\n",
  "-def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)\n",
  "-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)\n",
  "-    (z h : Bilin × Jet1 × Jet2) : Bilin :=\n",
  "-  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +\n",
  "-    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +\n",
  "-    (∑ i : Fin 3, ∑ j : Fin 3,\n",
  "-      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))\n",
  "-end FiniteAtlasSurvey\n",
  "-example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:354:33: error: expected token\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:390:21: error: expected token\n"
]
```

</details>

<details>
<summary>run-021</summary>

Source SHA-256: `d0019dc415af61554cb8034077f11ac9a245f9f72c712825f8e0253639ac468c`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-021.lean\n",
  "@@ -8,6 +8,7 @@\n",
  " namespace Poincare.ParabolicCutoffCommutator\n",
  " \n",
  " open Set ParabolicHolder ParabolicSolutionGraph\n",
  "+open scoped ContDiff\n",
  " \n",
  " variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n",
  " \n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-022</summary>

Source SHA-256: `510e78522440864ba5ba1434bcf7d394ad6368c4865905c00480203e52f2e126`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-022.lean\n",
  "@@ -409,4 +409,87 @@\n",
  "   obtain ⟨ddf, hddf, hddfb⟩ := h2 T\n",
  "   exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩\n",
  " \n",
  "+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/\n",
  "+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasFDerivAt (fun z => ψ z * G.u (t,z))\n",
  "+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=\n",
  "+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)\n",
  "+\n",
  "+/-- The second spatial product rule includes both mixed Hessian terms. -/\n",
  "+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)\n",
  "+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +\n",
  "+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +\n",
  "+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by\n",
  "+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)\n",
  "+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add\n",
  "+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)\n",
  "+\n",
  "+/-- A spatial cutoff is constant in the within-time product rule. -/\n",
  "+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=\n",
  "+  (G.hasDeriv_time t ht x).const_mul (ψ x)\n",
  "+\n",
  "+section Bilinear\n",
  "+variable {F H J : Type*}\n",
  "+  [NormedAddCommGroup F] [NormedSpace ℝ F]\n",
  "+  [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "+  [NormedAddCommGroup J] [NormedSpace ℝ J]\n",
  "+\n",
  "+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/\n",
  "+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n",
  "+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by\n",
  "+  intro p hp q hq\n",
  "+  have hf := ParabolicHolder.holder_le f hp hq\n",
  "+  have hg := ParabolicHolder.holder_le g hp hq\n",
  "+  have hf0 := ParabolicHolder.norm_le f p\n",
  "+  have hg0 := ParabolicHolder.norm_le g q\n",
  "+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α\n",
  "+  calc\n",
  "+    ‖B (f p) (g p) - B (f q) (g q)‖ =\n",
  "+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by\n",
  "+      congr 1\n",
  "+      simp only [map_sub, ContinuousLinearMap.sub_apply]\n",
  "+      abel\n",
  "+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _\n",
  "+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=\n",
  "+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)\n",
  "+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +\n",
  "+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by\n",
  "+      apply add_le_add\n",
  "+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg\n",
  "+          (norm_nonneg _) (by positivity)\n",
  "+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0\n",
  "+          (norm_nonneg _) (by positivity)\n",
  "+    _ = _ := by ring\n",
  "+\n",
  "+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/\n",
  "+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=\n",
  "+  ofFunction (fun p => B (f p) (g p))\n",
  "+    (fun p hp => by simp [zero_off f hp])\n",
  "+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans\n",
  "+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))\n",
  "+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩\n",
  "+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩\n",
  "+\n",
  "+/-- The bilinear carrier norm has an explicit product bound. -/\n",
  "+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n",
  "+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by\n",
  "+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)\n",
  "+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)\n",
  "+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)\n",
  "+    (fun p _ => (B.le_opNorm₂ _ _).trans\n",
  "+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))\n",
  "+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))\n",
  "+    (bilinear_holder B f g)\n",
  "+  nlinarith [h]\n",
  "+\n",
  "+end Bilinear\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:443:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicCutoffCommutator.bilinear_holder`:\n",
  "  [NormedSpace ℝ E]\n",
  "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n",
  "  omit [NormedSpace ℝ E] in theorem ...\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`\n"
]
```

</details>

<details>
<summary>run-023</summary>

Source SHA-256: `6e2f4eb61d1d4cee62c2c3540bff242dfdcf13b9d16b7ccf6934a274a3dec2aa`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-023.lean\n",
  "@@ -439,6 +439,7 @@\n",
  "   [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "   [NormedAddCommGroup J] [NormedSpace ℝ J]\n",
  " \n",
  "+omit [NormedSpace ℝ E] in\n",
  " /-- Continuous bilinear operations preserve the cylinder Hölder bound. -/\n",
  " theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)\n",
  "     (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n",
  "@@ -492,4 +493,49 @@\n",
  " \n",
  " end Bilinear\n",
  " \n",
  "+/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "+    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "+  u := f * G.u\n",
  "+  ut := f * G.ut\n",
  "+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.ddu +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u ddf +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "+  hasFDeriv := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "+  hasFDeriv_du := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "+      rfl\n",
  "+  hasDeriv_time := by\n",
  "+    intro t ht x\n",
  "+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "+      by_cases hs : (s,x) ∈ cylinder T\n",
  "+      · simp [mul_apply, hf (s,x) hs]\n",
  "+      · simp [mul_apply, zero_off G.u hs]\n",
  "+    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "+    · funext s; exact he s\n",
  "+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:482:0: warning: automatically included section variable(s) unused in theorem `Poincare.ParabolicCutoffCommutator.norm_bilinearY_le`:\n",
  "  [NormedSpace ℝ E]\n",
  "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n",
  "  omit [NormedSpace ℝ E] in theorem ...\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:508:21: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:510:16: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:528:6: error: Tactic `simp` failed with a nested error:\n",
  "(deterministic) timeout at `simp`, maximum number of heartbeats (200000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:531:19: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n"
]
```

</details>

<details>
<summary>run-024</summary>

Source SHA-256: `7561e3747b6ea1b35ca17e7f26a78d02113868265bc604d52d9e9f19c76150bd`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-024.lean\n",
  "@@ -4,6 +4,9 @@\n",
  " import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  " \n",
  " noncomputable section\n",
  "+\n",
  "+set_option maxHeartbeats 800000\n",
  "+set_option synthInstance.maxHeartbeats 200000\n",
  " \n",
  " namespace Poincare.ParabolicCutoffCommutator\n",
  " \n",
  "@@ -478,6 +481,7 @@\n",
  "         (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩\n",
  "     ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩\n",
  " \n",
  "+omit [NormedSpace ℝ E] in\n",
  " /-- The bilinear carrier norm has an explicit product bound. -/\n",
  " theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)\n",
  "     (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:512:21: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:514:16: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:532:57: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.lsmul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [add_apply, bilinearY, ofFunction_apply, C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵l̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵,̵hf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x), hdf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x),\n",
  "  ̲  ̲ ̲ ̲ ̲ ̲hddf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x)]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-025</summary>

Source SHA-256: `48f584fe3c6378fbd8e0b6257a3f457117e4cd736a8a36b4d091fa814dec3eb1`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-025.lean\n",
  "@@ -497,49 +497,8 @@\n",
  " \n",
  " end Bilinear\n",
  " \n",
  "-/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "-    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "-  u := f * G.u\n",
  "-  ut := f * G.ut\n",
  "-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.ddu +\n",
  "-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u ddf +\n",
  "-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "-  hasFDeriv := by\n",
  "-    intro t ht x\n",
  "-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "-    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "-    · funext z\n",
  "-      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "-  hasFDeriv_du := by\n",
  "-    intro t ht x\n",
  "-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "-    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "-    · funext z\n",
  "-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "-      rfl\n",
  "-  hasDeriv_time := by\n",
  "-    intro t ht x\n",
  "-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "-      by_cases hs : (s,x) ∈ cylinder T\n",
  "-      · simp [mul_apply, hf (s,x) hs]\n",
  "-      · simp [mul_apply, zero_off G.u hs]\n",
  "-    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "-    · funext s; exact he s\n",
  "-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "-\n",
  "+\n",
  "+#synth NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "+#synth IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "+#check (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/HessianInstance.lean \n",
  "exit: 1\n",
  "ContinuousLinearMap.toNormedSpace\n",
  "/tmp/parabolic-cutoff-commutator/HessianInstance.lean:502:0: error: failed to synthesize\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n",
  "/tmp/parabolic-cutoff-commutator/HessianInstance.lean:503:7: error: Type mismatch\n",
  "  ContinuousLinearMap.lsmul ℝ ℝ\n",
  "has type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Field.toSemifield.toDivisionSemiring.toSemiring\n",
  "      Field.toSemifield.toDivisionSemiring.toSemiring (RingHom.id ℝ) ?m.69\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid ?m.69\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid\n",
  "      NormedSpace.toModule NormedSpace.toModule\n",
  "but is expected to have type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid ContinuousLinearMap.module\n",
  "      ContinuousLinearMap.module\n"
]
```

</details>

<details>
<summary>run-026</summary>

Source SHA-256: `83ae562802c41c8aead146e51f1f895c25a3e1602af986b3f96d0c1f33501714`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-026.lean\n",
  "@@ -497,8 +497,49 @@\n",
  " \n",
  " end Bilinear\n",
  " \n",
  "-\n",
  "-#synth NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "-#synth IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "-#check (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "+    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "+  u := f * G.u\n",
  "+  ut := f * G.ut\n",
  "+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "+  hasFDeriv := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "+  hasFDeriv_du := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "+      rfl\n",
  "+  hasDeriv_time := by\n",
  "+    intro t ht x\n",
  "+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "+      by_cases hs : (s,x) ∈ cylinder T\n",
  "+      · simp [mul_apply, hf (s,x) hs]\n",
  "+      · simp [mul_apply, zero_off G.u hs]\n",
  "+    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "+    · funext s; exact he s\n",
  "+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:512:21: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:514:16: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:532:57: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.lsmul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [add_apply, bilinearY, ofFunction_apply, C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵l̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵,̵hf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x), hdf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x),\n",
  "  ̲  ̲ ̲ ̲ ̲ ̲hddf (̵t̵,̵x̵)̵(̲t̲,̲ ̲x̲)̲ (hmem x)]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-027</summary>

Source SHA-256: `1d3b75f50bd10250ae9c076c0ccd56b70cde371b6e7ec53d48c22e6509d44942`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-027.lean\n",
  "@@ -497,49 +497,7 @@\n",
  " \n",
  " end Bilinear\n",
  " \n",
  "-/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "-    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "-  u := f * G.u\n",
  "-  ut := f * G.ut\n",
  "-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +\n",
  "-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +\n",
  "-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "-  hasFDeriv := by\n",
  "-    intro t ht x\n",
  "-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "-    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "-    · funext z\n",
  "-      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "-  hasFDeriv_du := by\n",
  "-    intro t ht x\n",
  "-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "-    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "-    · funext z\n",
  "-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "-      rfl\n",
  "-  hasDeriv_time := by\n",
  "-    intro t ht x\n",
  "-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "-      by_cases hs : (s,x) ∈ cylinder T\n",
  "-      · simp [mul_apply, hf (s,x) hs]\n",
  "-      · simp [mul_apply, zero_off G.u hs]\n",
  "-    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "-    · funext s; exact he s\n",
  "-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "-\n",
  "+\n",
  "+example : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/HessianInstanceDirect.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-028</summary>

Source SHA-256: `a43bbfcc21b1fe3c21e4cb5da586f91b37196b0775f913a56b64532c1eef1f77`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-028.lean\n",
  "@@ -497,7 +497,52 @@\n",
  " \n",
  " end Bilinear\n",
  " \n",
  "-\n",
  "-example : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "   .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)\n",
  "+\n",
  "+/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "+    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "+  u := f * G.u\n",
  "+  ut := f * G.ut\n",
  "+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "+  hasFDeriv := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "+  hasFDeriv_du := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "+      rfl\n",
  "+  hasDeriv_time := by\n",
  "+    intro t ht x\n",
  "+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "+      by_cases hs : (s,x) ∈ cylinder T\n",
  "+      · simp [mul_apply, hf (s,x) hs]\n",
  "+      · simp [mul_apply, zero_off G.u hs]\n",
  "+    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "+    · funext s; exact he s\n",
  "+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-029</summary>

Source SHA-256: `9ddc6238057b3f31d6b1de3c53bd4f65999133214f189391df055aac20d7a866`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-029.lean\n",
  "@@ -545,4 +545,42 @@\n",
  "     · funext s; exact he s\n",
  "     · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  " \n",
  "+/-- Equality of the four stored carriers determines a derivative graph. -/\n",
  "+theorem graph_ext_components {G H : Graph (E := E) α T}\n",
  "+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :\n",
  "+    G = H := by\n",
  "+  cases G\n",
  "+  cases H\n",
  "+  simp_all\n",
  "+\n",
  "+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/\n",
  "+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :\n",
  "+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where\n",
  "+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf\n",
  "+  map_add' G H := by\n",
  "+    apply graph_ext_components\n",
  "+    all_goals\n",
  "+      apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change _ = _\n",
  "+      simp only [cutoffGraphOfCarriers, add_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "+        ContinuousLinearMap.lsmul_apply]\n",
  "+      change _ = _\n",
  "+      simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      <;> module\n",
  "+  map_smul' c G := by\n",
  "+    apply graph_ext_components\n",
  "+    all_goals\n",
  "+      apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      simp only [cutoffGraphOfCarriers, smul_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "+        ContinuousLinearMap.lsmul_apply]\n",
  "+      simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      <;> module\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:574:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:574:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:574:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:574:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:583:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:583:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:583:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:583:6: error: `simp` made no progress\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:40: warning: This simp argument is unused:\n",
  "  smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [cutoffGraphOfCarriers, s̵mul_apply, m̵u̵l̵_̵a̵p̵p̵l̵y̵,̵ ̵bilinearY, ofFunction_apply,\n",
  "          ContinuousLinearMap.lsmul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:74: warning: This simp argument is unused:\n",
  "  ofFunction_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [cutoffGraphOfCarriers, smul_apply, mul_apply, bilinearY, ̵o̵f̵F̵u̵n̵c̵t̵i̵o̵n̵_̵a̵p̵p̵l̵y̵,̵\n",
  "          ContinuousLinearMap.lsmul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-030</summary>

Source SHA-256: `1331d5edebadbaf12f04f7092267813f74aa9c7cebdeff05a0040d92050a7149`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-030.lean\n",
  "@@ -571,7 +571,7 @@\n",
  "       simp only [cutoffGraphOfCarriers, add_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "         ContinuousLinearMap.lsmul_apply]\n",
  "       change _ = _\n",
  "-      simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "       <;> module\n",
  "   map_smul' c G := by\n",
  "     apply graph_ext_components\n",
  "@@ -580,7 +580,7 @@\n",
  "       intro p hp\n",
  "       simp only [cutoffGraphOfCarriers, smul_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "         ContinuousLinearMap.lsmul_apply]\n",
  "-      simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "       <;> module\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:565:18: error: unsolved goals\n",
  "case hu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑(G + H).u) p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑({ u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ } +\n",
  "                { u := f * H.u, ut := f * H.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑H.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).u)\n",
  "      p\n",
  "\n",
  "case hut.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑(G + H).ut) p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑({ u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ } +\n",
  "                { u := f * H.u, ut := f * H.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑H.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).ut)\n",
  "      p\n",
  "\n",
  "case hdu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑(G + H).du) p + ↑(WithLp.fst ↑(G + H).u) p • ↑(WithLp.fst ↑df) p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑({ u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ } +\n",
  "                { u := f * H.u, ut := f * H.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑H.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).du)\n",
  "      p\n",
  "\n",
  "case hddu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑(G + H).ddu) p +\n",
  "        ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑(G + H).du) p) +\n",
  "      (↑(WithLp.fst ↑(G + H).u) p • ↑(WithLp.fst ↑ddf) p +\n",
  "        ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑(G + H).du) p)) (↑(WithLp.fst ↑df) p)) =\n",
  "    ↑(WithLp.fst\n",
  "          ↑({ u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ } +\n",
  "                { u := f * H.u, ut := f * H.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑H.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).ddu)\n",
  "      p\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:19: error: unsolved goals\n",
  "case hu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑(c • G).u) p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑((RingHom.id ℝ) c •\n",
  "                { u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).u)\n",
  "      p\n",
  "\n",
  "case hut.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p * ↑(WithLp.fst ↑(c • G).ut) p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑((RingHom.id ℝ) c •\n",
  "                { u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).ut)\n",
  "      p\n",
  "\n",
  "case hdu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst\n",
  "          ↑(ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑(c • G).du) p) ⋯ ⋯ ⋯ +\n",
  "              ofFunction (fun p => ↑(WithLp.fst ↑(c • G).u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯))\n",
  "      p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑((RingHom.id ℝ) c •\n",
  "                { u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).du)\n",
  "      p\n",
  "\n",
  "case hddu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst\n",
  "          ↑(ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑(c • G).ddu) p) ⋯ ⋯ ⋯ +\n",
  "                ofFunction\n",
  "                  (fun p =>\n",
  "                    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                      (↑(WithLp.fst ↑(c • G).du) p))\n",
  "                  ⋯ ⋯ ⋯ +\n",
  "              (ofFunction (fun p => ↑(WithLp.fst ↑(c • G).u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                ofFunction\n",
  "                  (fun p =>\n",
  "                    ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑(c • G).du) p))\n",
  "                      (↑(WithLp.fst ↑df) p))\n",
  "                  ⋯ ⋯ ⋯)))\n",
  "      p =\n",
  "    ↑(WithLp.fst\n",
  "          ↑((RingHom.id ℝ) c •\n",
  "                { u := f * G.u, ut := f * G.ut,\n",
  "                  du :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p) ⋯ ⋯ ⋯ +\n",
  "                      ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p) ⋯ ⋯ ⋯,\n",
  "                  ddu :=\n",
  "                    ofFunction (fun p => ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p))\n",
  "                              (↑(WithLp.fst ↑G.du) p))\n",
  "                          ⋯ ⋯ ⋯ +\n",
  "                      (ofFunction (fun p => ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p) ⋯ ⋯ ⋯ +\n",
  "                        ofFunction\n",
  "                          (fun p =>\n",
  "                            ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p))\n",
  "                              (↑(WithLp.fst ↑df) p))\n",
  "                          ⋯ ⋯ ⋯),\n",
  "                  zero_trace := ⋯, hasFDeriv := ⋯, hasFDeriv_du := ⋯, hasDeriv_time := ⋯ }).ddu)\n",
  "      p\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:40: warning: This simp argument is unused:\n",
  "  smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [cutoffGraphOfCarriers, s̵mul_apply, m̵u̵l̵_̵a̵p̵p̵l̵y̵,̵ ̵bilinearY, ofFunction_apply,\n",
  "          ContinuousLinearMap.lsmul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:74: warning: This simp argument is unused:\n",
  "  ofFunction_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [cutoffGraphOfCarriers, smul_apply, mul_apply, bilinearY, ̵o̵f̵F̵u̵n̵c̵t̵i̵o̵n̵_̵a̵p̵p̵l̵y̵,̵\n",
  "          ContinuousLinearMap.lsmul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-031</summary>

Source SHA-256: `0a47216d74a560e1f09f090501926b222464be3f165cce0553274316bba12b61`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-031.lean\n",
  "@@ -564,23 +564,47 @@\n",
  "   toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf\n",
  "   map_add' G H := by\n",
  "     apply graph_ext_components\n",
  "-    all_goals\n",
  "-      apply ParabolicHolder.ext\n",
  "-      intro p hp\n",
  "-      change _ = _\n",
  "-      simp only [cutoffGraphOfCarriers, add_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "-        ContinuousLinearMap.lsmul_apply]\n",
  "-      change _ = _\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))\n",
  "       try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> module\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))\n",
  "+      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)\n",
  "+      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))\n",
  "+      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      <;> first | ring | module\n",
  "   map_smul' c G := by\n",
  "     apply graph_ext_components\n",
  "-    all_goals\n",
  "-      apply ParabolicHolder.ext\n",
  "-      intro p hp\n",
  "-      simp only [cutoffGraphOfCarriers, smul_apply, mul_apply, bilinearY, ofFunction_apply,\n",
  "-        ContinuousLinearMap.lsmul_apply]\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (c • G.u p) = c • (f p * (G.u p))\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> module\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (c • G.ut p) = c • (f p * (G.ut p))\n",
  "+      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)\n",
  "+      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      <;> first | ring | module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))\n",
  "+      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      <;> first | ring | module\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:577:4: error: unsolved goals\n",
  "case hdu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • (↑(WithLp.fst ↑G.du) p + ↑(WithLp.fst ↑H.du) p) +\n",
  "      (↑(WithLp.fst ↑G.u) p + ↑(WithLp.fst ↑H.u) p) • ↑(WithLp.fst ↑df) p =\n",
  "    ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p + ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p +\n",
  "      (↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.du) p + ↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑df) p)\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:582:4: error: unsolved goals\n",
  "case hddu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "G H : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • (↑(WithLp.fst ↑G.ddu) p + ↑(WithLp.fst ↑H.ddu) p) +\n",
  "        (((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑G.du) p) +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑H.du) p)) +\n",
  "      ((↑(WithLp.fst ↑G.u) p + ↑(WithLp.fst ↑H.u) p) • ↑(WithLp.fst ↑ddf) p +\n",
  "        (((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p)) (↑(WithLp.fst ↑df) p) +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p)) (↑(WithLp.fst ↑df) p))) =\n",
  "    ↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑G.du) p) +\n",
  "        (↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p)) (↑(WithLp.fst ↑df) p)) +\n",
  "      (↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑H.ddu) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑H.du) p) +\n",
  "        (↑(WithLp.fst ↑H.u) p • ↑(WithLp.fst ↑ddf) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑H.du) p)) (↑(WithLp.fst ↑df) p)))\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:599:4: error: unsolved goals\n",
  "case hdu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • c • ↑(WithLp.fst ↑G.du) p + (↑(WithLp.fst ↑G.u) p * c) • ↑(WithLp.fst ↑df) p =\n",
  "    c • (↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.du) p + ↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑df) p)\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:604:4: error: unsolved goals\n",
  "case hddu.h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "c : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × E\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑f) p • c • ↑(WithLp.fst ↑G.ddu) p +\n",
  "        c • ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑G.du) p) +\n",
  "      ((↑(WithLp.fst ↑G.u) p * c) • ↑(WithLp.fst ↑ddf) p +\n",
  "        c • ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p)) (↑(WithLp.fst ↑df) p)) =\n",
  "    c •\n",
  "      (↑(WithLp.fst ↑f) p • ↑(WithLp.fst ↑G.ddu) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑df) p)) (↑(WithLp.fst ↑G.du) p) +\n",
  "        (↑(WithLp.fst ↑G.u) p • ↑(WithLp.fst ↑ddf) p +\n",
  "          ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (↑(WithLp.fst ↑G.du) p)) (↑(WithLp.fst ↑df) p)))\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-032</summary>

Source SHA-256: `8c177a84833bfd5f34924d24b6f74062cbb671dce869ea067e87fe6d6dc614b0`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-032.lean\n",
  "@@ -568,43 +568,43 @@\n",
  "       intro p hp\n",
  "       change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))\n",
  "       try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))\n",
  "       try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)\n",
  "       try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))\n",
  "       try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "   map_smul' c G := by\n",
  "     apply graph_ext_components\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (c • G.u p) = c • (f p * (G.u p))\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (c • G.ut p) = c • (f p * (G.ut p))\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | ring | module\n",
  "+      <;> first | (solve | ring) | module\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:586:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:603:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:608:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n"
]
```

</details>

<details>
<summary>run-033</summary>

Source SHA-256: `b8079b26161888bd313856d5f828b466fa36b1f421e5c4c4e59159f18f8beb27`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-033.lean\n",
  "@@ -607,4 +607,86 @@\n",
  "       try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "       <;> first | (solve | ring) | module\n",
  " \n",
  "+/-- The cutoff graph map is bounded in the original four-component norm. -/\n",
  "+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :\n",
  "+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,\n",
  "+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by\n",
  "+  let L1 := ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] ℝ)\n",
  "+  let L2 := ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)\n",
  "+  let Q := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "+  let A := ‖f‖ + ‖df‖ + ‖ddf‖\n",
  "+  let B := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖\n",
  "+  have hA : 0 ≤ A := by dsimp [A]; positivity\n",
  "+  have hB : 0 ≤ B := by dsimp [B]; positivity\n",
  "+  have hfA : ‖f‖ ≤ A := by dsimp [A]; positivity\n",
  "+  have hdfA : ‖df‖ ≤ A := by dsimp [A]; linarith [norm_nonneg f, norm_nonneg ddf]\n",
  "+  have hddfA : ‖ddf‖ ≤ A := by dsimp [A]; linarith [norm_nonneg f, norm_nonneg df]\n",
  "+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]\n",
  "+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]\n",
  "+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]\n",
  "+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]\n",
  "+  refine ⟨20 * B * A, ?_⟩\n",
  "+  intro G\n",
  "+  have hGu := norm_u_le G\n",
  "+  have hGut := norm_ut_le G\n",
  "+  have hGdu := norm_du_le G\n",
  "+  have hGddu := norm_ddu_le G\n",
  "+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _\n",
  "+      _ ≤ B * A * ‖G‖ := by\n",
  "+        calc\n",
  "+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA\n",
  "+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]\n",
  "+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _\n",
  "+      _ ≤ B * A * ‖G‖ := by\n",
  "+        calc\n",
  "+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA\n",
  "+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]\n",
  "+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  rw [ParabolicSolutionGraph.norm_eq]\n",
  "+  change ‖f * G.u‖ + ‖f * G.ut‖ +\n",
  "+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +\n",
  "+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +\n",
  "+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _\n",
  "+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)\n",
  "+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)\n",
  "+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)\n",
  "+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)\n",
  "+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)\n",
  "+  nlinarith\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:570:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:575:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:21: warning: This simp argument is unused:\n",
  "  map_add\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵a̵d̵d̵,̵ ̵ContinuousLinearMap.add_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:580:30: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.add_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_add,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵a̵d̵d̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:592:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:597:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:21: warning: This simp argument is unused:\n",
  "  map_smul\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [m̵a̵p̵_̵s̵m̵u̵l̵,̵ ̵ContinuousLinearMap.smul_apply]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:602:31: warning: This simp argument is unused:\n",
  "  ContinuousLinearMap.smul_apply\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [map_smul,̵ ̵C̵o̵n̵t̵i̵n̵u̵o̵u̵s̵L̵i̵n̵e̵a̵r̵M̵a̵p̵.̵s̵m̵u̵l̵_̵a̵p̵p̵l̵y̵]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:35: warning: this tactic is never executed\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unreachableTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:581:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:586:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:603:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:608:6: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:571:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:576:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:593:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:598:35: warning: 'module' tactic does nothing\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedTactic false`\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:623:29: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:625:35: error: failed to prove positivity/nonnegativity/nonzeroness\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:626:38: error: not a positivity goal\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:627:40: error: linarith failed to find a contradiction\n",
  "case h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "Q : StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "A : ℝ := ‖f‖ + ‖df‖ + ‖ddf‖\n",
  "B : ℝ := 1 + ‖L1‖ + ‖L2‖ + sorry\n",
  "hA : 0 ≤ A\n",
  "hB : 0 ≤ B\n",
  "hfA : ‖f‖ ≤ A\n",
  "a✝ : ‖↑f‖ + ‖↑df‖ + ‖↑ddf‖ < ‖↑df‖\n",
  "⊢ False\n",
  "failed\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:628:42: error: linarith failed to find a contradiction\n",
  "case h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "Q : StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "A : ℝ := ‖f‖ + ‖df‖ + ‖ddf‖\n",
  "B : ℝ := 1 + ‖L1‖ + ‖L2‖ + sorry\n",
  "hA : 0 ≤ A\n",
  "hB : 0 ≤ B\n",
  "hfA : ‖f‖ ≤ A\n",
  "hdfA : ‖df‖ ≤ A\n",
  "a✝ : ‖↑f‖ + ‖↑df‖ + ‖↑ddf‖ < ‖↑ddf‖\n",
  "⊢ False\n",
  "failed\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:629:65: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:630:65: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:631:12: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:632:78: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (StrongDual ℝ E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:662:23: error: Application type mismatch: The argument\n",
  "  L2\n",
  "has type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Field.toSemifield.toDivisionSemiring.toSemiring\n",
  "      Field.toSemifield.toDivisionSemiring.toSemiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace ContinuousLinearMap.toSeminormedAddCommGroup.toAddCommMonoid\n",
  "      (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      (@UniformSpace.toTopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "        (@PseudoMetricSpace.toUniformSpace (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "          (@SeminormedAddCommGroup.toPseudoMetricSpace (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "            ContinuousLinearMap.toSeminormedAddCommGroup)))\n",
  "      ContinuousLinearMap.toSeminormedAddCommGroup.toAddCommMonoid ContinuousLinearMap.toNormedSpace.toModule\n",
  "      ContinuousLinearMap.toNormedSpace.toModule\n",
  "but is expected to have type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace ContinuousLinearMap.toNormedAddCommGroup.toAddCommMonoid\n",
  "      ?m.1039\n",
  "      (@UniformSpace.toTopologicalSpace ?m.1039\n",
  "        (@PseudoMetricSpace.toUniformSpace ?m.1039\n",
  "          (@SeminormedAddCommGroup.toPseudoMetricSpace ?m.1039 NormedAddCommGroup.toSeminormedAddCommGroup)))\n",
  "      NormedAddCommGroup.toAddCommGroup.toAddCommMonoid ContinuousLinearMap.toNormedSpace.toModule NormedSpace.toModule\n",
  "in the application\n",
  "  bilinearY L2\n"
]
```

</details>

<details>
<summary>run-034</summary>

Source SHA-256: `1625e4e1cff3a942da1595ca1e2e8a1b60272e83a6590c0b94cd31dacef348c7`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-034.lean\n",
  "@@ -567,45 +567,40 @@\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))\n",
  "-      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      ring\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))\n",
  "-      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      ring\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)\n",
  "-      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))\n",
  "-      try simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      module\n",
  "   map_smul' c G := by\n",
  "     apply graph_ext_components\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (c • G.u p) = c • (f p * (G.u p))\n",
  "-      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      ring\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p * (c • G.ut p) = c • (f p * (G.ut p))\n",
  "-      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      ring\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)\n",
  "-      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      module\n",
  "     · apply ParabolicHolder.ext\n",
  "       intro p hp\n",
  "       change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))\n",
  "-      try simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "-      <;> first | (solve | ring) | module\n",
  "+      simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      module\n",
  "+\n",
  " \n",
  " /-- The cutoff graph map is bounded in the original four-component norm. -/\n",
  " theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "@@ -616,16 +611,18 @@\n",
  "     (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :\n",
  "     ∃ C : ℝ, ∀ G : Graph (E := E) α T,\n",
  "       ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by\n",
  "-  let L1 := ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] ℝ)\n",
  "-  let L2 := ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)\n",
  "-  let Q := ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance\n",
  "+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "   let A := ‖f‖ + ‖df‖ + ‖ddf‖\n",
  "   let B := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖\n",
  "   have hA : 0 ≤ A := by dsimp [A]; positivity\n",
  "   have hB : 0 ≤ B := by dsimp [B]; positivity\n",
  "-  have hfA : ‖f‖ ≤ A := by dsimp [A]; positivity\n",
  "-  have hdfA : ‖df‖ ≤ A := by dsimp [A]; linarith [norm_nonneg f, norm_nonneg ddf]\n",
  "-  have hddfA : ‖ddf‖ ≤ A := by dsimp [A]; linarith [norm_nonneg f, norm_nonneg df]\n",
  "+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]\n",
  "+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]\n",
  "+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]\n",
  "   have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]\n",
  "   have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]\n",
  "   have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:616:68: error: Type mismatch\n",
  "  ContinuousLinearMap.lsmul ℝ ℝ\n",
  "has type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Field.toSemifield.toDivisionSemiring.toSemiring\n",
  "      Field.toSemifield.toDivisionSemiring.toSemiring (RingHom.id ℝ) ?m.278\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid ?m.278\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid\n",
  "      NormedSpace.toModule NormedSpace.toModule\n",
  "but is expected to have type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid ContinuousLinearMap.module\n",
  "      ContinuousLinearMap.module\n"
]
```

</details>

<details>
<summary>run-035</summary>

Source SHA-256: `0227a3b723b0fbea564f7c2d51fb9406ae2bf464ecdfb087c0d9f2476a945276`.

```diff
--- preceding snapshot
+++ run-035.lean
@@ -613,7 +613,8 @@
       ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
   letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
   let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
   let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
     ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
   let A := ‖f‖ + ‖df‖ + ‖ddf‖
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:621:15: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:621:22: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:621:29: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:627:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:627:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:628:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:628:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:629:12: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:629:47: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:630:46: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  SeminormedAddGroup (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:643:89: error: Application type mismatch: The argument\n",
  "  norm_nonneg G\n",
  "has type\n",
  "  (0 : ℝ) ≤ ‖G‖\n",
  "but is expected to have type\n",
  "  (0 : ℕ) ≤ ?m.799\n",
  "in the application\n",
  "  mul_nonneg ?m.802 (norm_nonneg G)\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:650:89: error: Application type mismatch: The argument\n",
  "  norm_nonneg G\n",
  "has type\n",
  "  (0 : ℝ) ≤ ‖G‖\n",
  "but is expected to have type\n",
  "  (0 : ℕ) ≤ ?m.941\n",
  "in the application\n",
  "  mul_nonneg ?m.944 (norm_nonneg G)\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:653:34: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:654:29: error: unsolved goals\n",
  "case h₁.h₁.hbc\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "this : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ⋯\n",
  "L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "A : ℝ := ⋯\n",
  "B : ℕ := ⋯\n",
  "hA : 0 ≤ A\n",
  "hB : 0 ≤ B\n",
  "hfA : ‖f‖ ≤ A\n",
  "hdfA : ‖df‖ ≤ A\n",
  "hddfA : ‖ddf‖ ≤ A\n",
  "hL1 : sorry ≤ B\n",
  "hL2 : sorry ≤ B\n",
  "hQ : sorry ≤ B\n",
  "hB1 : 1 ≤ B\n",
  "G : Graph α T\n",
  "hGu : ‖G.u‖ ≤ ‖G‖\n",
  "hGut : ‖G.ut‖ ≤ ‖G‖\n",
  "hGdu : ‖G.du‖ ≤ ‖G‖\n",
  "hGddu : ‖G.ddu‖ ≤ ‖G‖\n",
  "hu : ‖f * G.u‖ ≤ ↑B * A * ‖G‖\n",
  "hut : ‖f * G.ut‖ ≤ ↑B * A * ‖G‖\n",
  "⊢ sorry ≤ ↑B\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:657:34: error(lean.synthInstanceFailed): failed to synthesize instance of type class\n",
  "  Norm (ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)\n",
  "\n",
  "Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:658:29: error: unsolved goals\n",
  "case h₁.h₁.hbc\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "ψ : E → ℝ\n",
  "hψ : ContDiff ℝ ∞ ψ\n",
  "f : Y α T ℝ\n",
  "df : Y α T (E →L[ℝ] ℝ)\n",
  "ddf : Y α T (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "hf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑f) p = ψ p.2\n",
  "hdf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑df) p = fderiv ℝ ψ p.2\n",
  "hddf : ∀ p ∈ cylinder T, ↑(WithLp.fst ↑ddf) p = fderiv ℝ (fderiv ℝ ψ) p.2\n",
  "this : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ⋯\n",
  "L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := ⋯\n",
  "A : ℝ := ⋯\n",
  "B : ℕ := ⋯\n",
  "hA : 0 ≤ A\n",
  "hB : 0 ≤ B\n",
  "hfA : ‖f‖ ≤ A\n",
  "hdfA : ‖df‖ ≤ A\n",
  "hddfA : ‖ddf‖ ≤ A\n",
  "hL1 : sorry ≤ B\n",
  "hL2 : sorry ≤ B\n",
  "hQ : sorry ≤ B\n",
  "hB1 : 1 ≤ B\n",
  "G : Graph α T\n",
  "hGu : ‖G.u‖ ≤ ‖G‖\n",
  "hGut : ‖G.ut‖ ≤ ‖G‖\n",
  "hGdu : ‖G.du‖ ≤ ‖G‖\n",
  "hGddu : ‖G.ddu‖ ≤ ‖G‖\n",
  "hu : ‖f * G.u‖ ≤ ↑B * A * ‖G‖\n",
  "hut : ‖f * G.ut‖ ≤ ↑B * A * ‖G‖\n",
  "ha : ‖bilinearY L1 f G.du‖ ≤ 3 * ↑B * A * ‖G‖\n",
  "⊢ sorry ≤ ↑B\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:660:23: error: Application type mismatch: The argument\n",
  "  L2\n",
  "has type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      ContinuousLinearMap.topologicalSpace ContinuousLinearMap.addCommMonoid ContinuousLinearMap.module\n",
  "      ContinuousLinearMap.module\n",
  "but is expected to have type\n",
  "  ℝ →L[ℝ]\n",
  "    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (E →L[ℝ] E →L[ℝ] ℝ)\n",
  "      PseudoMetricSpace.toUniformSpace.toTopologicalSpace ContinuousLinearMap.toNormedAddCommGroup.toAddCommMonoid\n",
  "      ?m.1295 PseudoMetricSpace.toUniformSpace.toTopologicalSpace NormedAddCommGroup.toAddCommGroup.toAddCommMonoid\n",
  "      ContinuousLinearMap.toNormedSpace.toModule NormedSpace.toModule\n",
  "in the application\n",
  "  bilinearY L2\n"
]
```

</details>

<details>
<summary>run-036</summary>

Source SHA-256: `4617430386744c46ff50883a4e5ec77761ca6388b3a432ca0c63c8e8ec4d7fba`.

```diff
--- preceding snapshot
+++ run-036.lean
@@ -611,14 +611,17 @@
     (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
     ∃ C : ℝ, ∀ G : Graph (E := E) α T,
       ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
   letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
   let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
   let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
     ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
   let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
     ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
   let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
   have hA : 0 ≤ A := by dsimp [A]; positivity
   have hB : 0 ≤ B := by dsimp [B]; positivity
   have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:679:32: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (800000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:680:18: error: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (800000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:605:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n"
]
```

</details>

<details>
<summary>run-037</summary>

Source SHA-256: `f068bc2cca1282f9b602b4f9d157651286ac956050b3e5a01448efeb4fd05683`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-037.lean\n",
  "@@ -602,6 +602,7 @@\n",
  "       module\n",
  " \n",
  " \n",
  "+set_option maxHeartbeats 4000000 in\n",
  " /-- The cutoff graph map is bounded in the original four-component norm. -/\n",
  " theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "     (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-038</summary>

Source SHA-256: `4cceb57622303f03f5ccc3239fd3137cecb51f4edd3e5c3e75e5cbd99f9442e2`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-038.lean\n",
  "@@ -691,4 +691,46 @@\n",
  "   have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)\n",
  "   nlinarith\n",
  " \n",
  "+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/\n",
  "+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,\n",
  "+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧\n",
  "+      (∀ G t, t ∈ Icc 0 T → ∀ x,\n",
  "+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧\n",
  "+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧\n",
  "+        (C G).ddu (t,x) =\n",
  "+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +\n",
  "+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +\n",
  "+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by\n",
  "+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1\n",
  "+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T\n",
  "+  have hf := fun p hp => (heq p hp).1\n",
  "+  have hdf := fun p hp => (heq p hp).2.1\n",
  "+  have hddf := fun p hp => (heq p hp).2.2\n",
  "+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf\n",
  "+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf\n",
  "+  let C := L.mkContinuous B hB\n",
  "+  refine ⟨C, ?_, ?_⟩\n",
  "+  · intro G p\n",
  "+    change f p * G.u p = ψ p.2 * G.u p\n",
  "+    by_cases hp : p ∈ cylinder T\n",
  "+    · rw [hf p hp]\n",
  "+    · simp [zero_off G.u hp]\n",
  "+  · intro G t ht x\n",
  "+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩\n",
  "+    change f (t,x) * G.ut (t,x) = _ ∧\n",
  "+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _\n",
  "+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) hp, hdf (t,x) hp]\n",
  "+    · change ((bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.ddu +\n",
  "+        bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "+        (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u ddf +\n",
  "+        bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)) (t,x) = _\n",
  "+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]\n",
  "+      rfl\n",
  "+\n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 1\n",
  "Poincare/Global/ParabolicCutoffCommutator.lean:728:13: error: Function expected at\n",
  "  bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.ddu + bilinearY ?m.616 df G.du +\n",
  "    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u ddf + bilinearY ?m.678 G.du df)\n",
  "but this term has type\n",
  "  ?m.694\n",
  "\n",
  "Note: Expected a function because this term is being applied to the argument\n",
  "  (t, x)\n"
]
```

</details>

<details>
<summary>run-039</summary>

Source SHA-256: `5bacded4042caff1cdbfb7dcc5604ee076f794307a30d58aef16ae3519d0a082`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-039.lean\n",
  "@@ -725,11 +725,8 @@\n",
  "     refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩\n",
  "     · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "         hf (t,x) hp, hdf (t,x) hp]\n",
  "-    · change ((bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.ddu +\n",
  "-        bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "-        (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u ddf +\n",
  "-        bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)) (t,x) = _\n",
  "-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _\n",
  "+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "         hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]\n",
  "       rfl\n",
  " \n"
]
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean -o .lake/build/lib/lean/Poincare/Global/ParabolicCutoffCommutator.olean
exit: 0
```

</details>

<details>
<summary>run-040</summary>

Source SHA-256: `b36359b79da42a1561c3e9abb56d41d3e38a4a6a7b79d3a008b71efd3f3a39d3`.

```diff
--- preceding snapshot
+++ run-040.lean
@@ -1,733 +1,16 @@
-import Poincare.Global.ParabolicHolderMultiplier
-import Poincare.Global.DuhamelSolutionOperatorBound
-import Mathlib.Analysis.Calculus.MeanValue
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-
-noncomputable section
-
-set_option maxHeartbeats 800000
-set_option synthInstance.maxHeartbeats 200000
-
-namespace Poincare.ParabolicCutoffCommutator
-
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-
-/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
-theorem quadratic_remainder
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
-    (x v : E) (hv : ‖v‖ = 1) :
-    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
-  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
-    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
-      convex_univ (mem_univ x) (mem_univ y)
-  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
-      (dh (x + s • v) v) s := by
-    simpa using (hd (x + s • v)).comp_hasDerivAt s
-      (((hasDerivAt_id s).smul_const v).const_add x)
-  have hdr (s : ℝ) : HasDerivAt
-      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
-      (dh (x + s • v) v - dh x v) s := by
-    simpa using ((hdline s).sub_const (h x)).sub
-      ((hasDerivAt_id s).mul_const (dh x v))
-  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
-    simp only [id_eq]
-    ring
-  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
-    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
-    (fun s _ => (hdr s).hasDerivWithinAt)
-    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
-    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
-  · exact hr
-  · calc
-      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
-      _ ≤ ‖dh (x + s • v) - dh x‖ := by
-        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
-      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
-
-/-- The finite-difference estimate with an arbitrary positive step. -/
-theorem finite_difference_derivative
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
-    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
-    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
-  have hr := quadratic_remainder hd hdd hb hη.le x v hv
-  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
-    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
-  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
-    calc
-      |η * dh x v| = |(h (x + η • v) - h x) -
-          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
-      _ ≤ |h (x + η • v) - h x| +
-          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
-      _ ≤ _ := add_le_add hu hr
-  rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_iff_right₀ hη).mp
-  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
-    field_simp
-  rw [he]
-  nlinarith
-
-/-- Optimizing the step gives a square-root bound on the full derivative. -/
-theorem derivative_norm_le_sqrt
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hδ : 0 < δ) (hM : 0 ≤ M)
-    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
-    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
-  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
-  intro v hv
-  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
-  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
-      3 * Real.sqrt δ * M := by
-    have hs := Real.sq_sqrt hδ.le
-    have hp := Real.sqrt_pos.mpr hδ
-    field_simp
-    nlinarith [congrArg (fun z : ℝ => z * M) hs]
-  exact h.trans_eq he
-
-variable {α T : ℝ}
-
-/-- Time increments of the value are controlled by the stored time derivative. -/
-theorem value_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
-  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-    (fun r hr => G.hasDeriv_time r hr x)
-    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
-  simpa only [Real.norm_eq_abs, mul_comm] using h
-
-/-- The gradient of any derivative graph is uniformly small at short times. -/
-theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
-    (norm_nonneg G) ?_ ?_ x
-  · intro y
-    calc
-      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
-      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
-  · intro y
-    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
-
-/-- The supremum of the gradient has the same square-root gain. -/
-theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
-    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply csSup_le (insert_nonempty _ _)
-  rintro r (rfl | ⟨p, rfl⟩)
-  · positivity
-  · exact gradient_bound G hT p.property.1 p.val.2
-
-/-- Time differences of the gradient require no mixed time-space derivative. -/
-theorem gradient_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
-  by_cases hst : t = s
-  · simp [hst]
-  · apply derivative_norm_le_sqrt
-      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
-      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
-      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
-      (value_time_increment G hs ht) ?_ x
-    intro y
-    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
-      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
-
-/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
-theorem gradient_space_increment (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
-    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Spatial value increments inherit the improved gradient bound. -/
-theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
-    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Split a power at a larger positive scale. -/
-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
-    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
-    r ^ b ≤ R ^ (b - a) * r ^ a := by
-  have he : r ^ b = r ^ (b - a) * r ^ a := by
-    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
-    congr 1
-    ring
-  rw [he]
-  exact mul_le_mul_of_nonneg_right
-    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
-
-/-- Interpolate a Lipschitz bound and a bound at scale R. -/
-theorem scale_interpolation {a L r R α : ℝ}
-    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
-    (hl : a ≤ L * r) (hb : a ≤ L * R) :
-    a ≤ L * R ^ (1 - α) * r ^ α := by
-  by_cases h : r ≤ R
-  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
-    rw [Real.rpow_one] at hp
-    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
-  · have he : R ^ (1 - α) * R ^ α = R := by
-      rw [← Real.rpow_add hR]
-      convert Real.rpow_one R using 2
-      ring
-    calc
-      a ≤ L * R := hb
-      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
-      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
-        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
-
-/-- The parabolic spatial scale is the square root of the time scale. -/
-theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
-    (Real.sqrt T) ^ p = T ^ (p / 2) := by
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
-  congr 1
-  ring
-
-/-- Spatial Hölder gradient increments carry the desired positive time power. -/
-theorem gradient_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤
-      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
-    (L := 6 * ‖G‖) (by positivity)
-    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
-    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
-      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
-  rw [sqrt_rpow hT.le] at h
-  nlinarith [h]
-
-/-- Spatial Hölder value increments gain one additional half power of time. -/
-theorem value_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤
-      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
-    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
-  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
-    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
-    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    (value_space_increment G hT ht x y)
-    ((abs_sub _ _).trans (by
-      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
-      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
-  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
-    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
-    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
-    rw [sqrt_rpow hT.le]
-    congr 1
-    ring
-  calc
-    |G.u (t,x) - G.u (t,y)| ≤ _ := h
-    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
-        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
-
-/-- The temporal Hölder gradient bound follows from the square-root increment. -/
-theorem gradient_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤
-      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
-    (show (0 : ℝ) < 1 / 2 by norm_num)
-  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
-  have hi := gradient_time_increment G hs ht x
-  rw [Real.sqrt_eq_rpow] at hi
-  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
-
-/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
-theorem value_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤
-      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
-  rw [Real.rpow_one] at hp
-  exact (value_time_increment G hs ht x).trans (by
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
-
-omit [NormedSpace ℝ E] in
-/-- Split a mixed increment through the point with the first time and second position. -/
-theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
-    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
-    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
-      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
-    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
-      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
-    HasHolderBound α (cylinder T) f (Kx + Kt) := by
-  intro p hp q hq
-  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
-    Real.rpow_le_rpow (norm_nonneg _) (by
-      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
-  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
-    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
-    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
-      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
-  calc
-    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
-      norm_sub_le_norm_sub_add_norm_sub _ _ _
-    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
-      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
-    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
-      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
-
-/-- Full gradient Hölder control, including mixed increments. -/
-theorem gradient_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
-  have h := holder_of_increments hα.le
-    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (fun t ht => gradient_space_holder G hα hα1 hT ht)
-    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
-  convert h using 1
-  ring
-
-/-- Full value Hölder control with its stronger time power. -/
-theorem value_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
-  have h := holder_of_increments (f := G.u) hα.le
-    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
-    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
-    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
-    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
-  convert h using 1
-  ring
-
-/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
-theorem interpolation_bounds (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
-  constructor
-  · have h := ParabolicHolder.norm_le_of_bounds G.u
-      (show 0 ≤ T * ‖G‖ by positivity)
-      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
-      (fun p hp => (time_bound G hp.1 p.2).trans
-        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
-      (value_holder G hα hα1 hT)
-    have hp : T ≤ T ^ (1-α/2) := by
-      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
-      exact (Real.rpow_one T).symm
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
-      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
-  · have h := ParabolicHolder.norm_le_of_bounds G.du
-      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
-      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-      (fun p hp => gradient_bound G hT hp.1 p.2)
-      (gradient_holder G hα hα1 hT)
-    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
-      rw [Real.sqrt_eq_rpow]
-      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
-
-/-- A universal constant satisfies the frozen interpolation target. -/
-theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
-      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
-  intro α hα hα1
-  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
-
-/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
-theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
-    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
-      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
-  classical
-  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
-  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
-  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
-  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
-    have h := scale_interpolation (L := 2*A+B) (R := 1)
-      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
-      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
-      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
-    simpa using h
-  refine ⟨A + (2*A+B), by positivity, ?_⟩
-  intro T
-  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
-  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
-    intro p hp; simp [f, hp]
-  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
-    intro p hp; simpa [f, hp] using hA p.2
-  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
-    intro p hp q hq
-    simp only [f, if_pos hp, if_pos hq]
-    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
-      (Real.rpow_le_rpow (norm_nonneg _) (by
-        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
-  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
-  refine ⟨fY, ?_, ?_⟩
-  · intro p hp
-    change f p = ψ p.2
-    simp [f, hp]
-  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
-
-/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
-theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
-    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
-      ∃ (f : Y (E := E) α T ℝ)
-        (df : Y (E := E) α T (E →L[ℝ] ℝ))
-        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
-      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
-        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
-      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
-  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
-  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
-  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
-  refine ⟨K0+K1+K2, by positivity, ?_⟩
-  intro T
-  obtain ⟨f, hf, hfb⟩ := h0 T
-  obtain ⟨df, hdf, hdfb⟩ := h1 T
-  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
-  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
-
-/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
-theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z * G.u (t,z))
-      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
-  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
-
-/-- The second spatial product rule includes both mixed Hessian terms. -/
-theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
-      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
-    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
-
-/-- A spatial cutoff is constant in the within-time product rule. -/
-theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
-  (G.hasDeriv_time t ht x).const_mul (ψ x)
-
-section Bilinear
-variable {F H J : Type*}
-  [NormedAddCommGroup F] [NormedSpace ℝ F]
-  [NormedAddCommGroup H] [NormedSpace ℝ H]
-  [NormedAddCommGroup J] [NormedSpace ℝ J]
-
-omit [NormedSpace ℝ E] in
-/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
-theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
-  intro p hp q hq
-  have hf := ParabolicHolder.holder_le f hp hq
-  have hg := ParabolicHolder.holder_le g hp hq
-  have hf0 := ParabolicHolder.norm_le f p
-  have hg0 := ParabolicHolder.norm_le g q
-  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
-  calc
-    ‖B (f p) (g p) - B (f q) (g q)‖ =
-        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
-      congr 1
-      simp only [map_sub, ContinuousLinearMap.sub_apply]
-      abel
-    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
-    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
-      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
-    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
-        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
-      apply add_le_add
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
-          (norm_nonneg _) (by positivity)
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
-          (norm_nonneg _) (by positivity)
-    _ = _ := by ring
-
-/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
-def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
-  ofFunction (fun p => B (f p) (g p))
-    (fun p hp => by simp [zero_off f hp])
-    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
-    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
-
-omit [NormedSpace ℝ E] in
-/-- The bilinear carrier norm has an explicit product bound. -/
-theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
-    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
-    (bilinear_holder B f g)
-  nlinarith [h]
-
-end Bilinear
-
-local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
-  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
-
-/-- Assemble the cutoff graph from its three spatial carriers. -/
-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
-    (G : Graph (E := E) α T) : Graph (E := E) α T where
-  u := f * G.u
-  ut := f * G.ut
-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
-  hasFDeriv := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv hψ G ht x using 1
-    · funext z
-      simp only [mul_apply, hf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
-  hasFDeriv_du := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv_du hψ G ht x using 1
-    · funext z
-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
-      rfl
-  hasDeriv_time := by
-    intro t ht x
-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
-      by_cases hs : (s,x) ∈ cylinder T
-      · simp [mul_apply, hf (s,x) hs]
-      · simp [mul_apply, zero_off G.u hs]
-    convert cutoff_hasDeriv_time ψ G ht x using 1
-    · funext s; exact he s
-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
-
-/-- Equality of the four stored carriers determines a derivative graph. -/
-theorem graph_ext_components {G H : Graph (E := E) α T}
-    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
-    G = H := by
-  cases G
-  cases H
-  simp_all
-
-/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
-def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
-  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
-  map_add' G H := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
-      simp only [map_add, ContinuousLinearMap.add_apply]
-      module
-  map_smul' c G := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.u p) = c • (f p * (G.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.ut p) = c • (f p * (G.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
-      simp only [map_smul, ContinuousLinearMap.smul_apply]
-      module
-
-
-set_option maxHeartbeats 4000000 in
-/-- The cutoff graph map is bounded in the original four-component norm. -/
-theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
-      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
-  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
-  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
-  let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
-  have hA : 0 ≤ A := by dsimp [A]; positivity
-  have hB : 0 ≤ B := by dsimp [B]; positivity
-  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
-  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
-  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
-  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
-  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
-  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
-  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
-  refine ⟨20 * B * A, ?_⟩
-  intro G
-  have hGu := norm_u_le G
-  have hGut := norm_ut_le G
-  have hGdu := norm_du_le G
-  have hGddu := norm_ddu_le G
-  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  rw [ParabolicSolutionGraph.norm_eq]
-  change ‖f * G.u‖ + ‖f * G.ut‖ +
-    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
-    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
-      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
-  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
-  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
-    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
-  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
-  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
-  nlinarith
-
-/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
-theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
-    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
-        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
-        (C G).ddu (t,x) =
-          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
-  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
-  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
-  have hf := fun p hp => (heq p hp).1
-  have hdf := fun p hp => (heq p hp).2.1
-  have hddf := fun p hp => (heq p hp).2.2
-  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
-  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
-  let C := L.mkContinuous B hB
-  refine ⟨C, ?_, ?_⟩
-  · intro G p
-    change f p * G.u p = ψ p.2 * G.u p
-    by_cases hp : p ∈ cylinder T
-    · rw [hf p hp]
-    · simp [zero_off G.u hp]
-  · intro G t ht x
-    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
-    change f (t,x) * G.ut (t,x) = _ ∧
-      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
-    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp]
-    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
-      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
-      rfl
-
-end Poincare.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicCutoffCommutator
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
+    | throwError "module not found"
+  let mut count := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      count := count + 1
+      elabCommand (← `(command| #print axioms $(mkIdent n)))
+      unless axs.size == 3 && axs.contains ``propext &&
+          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected foundational dependencies for {n}: {axs}"
+  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "exit: 1\n",
  "'Poincare.ParabolicCutoffCommutator.graph_ext_components' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_31' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_17' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_25' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_38' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_15' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_35' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_36' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_10' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_39' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers.eq_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_3' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicSolutionGraph.Graph.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_4' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_7' depends on axioms: [propext]\n",
  "/tmp/parabolic-cutoff-commutator/ModuleAudit.lean:3:0: error: Unexpected foundational dependencies for Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_7: [propext]\n"
]
```

</details>

<details>
<summary>run-041</summary>

Source SHA-256: `3ebd670033e51f42271ccb73a85f1230e400642d357d8df5ae6123aefc025885`.

```diff
--- preceding snapshot
+++ run-041.lean
@@ -1,16 +1,126 @@
 import Poincare.Global.ParabolicCutoffCommutator
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
-    | throwError "module not found"
-  let mut count := 0
-  for (n, _) in env.constants.map₁.toList do
-    if env.getModuleIdxFor? n == some idx then
-      let axs ← liftCoreM (collectAxioms n)
-      count := count + 1
-      elabCommand (← `(command| #print axioms $(mkIdent n)))
-      unless axs.size == 3 && axs.contains ``propext &&
-          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected foundational dependencies for {n}: {axs}"
-  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+local notation "V" => ClosedSmoothModel 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (p : ℝ × V) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_right
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :
+    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _
+    simp only [← mul_assoc, mul_comm _ r, mul_assoc, ← Finset.mul_sum]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),
+    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+end Poincare.ParabolicCutoffCommutator
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "exit: 1\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:61:6: error: Tactic `apply` failed: could not unify the conclusion of `@add_le_add_right`\n",
  "  ?a + ?b ≤ ?a + ?c\n",
  "with the goal\n",
  "  ∑ i, ‖b i * derivativeEntry G.du (e i) ⋯‖ + ‖c‖ * ‖G.u‖ ≤ ∑ i, ‖b i‖ * (2 * ‖G.du‖) + ‖c‖ * ‖G.u‖\n",
  "\n",
  "Note: The full type of `@add_le_add_right` is\n",
  "  ∀ {α : Type ?u.34709.9471} [inst : Add α] [inst_1 : LE α] [AddLeftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c\n",
  "\n",
  "α T : ℝ\n",
  "b : Fin 3 → Y α T ℝ\n",
  "c : Y α T ℝ\n",
  "G : Graph α T\n",
  "⊢ ∑ i, ‖b i * derivativeEntry G.du (e i) ⋯‖ + ‖c‖ * ‖G.u‖ ≤ ∑ i, ‖b i‖ * (2 * ‖G.du‖) + ‖c‖ * ‖G.u‖\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:101:19: error: unsolved goals\n",
  "case h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "b : Fin 3 → Y α T ℝ\n",
  "c : Y α T ℝ\n",
  "r : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × V\n",
  "hp : p ∈ cylinder T\n",
  "⊢ r * ↑(WithLp.fst ↑c) p * ↑(WithLp.fst ↑G.u) p + ∑ x, ↑(WithLp.fst ↑(b x)) p * r * (↑(WithLp.fst ↑G.du) p) (e x) =\n",
  "    ↑(WithLp.fst ↑c) p * ↑(WithLp.fst ↑G.u) p * (RingHom.id ℝ) r +\n",
  "      (∑ x, ↑(WithLp.fst ↑(b x)) p * (↑(WithLp.fst ↑G.du) p) (e x)) * (RingHom.id ℝ) r\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:106:15: warning: This simp argument is unused:\n",
  "  ← mul_assoc\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [̵←̵ ̵m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵m̵u̵l̵_̵c̵o̵m̵m̵[̲m̲u̲l̲_̲c̲o̲m̲m̲ _ r, mul_assoc, ← Finset.mul_sum]\n",
  "\n",
  "Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:106:28: warning: This simp argument is unused:\n",
  "  mul_comm _ r\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [← mul_assoc, mul_c̵o̵m̵m̵ ̵_̵ ̵r̵,̵ ̵m̵u̵l̵_̵assoc, ← Finset.mul_sum]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:106:42: warning: This simp argument is unused:\n",
  "  mul_assoc\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [← mul_assoc, mul_comm _ r, m̵u̵l̵_̵a̵s̵s̵o̵c̵,̵ ̵← Finset.mul_sum]\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:106:53: warning: This simp argument is unused:\n",
  "  ← Finset.mul_sum\n",
  "\n",
  "Hint: Omit it from the simp argument list.\n",
  "  simp only [← mul_assoc, mul_comm _ r, mul_assoc,̵ ̵←̵ ̵F̵i̵n̵s̵e̵t̵.̵m̵u̵l̵_̵s̵u̵m̵]\n",
  "\n",
  "Note: Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning.\n",
  "\n",
  "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`\n"
]
```

</details>

<details>
<summary>run-042</summary>

Source SHA-256: `dab340766f7b6a23bc18b71fa77cd88cb9372388b92fc3d86fffe9e06a98dcc7`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-042.lean\n",
  "@@ -58,7 +58,7 @@\n",
  "     _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=\n",
  "       add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)\n",
  "     _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by\n",
  "-      apply add_le_add_right\n",
  "+      apply add_le_add_left\n",
  "       apply Finset.sum_le_sum\n",
  "       intro i hi\n",
  "       exact (ParabolicHolder.norm_mul_le _ _).trans\n",
  "@@ -103,7 +103,7 @@\n",
  "     intro p hp\n",
  "     simp only [smul_apply, firstOrderForcing_apply]\n",
  "     change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _\n",
  "-    simp only [← mul_assoc, mul_comm _ r, mul_assoc, ← Finset.mul_sum]\n",
  "+    simp only [Fin.sum_univ_succ, smul_eq_mul, RingHom.id_apply]\n",
  "     ring\n",
  " \n",
  " /-- The frozen commutator operator target, with a universal constant. -/\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "exit: 1\n",
  "Try this:\n",
  "  [apply] ring_nf\n",
  "  \n",
  "  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.\n",
  "    \n",
  "  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring, abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:101:19: error: unsolved goals\n",
  "case h\n",
  "E : Type u_1\n",
  "inst✝¹ : NormedAddCommGroup E\n",
  "inst✝ : NormedSpace ℝ E\n",
  "α T : ℝ\n",
  "b : Fin 3 → Y α T ℝ\n",
  "c : Y α T ℝ\n",
  "r : ℝ\n",
  "G : Graph α T\n",
  "p : ℝ × V\n",
  "hp : p ∈ cylinder T\n",
  "⊢ ↑(WithLp.fst ↑(b 0)) p * r * (↑(WithLp.fst ↑G.du) p) (e 0) +\n",
  "            r * ↑(WithLp.fst ↑(b (Fin.succ 0))) p * (↑(WithLp.fst ↑G.du) p) (e (Fin.succ 0)) +\n",
  "          r * ↑(WithLp.fst ↑(b (Fin.succ 0).succ)) p * (↑(WithLp.fst ↑G.du) p) (e (Fin.succ 0).succ) +\n",
  "        r * ↑(WithLp.fst ↑c) p * ↑(WithLp.fst ↑G.u) p +\n",
  "      ∑ x, r * ↑(WithLp.fst ↑(b x.succ.succ.succ)) p * (↑(WithLp.fst ↑G.du) p) (e x.succ.succ.succ) =\n",
  "    ↑(WithLp.fst ↑(b 0)) p * r * (↑(WithLp.fst ↑G.du) p) (e 0) +\n",
  "            r * ↑(WithLp.fst ↑(b (Fin.succ 0))) p * (↑(WithLp.fst ↑G.du) p) (e (Fin.succ 0)) +\n",
  "          r * ↑(WithLp.fst ↑(b (Fin.succ 0).succ)) p * (↑(WithLp.fst ↑G.du) p) (e (Fin.succ 0).succ) +\n",
  "        r * ↑(WithLp.fst ↑c) p * ↑(WithLp.fst ↑G.u) p +\n",
  "      r * ∑ x, ↑(WithLp.fst ↑(b x.succ.succ.succ)) p * (↑(WithLp.fst ↑G.du) p) (e x.succ.succ.succ)\n"
]
```

</details>

<details>
<summary>run-043</summary>

Source SHA-256: `980ee02e1420673149b0da26d7a367532ed9cb63d4526995cc6f8e97dcfb4e49`.

```diff
--- preceding snapshot
+++ run-043.lean
@@ -1,126 +1,19 @@
 import Poincare.Global.ParabolicCutoffCommutator
-noncomputable section
-set_option maxHeartbeats 800000
-namespace Poincare.ParabolicCutoffCommutator
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
-
-/-- Evaluate a first derivative carrier on a unit direction. -/
-def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    Y (E := E) α T ℝ :=
-  ofFunction (fun p => H p v)
-    (fun p hp => by simp [zero_off H hp])
-    ⟨‖H‖, fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
-    ⟨‖H‖, fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
-
-/-- Evaluation is bounded in the full Hölder norm. -/
-theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
-    (norm_nonneg H) (norm_nonneg H)
-    (fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
-    (fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
-  linarith
-
-local notation "V" => ClosedSmoothModel 3
-local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
-
-/-- The first-order forcing associated to the explicit commutator coefficients. -/
-def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=
-  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u
-
-/-- The carrier evaluates to the first-order coefficient formula. -/
-theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (p : ℝ × V) :
-    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by
-  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
-    derivativeEntry, ofFunction_apply]
-
-/-- The commutator uses only the value and gradient norms. -/
-theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) :
-    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
-  calc
-    ‖firstOrderForcing b c G‖ ≤
-        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _
-    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=
-      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
-    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
-      apply add_le_add_left
-      apply Finset.sum_le_sum
-      intro i hi
-      exact (ParabolicHolder.norm_mul_le _ _).trans
-        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
-    _ = _ := by rw [← Finset.sum_mul]; ring
-
-/-- The commutator has separate positive time powers for its two coefficient families. -/
-theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
-  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
-  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
-  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
-  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
-  have h3 := norm_firstOrderForcing_le b c G
-  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
-
-/-- The common weaker time exponent controls both first-order terms. -/
-theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
-  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
-    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-  have h := firstOrder_time_bound b c G hα hα1 hT hT1
-  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
-
-/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
-def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :
-    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where
-  toFun := firstOrderForcing b c
-  map_add' G H := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [add_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _
-    simp only [mul_add, Finset.sum_add_distrib]
-    ring
-  map_smul' r G := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [smul_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _
-    simp only [Fin.sum_univ_succ, smul_eq_mul, RingHom.id_apply]
-    ring
-
-/-- The frozen commutator operator target, with a universal constant. -/
-theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),
-    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,
-      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧
-      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
-  intro α hα hα1
-  refine ⟨24, by norm_num, ?_⟩
-  intro T hT hT1 b c
-  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
-  let K := (firstOrderLinearMap b c).mkContinuous B
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
-  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-
-end Poincare.ParabolicCutoffCommutator
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
+    | throwError "module not found"
+  let mut count := 0
+  let mut bad := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      count := count + 1
+      elabCommand (← `(command| #print axioms $(mkIdent n)))
+      unless axs.size == 3 && axs.contains ``propext &&
+          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        bad := bad + 1
+        elabCommand (← `(command| #print $(mkIdent n)))
+        logInfo m!"MISMATCH {n}: {axs}"
+  logInfo m!"MODULE_DIAGNOSTIC declarations={count}; mismatches={bad}"
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleDiagnostic.lean \n",
  "exit: 0\n",
  "'Poincare.ParabolicCutoffCommutator.graph_ext_components' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_31' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_17' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_25' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_38' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_15' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_35' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_36' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_10' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_39' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers.eq_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_3' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicSolutionGraph.Graph.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_4' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_7' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_7.{u_1} : ∀ {R : Type u_1}\n",
  "  [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False :=\n",
  "fun {R} [AddMonoidWithOne R] [CharZero R] n => eq_false (Nat.cast_add_one_ne_zero n)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_7: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_26' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_7' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_1' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_1.{u_2} : ∀ {α : Type u_2} [inst : Zero α]\n",
  "  [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 2] [NeZero 2] => eq_false two_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_1: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_3' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_3.{u_2} : ∀ {α : Type u_2}\n",
  "  [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 4] [NeZero 4] => eq_false four_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_3: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_14' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_13' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_9' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_22' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_21' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.norm_bilinearY_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_3' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_3.{u_2} : ∀ {α : Type u_2} [inst : Zero α]\n",
  "  [inst_1 : OfNat α 4] [NeZero 4], (4 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 4] [NeZero 4] => eq_false four_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_3: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_29' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_20' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_5' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_5.{u_1} : ∀ {M₀ : Type u_1}\n",
  "  [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False :=\n",
  "fun {M₀} [MonoidWithZero M₀] {a} [IsReduced M₀] n h => eq_false (pow_ne_zero n h)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_5: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.sqrt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_11' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_28' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_8' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv_du' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_operator' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_24' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoffGraph_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_41' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicHolder.ofFunction.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_5' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_12' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_27' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_5' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_5.{u_1} : ∀ {M₀ : Type u_1}\n",
  "  [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀] (n : ℕ), a ≠ 0 → (a ^ n = 0) = False :=\n",
  "fun {M₀} [MonoidWithZero M₀] {a} [IsReduced M₀] n h => eq_false (pow_ne_zero n h)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_5: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasDeriv_time' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_4' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_4.{u_1} : ∀ {M₀ : Type u_1} [inst : Mul M₀]\n",
  "  [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀}, a ≠ 0 → b ≠ 0 → (a * b = 0) = False :=\n",
  "fun {M₀} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b} ha hb => eq_false (mul_ne_zero ha hb)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_4: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_32' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_19' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_jet_carriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.hessianBoundedSMul' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.power_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_33' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_34' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_2' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_2.{u_2} : ∀ {α : Type u_2} [inst : Zero α]\n",
  "  [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 3] [NeZero 3] => eq_false three_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_2: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_40' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder._abel_1_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_2' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_2.{u_2} : ∀ {α : Type u_2}\n",
  "  [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3], (3 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 3] [NeZero 3] => eq_false three_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_2: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_23' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.holder_of_increments' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_1' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_1.{u_2} : ∀ {α : Type u_2}\n",
  "  [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2], (2 = 0) = False :=\n",
  "fun {α} [Zero α] [OfNat α 2] [NeZero 2] => eq_false two_ne_zero\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_1: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_7' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_7.{u_1} : ∀ {R : Type u_1}\n",
  "  [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ), (↑n + 1 = 0) = False :=\n",
  "fun {R} [AddMonoidWithOne R] [CharZero R] n => eq_false (Nat.cast_add_one_ne_zero n)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt._simp_1_7: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_4' depends on axioms: [propext]\n",
  "theorem Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_4.{u_1} : ∀ {M₀ : Type u_1}\n",
  "  [inst : Mul M₀] [inst_1 : Zero M₀] [NoZeroDivisors M₀] {a b : M₀}, a ≠ 0 → b ≠ 0 → (a * b = 0) = False :=\n",
  "fun {M₀} [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b} ha hb => eq_false (mul_ne_zero ha hb)\n",
  "MISMATCH Poincare.ParabolicCutoffCommutator.finite_difference_derivative._simp_1_4: [propext]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_18' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_37' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_16' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_30' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "MODULE_DIAGNOSTIC declarations=104; mismatches=12\n"
]
```

</details>

<details>
<summary>run-044</summary>

Source SHA-256: `f983bac7078e741824bd76e2bc83eede607ce8613ae95037e9acd58d3e1b0140`.

```diff
--- preceding snapshot
+++ run-044.lean
@@ -1,19 +1,126 @@
 import Poincare.Global.ParabolicCutoffCommutator
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
-    | throwError "module not found"
-  let mut count := 0
-  let mut bad := 0
-  for (n, _) in env.constants.map₁.toList do
-    if env.getModuleIdxFor? n == some idx then
-      let axs ← liftCoreM (collectAxioms n)
-      count := count + 1
-      elabCommand (← `(command| #print axioms $(mkIdent n)))
-      unless axs.size == 3 && axs.contains ``propext &&
-          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        bad := bad + 1
-        elabCommand (← `(command| #print $(mkIdent n)))
-        logInfo m!"MISMATCH {n}: {axs}"
-  logInfo m!"MODULE_DIAGNOSTIC declarations={count}; mismatches={bad}"
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+local notation "V" => ClosedSmoothModel 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (p : ℝ × V) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_left
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :
+    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _
+    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),
+    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+end Poincare.ParabolicCutoffCommutator
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-045</summary>

Source SHA-256: `835681d53e229ef31c339402985e479af380556ee69a64999f60f20b762591f0`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-045.lean\n",
  "@@ -1,126 +1,739 @@\n",
  "-import Poincare.Global.ParabolicCutoffCommutator\n",
  "+import Poincare.Global.ParabolicHolderMultiplier\n",
  "+import Poincare.Global.DuhamelSolutionOperatorBound\n",
  "+import Mathlib.Analysis.Calculus.MeanValue\n",
  "+import Mathlib.Analysis.Calculus.ContDiff.RCLike\n",
  "+\n",
  " noncomputable section\n",
  "+\n",
  " set_option maxHeartbeats 800000\n",
  "+set_option synthInstance.maxHeartbeats 200000\n",
  "+\n",
  " namespace Poincare.ParabolicCutoffCommutator\n",
  "+\n",
  " open Set ParabolicHolder ParabolicSolutionGraph\n",
  " open scoped ContDiff\n",
  "-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}\n",
  "-\n",
  "-/-- Evaluate a first derivative carrier on a unit direction. -/\n",
  "-def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :\n",
  "-    Y (E := E) α T ℝ :=\n",
  "-  ofFunction (fun p => H p v)\n",
  "-    (fun p hp => by simp [zero_off H hp])\n",
  "-    ⟨‖H‖, fun p _ => by\n",
  "-      simpa [hv] using ((H p).le_opNorm v).trans\n",
  "-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩\n",
  "-    ⟨‖H‖, fun p hp q hq => by\n",
  "-      have h := (H p - H q).le_opNorm v\n",
  "-      simpa [hv] using h.trans\n",
  "-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩\n",
  "-\n",
  "-/-- Evaluation is bounded in the full Hölder norm. -/\n",
  "-theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :\n",
  "-    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by\n",
  "-  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)\n",
  "-    (norm_nonneg H) (norm_nonneg H)\n",
  "-    (fun p _ => by\n",
  "-      simpa [hv] using ((H p).le_opNorm v).trans\n",
  "-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))\n",
  "-    (fun p hp q hq => by\n",
  "-      have h := (H p - H q).le_opNorm v\n",
  "-      simpa [hv] using h.trans\n",
  "-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))\n",
  "-  linarith\n",
  "-\n",
  "-local notation \"V\" => ClosedSmoothModel 3\n",
  "-local notation \"e\" => EuclideanSpace.basisFun (Fin 3) ℝ\n",
  "-\n",
  "-/-- The first-order forcing associated to the explicit commutator coefficients. -/\n",
  "-def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)\n",
  "-    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=\n",
  "-  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u\n",
  "-\n",
  "-/-- The carrier evaluates to the first-order coefficient formula. -/\n",
  "-theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)\n",
  "-    (G : Graph (E := V) α T) (p : ℝ × V) :\n",
  "-    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by\n",
  "-  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,\n",
  "-    derivativeEntry, ofFunction_apply]\n",
  "-\n",
  "-/-- The commutator uses only the value and gradient norms. -/\n",
  "-theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)\n",
  "-    (G : Graph (E := V) α T) :\n",
  "-    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by\n",
  "+\n",
  "+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]\n",
  "+\n",
  "+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/\n",
  "+theorem quadratic_remainder\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)\n",
  "+    (x v : E) (hv : ‖v‖ = 1) :\n",
  "+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by\n",
  "+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=\n",
  "+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)\n",
  "+      convex_univ (mem_univ x) (mem_univ y)\n",
  "+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))\n",
  "+      (dh (x + s • v) v) s := by\n",
  "+    simpa using (hd (x + s • v)).comp_hasDerivAt s\n",
  "+      (((hasDerivAt_id s).smul_const v).const_add x)\n",
  "+  have hdr (s : ℝ) : HasDerivAt\n",
  "+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)\n",
  "+      (dh (x + s • v) v - dh x v) s := by\n",
  "+    simpa using ((hdline s).sub_const (h x)).sub\n",
  "+      ((hasDerivAt_id s).mul_const (dh x v))\n",
  "+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by\n",
  "+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1\n",
  "+    simp only [id_eq]\n",
  "+    ring\n",
  "+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary\n",
  "+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)\n",
  "+    (fun s _ => (hdr s).hasDerivWithinAt)\n",
  "+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)\n",
  "+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)\n",
  "+  · exact hr\n",
  "+  · calc\n",
  "+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl\n",
  "+      _ ≤ ‖dh (x + s • v) - dh x‖ := by\n",
  "+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v\n",
  "+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)\n",
  "+\n",
  "+/-- The finite-difference estimate with an arbitrary positive step. -/\n",
  "+theorem finite_difference_derivative\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)\n",
  "+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :\n",
  "+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by\n",
  "+  have hr := quadratic_remainder hd hdd hb hη.le x v hv\n",
  "+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=\n",
  "+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])\n",
  "+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by\n",
  "+    calc\n",
  "+      |η * dh x v| = |(h (x + η • v) - h x) -\n",
  "+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf\n",
  "+      _ ≤ |h (x + η • v) - h x| +\n",
  "+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _\n",
  "+      _ ≤ _ := add_le_add hu hr\n",
  "+  rw [abs_mul, abs_of_pos hη] at ht\n",
  "+  apply (mul_le_mul_iff_right₀ hη).mp\n",
  "+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by\n",
  "+    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)\n",
  "+    calc\n",
  "+      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring\n",
  "+      _ = _ := by rw [hc]\n",
  "+  rw [he]\n",
  "+  nlinarith\n",
  "+\n",
  "+/-- Optimizing the step gives a square-root bound on the full derivative. -/\n",
  "+theorem derivative_norm_le_sqrt\n",
  "+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}\n",
  "+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}\n",
  "+    (hd : ∀ x, HasFDerivAt h (dh x) x)\n",
  "+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)\n",
  "+    (hδ : 0 < δ) (hM : 0 ≤ M)\n",
  "+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)\n",
  "+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by\n",
  "+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)\n",
  "+  intro v hv\n",
  "+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv\n",
  "+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =\n",
  "+      3 * Real.sqrt δ * M := by\n",
  "+    have hs := Real.sq_sqrt hδ.le\n",
  "+    have hp := Real.sqrt_pos.mpr hδ\n",
  "+    have hc : δ / Real.sqrt δ = Real.sqrt δ := by\n",
  "+      apply (div_eq_iff (ne_of_gt hp)).2\n",
  "+      nlinarith\n",
  "+    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]\n",
  "+    ring\n",
  "+  exact h.trans_eq he\n",
  "+\n",
  "+variable {α T : ℝ}\n",
  "+\n",
  "+/-- Time increments of the value are controlled by the stored time derivative. -/\n",
  "+theorem value_time_increment (G : Graph (E := E) α T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by\n",
  "+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le\n",
  "+    (fun r hr => G.hasDeriv_time r hr x)\n",
  "+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht\n",
  "+  simpa only [Real.norm_eq_abs, mul_comm] using h\n",
  "+\n",
  "+/-- The gradient of any derivative graph is uniformly small at short times. -/\n",
  "+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by\n",
  "+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT\n",
  "+    (norm_nonneg G) ?_ ?_ x\n",
  "+  · intro y\n",
  "+    calc\n",
  "+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y\n",
  "+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le\n",
  "+  · intro y\n",
  "+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])\n",
  "+\n",
  "+/-- The supremum of the gradient has the same square-root gain. -/\n",
  "+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :\n",
  "+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by\n",
  "+  apply csSup_le (insert_nonempty _ _)\n",
  "+  rintro r (rfl | ⟨p, rfl⟩)\n",
  "+  · positivity\n",
  "+  · exact gradient_bound G hT p.property.1 p.val.2\n",
  "+\n",
  "+/-- Time differences of the gradient require no mixed time-space derivative. -/\n",
  "+theorem gradient_time_increment (G : Graph (E := E) α T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by\n",
  "+  by_cases hst : t = s\n",
  "+  · simp [hst]\n",
  "+  · apply derivative_norm_le_sqrt\n",
  "+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))\n",
  "+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))\n",
  "+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)\n",
  "+      (value_time_increment G hs ht) ?_ x\n",
  "+    intro y\n",
  "+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans\n",
  "+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])\n",
  "+\n",
  "+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/\n",
  "+theorem gradient_space_increment (G : Graph (E := E) α T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=\n",
  "+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)\n",
  "+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)\n",
  "+\n",
  "+/-- Spatial value increments inherit the improved gradient bound. -/\n",
  "+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=\n",
  "+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le\n",
  "+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)\n",
  "+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)\n",
  "+\n",
  "+/-- Split a power at a larger positive scale. -/\n",
  "+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)\n",
  "+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :\n",
  "+    r ^ b ≤ R ^ (b - a) * r ^ a := by\n",
  "+  have he : r ^ b = r ^ (b - a) * r ^ a := by\n",
  "+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]\n",
  "+    congr 1\n",
  "+    ring\n",
  "+  rw [he]\n",
  "+  exact mul_le_mul_of_nonneg_right\n",
  "+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)\n",
  "+\n",
  "+/-- Interpolate a Lipschitz bound and a bound at scale R. -/\n",
  "+theorem scale_interpolation {a L r R α : ℝ}\n",
  "+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)\n",
  "+    (hl : a ≤ L * r) (hb : a ≤ L * R) :\n",
  "+    a ≤ L * R ^ (1 - α) * r ^ α := by\n",
  "+  by_cases h : r ≤ R\n",
  "+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one\n",
  "+    rw [Real.rpow_one] at hp\n",
  "+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])\n",
  "+  · have he : R ^ (1 - α) * R ^ α = R := by\n",
  "+      rw [← Real.rpow_add hR]\n",
  "+      convert Real.rpow_one R using 2\n",
  "+      ring\n",
  "+    calc\n",
  "+      a ≤ L * R := hb\n",
  "+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]\n",
  "+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left\n",
  "+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)\n",
  "+\n",
  "+/-- The parabolic spatial scale is the square root of the time scale. -/\n",
  "+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :\n",
  "+    (Real.sqrt T) ^ p = T ^ (p / 2) := by\n",
  "+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]\n",
  "+  congr 1\n",
  "+  ring\n",
  "+\n",
  "+/-- Spatial Hölder gradient increments carry the desired positive time power. -/\n",
  "+theorem gradient_space_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    ‖G.du (t, x) - G.du (t, y)‖ ≤\n",
  "+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by\n",
  "+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)\n",
  "+    (L := 6 * ‖G‖) (by positivity)\n",
  "+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le\n",
  "+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))\n",
  "+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans\n",
  "+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))\n",
  "+  rw [sqrt_rpow hT.le] at h\n",
  "+  nlinarith [h]\n",
  "+\n",
  "+/-- Spatial Hölder value increments gain one additional half power of time. -/\n",
  "+theorem value_space_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :\n",
  "+    |G.u (t, x) - G.u (t, y)| ≤\n",
  "+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by\n",
  "+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=\n",
  "+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)\n",
  "+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)\n",
  "+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)\n",
  "+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le\n",
  "+    (value_space_increment G hT ht x y)\n",
  "+    ((abs_sub _ _).trans (by\n",
  "+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)\n",
  "+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))\n",
  "+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by\n",
  "+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]\n",
  "+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]\n",
  "+    rw [sqrt_rpow hT.le]\n",
  "+    congr 1\n",
  "+    ring\n",
  "   calc\n",
  "-    ‖firstOrderForcing b c G‖ ≤\n",
  "-        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _\n",
  "-    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=\n",
  "-      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)\n",
  "-    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by\n",
  "-      apply add_le_add_left\n",
  "-      apply Finset.sum_le_sum\n",
  "-      intro i hi\n",
  "-      exact (ParabolicHolder.norm_mul_le _ _).trans\n",
  "-        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))\n",
  "-    _ = _ := by rw [← Finset.sum_mul]; ring\n",
  "-\n",
  "-/-- The commutator has separate positive time powers for its two coefficient families. -/\n",
  "-theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)\n",
  "-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :\n",
  "-    ‖firstOrderForcing b c G‖ ≤\n",
  "-      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by\n",
  "-  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1\n",
  "-  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))\n",
  "-  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)\n",
  "-  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)\n",
  "-  have h3 := norm_firstOrderForcing_le b c G\n",
  "-  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]\n",
  "-\n",
  "-/-- The common weaker time exponent controls both first-order terms. -/\n",
  "-theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)\n",
  "-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :\n",
  "-    ‖firstOrderForcing b c G‖ ≤\n",
  "-      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by\n",
  "-  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=\n",
  "-    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)\n",
  "-  have h := firstOrder_time_bound b c G hα hα1 hT hT1\n",
  "-  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]\n",
  "-\n",
  "-/-- First-order coefficient multiplication is a linear map of derivative graphs. -/\n",
  "-def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :\n",
  "-    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where\n",
  "-  toFun := firstOrderForcing b c\n",
  "+    |G.u (t,x) - G.u (t,y)| ≤ _ := h\n",
  "+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =\n",
  "+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]\n",
  "+\n",
  "+/-- The temporal Hölder gradient bound follows from the square-root increment. -/\n",
  "+theorem gradient_time_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    ‖G.du (t, x) - G.du (s, x)‖ ≤\n",
  "+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by\n",
  "+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩\n",
  "+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ\n",
  "+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)\n",
  "+    (show (0 : ℝ) < 1 / 2 by norm_num)\n",
  "+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp\n",
  "+  have hi := gradient_time_increment G hs ht x\n",
  "+  rw [Real.sqrt_eq_rpow] at hi\n",
  "+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]\n",
  "+\n",
  "+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/\n",
  "+theorem value_time_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)\n",
  "+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    |G.u (t, x) - G.u (s, x)| ≤\n",
  "+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by\n",
  "+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩\n",
  "+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ\n",
  "+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one\n",
  "+  rw [Real.rpow_one] at hp\n",
  "+  exact (value_time_increment G hs ht x).trans (by\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])\n",
  "+\n",
  "+omit [NormedSpace ℝ E] in\n",
  "+/-- Split a mixed increment through the point with the first time and second position. -/\n",
  "+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]\n",
  "+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)\n",
  "+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,\n",
  "+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)\n",
  "+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,\n",
  "+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :\n",
  "+    HasHolderBound α (cylinder T) f (Kx + Kt) := by\n",
  "+  intro p hp q hq\n",
  "+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=\n",
  "+    Real.rpow_le_rpow (norm_nonneg _) (by\n",
  "+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα\n",
  "+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by\n",
  "+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]\n",
  "+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by\n",
  "+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα\n",
  "+  calc\n",
  "+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=\n",
  "+      norm_sub_le_norm_sub_add_norm_sub _ _ _\n",
  "+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=\n",
  "+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)\n",
  "+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by\n",
  "+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]\n",
  "+\n",
  "+/-- Full gradient Hölder control, including mixed increments. -/\n",
  "+theorem gradient_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :\n",
  "+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by\n",
  "+  have h := holder_of_increments hα.le\n",
  "+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+    (fun t ht => gradient_space_holder G hα hα1 hT ht)\n",
  "+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)\n",
  "+  convert h using 1\n",
  "+  ring\n",
  "+\n",
  "+/-- Full value Hölder control with its stronger time power. -/\n",
  "+theorem value_holder (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :\n",
  "+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by\n",
  "+  have h := holder_of_increments (f := G.u) hα.le\n",
  "+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)\n",
  "+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)\n",
  "+  convert h using 1\n",
  "+  ring\n",
  "+\n",
  "+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/\n",
  "+theorem interpolation_bounds (G : Graph (E := E) α T)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :\n",
  "+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by\n",
  "+  constructor\n",
  "+  · have h := ParabolicHolder.norm_le_of_bounds G.u\n",
  "+      (show 0 ≤ T * ‖G‖ by positivity)\n",
  "+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)\n",
  "+      (fun p hp => (time_bound G hp.1 p.2).trans\n",
  "+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))\n",
  "+      (value_holder G hα hα1 hT)\n",
  "+    have hp : T ≤ T ^ (1-α/2) := by\n",
  "+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1\n",
  "+      exact (Real.rpow_one T).symm\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),\n",
  "+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]\n",
  "+  · have h := ParabolicHolder.norm_le_of_bounds G.du\n",
  "+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)\n",
  "+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)\n",
  "+      (fun p hp => gradient_bound G hT hp.1 p.2)\n",
  "+      (gradient_holder G hα hα1 hT)\n",
  "+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by\n",
  "+      rw [Real.sqrt_eq_rpow]\n",
  "+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)\n",
  "+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]\n",
  "+\n",
  "+/-- A universal constant satisfies the frozen interpolation target. -/\n",
  "+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →\n",
  "+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,\n",
  "+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧\n",
  "+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by\n",
  "+  intro α hα hα1\n",
  "+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩\n",
  "+\n",
  "+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/\n",
  "+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]\n",
  "+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,\n",
  "+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by\n",
  "+  classical\n",
  "+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous\n",
  "+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)\n",
  "+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)\n",
  "+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by\n",
  "+    have h := scale_interpolation (L := 2*A+B) (R := 1)\n",
  "+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le\n",
  "+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))\n",
  "+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))\n",
  "+    simpa using h\n",
  "+  refine ⟨A + (2*A+B), by positivity, ?_⟩\n",
  "+  intro T\n",
  "+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0\n",
  "+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by\n",
  "+    intro p hp; simp [f, hp]\n",
  "+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by\n",
  "+    intro p hp; simpa [f, hp] using hA p.2\n",
  "+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by\n",
  "+    intro p hp q hq\n",
  "+    simp only [f, if_pos hp, if_pos hq]\n",
  "+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left\n",
  "+      (Real.rpow_le_rpow (norm_nonneg _) (by\n",
  "+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))\n",
  "+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩\n",
  "+  refine ⟨fY, ?_, ?_⟩\n",
  "+  · intro p hp\n",
  "+    change f p = ψ p.2\n",
  "+    simp [f, hp]\n",
  "+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder\n",
  "+\n",
  "+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/\n",
  "+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}\n",
  "+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)\n",
  "+    (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,\n",
  "+      ∃ (f : Y (E := E) α T ℝ)\n",
  "+        (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),\n",
  "+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧\n",
  "+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧\n",
  "+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by\n",
  "+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)\n",
  "+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)\n",
  "+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1\n",
  "+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1\n",
  "+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1\n",
  "+  refine ⟨K0+K1+K2, by positivity, ?_⟩\n",
  "+  intro T\n",
  "+  obtain ⟨f, hf, hfb⟩ := h0 T\n",
  "+  obtain ⟨df, hdf, hdfb⟩ := h1 T\n",
  "+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T\n",
  "+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩\n",
  "+\n",
  "+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/\n",
  "+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasFDerivAt (fun z => ψ z * G.u (t,z))\n",
  "+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=\n",
  "+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)\n",
  "+\n",
  "+/-- The second spatial product rule includes both mixed Hessian terms. -/\n",
  "+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)\n",
  "+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +\n",
  "+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +\n",
  "+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by\n",
  "+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)\n",
  "+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add\n",
  "+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)\n",
  "+\n",
  "+/-- A spatial cutoff is constant in the within-time product rule. -/\n",
  "+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)\n",
  "+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :\n",
  "+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=\n",
  "+  (G.hasDeriv_time t ht x).const_mul (ψ x)\n",
  "+\n",
  "+section Bilinear\n",
  "+variable {F H J : Type*}\n",
  "+  [NormedAddCommGroup F] [NormedSpace ℝ F]\n",
  "+  [NormedAddCommGroup H] [NormedSpace ℝ H]\n",
  "+  [NormedAddCommGroup J] [NormedSpace ℝ J]\n",
  "+\n",
  "+omit [NormedSpace ℝ E] in\n",
  "+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/\n",
  "+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n",
  "+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by\n",
  "+  intro p hp q hq\n",
  "+  have hf := ParabolicHolder.holder_le f hp hq\n",
  "+  have hg := ParabolicHolder.holder_le g hp hq\n",
  "+  have hf0 := ParabolicHolder.norm_le f p\n",
  "+  have hg0 := ParabolicHolder.norm_le g q\n",
  "+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α\n",
  "+  calc\n",
  "+    ‖B (f p) (g p) - B (f q) (g q)‖ =\n",
  "+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by\n",
  "+      congr 1\n",
  "+      simp only [map_sub, ContinuousLinearMap.sub_apply]\n",
  "+      abel\n",
  "+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _\n",
  "+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=\n",
  "+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)\n",
  "+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +\n",
  "+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by\n",
  "+      apply add_le_add\n",
  "+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg\n",
  "+          (norm_nonneg _) (by positivity)\n",
  "+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0\n",
  "+          (norm_nonneg _) (by positivity)\n",
  "+    _ = _ := by ring\n",
  "+\n",
  "+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/\n",
  "+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=\n",
  "+  ofFunction (fun p => B (f p) (g p))\n",
  "+    (fun p hp => by simp [zero_off f hp])\n",
  "+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans\n",
  "+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))\n",
  "+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩\n",
  "+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩\n",
  "+\n",
  "+omit [NormedSpace ℝ E] in\n",
  "+/-- The bilinear carrier norm has an explicit product bound. -/\n",
  "+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)\n",
  "+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :\n",
  "+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by\n",
  "+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)\n",
  "+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)\n",
  "+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)\n",
  "+    (fun p _ => (B.le_opNorm₂ _ _).trans\n",
  "+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))\n",
  "+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))\n",
  "+    (bilinear_holder B f g)\n",
  "+  nlinarith [h]\n",
  "+\n",
  "+end Bilinear\n",
  "+\n",
  "+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)\n",
  "+\n",
  "+/-- Assemble the cutoff graph from its three spatial carriers. -/\n",
  "+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)\n",
  "+    (G : Graph (E := E) α T) : Graph (E := E) α T where\n",
  "+  u := f * G.u\n",
  "+  ut := f * G.ut\n",
  "+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df\n",
  "+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +\n",
  "+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +\n",
  "+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)\n",
  "+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]\n",
  "+  hasFDeriv := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [mul_apply, hf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]\n",
  "+  hasFDeriv_du := by\n",
  "+    intro t ht x\n",
  "+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩\n",
  "+    convert cutoff_hasFDeriv_du hψ G ht x using 1\n",
  "+    · funext z\n",
  "+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]\n",
  "+      rfl\n",
  "+  hasDeriv_time := by\n",
  "+    intro t ht x\n",
  "+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by\n",
  "+      by_cases hs : (s,x) ∈ cylinder T\n",
  "+      · simp [mul_apply, hf (s,x) hs]\n",
  "+      · simp [mul_apply, zero_off G.u hs]\n",
  "+    convert cutoff_hasDeriv_time ψ G ht x using 1\n",
  "+    · funext s; exact he s\n",
  "+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]\n",
  "+\n",
  "+/-- Equality of the four stored carriers determines a derivative graph. -/\n",
  "+theorem graph_ext_components {G H : Graph (E := E) α T}\n",
  "+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :\n",
  "+    G = H := by\n",
  "+  cases G\n",
  "+  cases H\n",
  "+  simp_all\n",
  "+\n",
  "+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/\n",
  "+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :\n",
  "+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where\n",
  "+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf\n",
  "   map_add' G H := by\n",
  "-    apply ParabolicHolder.ext\n",
  "-    intro p hp\n",
  "-    simp only [add_apply, firstOrderForcing_apply]\n",
  "-    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _\n",
  "-    simp only [mul_add, Finset.sum_add_distrib]\n",
  "-    ring\n",
  "-  map_smul' r G := by\n",
  "-    apply ParabolicHolder.ext\n",
  "-    intro p hp\n",
  "-    simp only [smul_apply, firstOrderForcing_apply]\n",
  "-    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _\n",
  "-    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]\n",
  "-    ring\n",
  "-\n",
  "-/-- The frozen commutator operator target, with a universal constant. -/\n",
  "-theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →\n",
  "-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →\n",
  "-    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),\n",
  "-    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,\n",
  "-      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧\n",
  "-      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by\n",
  "-  intro α hα hα1\n",
  "-  refine ⟨24, by norm_num, ?_⟩\n",
  "-  intro T hT hT1 b c\n",
  "-  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)\n",
  "-  let K := (firstOrderLinearMap b c).mkContinuous B\n",
  "-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)\n",
  "-  refine ⟨K, firstOrderForcing_apply b c, ?_⟩\n",
  "-  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)\n",
  "-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)\n",
  "+    apply graph_ext_components\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))\n",
  "+      ring\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))\n",
  "+      ring\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)\n",
  "+      module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))\n",
  "+      simp only [map_add, ContinuousLinearMap.add_apply]\n",
  "+      module\n",
  "+  map_smul' c G := by\n",
  "+    apply graph_ext_components\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (c • G.u p) = c • (f p * (G.u p))\n",
  "+      ring\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p * (c • G.ut p) = c • (f p * (G.ut p))\n",
  "+      ring\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)\n",
  "+      module\n",
  "+    · apply ParabolicHolder.ext\n",
  "+      intro p hp\n",
  "+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))\n",
  "+      simp only [map_smul, ContinuousLinearMap.smul_apply]\n",
  "+      module\n",
  "+\n",
  "+\n",
  "+set_option maxHeartbeats 4000000 in\n",
  "+/-- The cutoff graph map is bounded in the original four-component norm. -/\n",
  "+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))\n",
  "+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))\n",
  "+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)\n",
  "+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)\n",
  "+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :\n",
  "+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,\n",
  "+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by\n",
  "+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance\n",
  "+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance\n",
  "+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance\n",
  "+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance\n",
  "+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ\n",
  "+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)\n",
  "+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=\n",
  "+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)\n",
  "+  let A := ‖f‖ + ‖df‖ + ‖ddf‖\n",
  "+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖\n",
  "+  have hA : 0 ≤ A := by dsimp [A]; positivity\n",
  "+  have hB : 0 ≤ B := by dsimp [B]; positivity\n",
  "+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]\n",
  "+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]\n",
  "+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]\n",
  "+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]\n",
  "+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]\n",
  "+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]\n",
  "+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]\n",
  "+  refine ⟨20 * B * A, ?_⟩\n",
  "+  intro G\n",
  "+  have hGu := norm_u_le G\n",
  "+  have hGut := norm_ut_le G\n",
  "+  have hGdu := norm_du_le G\n",
  "+  have hGddu := norm_ddu_le G\n",
  "+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _\n",
  "+      _ ≤ B * A * ‖G‖ := by\n",
  "+        calc\n",
  "+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA\n",
  "+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]\n",
  "+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _\n",
  "+      _ ≤ B * A * ‖G‖ := by\n",
  "+        calc\n",
  "+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA\n",
  "+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]\n",
  "+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * A * ‖G‖ := by gcongr\n",
  "+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by\n",
  "+    calc\n",
  "+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _\n",
  "+      _ ≤ 3 * B * ‖G‖ * A := by gcongr\n",
  "+      _ = _ := by ring\n",
  "+  rw [ParabolicSolutionGraph.norm_eq]\n",
  "+  change ‖f * G.u‖ + ‖f * G.ut‖ +\n",
  "+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +\n",
  "+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +\n",
  "+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _\n",
  "+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)\n",
  "+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)\n",
  "+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)\n",
  "+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)\n",
  "+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)\n",
  "+  nlinarith\n",
  "+\n",
  "+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/\n",
  "+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :\n",
  "+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,\n",
  "+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧\n",
  "+      (∀ G t, t ∈ Icc 0 T → ∀ x,\n",
  "+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧\n",
  "+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧\n",
  "+        (C G).ddu (t,x) =\n",
  "+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +\n",
  "+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +\n",
  "+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by\n",
  "+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1\n",
  "+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T\n",
  "+  have hf := fun p hp => (heq p hp).1\n",
  "+  have hdf := fun p hp => (heq p hp).2.1\n",
  "+  have hddf := fun p hp => (heq p hp).2.2\n",
  "+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf\n",
  "+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf\n",
  "+  let C := L.mkContinuous B hB\n",
  "+  refine ⟨C, ?_, ?_⟩\n",
  "+  · intro G p\n",
  "+    change f p * G.u p = ψ p.2 * G.u p\n",
  "+    by_cases hp : p ∈ cylinder T\n",
  "+    · rw [hf p hp]\n",
  "+    · simp [zero_off G.u hp]\n",
  "+  · intro G t ht x\n",
  "+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩\n",
  "+    change f (t,x) * G.ut (t,x) = _ ∧\n",
  "+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +\n",
  "+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _\n",
  "+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩\n",
  "+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) hp, hdf (t,x) hp]\n",
  "+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _\n",
  "+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,\n",
  "+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]\n",
  "+      rfl\n",
  " \n",
  " end Poincare.ParabolicCutoffCommutator\n"
]
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean -o .lake/build/lib/lean/Poincare/Global/ParabolicCutoffCommutator.olean
exit: 0
```

</details>

<details>
<summary>run-046</summary>

Source SHA-256: `b36359b79da42a1561c3e9abb56d41d3e38a4a6a7b79d3a008b71efd3f3a39d3`.

```diff
--- preceding snapshot
+++ run-046.lean
@@ -1,739 +1,16 @@
-import Poincare.Global.ParabolicHolderMultiplier
-import Poincare.Global.DuhamelSolutionOperatorBound
-import Mathlib.Analysis.Calculus.MeanValue
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-
-noncomputable section
-
-set_option maxHeartbeats 800000
-set_option synthInstance.maxHeartbeats 200000
-
-namespace Poincare.ParabolicCutoffCommutator
-
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-
-/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
-theorem quadratic_remainder
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
-    (x v : E) (hv : ‖v‖ = 1) :
-    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
-  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
-    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
-      convex_univ (mem_univ x) (mem_univ y)
-  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
-      (dh (x + s • v) v) s := by
-    simpa using (hd (x + s • v)).comp_hasDerivAt s
-      (((hasDerivAt_id s).smul_const v).const_add x)
-  have hdr (s : ℝ) : HasDerivAt
-      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
-      (dh (x + s • v) v - dh x v) s := by
-    simpa using ((hdline s).sub_const (h x)).sub
-      ((hasDerivAt_id s).mul_const (dh x v))
-  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
-    simp only [id_eq]
-    ring
-  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
-    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
-    (fun s _ => (hdr s).hasDerivWithinAt)
-    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
-    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
-  · exact hr
-  · calc
-      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
-      _ ≤ ‖dh (x + s • v) - dh x‖ := by
-        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
-      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
-
-/-- The finite-difference estimate with an arbitrary positive step. -/
-theorem finite_difference_derivative
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
-    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
-    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
-  have hr := quadratic_remainder hd hdd hb hη.le x v hv
-  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
-    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
-  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
-    calc
-      |η * dh x v| = |(h (x + η • v) - h x) -
-          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
-      _ ≤ |h (x + η • v) - h x| +
-          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
-      _ ≤ _ := add_le_add hu hr
-  rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_iff_right₀ hη).mp
-  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
-    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
-    calc
-      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
-      _ = _ := by rw [hc]
-  rw [he]
-  nlinarith
-
-/-- Optimizing the step gives a square-root bound on the full derivative. -/
-theorem derivative_norm_le_sqrt
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hδ : 0 < δ) (hM : 0 ≤ M)
-    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
-    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
-  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
-  intro v hv
-  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
-  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
-      3 * Real.sqrt δ * M := by
-    have hs := Real.sq_sqrt hδ.le
-    have hp := Real.sqrt_pos.mpr hδ
-    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
-      apply (div_eq_iff (ne_of_gt hp)).2
-      nlinarith
-    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
-    ring
-  exact h.trans_eq he
-
-variable {α T : ℝ}
-
-/-- Time increments of the value are controlled by the stored time derivative. -/
-theorem value_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
-  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-    (fun r hr => G.hasDeriv_time r hr x)
-    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
-  simpa only [Real.norm_eq_abs, mul_comm] using h
-
-/-- The gradient of any derivative graph is uniformly small at short times. -/
-theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
-    (norm_nonneg G) ?_ ?_ x
-  · intro y
-    calc
-      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
-      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
-  · intro y
-    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
-
-/-- The supremum of the gradient has the same square-root gain. -/
-theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
-    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply csSup_le (insert_nonempty _ _)
-  rintro r (rfl | ⟨p, rfl⟩)
-  · positivity
-  · exact gradient_bound G hT p.property.1 p.val.2
-
-/-- Time differences of the gradient require no mixed time-space derivative. -/
-theorem gradient_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
-  by_cases hst : t = s
-  · simp [hst]
-  · apply derivative_norm_le_sqrt
-      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
-      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
-      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
-      (value_time_increment G hs ht) ?_ x
-    intro y
-    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
-      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
-
-/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
-theorem gradient_space_increment (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
-    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Spatial value increments inherit the improved gradient bound. -/
-theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
-    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Split a power at a larger positive scale. -/
-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
-    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
-    r ^ b ≤ R ^ (b - a) * r ^ a := by
-  have he : r ^ b = r ^ (b - a) * r ^ a := by
-    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
-    congr 1
-    ring
-  rw [he]
-  exact mul_le_mul_of_nonneg_right
-    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
-
-/-- Interpolate a Lipschitz bound and a bound at scale R. -/
-theorem scale_interpolation {a L r R α : ℝ}
-    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
-    (hl : a ≤ L * r) (hb : a ≤ L * R) :
-    a ≤ L * R ^ (1 - α) * r ^ α := by
-  by_cases h : r ≤ R
-  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
-    rw [Real.rpow_one] at hp
-    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
-  · have he : R ^ (1 - α) * R ^ α = R := by
-      rw [← Real.rpow_add hR]
-      convert Real.rpow_one R using 2
-      ring
-    calc
-      a ≤ L * R := hb
-      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
-      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
-        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
-
-/-- The parabolic spatial scale is the square root of the time scale. -/
-theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
-    (Real.sqrt T) ^ p = T ^ (p / 2) := by
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
-  congr 1
-  ring
-
-/-- Spatial Hölder gradient increments carry the desired positive time power. -/
-theorem gradient_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤
-      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
-    (L := 6 * ‖G‖) (by positivity)
-    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
-    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
-      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
-  rw [sqrt_rpow hT.le] at h
-  nlinarith [h]
-
-/-- Spatial Hölder value increments gain one additional half power of time. -/
-theorem value_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤
-      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
-    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
-  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
-    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
-    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    (value_space_increment G hT ht x y)
-    ((abs_sub _ _).trans (by
-      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
-      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
-  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
-    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
-    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
-    rw [sqrt_rpow hT.le]
-    congr 1
-    ring
-  calc
-    |G.u (t,x) - G.u (t,y)| ≤ _ := h
-    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
-        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
-
-/-- The temporal Hölder gradient bound follows from the square-root increment. -/
-theorem gradient_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤
-      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
-    (show (0 : ℝ) < 1 / 2 by norm_num)
-  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
-  have hi := gradient_time_increment G hs ht x
-  rw [Real.sqrt_eq_rpow] at hi
-  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
-
-/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
-theorem value_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤
-      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
-  rw [Real.rpow_one] at hp
-  exact (value_time_increment G hs ht x).trans (by
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
-
-omit [NormedSpace ℝ E] in
-/-- Split a mixed increment through the point with the first time and second position. -/
-theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
-    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
-    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
-      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
-    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
-      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
-    HasHolderBound α (cylinder T) f (Kx + Kt) := by
-  intro p hp q hq
-  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
-    Real.rpow_le_rpow (norm_nonneg _) (by
-      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
-  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
-    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
-    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
-      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
-  calc
-    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
-      norm_sub_le_norm_sub_add_norm_sub _ _ _
-    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
-      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
-    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
-      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
-
-/-- Full gradient Hölder control, including mixed increments. -/
-theorem gradient_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
-  have h := holder_of_increments hα.le
-    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (fun t ht => gradient_space_holder G hα hα1 hT ht)
-    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
-  convert h using 1
-  ring
-
-/-- Full value Hölder control with its stronger time power. -/
-theorem value_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
-  have h := holder_of_increments (f := G.u) hα.le
-    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
-    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
-    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
-    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
-  convert h using 1
-  ring
-
-/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
-theorem interpolation_bounds (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
-  constructor
-  · have h := ParabolicHolder.norm_le_of_bounds G.u
-      (show 0 ≤ T * ‖G‖ by positivity)
-      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
-      (fun p hp => (time_bound G hp.1 p.2).trans
-        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
-      (value_holder G hα hα1 hT)
-    have hp : T ≤ T ^ (1-α/2) := by
-      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
-      exact (Real.rpow_one T).symm
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
-      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
-  · have h := ParabolicHolder.norm_le_of_bounds G.du
-      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
-      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-      (fun p hp => gradient_bound G hT hp.1 p.2)
-      (gradient_holder G hα hα1 hT)
-    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
-      rw [Real.sqrt_eq_rpow]
-      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
-
-/-- A universal constant satisfies the frozen interpolation target. -/
-theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
-      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
-  intro α hα hα1
-  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
-
-/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
-theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
-    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
-      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
-  classical
-  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
-  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
-  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
-  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
-    have h := scale_interpolation (L := 2*A+B) (R := 1)
-      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
-      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
-      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
-    simpa using h
-  refine ⟨A + (2*A+B), by positivity, ?_⟩
-  intro T
-  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
-  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
-    intro p hp; simp [f, hp]
-  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
-    intro p hp; simpa [f, hp] using hA p.2
-  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
-    intro p hp q hq
-    simp only [f, if_pos hp, if_pos hq]
-    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
-      (Real.rpow_le_rpow (norm_nonneg _) (by
-        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
-  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
-  refine ⟨fY, ?_, ?_⟩
-  · intro p hp
-    change f p = ψ p.2
-    simp [f, hp]
-  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
-
-/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
-theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
-    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
-      ∃ (f : Y (E := E) α T ℝ)
-        (df : Y (E := E) α T (E →L[ℝ] ℝ))
-        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
-      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
-        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
-      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
-  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
-  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
-  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
-  refine ⟨K0+K1+K2, by positivity, ?_⟩
-  intro T
-  obtain ⟨f, hf, hfb⟩ := h0 T
-  obtain ⟨df, hdf, hdfb⟩ := h1 T
-  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
-  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
-
-/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
-theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z * G.u (t,z))
-      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
-  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
-
-/-- The second spatial product rule includes both mixed Hessian terms. -/
-theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
-      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
-    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
-
-/-- A spatial cutoff is constant in the within-time product rule. -/
-theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
-  (G.hasDeriv_time t ht x).const_mul (ψ x)
-
-section Bilinear
-variable {F H J : Type*}
-  [NormedAddCommGroup F] [NormedSpace ℝ F]
-  [NormedAddCommGroup H] [NormedSpace ℝ H]
-  [NormedAddCommGroup J] [NormedSpace ℝ J]
-
-omit [NormedSpace ℝ E] in
-/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
-theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
-  intro p hp q hq
-  have hf := ParabolicHolder.holder_le f hp hq
-  have hg := ParabolicHolder.holder_le g hp hq
-  have hf0 := ParabolicHolder.norm_le f p
-  have hg0 := ParabolicHolder.norm_le g q
-  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
-  calc
-    ‖B (f p) (g p) - B (f q) (g q)‖ =
-        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
-      congr 1
-      simp only [map_sub, ContinuousLinearMap.sub_apply]
-      abel
-    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
-    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
-      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
-    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
-        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
-      apply add_le_add
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
-          (norm_nonneg _) (by positivity)
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
-          (norm_nonneg _) (by positivity)
-    _ = _ := by ring
-
-/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
-def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
-  ofFunction (fun p => B (f p) (g p))
-    (fun p hp => by simp [zero_off f hp])
-    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
-    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
-
-omit [NormedSpace ℝ E] in
-/-- The bilinear carrier norm has an explicit product bound. -/
-theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
-    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
-    (bilinear_holder B f g)
-  nlinarith [h]
-
-end Bilinear
-
-local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
-  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
-
-/-- Assemble the cutoff graph from its three spatial carriers. -/
-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
-    (G : Graph (E := E) α T) : Graph (E := E) α T where
-  u := f * G.u
-  ut := f * G.ut
-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
-  hasFDeriv := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv hψ G ht x using 1
-    · funext z
-      simp only [mul_apply, hf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
-  hasFDeriv_du := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv_du hψ G ht x using 1
-    · funext z
-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
-      rfl
-  hasDeriv_time := by
-    intro t ht x
-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
-      by_cases hs : (s,x) ∈ cylinder T
-      · simp [mul_apply, hf (s,x) hs]
-      · simp [mul_apply, zero_off G.u hs]
-    convert cutoff_hasDeriv_time ψ G ht x using 1
-    · funext s; exact he s
-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
-
-/-- Equality of the four stored carriers determines a derivative graph. -/
-theorem graph_ext_components {G H : Graph (E := E) α T}
-    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
-    G = H := by
-  cases G
-  cases H
-  simp_all
-
-/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
-def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
-  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
-  map_add' G H := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
-      simp only [map_add, ContinuousLinearMap.add_apply]
-      module
-  map_smul' c G := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.u p) = c • (f p * (G.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.ut p) = c • (f p * (G.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
-      simp only [map_smul, ContinuousLinearMap.smul_apply]
-      module
-
-
-set_option maxHeartbeats 4000000 in
-/-- The cutoff graph map is bounded in the original four-component norm. -/
-theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
-      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
-  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
-  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
-  let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
-  have hA : 0 ≤ A := by dsimp [A]; positivity
-  have hB : 0 ≤ B := by dsimp [B]; positivity
-  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
-  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
-  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
-  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
-  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
-  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
-  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
-  refine ⟨20 * B * A, ?_⟩
-  intro G
-  have hGu := norm_u_le G
-  have hGut := norm_ut_le G
-  have hGdu := norm_du_le G
-  have hGddu := norm_ddu_le G
-  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  rw [ParabolicSolutionGraph.norm_eq]
-  change ‖f * G.u‖ + ‖f * G.ut‖ +
-    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
-    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
-      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
-  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
-  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
-    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
-  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
-  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
-  nlinarith
-
-/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
-theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
-    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
-        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
-        (C G).ddu (t,x) =
-          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
-  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
-  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
-  have hf := fun p hp => (heq p hp).1
-  have hdf := fun p hp => (heq p hp).2.1
-  have hddf := fun p hp => (heq p hp).2.2
-  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
-  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
-  let C := L.mkContinuous B hB
-  refine ⟨C, ?_, ?_⟩
-  · intro G p
-    change f p * G.u p = ψ p.2 * G.u p
-    by_cases hp : p ∈ cylinder T
-    · rw [hf p hp]
-    · simp [zero_off G.u hp]
-  · intro G t ht x
-    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
-    change f (t,x) * G.ut (t,x) = _ ∧
-      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
-    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp]
-    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
-      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
-      rfl
-
-end Poincare.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicCutoffCommutator
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
+    | throwError "module not found"
+  let mut count := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      count := count + 1
+      elabCommand (← `(command| #print axioms $(mkIdent n)))
+      unless axs.size == 3 && axs.contains ``propext &&
+          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected foundational dependencies for {n}: {axs}"
+  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "exit: 0\n",
  "'Poincare.ParabolicCutoffCommutator.graph_ext_components' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_31' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_17' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_25' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_38' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_15' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_35' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_36' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_10' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_39' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers.eq_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_3' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicSolutionGraph.Graph.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_4' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_26' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_7' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_14' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_13' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_9' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_22' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_21' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.norm_bilinearY_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_29' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_20' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.sqrt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_11' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_28' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_8' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv_du' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_operator' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_24' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoffGraph_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_41' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicHolder.ofFunction.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_5' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_12' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_27' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasDeriv_time' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_32' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_19' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_jet_carriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.hessianBoundedSMul' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.power_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_33' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_34' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_40' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder._abel_1_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_23' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.holder_of_increments' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_18' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_37' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_16' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_30' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "EXACT_MODULE_AUDIT declarations=90; every declaration has exactly the required three dependencies\n"
]
```

</details>

<details>
<summary>run-047</summary>

Source SHA-256: `67078ffd061f52818bb3ce249aa60934c1dc312f183af782e01b61c08d093ef9`.

```diff
--- preceding snapshot
+++ run-047.lean
@@ -1,16 +1,155 @@
 import Poincare.Global.ParabolicCutoffCommutator
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
-    | throwError "module not found"
-  let mut count := 0
-  for (n, _) in env.constants.map₁.toList do
-    if env.getModuleIdxFor? n == some idx then
-      let axs ← liftCoreM (collectAxioms n)
-      count := count + 1
-      elabCommand (← `(command| #print axioms $(mkIdent n)))
-      unless axs.size == 3 && axs.contains ``propext &&
-          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected foundational dependencies for {n}: {axs}"
-  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+local notation "V" => ClosedSmoothModel 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (p : ℝ × V) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_left
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :
+    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _
+    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),
+    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
+theorem cutoff_commutator_identity {ψ : V → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
+    (a : Fin 3 → Fin 3 → Y (E := V) α T ℝ)
+    (drift : Fin 3 → Y (E := V) α T ℝ) (potential : Y (E := V) α T ℝ)
+    (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
+    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
+      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x (e j)))
+    (hc : ∀ t ∈ Icc 0 T, ∀ x,
+      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x (e j) (e k)) -
+        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x (e j)) :
+    ∃ C : Graph (E := V) α T →L[ℝ] Graph (E := V) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) (e i) (e j)) -
+          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) (e i)) - potential (t,x) * (C G).u (t,x)) -
+        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) (e i) (e j)) -
+          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) (e i)) - potential (t,x) * G.u (t,x)) =
+        (∑ i : Fin 3, b i (t,x) * G.du (t,x) (e i)) + c (t,x) * G.u (t,x)) := by
+  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro G t ht x
+  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
+  rw [hut, hdu, hddu, hu G (t,x)]
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+end Poincare.ParabolicCutoffCommutator
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "exit: 1\n",
  "/tmp/parabolic-cutoff-commutator/Item4.lean:126:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached\n",
  "\n",
  "Note: Use `set_option maxHeartbeats <num>` to set the limit.\n",
  "\n",
  "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n"
]
```

</details>

<details>
<summary>run-048</summary>

Source SHA-256: `1ddc66d279f0b7ee3fe6cac770af97c6aec57971225c9baacdb9a10fb4abe11e`.

```json
[
  "--- preceding snapshot\n",
  "+++ run-048.lean\n",
  "@@ -123,6 +123,7 @@\n",
  "   exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)\n",
  "     (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)\n",
  " \n",
  "+set_option maxHeartbeats 4000000 in\n",
  " /-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/\n",
  " theorem cutoff_commutator_identity {ψ : V → ℝ} (hψ : ContDiff ℝ ∞ ψ)\n",
  "     (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)\n"
]
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-049</summary>

Source SHA-256: `9deb0403ba528cfb4f13a7573212e631dd7855205f975974d77dce26872c8d0d`.

```diff
--- preceding snapshot
+++ run-049.lean
@@ -1,4 +1,743 @@
-import Poincare.Global.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicHolderMultiplier
+import Poincare.Global.DuhamelSolutionOperatorBound
+import Mathlib.Analysis.Calculus.MeanValue
+import Mathlib.Analysis.Calculus.ContDiff.RCLike
+
+noncomputable section
+
+set_option maxHeartbeats 800000
+set_option synthInstance.maxHeartbeats 200000
+
+namespace Poincare.ParabolicCutoffCommutator
+
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+
+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
+theorem quadratic_remainder
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
+    (x v : E) (hv : ‖v‖ = 1) :
+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
+      convex_univ (mem_univ x) (mem_univ y)
+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
+      (dh (x + s • v) v) s := by
+    simpa using (hd (x + s • v)).comp_hasDerivAt s
+      (((hasDerivAt_id s).smul_const v).const_add x)
+  have hdr (s : ℝ) : HasDerivAt
+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
+      (dh (x + s • v) v - dh x v) s := by
+    simpa using ((hdline s).sub_const (h x)).sub
+      ((hasDerivAt_id s).mul_const (dh x v))
+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
+    simp only [id_eq]
+    ring
+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
+    (fun s _ => (hdr s).hasDerivWithinAt)
+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
+  · exact hr
+  · calc
+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
+      _ ≤ ‖dh (x + s • v) - dh x‖ := by
+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
+
+/-- The finite-difference estimate with an arbitrary positive step. -/
+theorem finite_difference_derivative
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
+  have hr := quadratic_remainder hd hdd hb hη.le x v hv
+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
+    calc
+      |η * dh x v| = |(h (x + η • v) - h x) -
+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
+      _ ≤ |h (x + η • v) - h x| +
+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
+      _ ≤ _ := add_le_add hu hr
+  rw [abs_mul, abs_of_pos hη] at ht
+  apply (mul_le_mul_iff_right₀ hη).mp
+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
+    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
+    calc
+      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
+      _ = _ := by rw [hc]
+  rw [he]
+  nlinarith
+
+/-- Optimizing the step gives a square-root bound on the full derivative. -/
+theorem derivative_norm_le_sqrt
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hδ : 0 < δ) (hM : 0 ≤ M)
+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
+  intro v hv
+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
+      3 * Real.sqrt δ * M := by
+    have hs := Real.sq_sqrt hδ.le
+    have hp := Real.sqrt_pos.mpr hδ
+    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
+      apply (div_eq_iff (ne_of_gt hp)).2
+      nlinarith
+    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
+    ring
+  exact h.trans_eq he
+
+variable {α T : ℝ}
+
+/-- Time increments of the value are controlled by the stored time derivative. -/
+theorem value_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun r hr => G.hasDeriv_time r hr x)
+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
+  simpa only [Real.norm_eq_abs, mul_comm] using h
+
+/-- The gradient of any derivative graph is uniformly small at short times. -/
+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
+    (norm_nonneg G) ?_ ?_ x
+  · intro y
+    calc
+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
+  · intro y
+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
+
+/-- The supremum of the gradient has the same square-root gain. -/
+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · positivity
+  · exact gradient_bound G hT p.property.1 p.val.2
+
+/-- Time differences of the gradient require no mixed time-space derivative. -/
+theorem gradient_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
+  by_cases hst : t = s
+  · simp [hst]
+  · apply derivative_norm_le_sqrt
+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
+      (value_time_increment G hs ht) ?_ x
+    intro y
+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
+
+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
+theorem gradient_space_increment (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Spatial value increments inherit the improved gradient bound. -/
+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Split a power at a larger positive scale. -/
+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
+    r ^ b ≤ R ^ (b - a) * r ^ a := by
+  have he : r ^ b = r ^ (b - a) * r ^ a := by
+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
+    congr 1
+    ring
+  rw [he]
+  exact mul_le_mul_of_nonneg_right
+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
+
+/-- Interpolate a Lipschitz bound and a bound at scale R. -/
+theorem scale_interpolation {a L r R α : ℝ}
+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (hl : a ≤ L * r) (hb : a ≤ L * R) :
+    a ≤ L * R ^ (1 - α) * r ^ α := by
+  by_cases h : r ≤ R
+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
+    rw [Real.rpow_one] at hp
+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
+  · have he : R ^ (1 - α) * R ^ α = R := by
+      rw [← Real.rpow_add hR]
+      convert Real.rpow_one R using 2
+      ring
+    calc
+      a ≤ L * R := hb
+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
+
+/-- The parabolic spatial scale is the square root of the time scale. -/
+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
+    (Real.sqrt T) ^ p = T ^ (p / 2) := by
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
+  congr 1
+  ring
+
+/-- Spatial Hölder gradient increments carry the desired positive time power. -/
+theorem gradient_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤
+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
+    (L := 6 * ‖G‖) (by positivity)
+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
+  rw [sqrt_rpow hT.le] at h
+  nlinarith [h]
+
+/-- Spatial Hölder value increments gain one additional half power of time. -/
+theorem value_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤
+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    (value_space_increment G hT ht x y)
+    ((abs_sub _ _).trans (by
+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
+    rw [sqrt_rpow hT.le]
+    congr 1
+    ring
+  calc
+    |G.u (t,x) - G.u (t,y)| ≤ _ := h
+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
+
+/-- The temporal Hölder gradient bound follows from the square-root increment. -/
+theorem gradient_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤
+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
+    (show (0 : ℝ) < 1 / 2 by norm_num)
+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
+  have hi := gradient_time_increment G hs ht x
+  rw [Real.sqrt_eq_rpow] at hi
+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
+
+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
+theorem value_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤
+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
+  rw [Real.rpow_one] at hp
+  exact (value_time_increment G hs ht x).trans (by
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
+
+omit [NormedSpace ℝ E] in
+/-- Split a mixed increment through the point with the first time and second position. -/
+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
+    HasHolderBound α (cylinder T) f (Kx + Kt) := by
+  intro p hp q hq
+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (by
+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
+  calc
+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
+      norm_sub_le_norm_sub_add_norm_sub _ _ _
+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
+
+/-- Full gradient Hölder control, including mixed increments. -/
+theorem gradient_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
+  have h := holder_of_increments hα.le
+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (fun t ht => gradient_space_holder G hα hα1 hT ht)
+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
+  convert h using 1
+  ring
+
+/-- Full value Hölder control with its stronger time power. -/
+theorem value_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
+  have h := holder_of_increments (f := G.u) hα.le
+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
+  convert h using 1
+  ring
+
+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
+theorem interpolation_bounds (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
+  constructor
+  · have h := ParabolicHolder.norm_le_of_bounds G.u
+      (show 0 ≤ T * ‖G‖ by positivity)
+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
+      (fun p hp => (time_bound G hp.1 p.2).trans
+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
+      (value_holder G hα hα1 hT)
+    have hp : T ≤ T ^ (1-α/2) := by
+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
+      exact (Real.rpow_one T).symm
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
+  · have h := ParabolicHolder.norm_le_of_bounds G.du
+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+      (fun p hp => gradient_bound G hT hp.1 p.2)
+      (gradient_holder G hα hα1 hT)
+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
+      rw [Real.sqrt_eq_rpow]
+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
+
+/-- A universal constant satisfies the frozen interpolation target. -/
+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
+  intro α hα hα1
+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
+
+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
+  classical
+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+    have h := scale_interpolation (L := 2*A+B) (R := 1)
+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
+    simpa using h
+  refine ⟨A + (2*A+B), by positivity, ?_⟩
+  intro T
+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
+    intro p hp; simp [f, hp]
+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
+    intro p hp; simpa [f, hp] using hA p.2
+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
+    intro p hp q hq
+    simp only [f, if_pos hp, if_pos hq]
+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow (norm_nonneg _) (by
+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
+  refine ⟨fY, ?_, ?_⟩
+  · intro p hp
+    change f p = ψ p.2
+    simp [f, hp]
+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
+
+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
+      ∃ (f : Y (E := E) α T ℝ)
+        (df : Y (E := E) α T (E →L[ℝ] ℝ))
+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
+  refine ⟨K0+K1+K2, by positivity, ?_⟩
+  intro T
+  obtain ⟨f, hf, hfb⟩ := h0 T
+  obtain ⟨df, hdf, hdfb⟩ := h1 T
+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
+
+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z * G.u (t,z))
+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
+
+/-- The second spatial product rule includes both mixed Hessian terms. -/
+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
+
+/-- A spatial cutoff is constant in the within-time product rule. -/
+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
+  (G.hasDeriv_time t ht x).const_mul (ψ x)
+
+section Bilinear
+variable {F H J : Type*}
+  [NormedAddCommGroup F] [NormedSpace ℝ F]
+  [NormedAddCommGroup H] [NormedSpace ℝ H]
+  [NormedAddCommGroup J] [NormedSpace ℝ J]
+
+omit [NormedSpace ℝ E] in
+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
+  intro p hp q hq
+  have hf := ParabolicHolder.holder_le f hp hq
+  have hg := ParabolicHolder.holder_le g hp hq
+  have hf0 := ParabolicHolder.norm_le f p
+  have hg0 := ParabolicHolder.norm_le g q
+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
+  calc
+    ‖B (f p) (g p) - B (f q) (g q)‖ =
+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
+      congr 1
+      simp only [map_sub, ContinuousLinearMap.sub_apply]
+      abel
+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
+      apply add_le_add
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
+          (norm_nonneg _) (by positivity)
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
+          (norm_nonneg _) (by positivity)
+    _ = _ := by ring
+
+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
+  ofFunction (fun p => B (f p) (g p))
+    (fun p hp => by simp [zero_off f hp])
+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
+
+omit [NormedSpace ℝ E] in
+/-- The bilinear carrier norm has an explicit product bound. -/
+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
+    (bilinear_holder B f g)
+  nlinarith [h]
+
+end Bilinear
+
+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
+
+/-- Assemble the cutoff graph from its three spatial carriers. -/
+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
+    (G : Graph (E := E) α T) : Graph (E := E) α T where
+  u := f * G.u
+  ut := f * G.ut
+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
+  hasFDeriv := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv hψ G ht x using 1
+    · funext z
+      simp only [mul_apply, hf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
+  hasFDeriv_du := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv_du hψ G ht x using 1
+    · funext z
+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
+      rfl
+  hasDeriv_time := by
+    intro t ht x
+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
+      by_cases hs : (s,x) ∈ cylinder T
+      · simp [mul_apply, hf (s,x) hs]
+      · simp [mul_apply, zero_off G.u hs]
+    convert cutoff_hasDeriv_time ψ G ht x using 1
+    · funext s; exact he s
+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
+
+/-- Equality of the four stored carriers determines a derivative graph. -/
+theorem graph_ext_components {G H : Graph (E := E) α T}
+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
+    G = H := by
+  cases G
+  cases H
+  simp_all
+
+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
+  map_add' G H := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
+      simp only [map_add, ContinuousLinearMap.add_apply]
+      module
+  map_smul' c G := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.u p) = c • (f p * (G.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.ut p) = c • (f p * (G.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
+      simp only [map_smul, ContinuousLinearMap.smul_apply]
+      module
+
+
+set_option maxHeartbeats 4000000 in
+/-- The cutoff graph map is bounded in the original four-component norm. -/
+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
+  let A := ‖f‖ + ‖df‖ + ‖ddf‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  have hA : 0 ≤ A := by dsimp [A]; positivity
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
+  refine ⟨20 * B * A, ?_⟩
+  intro G
+  have hGu := norm_u_le G
+  have hGut := norm_ut_le G
+  have hGdu := norm_du_le G
+  have hGddu := norm_ddu_le G
+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  rw [ParabolicSolutionGraph.norm_eq]
+  change ‖f * G.u‖ + ‖f * G.ut‖ +
+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
+  nlinarith
+
+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
+        (C G).ddu (t,x) =
+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
+  have hf := fun p hp => (heq p hp).1
+  have hdf := fun p hp => (heq p hp).2.1
+  have hddf := fun p hp => (heq p hp).2.2
+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
+  let C := L.mkContinuous B hB
+  refine ⟨C, ?_, ?_⟩
+  · intro G p
+    change f p * G.u p = ψ p.2 * G.u p
+    by_cases hp : p ∈ cylinder T
+    · rw [hf p hp]
+    · simp [zero_off G.u hp]
+  · intro G t ht x
+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
+    change f (t,x) * G.ut (t,x) = _ ∧
+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp]
+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
+      rfl
+
+end Poincare.ParabolicCutoffCommutator
+
 noncomputable section
 set_option maxHeartbeats 800000
 namespace Poincare.ParabolicCutoffCommutator
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean -o .lake/build/lib/lean/Poincare/Global/ParabolicCutoffCommutator.olean
exit: 0
```

</details>

<details>
<summary>run-050</summary>

Source SHA-256: `b36359b79da42a1561c3e9abb56d41d3e38a4a6a7b79d3a008b71efd3f3a39d3`.

```diff
--- preceding snapshot
+++ run-050.lean
@@ -1,895 +1,16 @@
-import Poincare.Global.ParabolicHolderMultiplier
-import Poincare.Global.DuhamelSolutionOperatorBound
-import Mathlib.Analysis.Calculus.MeanValue
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-
-noncomputable section
-
-set_option maxHeartbeats 800000
-set_option synthInstance.maxHeartbeats 200000
-
-namespace Poincare.ParabolicCutoffCommutator
-
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-
-/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
-theorem quadratic_remainder
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
-    (x v : E) (hv : ‖v‖ = 1) :
-    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
-  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
-    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
-      convex_univ (mem_univ x) (mem_univ y)
-  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
-      (dh (x + s • v) v) s := by
-    simpa using (hd (x + s • v)).comp_hasDerivAt s
-      (((hasDerivAt_id s).smul_const v).const_add x)
-  have hdr (s : ℝ) : HasDerivAt
-      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
-      (dh (x + s • v) v - dh x v) s := by
-    simpa using ((hdline s).sub_const (h x)).sub
-      ((hasDerivAt_id s).mul_const (dh x v))
-  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
-    simp only [id_eq]
-    ring
-  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
-    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
-    (fun s _ => (hdr s).hasDerivWithinAt)
-    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
-    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
-  · exact hr
-  · calc
-      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
-      _ ≤ ‖dh (x + s • v) - dh x‖ := by
-        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
-      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
-
-/-- The finite-difference estimate with an arbitrary positive step. -/
-theorem finite_difference_derivative
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
-    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
-    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
-  have hr := quadratic_remainder hd hdd hb hη.le x v hv
-  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
-    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
-  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
-    calc
-      |η * dh x v| = |(h (x + η • v) - h x) -
-          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
-      _ ≤ |h (x + η • v) - h x| +
-          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
-      _ ≤ _ := add_le_add hu hr
-  rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_iff_right₀ hη).mp
-  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
-    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
-    calc
-      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
-      _ = _ := by rw [hc]
-  rw [he]
-  nlinarith
-
-/-- Optimizing the step gives a square-root bound on the full derivative. -/
-theorem derivative_norm_le_sqrt
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hδ : 0 < δ) (hM : 0 ≤ M)
-    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
-    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
-  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
-  intro v hv
-  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
-  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
-      3 * Real.sqrt δ * M := by
-    have hs := Real.sq_sqrt hδ.le
-    have hp := Real.sqrt_pos.mpr hδ
-    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
-      apply (div_eq_iff (ne_of_gt hp)).2
-      nlinarith
-    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
-    ring
-  exact h.trans_eq he
-
-variable {α T : ℝ}
-
-/-- Time increments of the value are controlled by the stored time derivative. -/
-theorem value_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
-  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-    (fun r hr => G.hasDeriv_time r hr x)
-    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
-  simpa only [Real.norm_eq_abs, mul_comm] using h
-
-/-- The gradient of any derivative graph is uniformly small at short times. -/
-theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
-    (norm_nonneg G) ?_ ?_ x
-  · intro y
-    calc
-      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
-      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
-  · intro y
-    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
-
-/-- The supremum of the gradient has the same square-root gain. -/
-theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
-    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply csSup_le (insert_nonempty _ _)
-  rintro r (rfl | ⟨p, rfl⟩)
-  · positivity
-  · exact gradient_bound G hT p.property.1 p.val.2
-
-/-- Time differences of the gradient require no mixed time-space derivative. -/
-theorem gradient_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
-  by_cases hst : t = s
-  · simp [hst]
-  · apply derivative_norm_le_sqrt
-      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
-      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
-      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
-      (value_time_increment G hs ht) ?_ x
-    intro y
-    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
-      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
-
-/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
-theorem gradient_space_increment (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
-    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Spatial value increments inherit the improved gradient bound. -/
-theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
-    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Split a power at a larger positive scale. -/
-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
-    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
-    r ^ b ≤ R ^ (b - a) * r ^ a := by
-  have he : r ^ b = r ^ (b - a) * r ^ a := by
-    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
-    congr 1
-    ring
-  rw [he]
-  exact mul_le_mul_of_nonneg_right
-    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
-
-/-- Interpolate a Lipschitz bound and a bound at scale R. -/
-theorem scale_interpolation {a L r R α : ℝ}
-    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
-    (hl : a ≤ L * r) (hb : a ≤ L * R) :
-    a ≤ L * R ^ (1 - α) * r ^ α := by
-  by_cases h : r ≤ R
-  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
-    rw [Real.rpow_one] at hp
-    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
-  · have he : R ^ (1 - α) * R ^ α = R := by
-      rw [← Real.rpow_add hR]
-      convert Real.rpow_one R using 2
-      ring
-    calc
-      a ≤ L * R := hb
-      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
-      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
-        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
-
-/-- The parabolic spatial scale is the square root of the time scale. -/
-theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
-    (Real.sqrt T) ^ p = T ^ (p / 2) := by
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
-  congr 1
-  ring
-
-/-- Spatial Hölder gradient increments carry the desired positive time power. -/
-theorem gradient_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤
-      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
-    (L := 6 * ‖G‖) (by positivity)
-    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
-    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
-      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
-  rw [sqrt_rpow hT.le] at h
-  nlinarith [h]
-
-/-- Spatial Hölder value increments gain one additional half power of time. -/
-theorem value_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤
-      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
-    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
-  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
-    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
-    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    (value_space_increment G hT ht x y)
-    ((abs_sub _ _).trans (by
-      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
-      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
-  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
-    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
-    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
-    rw [sqrt_rpow hT.le]
-    congr 1
-    ring
-  calc
-    |G.u (t,x) - G.u (t,y)| ≤ _ := h
-    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
-        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
-
-/-- The temporal Hölder gradient bound follows from the square-root increment. -/
-theorem gradient_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤
-      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
-    (show (0 : ℝ) < 1 / 2 by norm_num)
-  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
-  have hi := gradient_time_increment G hs ht x
-  rw [Real.sqrt_eq_rpow] at hi
-  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
-
-/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
-theorem value_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤
-      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
-  rw [Real.rpow_one] at hp
-  exact (value_time_increment G hs ht x).trans (by
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
-
-omit [NormedSpace ℝ E] in
-/-- Split a mixed increment through the point with the first time and second position. -/
-theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
-    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
-    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
-      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
-    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
-      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
-    HasHolderBound α (cylinder T) f (Kx + Kt) := by
-  intro p hp q hq
-  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
-    Real.rpow_le_rpow (norm_nonneg _) (by
-      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
-  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
-    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
-    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
-      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
-  calc
-    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
-      norm_sub_le_norm_sub_add_norm_sub _ _ _
-    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
-      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
-    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
-      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
-
-/-- Full gradient Hölder control, including mixed increments. -/
-theorem gradient_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
-  have h := holder_of_increments hα.le
-    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (fun t ht => gradient_space_holder G hα hα1 hT ht)
-    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
-  convert h using 1
-  ring
-
-/-- Full value Hölder control with its stronger time power. -/
-theorem value_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
-  have h := holder_of_increments (f := G.u) hα.le
-    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
-    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
-    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
-    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
-  convert h using 1
-  ring
-
-/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
-theorem interpolation_bounds (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
-  constructor
-  · have h := ParabolicHolder.norm_le_of_bounds G.u
-      (show 0 ≤ T * ‖G‖ by positivity)
-      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
-      (fun p hp => (time_bound G hp.1 p.2).trans
-        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
-      (value_holder G hα hα1 hT)
-    have hp : T ≤ T ^ (1-α/2) := by
-      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
-      exact (Real.rpow_one T).symm
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
-      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
-  · have h := ParabolicHolder.norm_le_of_bounds G.du
-      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
-      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-      (fun p hp => gradient_bound G hT hp.1 p.2)
-      (gradient_holder G hα hα1 hT)
-    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
-      rw [Real.sqrt_eq_rpow]
-      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
-
-/-- A universal constant satisfies the frozen interpolation target. -/
-theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
-      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
-  intro α hα hα1
-  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
-
-/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
-theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
-    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
-      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
-  classical
-  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
-  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
-  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
-  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
-    have h := scale_interpolation (L := 2*A+B) (R := 1)
-      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
-      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
-      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
-    simpa using h
-  refine ⟨A + (2*A+B), by positivity, ?_⟩
-  intro T
-  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
-  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
-    intro p hp; simp [f, hp]
-  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
-    intro p hp; simpa [f, hp] using hA p.2
-  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
-    intro p hp q hq
-    simp only [f, if_pos hp, if_pos hq]
-    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
-      (Real.rpow_le_rpow (norm_nonneg _) (by
-        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
-  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
-  refine ⟨fY, ?_, ?_⟩
-  · intro p hp
-    change f p = ψ p.2
-    simp [f, hp]
-  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
-
-/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
-theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
-    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
-      ∃ (f : Y (E := E) α T ℝ)
-        (df : Y (E := E) α T (E →L[ℝ] ℝ))
-        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
-      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
-        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
-      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
-  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
-  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
-  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
-  refine ⟨K0+K1+K2, by positivity, ?_⟩
-  intro T
-  obtain ⟨f, hf, hfb⟩ := h0 T
-  obtain ⟨df, hdf, hdfb⟩ := h1 T
-  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
-  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
-
-/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
-theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z * G.u (t,z))
-      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
-  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
-
-/-- The second spatial product rule includes both mixed Hessian terms. -/
-theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
-      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
-    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
-
-/-- A spatial cutoff is constant in the within-time product rule. -/
-theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
-  (G.hasDeriv_time t ht x).const_mul (ψ x)
-
-section Bilinear
-variable {F H J : Type*}
-  [NormedAddCommGroup F] [NormedSpace ℝ F]
-  [NormedAddCommGroup H] [NormedSpace ℝ H]
-  [NormedAddCommGroup J] [NormedSpace ℝ J]
-
-omit [NormedSpace ℝ E] in
-/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
-theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
-  intro p hp q hq
-  have hf := ParabolicHolder.holder_le f hp hq
-  have hg := ParabolicHolder.holder_le g hp hq
-  have hf0 := ParabolicHolder.norm_le f p
-  have hg0 := ParabolicHolder.norm_le g q
-  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
-  calc
-    ‖B (f p) (g p) - B (f q) (g q)‖ =
-        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
-      congr 1
-      simp only [map_sub, ContinuousLinearMap.sub_apply]
-      abel
-    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
-    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
-      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
-    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
-        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
-      apply add_le_add
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
-          (norm_nonneg _) (by positivity)
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
-          (norm_nonneg _) (by positivity)
-    _ = _ := by ring
-
-/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
-def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
-  ofFunction (fun p => B (f p) (g p))
-    (fun p hp => by simp [zero_off f hp])
-    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
-    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
-
-omit [NormedSpace ℝ E] in
-/-- The bilinear carrier norm has an explicit product bound. -/
-theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
-    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
-    (bilinear_holder B f g)
-  nlinarith [h]
-
-end Bilinear
-
-local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
-  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
-
-/-- Assemble the cutoff graph from its three spatial carriers. -/
-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
-    (G : Graph (E := E) α T) : Graph (E := E) α T where
-  u := f * G.u
-  ut := f * G.ut
-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
-  hasFDeriv := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv hψ G ht x using 1
-    · funext z
-      simp only [mul_apply, hf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
-  hasFDeriv_du := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv_du hψ G ht x using 1
-    · funext z
-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
-      rfl
-  hasDeriv_time := by
-    intro t ht x
-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
-      by_cases hs : (s,x) ∈ cylinder T
-      · simp [mul_apply, hf (s,x) hs]
-      · simp [mul_apply, zero_off G.u hs]
-    convert cutoff_hasDeriv_time ψ G ht x using 1
-    · funext s; exact he s
-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
-
-/-- Equality of the four stored carriers determines a derivative graph. -/
-theorem graph_ext_components {G H : Graph (E := E) α T}
-    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
-    G = H := by
-  cases G
-  cases H
-  simp_all
-
-/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
-def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
-  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
-  map_add' G H := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
-      simp only [map_add, ContinuousLinearMap.add_apply]
-      module
-  map_smul' c G := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.u p) = c • (f p * (G.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.ut p) = c • (f p * (G.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
-      simp only [map_smul, ContinuousLinearMap.smul_apply]
-      module
-
-
-set_option maxHeartbeats 4000000 in
-/-- The cutoff graph map is bounded in the original four-component norm. -/
-theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
-      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
-  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
-  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
-  let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
-  have hA : 0 ≤ A := by dsimp [A]; positivity
-  have hB : 0 ≤ B := by dsimp [B]; positivity
-  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
-  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
-  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
-  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
-  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
-  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
-  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
-  refine ⟨20 * B * A, ?_⟩
-  intro G
-  have hGu := norm_u_le G
-  have hGut := norm_ut_le G
-  have hGdu := norm_du_le G
-  have hGddu := norm_ddu_le G
-  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  rw [ParabolicSolutionGraph.norm_eq]
-  change ‖f * G.u‖ + ‖f * G.ut‖ +
-    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
-    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
-      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
-  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
-  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
-    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
-  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
-  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
-  nlinarith
-
-/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
-theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
-    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
-        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
-        (C G).ddu (t,x) =
-          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
-  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
-  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
-  have hf := fun p hp => (heq p hp).1
-  have hdf := fun p hp => (heq p hp).2.1
-  have hddf := fun p hp => (heq p hp).2.2
-  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
-  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
-  let C := L.mkContinuous B hB
-  refine ⟨C, ?_, ?_⟩
-  · intro G p
-    change f p * G.u p = ψ p.2 * G.u p
-    by_cases hp : p ∈ cylinder T
-    · rw [hf p hp]
-    · simp [zero_off G.u hp]
-  · intro G t ht x
-    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
-    change f (t,x) * G.ut (t,x) = _ ∧
-      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
-    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp]
-    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
-      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
-      rfl
-
-end Poincare.ParabolicCutoffCommutator
-
-noncomputable section
-set_option maxHeartbeats 800000
-namespace Poincare.ParabolicCutoffCommutator
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
-
-/-- Evaluate a first derivative carrier on a unit direction. -/
-def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    Y (E := E) α T ℝ :=
-  ofFunction (fun p => H p v)
-    (fun p hp => by simp [zero_off H hp])
-    ⟨‖H‖, fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
-    ⟨‖H‖, fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
-
-/-- Evaluation is bounded in the full Hölder norm. -/
-theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
-    (norm_nonneg H) (norm_nonneg H)
-    (fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
-    (fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
-  linarith
-
-local notation "V" => ClosedSmoothModel 3
-local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
-
-/-- The first-order forcing associated to the explicit commutator coefficients. -/
-def firstOrderForcing (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) : Y (E := V) α T ℝ :=
-  (∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)) + c * G.u
-
-/-- The carrier evaluates to the first-order coefficient formula. -/
-theorem firstOrderForcing_apply (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (p : ℝ × V) :
-    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p := by
-  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
-    derivativeEntry, ofFunction_apply]
-
-/-- The commutator uses only the value and gradient norms. -/
-theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) :
-    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
-  calc
-    ‖firstOrderForcing b c G‖ ≤
-        ‖∑ i : Fin 3, b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖ + ‖c * G.u‖ := norm_add_le _ _
-    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du (e i) (OrthonormalBasis.norm_eq_one e i)‖) + ‖c‖ * ‖G.u‖ :=
-      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
-    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
-      apply add_le_add_left
-      apply Finset.sum_le_sum
-      intro i hi
-      exact (ParabolicHolder.norm_mul_le _ _).trans
-        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
-    _ = _ := by rw [← Finset.sum_mul]; ring
-
-/-- The commutator has separate positive time powers for its two coefficient families. -/
-theorem firstOrder_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
-  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
-  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
-  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
-  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
-  have h3 := norm_firstOrderForcing_le b c G
-  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
-
-/-- The common weaker time exponent controls both first-order terms. -/
-theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (G : Graph (E := V) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
-  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
-    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-  have h := firstOrder_time_bound b c G hα hα1 hT hT1
-  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
-
-/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
-def firstOrderLinearMap (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ) :
-    Graph (E := V) α T →ₗ[ℝ] Y (E := V) α T ℝ where
-  toFun := firstOrderForcing b c
-  map_add' G H := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [add_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (G.du p (e i) + H.du p (e i))) + c p * (G.u p + H.u p) = _
-    simp only [mul_add, Finset.sum_add_distrib]
-    ring
-  map_smul' r G := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [smul_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (r * G.du p (e i))) + c p * (r * G.u p) = _
-    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
-    ring
-
-/-- The frozen commutator operator target, with a universal constant. -/
-theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∀ (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ),
-    ∃ K : Graph (E := V) α T →L[ℝ] Y (E := V) α T ℝ,
-      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p (e i)) + c p * G.u p) ∧
-      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
-  intro α hα hα1
-  refine ⟨24, by norm_num, ?_⟩
-  intro T hT hT1 b c
-  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
-  let K := (firstOrderLinearMap b c).mkContinuous B
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
-  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-
-set_option maxHeartbeats 4000000 in
-/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
-theorem cutoff_commutator_identity {ψ : V → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
-    (a : Fin 3 → Fin 3 → Y (E := V) α T ℝ)
-    (drift : Fin 3 → Y (E := V) α T ℝ) (potential : Y (E := V) α T ℝ)
-    (b : Fin 3 → Y (E := V) α T ℝ) (c : Y (E := V) α T ℝ)
-    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
-      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x (e j)))
-    (hc : ∀ t ∈ Icc 0 T, ∀ x,
-      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x (e j) (e k)) -
-        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x (e j)) :
-    ∃ C : Graph (E := V) α T →L[ℝ] Graph (E := V) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) (e i) (e j)) -
-          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) (e i)) - potential (t,x) * (C G).u (t,x)) -
-        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) (e i) (e j)) -
-          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) (e i)) - potential (t,x) * G.u (t,x)) =
-        (∑ i : Fin 3, b i (t,x) * G.du (t,x) (e i)) + c (t,x) * G.u (t,x)) := by
-  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
-  refine ⟨C, hu, ?_⟩
-  intro G t ht x
-  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
-  rw [hut, hdu, hddu, hu G (t,x)]
-  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
-    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
-    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
-  ring
-
-end Poincare.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicCutoffCommutator
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
+    | throwError "module not found"
+  let mut count := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      count := count + 1
+      elabCommand (← `(command| #print axioms $(mkIdent n)))
+      unless axs.size == 3 && axs.contains ``propext &&
+          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected foundational dependencies for {n}: {axs}"
+  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "exit: 1\n",
  "'Poincare.ParabolicCutoffCommutator.graph_ext_components' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'_private.Poincare.Global.ParabolicCutoffCommutator.0.Poincare.ParabolicCutoffCommutator._aux_Poincare_Global_ParabolicCutoffCommutator___unexpand_EuclideanSpace_basisFun_1' does not depend on any axioms\n",
  "/tmp/parabolic-cutoff-commutator/ModuleAudit.lean:3:0: error: Unexpected foundational dependencies for _private.Poincare.Global.ParabolicCutoffCommutator.0.Poincare.ParabolicCutoffCommutator._aux_Poincare_Global_ParabolicCutoffCommutator___unexpand_EuclideanSpace_basisFun_1: []\n"
]
```

</details>

<details>
<summary>run-051</summary>

Source SHA-256: `212b645f952257284ec45e9025b1d20bab0ac815998b6f7bc8aee5fc096465c2`.

```diff
--- preceding snapshot
+++ run-051.lean
@@ -1,16 +1,266 @@
 import Poincare.Global.ParabolicCutoffCommutator
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
-    | throwError "module not found"
-  let mut count := 0
-  for (n, _) in env.constants.map₁.toList do
-    if env.getModuleIdxFor? n == some idx then
-      let axs ← liftCoreM (collectAxioms n)
-      count := count + 1
-      elabCommand (← `(command| #print axioms $(mkIdent n)))
-      unless axs.size == 3 && axs.contains ``propext &&
-          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected foundational dependencies for {n}: {axs}"
-  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
+import Poincare.Global.NearIdentityParabolicRightInverse
+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
+import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
+import Poincare.Global.DeTurckPrincipalIdentity
+import Poincare.Global.CompactCoefficientEllipticity
+import Mathlib.Analysis.Calculus.ContDiff.RCLike
+import Mathlib.Topology.MetricSpace.Contracting
+
+set_option autoImplicit false
+noncomputable section
+open Set
+open scoped Manifold ContDiff
+namespace FiniteAtlasSurvey
+open Poincare
+local notation "E" => ClosedSmoothModel 3
+local notation "I" => closedSmoothModelWithCorners 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
+abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
+abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
+  [IsManifold I ∞ M]
+
+structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
+    [IsManifold I ∞ M] where
+  cover : FiniteExtendedChartCover (n := 3) (M := M)
+  region : Fin cover.chartCount → Set M
+  region_open : ∀ i, IsOpen (region i)
+  region_cover : (⋃ i, region i) = univ
+  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
+  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
+  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
+  subordinate : partition.IsSubordinate region
+
+variable (A : AtlasData M)
+abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
+abbrev LocalProduct (H : Type*) := Index A → H
+
+def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
+def coordSupport (i : Fin A.cover.chartCount) : Set E :=
+  chart A i '' tsupport (A.partition i)
+def change (i j : Fin A.cover.chartCount) (z : E) : E :=
+  chart A j ((chart A i).symm z)
+def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
+  (fderiv ℝ (change A i j) (chart A i x) (e a)) c
+
+def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
+  ({ toFun := fun f => f p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
+
+def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
+  ({ toFun := fun G => G.u p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)
+
+variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
+def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
+    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
+  (ev p).comp (ContinuousLinearMap.proj (i, a, b))
+
+def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
+    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
+  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
+    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
+      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)
+
+def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
+    ⨅ (z : {z : E // z ∉ coordSupport A i}),
+    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap
+
+def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
+    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap
+
+def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
+    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
+    LinearMap.ker (overlap A ev i j a b t x).toLinearMap
+
+def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
+abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
+abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
+
+structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
+  entries : LocalProduct A H
+  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
+  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
+  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
+    overlap A ev i j a b t x entries = 0
+
+-- Statement definitions, not proofs of closedness, completeness or equivalence.
+def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
+  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
+def carrierCompleteGoal (α T : ℝ) : Prop :=
+  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
+def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
+  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)
+
+-- Positive-time candidate strengthened norm functional; no norm instance claimed.
+def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
+  T ^ (-(1 - α / 2)) * ‖G.u‖ +
+  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖
+
+def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
+    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖
+
+-- Coefficients are the resulting commutator coefficients, already zero-extended.
+def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
+    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
+  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p
+
+def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
+  ∃ K : Jet α T →L[ℝ] Scalar α T,
+    (∀ G p, K G p = firstOrderValue b c G p) ∧
+    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)
+
+structure CutoffData (α T : ℝ) where
+  psi : E → ℝ
+  smooth : ContDiff ℝ ∞ psi
+  compact : HasCompactSupport psi
+  a : Fin 3 → Fin 3 → Scalar α T
+  drift : Fin 3 → Scalar α T
+  b : Fin 3 → Scalar α T
+  c : Scalar α T
+  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
+    b k (t,x) = -(∑ j : Fin 3,
+      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
+  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
+    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
+      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
+      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)
+
+def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
+    ∀ G p, (C G).u p = D.psi p.2 * G.u p
+
+structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
+  S : Scalar α T →L[ℝ] Jet α T
+  bound : ‖S‖ ≤ C_S
+  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
+    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
+      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)
+
+def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
+    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
+  0 < α → 0 < T →
+  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
+  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
+  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
+    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖
+
+-- Actual chart coefficient agreement is separate from the frozen analytic data.
+structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
+  cutoff : E → ℝ
+  smooth : ContDiff ℝ ∞ cutoff
+  compact : HasCompactSupport cutoff
+  one_on : ∀ z ∈ U, cutoff z = 1
+  b : Fin 3 → Fin 3 → Scalar α T
+  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
+    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))
+
+def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
+    (N : X_M A α T → Y_M A α T) : Prop :=
+  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
+    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
+  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
+def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
+    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
+    (G : Jet α T) (p : ℝ × E) : ℝ :=
+  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
+    a i j p * G.ddu p (e i) (e j)) -
+    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p
+
+def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
+    (potential : Scalar α T) : Prop :=
+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
+    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
+    (∀ G t, t ∈ Icc 0 T → ∀ x,
+      localLinearValue D.a D.drift potential (C G) (t,x) -
+        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
+          firstOrderValue D.b D.c G (t,x))
+
+def oscillationExtensionGoal : Prop :=
+  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
+  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
+  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
+  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
+  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
+    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
+  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∃ b : Fin 3 → Fin 3 → Scalar α T,
+      (∀ t ∈ Icc 0 T, ∀ x i j,
+        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
+      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
+      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)
+
+def frozenCLMGoal : Prop :=
+  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
+  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
+  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
+  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)
+
+abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
+  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
+
+def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
+  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)
+
+def localizedValue {T : ℝ} (F : TensorField (M := M) T)
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
+  classical
+  exact if ht : p.1 ∈ Icc 0 T then
+    if p.2 ∈ (chart A i).target then
+      let x := (chart A i).symm p.2
+      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
+    else 0
+  else 0
+
+def reconstructionGoal (α T : ℝ) : Prop :=
+  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
+    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p
+
+abbrev Jet1 := E →L[ℝ] Bilin
+abbrev Jet2 := E →L[ℝ] Jet1
+
+def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
+    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
+  (∑ i : Fin 3, ∑ j : Fin 3,
+    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
+    DeTurckPrincipalIdentity.lowerTerm B DB G J
+
+set_option synthInstance.maxHeartbeats 400000 in
+def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
+    (z h : Bilin × Jet1 × Jet2) : Bilin :=
+  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
+    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
+    (∑ i : Fin 3, ∑ j : Fin 3,
+      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
+end FiniteAtlasSurvey
+
+example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation
+example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) : FiniteAtlasSurvey.cutoffGraphGoal D := by
+  intro hα hα1 hT hT1
+  obtain ⟨C, hu, _⟩ := Poincare.ParabolicCutoffCommutator.exists_cutoff_operator D.smooth D.compact hα hα1
+  exact ⟨C, hu⟩
+
+example : FiniteAtlasSurvey.commutatorGoal := Poincare.ParabolicCutoffCommutator.commutator
+example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) (potential : FiniteAtlasSurvey.Scalar α T) :
+    FiniteAtlasSurvey.cutoffIdentityGoal D potential := by
+  intro hα hα1 hT hT1
+  exact Poincare.ParabolicCutoffCommutator.cutoff_commutator_identity D.smooth D.compact hα hα1
+    D.a D.drift potential D.b D.c D.b_eq D.c_eq
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/FinalTargets.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-052</summary>

Source SHA-256: `3615959ec31f85634f640f9ea4e9b197eeefbf2e09d29eb4864f5b099ad9af82`.

```diff
--- preceding snapshot
+++ run-052.lean
@@ -1,266 +1,893 @@
-import Poincare.Global.ParabolicCutoffCommutator
-import Poincare.Global.NearIdentityParabolicRightInverse
-import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
-import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
-import Poincare.Global.DeTurckPrincipalIdentity
-import Poincare.Global.CompactCoefficientEllipticity
+import Poincare.Global.ParabolicHolderMultiplier
+import Poincare.Global.DuhamelSolutionOperatorBound
+import Mathlib.Analysis.Calculus.MeanValue
 import Mathlib.Analysis.Calculus.ContDiff.RCLike
-import Mathlib.Topology.MetricSpace.Contracting
-
-set_option autoImplicit false
+
 noncomputable section
-open Set
-open scoped Manifold ContDiff
-namespace FiniteAtlasSurvey
-open Poincare
-local notation "E" => ClosedSmoothModel 3
-local notation "I" => closedSmoothModelWithCorners 3
-local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
-abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
-abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
-abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
-
-universe u
-variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
-  [IsManifold I ∞ M]
-
-structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
-    [IsManifold I ∞ M] where
-  cover : FiniteExtendedChartCover (n := 3) (M := M)
-  region : Fin cover.chartCount → Set M
-  region_open : ∀ i, IsOpen (region i)
-  region_cover : (⋃ i, region i) = univ
-  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
-  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
-  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
-  subordinate : partition.IsSubordinate region
-
-variable (A : AtlasData M)
-abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
-abbrev LocalProduct (H : Type*) := Index A → H
-
-def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
-def coordSupport (i : Fin A.cover.chartCount) : Set E :=
-  chart A i '' tsupport (A.partition i)
-def change (i j : Fin A.cover.chartCount) (z : E) : E :=
-  chart A j ((chart A i).symm z)
-def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
-  (fderiv ℝ (change A i j) (chart A i x) (e a)) c
-
-def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
-  ({ toFun := fun f => f p
-     map_add' := fun _ _ => rfl
-     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
-    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
-
-def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
-  ({ toFun := fun G => G.u p
-     map_add' := fun _ _ => rfl
-     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
-    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)
-
-variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
-def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
-    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
-  (ev p).comp (ContinuousLinearMap.proj (i, a, b))
-
-def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
-    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
-  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
-    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
-      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)
-
-def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
-    ⨅ (z : {z : E // z ∉ coordSupport A i}),
-    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap
-
-def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
-    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap
-
-def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
-    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
-    LinearMap.ker (overlap A ev i j a b t x).toLinearMap
-
-def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
-abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
-abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
-
-structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
-  entries : LocalProduct A H
-  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
-  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
-  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
-    overlap A ev i j a b t x entries = 0
-
--- Statement definitions, not proofs of closedness, completeness or equivalence.
-def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
-  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
-def carrierCompleteGoal (α T : ℝ) : Prop :=
-  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
-def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
-  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)
-
--- Positive-time candidate strengthened norm functional; no norm instance claimed.
-def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
-  T ^ (-(1 - α / 2)) * ‖G.u‖ +
-  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖
-
-def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
-    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖
-
--- Coefficients are the resulting commutator coefficients, already zero-extended.
-def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
-    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
-  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p
-
-def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
-  ∃ K : Jet α T →L[ℝ] Scalar α T,
-    (∀ G p, K G p = firstOrderValue b c G p) ∧
-    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)
-
-structure CutoffData (α T : ℝ) where
-  psi : E → ℝ
-  smooth : ContDiff ℝ ∞ psi
-  compact : HasCompactSupport psi
-  a : Fin 3 → Fin 3 → Scalar α T
-  drift : Fin 3 → Scalar α T
-  b : Fin 3 → Scalar α T
-  c : Scalar α T
-  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
-    b k (t,x) = -(∑ j : Fin 3,
-      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
-  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
-    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
-      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
-      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)
-
-def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
-    ∀ G p, (C G).u p = D.psi p.2 * G.u p
-
-structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
-  S : Scalar α T →L[ℝ] Jet α T
-  bound : ‖S‖ ≤ C_S
-  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
-    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
-      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)
-
-def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
-    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
-  0 < α → 0 < T →
-  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
-  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
-  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
-    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖
-
--- Actual chart coefficient agreement is separate from the frozen analytic data.
-structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
-  cutoff : E → ℝ
-  smooth : ContDiff ℝ ∞ cutoff
-  compact : HasCompactSupport cutoff
-  one_on : ∀ z ∈ U, cutoff z = 1
-  b : Fin 3 → Fin 3 → Scalar α T
-  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
-    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))
-
-def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
-    (N : X_M A α T → Y_M A α T) : Prop :=
-  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
-    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
-  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
-def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
-    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
-    (G : Jet α T) (p : ℝ × E) : ℝ :=
-  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
-    a i j p * G.ddu p (e i) (e j)) -
-    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p
-
-def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
-    (potential : Scalar α T) : Prop :=
-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
-    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
-    (∀ G t, t ∈ Icc 0 T → ∀ x,
-      localLinearValue D.a D.drift potential (C G) (t,x) -
-        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
-          firstOrderValue D.b D.c G (t,x))
-
-def oscillationExtensionGoal : Prop :=
-  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
-  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
-  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
-  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
-  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
-    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
-  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∃ b : Fin 3 → Fin 3 → Scalar α T,
-      (∀ t ∈ Icc 0 T, ∀ x i j,
-        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
-      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
-      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)
-
-def frozenCLMGoal : Prop :=
-  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
-  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
-  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
-  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)
-
-abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
-  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
-
-def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
-  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)
-
-def localizedValue {T : ℝ} (F : TensorField (M := M) T)
-    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
+
+set_option maxHeartbeats 800000
+set_option synthInstance.maxHeartbeats 200000
+
+namespace Poincare.ParabolicCutoffCommutator
+
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+
+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
+theorem quadratic_remainder
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
+    (x v : E) (hv : ‖v‖ = 1) :
+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
+      convex_univ (mem_univ x) (mem_univ y)
+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
+      (dh (x + s • v) v) s := by
+    simpa using (hd (x + s • v)).comp_hasDerivAt s
+      (((hasDerivAt_id s).smul_const v).const_add x)
+  have hdr (s : ℝ) : HasDerivAt
+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
+      (dh (x + s • v) v - dh x v) s := by
+    simpa using ((hdline s).sub_const (h x)).sub
+      ((hasDerivAt_id s).mul_const (dh x v))
+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
+    simp only [id_eq]
+    ring
+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
+    (fun s _ => (hdr s).hasDerivWithinAt)
+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
+  · exact hr
+  · calc
+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
+      _ ≤ ‖dh (x + s • v) - dh x‖ := by
+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
+
+/-- The finite-difference estimate with an arbitrary positive step. -/
+theorem finite_difference_derivative
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
+  have hr := quadratic_remainder hd hdd hb hη.le x v hv
+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
+    calc
+      |η * dh x v| = |(h (x + η • v) - h x) -
+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
+      _ ≤ |h (x + η • v) - h x| +
+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
+      _ ≤ _ := add_le_add hu hr
+  rw [abs_mul, abs_of_pos hη] at ht
+  apply (mul_le_mul_iff_right₀ hη).mp
+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
+    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
+    calc
+      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
+      _ = _ := by rw [hc]
+  rw [he]
+  nlinarith
+
+/-- Optimizing the step gives a square-root bound on the full derivative. -/
+theorem derivative_norm_le_sqrt
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hδ : 0 < δ) (hM : 0 ≤ M)
+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
+  intro v hv
+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
+      3 * Real.sqrt δ * M := by
+    have hs := Real.sq_sqrt hδ.le
+    have hp := Real.sqrt_pos.mpr hδ
+    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
+      apply (div_eq_iff (ne_of_gt hp)).2
+      nlinarith
+    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
+    ring
+  exact h.trans_eq he
+
+variable {α T : ℝ}
+
+/-- Time increments of the value are controlled by the stored time derivative. -/
+theorem value_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun r hr => G.hasDeriv_time r hr x)
+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
+  simpa only [Real.norm_eq_abs, mul_comm] using h
+
+/-- The gradient of any derivative graph is uniformly small at short times. -/
+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
+    (norm_nonneg G) ?_ ?_ x
+  · intro y
+    calc
+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
+  · intro y
+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
+
+/-- The supremum of the gradient has the same square-root gain. -/
+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · positivity
+  · exact gradient_bound G hT p.property.1 p.val.2
+
+/-- Time differences of the gradient require no mixed time-space derivative. -/
+theorem gradient_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
+  by_cases hst : t = s
+  · simp [hst]
+  · apply derivative_norm_le_sqrt
+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
+      (value_time_increment G hs ht) ?_ x
+    intro y
+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
+
+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
+theorem gradient_space_increment (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Spatial value increments inherit the improved gradient bound. -/
+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Split a power at a larger positive scale. -/
+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
+    r ^ b ≤ R ^ (b - a) * r ^ a := by
+  have he : r ^ b = r ^ (b - a) * r ^ a := by
+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
+    congr 1
+    ring
+  rw [he]
+  exact mul_le_mul_of_nonneg_right
+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
+
+/-- Interpolate a Lipschitz bound and a bound at scale R. -/
+theorem scale_interpolation {a L r R α : ℝ}
+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (hl : a ≤ L * r) (hb : a ≤ L * R) :
+    a ≤ L * R ^ (1 - α) * r ^ α := by
+  by_cases h : r ≤ R
+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
+    rw [Real.rpow_one] at hp
+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
+  · have he : R ^ (1 - α) * R ^ α = R := by
+      rw [← Real.rpow_add hR]
+      convert Real.rpow_one R using 2
+      ring
+    calc
+      a ≤ L * R := hb
+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
+
+/-- The parabolic spatial scale is the square root of the time scale. -/
+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
+    (Real.sqrt T) ^ p = T ^ (p / 2) := by
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
+  congr 1
+  ring
+
+/-- Spatial Hölder gradient increments carry the desired positive time power. -/
+theorem gradient_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤
+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
+    (L := 6 * ‖G‖) (by positivity)
+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
+  rw [sqrt_rpow hT.le] at h
+  nlinarith [h]
+
+/-- Spatial Hölder value increments gain one additional half power of time. -/
+theorem value_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤
+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    (value_space_increment G hT ht x y)
+    ((abs_sub _ _).trans (by
+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
+    rw [sqrt_rpow hT.le]
+    congr 1
+    ring
+  calc
+    |G.u (t,x) - G.u (t,y)| ≤ _ := h
+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
+
+/-- The temporal Hölder gradient bound follows from the square-root increment. -/
+theorem gradient_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤
+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
+    (show (0 : ℝ) < 1 / 2 by norm_num)
+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
+  have hi := gradient_time_increment G hs ht x
+  rw [Real.sqrt_eq_rpow] at hi
+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
+
+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
+theorem value_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤
+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
+  rw [Real.rpow_one] at hp
+  exact (value_time_increment G hs ht x).trans (by
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
+
+omit [NormedSpace ℝ E] in
+/-- Split a mixed increment through the point with the first time and second position. -/
+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
+    HasHolderBound α (cylinder T) f (Kx + Kt) := by
+  intro p hp q hq
+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (by
+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
+  calc
+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
+      norm_sub_le_norm_sub_add_norm_sub _ _ _
+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
+
+/-- Full gradient Hölder control, including mixed increments. -/
+theorem gradient_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
+  have h := holder_of_increments hα.le
+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (fun t ht => gradient_space_holder G hα hα1 hT ht)
+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
+  convert h using 1
+  ring
+
+/-- Full value Hölder control with its stronger time power. -/
+theorem value_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
+  have h := holder_of_increments (f := G.u) hα.le
+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
+  convert h using 1
+  ring
+
+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
+theorem interpolation_bounds (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
+  constructor
+  · have h := ParabolicHolder.norm_le_of_bounds G.u
+      (show 0 ≤ T * ‖G‖ by positivity)
+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
+      (fun p hp => (time_bound G hp.1 p.2).trans
+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
+      (value_holder G hα hα1 hT)
+    have hp : T ≤ T ^ (1-α/2) := by
+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
+      exact (Real.rpow_one T).symm
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
+  · have h := ParabolicHolder.norm_le_of_bounds G.du
+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+      (fun p hp => gradient_bound G hT hp.1 p.2)
+      (gradient_holder G hα hα1 hT)
+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
+      rw [Real.sqrt_eq_rpow]
+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
+
+/-- A universal constant satisfies the frozen interpolation target. -/
+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
+  intro α hα hα1
+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
+
+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
   classical
-  exact if ht : p.1 ∈ Icc 0 T then
-    if p.2 ∈ (chart A i).target then
-      let x := (chart A i).symm p.2
-      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
-    else 0
-  else 0
-
-def reconstructionGoal (α T : ℝ) : Prop :=
-  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
-    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p
-
-abbrev Jet1 := E →L[ℝ] Bilin
-abbrev Jet2 := E →L[ℝ] Jet1
-
-def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
-    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
-  (∑ i : Fin 3, ∑ j : Fin 3,
-    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
-    DeTurckPrincipalIdentity.lowerTerm B DB G J
-
-set_option synthInstance.maxHeartbeats 400000 in
-def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
-    (z h : Bilin × Jet1 × Jet2) : Bilin :=
-  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
-    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
-    (∑ i : Fin 3, ∑ j : Fin 3,
-      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
-end FiniteAtlasSurvey
-
-example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation
-example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) : FiniteAtlasSurvey.cutoffGraphGoal D := by
-  intro hα hα1 hT hT1
-  obtain ⟨C, hu, _⟩ := Poincare.ParabolicCutoffCommutator.exists_cutoff_operator D.smooth D.compact hα hα1
-  exact ⟨C, hu⟩
-
-example : FiniteAtlasSurvey.commutatorGoal := Poincare.ParabolicCutoffCommutator.commutator
-example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) (potential : FiniteAtlasSurvey.Scalar α T) :
-    FiniteAtlasSurvey.cutoffIdentityGoal D potential := by
-  intro hα hα1 hT hT1
-  exact Poincare.ParabolicCutoffCommutator.cutoff_commutator_identity D.smooth D.compact hα hα1
-    D.a D.drift potential D.b D.c D.b_eq D.c_eq
+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+    have h := scale_interpolation (L := 2*A+B) (R := 1)
+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
+    simpa using h
+  refine ⟨A + (2*A+B), by positivity, ?_⟩
+  intro T
+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
+    intro p hp; simp [f, hp]
+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
+    intro p hp; simpa [f, hp] using hA p.2
+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
+    intro p hp q hq
+    simp only [f, if_pos hp, if_pos hq]
+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow (norm_nonneg _) (by
+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
+  refine ⟨fY, ?_, ?_⟩
+  · intro p hp
+    change f p = ψ p.2
+    simp [f, hp]
+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
+
+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
+      ∃ (f : Y (E := E) α T ℝ)
+        (df : Y (E := E) α T (E →L[ℝ] ℝ))
+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
+  refine ⟨K0+K1+K2, by positivity, ?_⟩
+  intro T
+  obtain ⟨f, hf, hfb⟩ := h0 T
+  obtain ⟨df, hdf, hdfb⟩ := h1 T
+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
+
+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z * G.u (t,z))
+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
+
+/-- The second spatial product rule includes both mixed Hessian terms. -/
+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
+
+/-- A spatial cutoff is constant in the within-time product rule. -/
+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
+  (G.hasDeriv_time t ht x).const_mul (ψ x)
+
+section Bilinear
+variable {F H J : Type*}
+  [NormedAddCommGroup F] [NormedSpace ℝ F]
+  [NormedAddCommGroup H] [NormedSpace ℝ H]
+  [NormedAddCommGroup J] [NormedSpace ℝ J]
+
+omit [NormedSpace ℝ E] in
+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
+  intro p hp q hq
+  have hf := ParabolicHolder.holder_le f hp hq
+  have hg := ParabolicHolder.holder_le g hp hq
+  have hf0 := ParabolicHolder.norm_le f p
+  have hg0 := ParabolicHolder.norm_le g q
+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
+  calc
+    ‖B (f p) (g p) - B (f q) (g q)‖ =
+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
+      congr 1
+      simp only [map_sub, ContinuousLinearMap.sub_apply]
+      abel
+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
+      apply add_le_add
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
+          (norm_nonneg _) (by positivity)
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
+          (norm_nonneg _) (by positivity)
+    _ = _ := by ring
+
+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
+  ofFunction (fun p => B (f p) (g p))
+    (fun p hp => by simp [zero_off f hp])
+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
+
+omit [NormedSpace ℝ E] in
+/-- The bilinear carrier norm has an explicit product bound. -/
+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
+    (bilinear_holder B f g)
+  nlinarith [h]
+
+end Bilinear
+
+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
+
+/-- Assemble the cutoff graph from its three spatial carriers. -/
+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
+    (G : Graph (E := E) α T) : Graph (E := E) α T where
+  u := f * G.u
+  ut := f * G.ut
+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
+  hasFDeriv := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv hψ G ht x using 1
+    · funext z
+      simp only [mul_apply, hf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
+  hasFDeriv_du := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv_du hψ G ht x using 1
+    · funext z
+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
+      rfl
+  hasDeriv_time := by
+    intro t ht x
+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
+      by_cases hs : (s,x) ∈ cylinder T
+      · simp [mul_apply, hf (s,x) hs]
+      · simp [mul_apply, zero_off G.u hs]
+    convert cutoff_hasDeriv_time ψ G ht x using 1
+    · funext s; exact he s
+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
+
+/-- Equality of the four stored carriers determines a derivative graph. -/
+theorem graph_ext_components {G H : Graph (E := E) α T}
+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
+    G = H := by
+  cases G
+  cases H
+  simp_all
+
+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
+  map_add' G H := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
+      simp only [map_add, ContinuousLinearMap.add_apply]
+      module
+  map_smul' c G := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.u p) = c • (f p * (G.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.ut p) = c • (f p * (G.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
+      simp only [map_smul, ContinuousLinearMap.smul_apply]
+      module
+
+
+set_option maxHeartbeats 4000000 in
+/-- The cutoff graph map is bounded in the original four-component norm. -/
+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
+  let A := ‖f‖ + ‖df‖ + ‖ddf‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  have hA : 0 ≤ A := by dsimp [A]; positivity
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
+  refine ⟨20 * B * A, ?_⟩
+  intro G
+  have hGu := norm_u_le G
+  have hGut := norm_ut_le G
+  have hGdu := norm_du_le G
+  have hGddu := norm_ddu_le G
+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  rw [ParabolicSolutionGraph.norm_eq]
+  change ‖f * G.u‖ + ‖f * G.ut‖ +
+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
+  nlinarith
+
+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
+        (C G).ddu (t,x) =
+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
+  have hf := fun p hp => (heq p hp).1
+  have hdf := fun p hp => (heq p hp).2.1
+  have hddf := fun p hp => (heq p hp).2.2
+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
+  let C := L.mkContinuous B hB
+  refine ⟨C, ?_, ?_⟩
+  · intro G p
+    change f p * G.u p = ψ p.2 * G.u p
+    by_cases hp : p ∈ cylinder T
+    · rw [hf p hp]
+    · simp [zero_off G.u hp]
+  · intro G t ht x
+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
+    change f (t,x) * G.ut (t,x) = _ ∧
+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp]
+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
+      rfl
+
+end Poincare.ParabolicCutoffCommutator
+
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) : Y (E := (ClosedSmoothModel 3)) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_left
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
+    Graph (E := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) + H.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (r * G.u p) = _
+    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ),
+    ∃ K : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+set_option maxHeartbeats 4000000 in
+/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
+theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
+    (a : Fin 3 → Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (drift : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (potential : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
+      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)))
+    (hc : ∀ t ∈ Icc 0 T, ∀ x,
+      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) -
+        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∃ C : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Graph (E := (ClosedSmoothModel 3)) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * (C G).u (t,x)) -
+        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * G.u (t,x)) =
+        (∑ i : Fin 3, b i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c (t,x) * G.u (t,x)) := by
+  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro G t ht x
+  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
+  rw [hut, hdu, hddu, hu G (t,x)]
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+end Poincare.ParabolicCutoffCommutator
```

```text
$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean -o .lake/build/lib/lean/Poincare/Global/ParabolicCutoffCommutator.olean
exit: 0
```

</details>

<details>
<summary>run-053</summary>

Source SHA-256: `b36359b79da42a1561c3e9abb56d41d3e38a4a6a7b79d3a008b71efd3f3a39d3`.

```diff
--- preceding snapshot
+++ run-053.lean
@@ -1,893 +1,16 @@
-import Poincare.Global.ParabolicHolderMultiplier
-import Poincare.Global.DuhamelSolutionOperatorBound
-import Mathlib.Analysis.Calculus.MeanValue
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-
-noncomputable section
-
-set_option maxHeartbeats 800000
-set_option synthInstance.maxHeartbeats 200000
-
-namespace Poincare.ParabolicCutoffCommutator
-
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-
-/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
-theorem quadratic_remainder
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
-    (x v : E) (hv : ‖v‖ = 1) :
-    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
-  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
-    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
-      convex_univ (mem_univ x) (mem_univ y)
-  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
-      (dh (x + s • v) v) s := by
-    simpa using (hd (x + s • v)).comp_hasDerivAt s
-      (((hasDerivAt_id s).smul_const v).const_add x)
-  have hdr (s : ℝ) : HasDerivAt
-      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
-      (dh (x + s • v) v - dh x v) s := by
-    simpa using ((hdline s).sub_const (h x)).sub
-      ((hasDerivAt_id s).mul_const (dh x v))
-  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
-    simp only [id_eq]
-    ring
-  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
-    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
-    (fun s _ => (hdr s).hasDerivWithinAt)
-    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
-    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
-  · exact hr
-  · calc
-      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
-      _ ≤ ‖dh (x + s • v) - dh x‖ := by
-        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
-      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
-
-/-- The finite-difference estimate with an arbitrary positive step. -/
-theorem finite_difference_derivative
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
-    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
-    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
-  have hr := quadratic_remainder hd hdd hb hη.le x v hv
-  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
-    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
-  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
-    calc
-      |η * dh x v| = |(h (x + η • v) - h x) -
-          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
-      _ ≤ |h (x + η • v) - h x| +
-          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
-      _ ≤ _ := add_le_add hu hr
-  rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_iff_right₀ hη).mp
-  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
-    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
-    calc
-      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
-      _ = _ := by rw [hc]
-  rw [he]
-  nlinarith
-
-/-- Optimizing the step gives a square-root bound on the full derivative. -/
-theorem derivative_norm_le_sqrt
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hδ : 0 < δ) (hM : 0 ≤ M)
-    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
-    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
-  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
-  intro v hv
-  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
-  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
-      3 * Real.sqrt δ * M := by
-    have hs := Real.sq_sqrt hδ.le
-    have hp := Real.sqrt_pos.mpr hδ
-    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
-      apply (div_eq_iff (ne_of_gt hp)).2
-      nlinarith
-    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
-    ring
-  exact h.trans_eq he
-
-variable {α T : ℝ}
-
-/-- Time increments of the value are controlled by the stored time derivative. -/
-theorem value_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
-  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-    (fun r hr => G.hasDeriv_time r hr x)
-    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
-  simpa only [Real.norm_eq_abs, mul_comm] using h
-
-/-- The gradient of any derivative graph is uniformly small at short times. -/
-theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
-    (norm_nonneg G) ?_ ?_ x
-  · intro y
-    calc
-      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
-      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
-  · intro y
-    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
-
-/-- The supremum of the gradient has the same square-root gain. -/
-theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
-    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply csSup_le (insert_nonempty _ _)
-  rintro r (rfl | ⟨p, rfl⟩)
-  · positivity
-  · exact gradient_bound G hT p.property.1 p.val.2
-
-/-- Time differences of the gradient require no mixed time-space derivative. -/
-theorem gradient_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
-  by_cases hst : t = s
-  · simp [hst]
-  · apply derivative_norm_le_sqrt
-      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
-      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
-      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
-      (value_time_increment G hs ht) ?_ x
-    intro y
-    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
-      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
-
-/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
-theorem gradient_space_increment (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
-    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Spatial value increments inherit the improved gradient bound. -/
-theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
-    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Split a power at a larger positive scale. -/
-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
-    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
-    r ^ b ≤ R ^ (b - a) * r ^ a := by
-  have he : r ^ b = r ^ (b - a) * r ^ a := by
-    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
-    congr 1
-    ring
-  rw [he]
-  exact mul_le_mul_of_nonneg_right
-    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
-
-/-- Interpolate a Lipschitz bound and a bound at scale R. -/
-theorem scale_interpolation {a L r R α : ℝ}
-    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
-    (hl : a ≤ L * r) (hb : a ≤ L * R) :
-    a ≤ L * R ^ (1 - α) * r ^ α := by
-  by_cases h : r ≤ R
-  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
-    rw [Real.rpow_one] at hp
-    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
-  · have he : R ^ (1 - α) * R ^ α = R := by
-      rw [← Real.rpow_add hR]
-      convert Real.rpow_one R using 2
-      ring
-    calc
-      a ≤ L * R := hb
-      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
-      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
-        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
-
-/-- The parabolic spatial scale is the square root of the time scale. -/
-theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
-    (Real.sqrt T) ^ p = T ^ (p / 2) := by
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
-  congr 1
-  ring
-
-/-- Spatial Hölder gradient increments carry the desired positive time power. -/
-theorem gradient_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤
-      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
-    (L := 6 * ‖G‖) (by positivity)
-    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
-    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
-      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
-  rw [sqrt_rpow hT.le] at h
-  nlinarith [h]
-
-/-- Spatial Hölder value increments gain one additional half power of time. -/
-theorem value_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤
-      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
-    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
-  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
-    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
-    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    (value_space_increment G hT ht x y)
-    ((abs_sub _ _).trans (by
-      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
-      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
-  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
-    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
-    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
-    rw [sqrt_rpow hT.le]
-    congr 1
-    ring
-  calc
-    |G.u (t,x) - G.u (t,y)| ≤ _ := h
-    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
-        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
-
-/-- The temporal Hölder gradient bound follows from the square-root increment. -/
-theorem gradient_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤
-      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
-    (show (0 : ℝ) < 1 / 2 by norm_num)
-  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
-  have hi := gradient_time_increment G hs ht x
-  rw [Real.sqrt_eq_rpow] at hi
-  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
-
-/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
-theorem value_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤
-      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
-  rw [Real.rpow_one] at hp
-  exact (value_time_increment G hs ht x).trans (by
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
-
-omit [NormedSpace ℝ E] in
-/-- Split a mixed increment through the point with the first time and second position. -/
-theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
-    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
-    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
-      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
-    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
-      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
-    HasHolderBound α (cylinder T) f (Kx + Kt) := by
-  intro p hp q hq
-  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
-    Real.rpow_le_rpow (norm_nonneg _) (by
-      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
-  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
-    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
-    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
-      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
-  calc
-    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
-      norm_sub_le_norm_sub_add_norm_sub _ _ _
-    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
-      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
-    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
-      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
-
-/-- Full gradient Hölder control, including mixed increments. -/
-theorem gradient_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
-  have h := holder_of_increments hα.le
-    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (fun t ht => gradient_space_holder G hα hα1 hT ht)
-    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
-  convert h using 1
-  ring
-
-/-- Full value Hölder control with its stronger time power. -/
-theorem value_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
-  have h := holder_of_increments (f := G.u) hα.le
-    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
-    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
-    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
-    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
-  convert h using 1
-  ring
-
-/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
-theorem interpolation_bounds (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
-  constructor
-  · have h := ParabolicHolder.norm_le_of_bounds G.u
-      (show 0 ≤ T * ‖G‖ by positivity)
-      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
-      (fun p hp => (time_bound G hp.1 p.2).trans
-        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
-      (value_holder G hα hα1 hT)
-    have hp : T ≤ T ^ (1-α/2) := by
-      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
-      exact (Real.rpow_one T).symm
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
-      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
-  · have h := ParabolicHolder.norm_le_of_bounds G.du
-      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
-      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-      (fun p hp => gradient_bound G hT hp.1 p.2)
-      (gradient_holder G hα hα1 hT)
-    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
-      rw [Real.sqrt_eq_rpow]
-      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
-
-/-- A universal constant satisfies the frozen interpolation target. -/
-theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
-      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
-  intro α hα hα1
-  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
-
-/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
-theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
-    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
-      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
-  classical
-  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
-  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
-  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
-  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
-    have h := scale_interpolation (L := 2*A+B) (R := 1)
-      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
-      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
-      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
-    simpa using h
-  refine ⟨A + (2*A+B), by positivity, ?_⟩
-  intro T
-  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
-  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
-    intro p hp; simp [f, hp]
-  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
-    intro p hp; simpa [f, hp] using hA p.2
-  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
-    intro p hp q hq
-    simp only [f, if_pos hp, if_pos hq]
-    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
-      (Real.rpow_le_rpow (norm_nonneg _) (by
-        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
-  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
-  refine ⟨fY, ?_, ?_⟩
-  · intro p hp
-    change f p = ψ p.2
-    simp [f, hp]
-  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
-
-/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
-theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
-    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
-      ∃ (f : Y (E := E) α T ℝ)
-        (df : Y (E := E) α T (E →L[ℝ] ℝ))
-        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
-      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
-        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
-      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
-  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
-  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
-  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
-  refine ⟨K0+K1+K2, by positivity, ?_⟩
-  intro T
-  obtain ⟨f, hf, hfb⟩ := h0 T
-  obtain ⟨df, hdf, hdfb⟩ := h1 T
-  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
-  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
-
-/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
-theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z * G.u (t,z))
-      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
-  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
-
-/-- The second spatial product rule includes both mixed Hessian terms. -/
-theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
-      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
-    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
-
-/-- A spatial cutoff is constant in the within-time product rule. -/
-theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
-  (G.hasDeriv_time t ht x).const_mul (ψ x)
-
-section Bilinear
-variable {F H J : Type*}
-  [NormedAddCommGroup F] [NormedSpace ℝ F]
-  [NormedAddCommGroup H] [NormedSpace ℝ H]
-  [NormedAddCommGroup J] [NormedSpace ℝ J]
-
-omit [NormedSpace ℝ E] in
-/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
-theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
-  intro p hp q hq
-  have hf := ParabolicHolder.holder_le f hp hq
-  have hg := ParabolicHolder.holder_le g hp hq
-  have hf0 := ParabolicHolder.norm_le f p
-  have hg0 := ParabolicHolder.norm_le g q
-  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
-  calc
-    ‖B (f p) (g p) - B (f q) (g q)‖ =
-        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
-      congr 1
-      simp only [map_sub, ContinuousLinearMap.sub_apply]
-      abel
-    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
-    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
-      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
-    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
-        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
-      apply add_le_add
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
-          (norm_nonneg _) (by positivity)
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
-          (norm_nonneg _) (by positivity)
-    _ = _ := by ring
-
-/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
-def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
-  ofFunction (fun p => B (f p) (g p))
-    (fun p hp => by simp [zero_off f hp])
-    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
-    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
-
-omit [NormedSpace ℝ E] in
-/-- The bilinear carrier norm has an explicit product bound. -/
-theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
-    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
-    (bilinear_holder B f g)
-  nlinarith [h]
-
-end Bilinear
-
-local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
-  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
-
-/-- Assemble the cutoff graph from its three spatial carriers. -/
-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
-    (G : Graph (E := E) α T) : Graph (E := E) α T where
-  u := f * G.u
-  ut := f * G.ut
-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
-  hasFDeriv := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv hψ G ht x using 1
-    · funext z
-      simp only [mul_apply, hf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
-  hasFDeriv_du := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv_du hψ G ht x using 1
-    · funext z
-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
-      rfl
-  hasDeriv_time := by
-    intro t ht x
-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
-      by_cases hs : (s,x) ∈ cylinder T
-      · simp [mul_apply, hf (s,x) hs]
-      · simp [mul_apply, zero_off G.u hs]
-    convert cutoff_hasDeriv_time ψ G ht x using 1
-    · funext s; exact he s
-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
-
-/-- Equality of the four stored carriers determines a derivative graph. -/
-theorem graph_ext_components {G H : Graph (E := E) α T}
-    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
-    G = H := by
-  cases G
-  cases H
-  simp_all
-
-/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
-def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
-  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
-  map_add' G H := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
-      simp only [map_add, ContinuousLinearMap.add_apply]
-      module
-  map_smul' c G := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.u p) = c • (f p * (G.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.ut p) = c • (f p * (G.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
-      simp only [map_smul, ContinuousLinearMap.smul_apply]
-      module
-
-
-set_option maxHeartbeats 4000000 in
-/-- The cutoff graph map is bounded in the original four-component norm. -/
-theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
-      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
-  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
-  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
-  let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
-  have hA : 0 ≤ A := by dsimp [A]; positivity
-  have hB : 0 ≤ B := by dsimp [B]; positivity
-  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
-  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
-  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
-  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
-  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
-  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
-  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
-  refine ⟨20 * B * A, ?_⟩
-  intro G
-  have hGu := norm_u_le G
-  have hGut := norm_ut_le G
-  have hGdu := norm_du_le G
-  have hGddu := norm_ddu_le G
-  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  rw [ParabolicSolutionGraph.norm_eq]
-  change ‖f * G.u‖ + ‖f * G.ut‖ +
-    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
-    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
-      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
-  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
-  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
-    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
-  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
-  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
-  nlinarith
-
-/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
-theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
-    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
-        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
-        (C G).ddu (t,x) =
-          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
-  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
-  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
-  have hf := fun p hp => (heq p hp).1
-  have hdf := fun p hp => (heq p hp).2.1
-  have hddf := fun p hp => (heq p hp).2.2
-  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
-  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
-  let C := L.mkContinuous B hB
-  refine ⟨C, ?_, ?_⟩
-  · intro G p
-    change f p * G.u p = ψ p.2 * G.u p
-    by_cases hp : p ∈ cylinder T
-    · rw [hf p hp]
-    · simp [zero_off G.u hp]
-  · intro G t ht x
-    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
-    change f (t,x) * G.ut (t,x) = _ ∧
-      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
-    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp]
-    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
-      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
-      rfl
-
-end Poincare.ParabolicCutoffCommutator
-
-noncomputable section
-set_option maxHeartbeats 800000
-namespace Poincare.ParabolicCutoffCommutator
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
-
-/-- Evaluate a first derivative carrier on a unit direction. -/
-def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    Y (E := E) α T ℝ :=
-  ofFunction (fun p => H p v)
-    (fun p hp => by simp [zero_off H hp])
-    ⟨‖H‖, fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
-    ⟨‖H‖, fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
-
-/-- Evaluation is bounded in the full Hölder norm. -/
-theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
-    (norm_nonneg H) (norm_nonneg H)
-    (fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
-    (fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
-  linarith
-
-
-/-- The first-order forcing associated to the explicit commutator coefficients. -/
-def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) : Y (E := (ClosedSmoothModel 3)) α T ℝ :=
-  (∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c * G.u
-
-/-- The carrier evaluates to the first-order coefficient formula. -/
-theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) :
-    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p := by
-  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
-    derivativeEntry, ofFunction_apply]
-
-/-- The commutator uses only the value and gradient norms. -/
-theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) :
-    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
-  calc
-    ‖firstOrderForcing b c G‖ ≤
-        ‖∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ + ‖c * G.u‖ := norm_add_le _ _
-    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖) + ‖c‖ * ‖G.u‖ :=
-      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
-    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
-      apply add_le_add_left
-      apply Finset.sum_le_sum
-      intro i hi
-      exact (ParabolicHolder.norm_mul_le _ _).trans
-        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
-    _ = _ := by rw [← Finset.sum_mul]; ring
-
-/-- The commutator has separate positive time powers for its two coefficient families. -/
-theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
-  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
-  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
-  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
-  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
-  have h3 := norm_firstOrderForcing_le b c G
-  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
-
-/-- The common weaker time exponent controls both first-order terms. -/
-theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
-  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
-    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-  have h := firstOrder_time_bound b c G hα hα1 hT hT1
-  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
-
-/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
-def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
-    Graph (E := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ where
-  toFun := firstOrderForcing b c
-  map_add' G H := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [add_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) + H.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (G.u p + H.u p) = _
-    simp only [mul_add, Finset.sum_add_distrib]
-    ring
-  map_smul' r G := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [smul_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (r * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (r * G.u p) = _
-    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
-    ring
-
-/-- The frozen commutator operator target, with a universal constant. -/
-theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∀ (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ),
-    ∃ K : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ,
-      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p) ∧
-      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
-  intro α hα hα1
-  refine ⟨24, by norm_num, ?_⟩
-  intro T hT hT1 b c
-  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
-  let K := (firstOrderLinearMap b c).mkContinuous B
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
-  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-
-set_option maxHeartbeats 4000000 in
-/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
-theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
-    (a : Fin 3 → Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (drift : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (potential : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
-      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)))
-    (hc : ∀ t ∈ Icc 0 T, ∀ x,
-      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) -
-        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
-    ∃ C : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Graph (E := (ClosedSmoothModel 3)) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
-          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * (C G).u (t,x)) -
-        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
-          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * G.u (t,x)) =
-        (∑ i : Fin 3, b i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c (t,x) * G.u (t,x)) := by
-  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
-  refine ⟨C, hu, ?_⟩
-  intro G t ht x
-  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
-  rw [hut, hdu, hddu, hu G (t,x)]
-  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
-    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
-    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
-  ring
-
-end Poincare.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicCutoffCommutator
+open Lean Elab Command in
+run_cmd do
+  let env ← getEnv
+  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
+    | throwError "module not found"
+  let mut count := 0
+  for (n, _) in env.constants.map₁.toList do
+    if env.getModuleIdxFor? n == some idx then
+      let axs ← liftCoreM (collectAxioms n)
+      count := count + 1
+      elabCommand (← `(command| #print axioms $(mkIdent n)))
+      unless axs.size == 3 && axs.contains ``propext &&
+          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
+        throwError "Unexpected foundational dependencies for {n}: {axs}"
+  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "exit: 0\n",
  "'Poincare.ParabolicCutoffCommutator.graph_ext_components' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_6' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing_apply' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_31' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_6' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_7' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_17' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_25' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_38' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.scale_interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_15' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.supNorm_gradient_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_35' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.norm_derivativeEntry_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_36' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_10' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_39' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers.eq_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderLinearMap._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_3' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.commutator' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicSolutionGraph.Graph.mk.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_4' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_26' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_7' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry._proof_2' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivative_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry.congr_simp' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_14' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_13' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry._proof_3' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_9' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_22' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.norm_firstOrderForcing_le' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_21' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.norm_bilinearY_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_29' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_20' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing._proof_3' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrder_common_time_bound' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.sqrt_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_11' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_28' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_8' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasFDeriv_du' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_operator' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_24' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoffGraph_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.interpolation' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_space_increment' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_41' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicHolder.ofFunction.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_5' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.finite_difference_derivative' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_12' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_27' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.derivativeEntry' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_hasDeriv_time' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_32' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_19' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.exists_cutoff_jet_carriers' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_4' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.hessianBoundedSMul' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.power_scale_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_33' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderLinearMap' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_34' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.value_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffLinearMapOfCarriers._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_40' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinear_holder._abel_1_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoff_commutator_identity' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.gradient_time_holder' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_23' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.holder_of_increments' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.bilinearY._proof_5' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_18' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_37' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_16' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderLinearMap._proof_2' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrderForcing._proof_1' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.firstOrder_time_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
  "'Poincare.ParabolicCutoffCommutator.cutoffGraphOfCarriers._proof_30' depends on axioms: [propext,\n",
  " Classical.choice,\n",
  " Quot.sound]\n",
  "EXACT_MODULE_AUDIT declarations=111; every declaration has exactly the required three dependencies\n"
]
```

</details>

<details>
<summary>run-054</summary>

Source SHA-256: `3615959ec31f85634f640f9ea4e9b197eeefbf2e09d29eb4864f5b099ad9af82`.

```diff
--- preceding snapshot
+++ run-054.lean
@@ -1,16 +1,893 @@
-import Poincare.Global.ParabolicCutoffCommutator
-open Lean Elab Command in
-run_cmd do
-  let env ← getEnv
-  let some idx := env.getModuleIdx? `Poincare.Global.ParabolicCutoffCommutator
-    | throwError "module not found"
-  let mut count := 0
-  for (n, _) in env.constants.map₁.toList do
-    if env.getModuleIdxFor? n == some idx then
-      let axs ← liftCoreM (collectAxioms n)
-      count := count + 1
-      elabCommand (← `(command| #print axioms $(mkIdent n)))
-      unless axs.size == 3 && axs.contains ``propext &&
-          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
-        throwError "Unexpected foundational dependencies for {n}: {axs}"
-  logInfo m!"EXACT_MODULE_AUDIT declarations={count}; every declaration has exactly the required three dependencies"
+import Poincare.Global.ParabolicHolderMultiplier
+import Poincare.Global.DuhamelSolutionOperatorBound
+import Mathlib.Analysis.Calculus.MeanValue
+import Mathlib.Analysis.Calculus.ContDiff.RCLike
+
+noncomputable section
+
+set_option maxHeartbeats 800000
+set_option synthInstance.maxHeartbeats 200000
+
+namespace Poincare.ParabolicCutoffCommutator
+
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+
+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
+theorem quadratic_remainder
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
+    (x v : E) (hv : ‖v‖ = 1) :
+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
+      convex_univ (mem_univ x) (mem_univ y)
+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
+      (dh (x + s • v) v) s := by
+    simpa using (hd (x + s • v)).comp_hasDerivAt s
+      (((hasDerivAt_id s).smul_const v).const_add x)
+  have hdr (s : ℝ) : HasDerivAt
+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
+      (dh (x + s • v) v - dh x v) s := by
+    simpa using ((hdline s).sub_const (h x)).sub
+      ((hasDerivAt_id s).mul_const (dh x v))
+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
+    simp only [id_eq]
+    ring
+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
+    (fun s _ => (hdr s).hasDerivWithinAt)
+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
+  · exact hr
+  · calc
+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
+      _ ≤ ‖dh (x + s • v) - dh x‖ := by
+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
+
+/-- The finite-difference estimate with an arbitrary positive step. -/
+theorem finite_difference_derivative
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
+  have hr := quadratic_remainder hd hdd hb hη.le x v hv
+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
+    calc
+      |η * dh x v| = |(h (x + η • v) - h x) -
+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
+      _ ≤ |h (x + η • v) - h x| +
+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
+      _ ≤ _ := add_le_add hu hr
+  rw [abs_mul, abs_of_pos hη] at ht
+  apply (mul_le_mul_iff_right₀ hη).mp
+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
+    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
+    calc
+      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
+      _ = _ := by rw [hc]
+  rw [he]
+  nlinarith
+
+/-- Optimizing the step gives a square-root bound on the full derivative. -/
+theorem derivative_norm_le_sqrt
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hδ : 0 < δ) (hM : 0 ≤ M)
+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
+  intro v hv
+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
+      3 * Real.sqrt δ * M := by
+    have hs := Real.sq_sqrt hδ.le
+    have hp := Real.sqrt_pos.mpr hδ
+    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
+      apply (div_eq_iff (ne_of_gt hp)).2
+      nlinarith
+    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
+    ring
+  exact h.trans_eq he
+
+variable {α T : ℝ}
+
+/-- Time increments of the value are controlled by the stored time derivative. -/
+theorem value_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun r hr => G.hasDeriv_time r hr x)
+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
+  simpa only [Real.norm_eq_abs, mul_comm] using h
+
+/-- The gradient of any derivative graph is uniformly small at short times. -/
+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
+    (norm_nonneg G) ?_ ?_ x
+  · intro y
+    calc
+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
+  · intro y
+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
+
+/-- The supremum of the gradient has the same square-root gain. -/
+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · positivity
+  · exact gradient_bound G hT p.property.1 p.val.2
+
+/-- Time differences of the gradient require no mixed time-space derivative. -/
+theorem gradient_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
+  by_cases hst : t = s
+  · simp [hst]
+  · apply derivative_norm_le_sqrt
+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
+      (value_time_increment G hs ht) ?_ x
+    intro y
+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
+
+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
+theorem gradient_space_increment (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Spatial value increments inherit the improved gradient bound. -/
+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Split a power at a larger positive scale. -/
+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
+    r ^ b ≤ R ^ (b - a) * r ^ a := by
+  have he : r ^ b = r ^ (b - a) * r ^ a := by
+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
+    congr 1
+    ring
+  rw [he]
+  exact mul_le_mul_of_nonneg_right
+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
+
+/-- Interpolate a Lipschitz bound and a bound at scale R. -/
+theorem scale_interpolation {a L r R α : ℝ}
+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (hl : a ≤ L * r) (hb : a ≤ L * R) :
+    a ≤ L * R ^ (1 - α) * r ^ α := by
+  by_cases h : r ≤ R
+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
+    rw [Real.rpow_one] at hp
+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
+  · have he : R ^ (1 - α) * R ^ α = R := by
+      rw [← Real.rpow_add hR]
+      convert Real.rpow_one R using 2
+      ring
+    calc
+      a ≤ L * R := hb
+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
+
+/-- The parabolic spatial scale is the square root of the time scale. -/
+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
+    (Real.sqrt T) ^ p = T ^ (p / 2) := by
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
+  congr 1
+  ring
+
+/-- Spatial Hölder gradient increments carry the desired positive time power. -/
+theorem gradient_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤
+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
+    (L := 6 * ‖G‖) (by positivity)
+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
+  rw [sqrt_rpow hT.le] at h
+  nlinarith [h]
+
+/-- Spatial Hölder value increments gain one additional half power of time. -/
+theorem value_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤
+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    (value_space_increment G hT ht x y)
+    ((abs_sub _ _).trans (by
+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
+    rw [sqrt_rpow hT.le]
+    congr 1
+    ring
+  calc
+    |G.u (t,x) - G.u (t,y)| ≤ _ := h
+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
+
+/-- The temporal Hölder gradient bound follows from the square-root increment. -/
+theorem gradient_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤
+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
+    (show (0 : ℝ) < 1 / 2 by norm_num)
+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
+  have hi := gradient_time_increment G hs ht x
+  rw [Real.sqrt_eq_rpow] at hi
+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
+
+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
+theorem value_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤
+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
+  rw [Real.rpow_one] at hp
+  exact (value_time_increment G hs ht x).trans (by
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
+
+omit [NormedSpace ℝ E] in
+/-- Split a mixed increment through the point with the first time and second position. -/
+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
+    HasHolderBound α (cylinder T) f (Kx + Kt) := by
+  intro p hp q hq
+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (by
+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
+  calc
+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
+      norm_sub_le_norm_sub_add_norm_sub _ _ _
+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
+
+/-- Full gradient Hölder control, including mixed increments. -/
+theorem gradient_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
+  have h := holder_of_increments hα.le
+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (fun t ht => gradient_space_holder G hα hα1 hT ht)
+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
+  convert h using 1
+  ring
+
+/-- Full value Hölder control with its stronger time power. -/
+theorem value_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
+  have h := holder_of_increments (f := G.u) hα.le
+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
+  convert h using 1
+  ring
+
+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
+theorem interpolation_bounds (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
+  constructor
+  · have h := ParabolicHolder.norm_le_of_bounds G.u
+      (show 0 ≤ T * ‖G‖ by positivity)
+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
+      (fun p hp => (time_bound G hp.1 p.2).trans
+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
+      (value_holder G hα hα1 hT)
+    have hp : T ≤ T ^ (1-α/2) := by
+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
+      exact (Real.rpow_one T).symm
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
+  · have h := ParabolicHolder.norm_le_of_bounds G.du
+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+      (fun p hp => gradient_bound G hT hp.1 p.2)
+      (gradient_holder G hα hα1 hT)
+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
+      rw [Real.sqrt_eq_rpow]
+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
+
+/-- A universal constant satisfies the frozen interpolation target. -/
+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
+  intro α hα hα1
+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
+
+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
+  classical
+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+    have h := scale_interpolation (L := 2*A+B) (R := 1)
+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
+    simpa using h
+  refine ⟨A + (2*A+B), by positivity, ?_⟩
+  intro T
+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
+    intro p hp; simp [f, hp]
+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
+    intro p hp; simpa [f, hp] using hA p.2
+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
+    intro p hp q hq
+    simp only [f, if_pos hp, if_pos hq]
+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow (norm_nonneg _) (by
+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
+  refine ⟨fY, ?_, ?_⟩
+  · intro p hp
+    change f p = ψ p.2
+    simp [f, hp]
+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
+
+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
+      ∃ (f : Y (E := E) α T ℝ)
+        (df : Y (E := E) α T (E →L[ℝ] ℝ))
+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
+  refine ⟨K0+K1+K2, by positivity, ?_⟩
+  intro T
+  obtain ⟨f, hf, hfb⟩ := h0 T
+  obtain ⟨df, hdf, hdfb⟩ := h1 T
+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
+
+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z * G.u (t,z))
+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
+
+/-- The second spatial product rule includes both mixed Hessian terms. -/
+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
+
+/-- A spatial cutoff is constant in the within-time product rule. -/
+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
+  (G.hasDeriv_time t ht x).const_mul (ψ x)
+
+section Bilinear
+variable {F H J : Type*}
+  [NormedAddCommGroup F] [NormedSpace ℝ F]
+  [NormedAddCommGroup H] [NormedSpace ℝ H]
+  [NormedAddCommGroup J] [NormedSpace ℝ J]
+
+omit [NormedSpace ℝ E] in
+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
+  intro p hp q hq
+  have hf := ParabolicHolder.holder_le f hp hq
+  have hg := ParabolicHolder.holder_le g hp hq
+  have hf0 := ParabolicHolder.norm_le f p
+  have hg0 := ParabolicHolder.norm_le g q
+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
+  calc
+    ‖B (f p) (g p) - B (f q) (g q)‖ =
+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
+      congr 1
+      simp only [map_sub, ContinuousLinearMap.sub_apply]
+      abel
+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
+      apply add_le_add
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
+          (norm_nonneg _) (by positivity)
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
+          (norm_nonneg _) (by positivity)
+    _ = _ := by ring
+
+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
+  ofFunction (fun p => B (f p) (g p))
+    (fun p hp => by simp [zero_off f hp])
+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
+
+omit [NormedSpace ℝ E] in
+/-- The bilinear carrier norm has an explicit product bound. -/
+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
+    (bilinear_holder B f g)
+  nlinarith [h]
+
+end Bilinear
+
+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
+
+/-- Assemble the cutoff graph from its three spatial carriers. -/
+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
+    (G : Graph (E := E) α T) : Graph (E := E) α T where
+  u := f * G.u
+  ut := f * G.ut
+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
+  hasFDeriv := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv hψ G ht x using 1
+    · funext z
+      simp only [mul_apply, hf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
+  hasFDeriv_du := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv_du hψ G ht x using 1
+    · funext z
+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
+      rfl
+  hasDeriv_time := by
+    intro t ht x
+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
+      by_cases hs : (s,x) ∈ cylinder T
+      · simp [mul_apply, hf (s,x) hs]
+      · simp [mul_apply, zero_off G.u hs]
+    convert cutoff_hasDeriv_time ψ G ht x using 1
+    · funext s; exact he s
+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
+
+/-- Equality of the four stored carriers determines a derivative graph. -/
+theorem graph_ext_components {G H : Graph (E := E) α T}
+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
+    G = H := by
+  cases G
+  cases H
+  simp_all
+
+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
+  map_add' G H := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
+      simp only [map_add, ContinuousLinearMap.add_apply]
+      module
+  map_smul' c G := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.u p) = c • (f p * (G.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.ut p) = c • (f p * (G.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
+      simp only [map_smul, ContinuousLinearMap.smul_apply]
+      module
+
+
+set_option maxHeartbeats 4000000 in
+/-- The cutoff graph map is bounded in the original four-component norm. -/
+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
+  let A := ‖f‖ + ‖df‖ + ‖ddf‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  have hA : 0 ≤ A := by dsimp [A]; positivity
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
+  refine ⟨20 * B * A, ?_⟩
+  intro G
+  have hGu := norm_u_le G
+  have hGut := norm_ut_le G
+  have hGdu := norm_du_le G
+  have hGddu := norm_ddu_le G
+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  rw [ParabolicSolutionGraph.norm_eq]
+  change ‖f * G.u‖ + ‖f * G.ut‖ +
+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
+  nlinarith
+
+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
+        (C G).ddu (t,x) =
+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
+  have hf := fun p hp => (heq p hp).1
+  have hdf := fun p hp => (heq p hp).2.1
+  have hddf := fun p hp => (heq p hp).2.2
+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
+  let C := L.mkContinuous B hB
+  refine ⟨C, ?_, ?_⟩
+  · intro G p
+    change f p * G.u p = ψ p.2 * G.u p
+    by_cases hp : p ∈ cylinder T
+    · rw [hf p hp]
+    · simp [zero_off G.u hp]
+  · intro G t ht x
+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
+    change f (t,x) * G.ut (t,x) = _ ∧
+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp]
+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
+      rfl
+
+end Poincare.ParabolicCutoffCommutator
+
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) : Y (E := (ClosedSmoothModel 3)) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_left
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
+    Graph (E := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) + H.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (r * G.u p) = _
+    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ),
+    ∃ K : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+set_option maxHeartbeats 4000000 in
+/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
+theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
+    (a : Fin 3 → Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (drift : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (potential : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
+      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)))
+    (hc : ∀ t ∈ Icc 0 T, ∀ x,
+      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) -
+        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∃ C : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Graph (E := (ClosedSmoothModel 3)) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * (C G).u (t,x)) -
+        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * G.u (t,x)) =
+        (∑ i : Fin 3, b i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c (t,x) * G.u (t,x)) := by
+  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro G t ht x
+  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
+  rw [hut, hdu, hddu, hu G (t,x)]
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+end Poincare.ParabolicCutoffCommutator
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-055</summary>

Source SHA-256: `8feb65d0677a10c1ba7269ea2c9d551791795bbcd50022d02d73413509306249`.

```diff
--- preceding snapshot
+++ run-055.lean
@@ -1,893 +1,44 @@
-import Poincare.Global.ParabolicHolderMultiplier
-import Poincare.Global.DuhamelSolutionOperatorBound
-import Mathlib.Analysis.Calculus.MeanValue
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-
-noncomputable section
-
-set_option maxHeartbeats 800000
-set_option synthInstance.maxHeartbeats 200000
-
-namespace Poincare.ParabolicCutoffCommutator
-
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
-
-/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
-theorem quadratic_remainder
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
-    (x v : E) (hv : ‖v‖ = 1) :
-    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
-  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
-    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
-      convex_univ (mem_univ x) (mem_univ y)
-  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
-      (dh (x + s • v) v) s := by
-    simpa using (hd (x + s • v)).comp_hasDerivAt s
-      (((hasDerivAt_id s).smul_const v).const_add x)
-  have hdr (s : ℝ) : HasDerivAt
-      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
-      (dh (x + s • v) v - dh x v) s := by
-    simpa using ((hdline s).sub_const (h x)).sub
-      ((hasDerivAt_id s).mul_const (dh x v))
-  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
-    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
-    simp only [id_eq]
-    ring
-  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
-    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
-    (fun s _ => (hdr s).hasDerivWithinAt)
-    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
-    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
-  · exact hr
-  · calc
-      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
-      _ ≤ ‖dh (x + s • v) - dh x‖ := by
-        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
-      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
-
-/-- The finite-difference estimate with an arbitrary positive step. -/
-theorem finite_difference_derivative
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
-    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
-    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
-  have hr := quadratic_remainder hd hdd hb hη.le x v hv
-  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
-    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
-  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
-    calc
-      |η * dh x v| = |(h (x + η • v) - h x) -
-          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
-      _ ≤ |h (x + η • v) - h x| +
-          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
-      _ ≤ _ := add_le_add hu hr
-  rw [abs_mul, abs_of_pos hη] at ht
-  apply (mul_le_mul_iff_right₀ hη).mp
-  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
-    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
-    calc
-      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
-      _ = _ := by rw [hc]
-  rw [he]
-  nlinarith
-
-/-- Optimizing the step gives a square-root bound on the full derivative. -/
-theorem derivative_norm_le_sqrt
-    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
-    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
-    (hd : ∀ x, HasFDerivAt h (dh x) x)
-    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
-    (hδ : 0 < δ) (hM : 0 ≤ M)
-    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
-    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
-  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
-  intro v hv
-  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
-  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
-      3 * Real.sqrt δ * M := by
-    have hs := Real.sq_sqrt hδ.le
-    have hp := Real.sqrt_pos.mpr hδ
-    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
-      apply (div_eq_iff (ne_of_gt hp)).2
-      nlinarith
-    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
-    ring
-  exact h.trans_eq he
-
-variable {α T : ℝ}
-
-/-- Time increments of the value are controlled by the stored time derivative. -/
-theorem value_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
-  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-    (fun r hr => G.hasDeriv_time r hr x)
-    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
-  simpa only [Real.norm_eq_abs, mul_comm] using h
-
-/-- The gradient of any derivative graph is uniformly small at short times. -/
-theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
-    (norm_nonneg G) ?_ ?_ x
-  · intro y
-    calc
-      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
-      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
-  · intro y
-    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
-
-/-- The supremum of the gradient has the same square-root gain. -/
-theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
-    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
-  apply csSup_le (insert_nonempty _ _)
-  rintro r (rfl | ⟨p, rfl⟩)
-  · positivity
-  · exact gradient_bound G hT p.property.1 p.val.2
-
-/-- Time differences of the gradient require no mixed time-space derivative. -/
-theorem gradient_time_increment (G : Graph (E := E) α T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
-  by_cases hst : t = s
-  · simp [hst]
-  · apply derivative_norm_le_sqrt
-      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
-      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
-      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
-      (value_time_increment G hs ht) ?_ x
-    intro y
-    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
-      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
-
-/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
-theorem gradient_space_increment (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
-    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Spatial value increments inherit the improved gradient bound. -/
-theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
-  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
-    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
-
-/-- Split a power at a larger positive scale. -/
-theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
-    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
-    r ^ b ≤ R ^ (b - a) * r ^ a := by
-  have he : r ^ b = r ^ (b - a) * r ^ a := by
-    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
-    congr 1
-    ring
-  rw [he]
-  exact mul_le_mul_of_nonneg_right
-    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
-
-/-- Interpolate a Lipschitz bound and a bound at scale R. -/
-theorem scale_interpolation {a L r R α : ℝ}
-    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
-    (hl : a ≤ L * r) (hb : a ≤ L * R) :
-    a ≤ L * R ^ (1 - α) * r ^ α := by
-  by_cases h : r ≤ R
-  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
-    rw [Real.rpow_one] at hp
-    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
-  · have he : R ^ (1 - α) * R ^ α = R := by
-      rw [← Real.rpow_add hR]
-      convert Real.rpow_one R using 2
-      ring
-    calc
-      a ≤ L * R := hb
-      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
-      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
-        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
-
-/-- The parabolic spatial scale is the square root of the time scale. -/
-theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
-    (Real.sqrt T) ^ p = T ^ (p / 2) := by
-  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
-  congr 1
-  ring
-
-/-- Spatial Hölder gradient increments carry the desired positive time power. -/
-theorem gradient_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    ‖G.du (t, x) - G.du (t, y)‖ ≤
-      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
-    (L := 6 * ‖G‖) (by positivity)
-    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
-    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
-      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
-  rw [sqrt_rpow hT.le] at h
-  nlinarith [h]
-
-/-- Spatial Hölder value increments gain one additional half power of time. -/
-theorem value_space_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
-    |G.u (t, x) - G.u (t, y)| ≤
-      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
-  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
-    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
-  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
-    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
-    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
-    (value_space_increment G hT ht x y)
-    ((abs_sub _ _).trans (by
-      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
-      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
-  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
-    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
-    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
-    rw [sqrt_rpow hT.le]
-    congr 1
-    ring
-  calc
-    |G.u (t,x) - G.u (t,y)| ≤ _ := h
-    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
-        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
-
-/-- The temporal Hölder gradient bound follows from the square-root increment. -/
-theorem gradient_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    ‖G.du (t, x) - G.du (s, x)‖ ≤
-      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
-    (show (0 : ℝ) < 1 / 2 by norm_num)
-  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
-  have hi := gradient_time_increment G hs ht x
-  rw [Real.sqrt_eq_rpow] at hi
-  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
-
-/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
-theorem value_time_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
-    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
-    |G.u (t, x) - G.u (s, x)| ≤
-      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
-  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
-  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
-    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
-  rw [Real.rpow_one] at hp
-  exact (value_time_increment G hs ht x).trans (by
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
-
-omit [NormedSpace ℝ E] in
-/-- Split a mixed increment through the point with the first time and second position. -/
-theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
-    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
-    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
-      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
-    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
-      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
-    HasHolderBound α (cylinder T) f (Kx + Kt) := by
-  intro p hp q hq
-  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
-    Real.rpow_le_rpow (norm_nonneg _) (by
-      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
-  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
-    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
-    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
-      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
-  calc
-    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
-      norm_sub_le_norm_sub_add_norm_sub _ _ _
-    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
-      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
-    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
-      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
-
-/-- Full gradient Hölder control, including mixed increments. -/
-theorem gradient_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
-  have h := holder_of_increments hα.le
-    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-    (fun t ht => gradient_space_holder G hα hα1 hT ht)
-    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
-  convert h using 1
-  ring
-
-/-- Full value Hölder control with its stronger time power. -/
-theorem value_holder (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
-    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
-  have h := holder_of_increments (f := G.u) hα.le
-    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
-    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
-    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
-    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
-  convert h using 1
-  ring
-
-/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
-theorem interpolation_bounds (G : Graph (E := E) α T)
-    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
-  constructor
-  · have h := ParabolicHolder.norm_le_of_bounds G.u
-      (show 0 ≤ T * ‖G‖ by positivity)
-      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
-      (fun p hp => (time_bound G hp.1 p.2).trans
-        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
-      (value_holder G hα hα1 hT)
-    have hp : T ≤ T ^ (1-α/2) := by
-      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
-      exact (Real.rpow_one T).symm
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
-      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
-  · have h := ParabolicHolder.norm_le_of_bounds G.du
-      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
-      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
-      (fun p hp => gradient_bound G hT hp.1 p.2)
-      (gradient_holder G hα hα1 hT)
-    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
-      rw [Real.sqrt_eq_rpow]
-      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
-
-/-- A universal constant satisfies the frozen interpolation target. -/
-theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
-      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
-  intro α hα hα1
-  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
-
-/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
-theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
-    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
-      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
-  classical
-  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
-  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
-  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
-  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
-    have h := scale_interpolation (L := 2*A+B) (R := 1)
-      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
-      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
-      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
-    simpa using h
-  refine ⟨A + (2*A+B), by positivity, ?_⟩
-  intro T
-  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
-  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
-    intro p hp; simp [f, hp]
-  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
-    intro p hp; simpa [f, hp] using hA p.2
-  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
-    intro p hp q hq
-    simp only [f, if_pos hp, if_pos hq]
-    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
-      (Real.rpow_le_rpow (norm_nonneg _) (by
-        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
-  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
-  refine ⟨fY, ?_, ?_⟩
-  · intro p hp
-    change f p = ψ p.2
-    simp [f, hp]
-  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
-
-/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
-theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
-    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
-    (hα : 0 < α) (hα1 : α < 1) :
-    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
-      ∃ (f : Y (E := E) α T ℝ)
-        (df : Y (E := E) α T (E →L[ℝ] ℝ))
-        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
-      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
-        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
-      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
-  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
-  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
-  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
-  refine ⟨K0+K1+K2, by positivity, ?_⟩
-  intro T
-  obtain ⟨f, hf, hfb⟩ := h0 T
-  obtain ⟨df, hdf, hdfb⟩ := h1 T
-  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
-  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
-
-/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
-theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z * G.u (t,z))
-      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
-  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
-
-/-- The second spatial product rule includes both mixed Hessian terms. -/
-theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
-      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
-  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
-  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
-    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
-
-/-- A spatial cutoff is constant in the within-time product rule. -/
-theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
-    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
-    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
-  (G.hasDeriv_time t ht x).const_mul (ψ x)
-
-section Bilinear
-variable {F H J : Type*}
-  [NormedAddCommGroup F] [NormedSpace ℝ F]
-  [NormedAddCommGroup H] [NormedSpace ℝ H]
-  [NormedAddCommGroup J] [NormedSpace ℝ J]
-
-omit [NormedSpace ℝ E] in
-/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
-theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
-  intro p hp q hq
-  have hf := ParabolicHolder.holder_le f hp hq
-  have hg := ParabolicHolder.holder_le g hp hq
-  have hf0 := ParabolicHolder.norm_le f p
-  have hg0 := ParabolicHolder.norm_le g q
-  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
-  calc
-    ‖B (f p) (g p) - B (f q) (g q)‖ =
-        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
-      congr 1
-      simp only [map_sub, ContinuousLinearMap.sub_apply]
-      abel
-    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
-    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
-      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
-    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
-        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
-      apply add_le_add
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
-          (norm_nonneg _) (by positivity)
-      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
-          (norm_nonneg _) (by positivity)
-    _ = _ := by ring
-
-/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
-def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
-  ofFunction (fun p => B (f p) (g p))
-    (fun p hp => by simp [zero_off f hp])
-    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
-    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
-
-omit [NormedSpace ℝ E] in
-/-- The bilinear carrier norm has an explicit product bound. -/
-theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
-    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
-    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
-    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
-    (fun p _ => (B.le_opNorm₂ _ _).trans
-      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
-        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
-    (bilinear_holder B f g)
-  nlinarith [h]
-
-end Bilinear
-
-local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
-  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
-
-/-- Assemble the cutoff graph from its three spatial carriers. -/
-def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
-    (G : Graph (E := E) α T) : Graph (E := E) α T where
-  u := f * G.u
-  ut := f * G.ut
-  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
-  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
-    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
-    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
-  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
-  hasFDeriv := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv hψ G ht x using 1
-    · funext z
-      simp only [mul_apply, hf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
-  hasFDeriv_du := by
-    intro t ht x
-    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
-    convert cutoff_hasFDeriv_du hψ G ht x using 1
-    · funext z
-      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
-      rfl
-  hasDeriv_time := by
-    intro t ht x
-    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
-      by_cases hs : (s,x) ∈ cylinder T
-      · simp [mul_apply, hf (s,x) hs]
-      · simp [mul_apply, zero_off G.u hs]
-    convert cutoff_hasDeriv_time ψ G ht x using 1
-    · funext s; exact he s
-    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
-
-/-- Equality of the four stored carriers determines a derivative graph. -/
-theorem graph_ext_components {G H : Graph (E := E) α T}
-    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
-    G = H := by
-  cases G
-  cases H
-  simp_all
-
-/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
-def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
-  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
-  map_add' G H := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
-      simp only [map_add, ContinuousLinearMap.add_apply]
-      module
-  map_smul' c G := by
-    apply graph_ext_components
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.u p) = c • (f p * (G.u p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p * (c • G.ut p) = c • (f p * (G.ut p))
-      ring
-    · apply ParabolicHolder.ext
-      intro p hp
-      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
-      module
-    · apply ParabolicHolder.ext
-      intro p hp
-      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
-      simp only [map_smul, ContinuousLinearMap.smul_apply]
-      module
-
-
-set_option maxHeartbeats 4000000 in
-/-- The cutoff graph map is bounded in the original four-component norm. -/
-theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
-    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
-    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
-    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
-    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
-    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
-      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
-  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
-  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
-  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
-  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
-  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
-    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
-  let A := ‖f‖ + ‖df‖ + ‖ddf‖
-  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
-  have hA : 0 ≤ A := by dsimp [A]; positivity
-  have hB : 0 ≤ B := by dsimp [B]; positivity
-  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
-  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
-  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
-  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
-  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
-  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
-  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
-  refine ⟨20 * B * A, ?_⟩
-  intro G
-  have hGu := norm_u_le G
-  have hGut := norm_ut_le G
-  have hGdu := norm_du_le G
-  have hGddu := norm_ddu_le G
-  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
-    calc
-      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
-      _ ≤ B * A * ‖G‖ := by
-        calc
-          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
-          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
-  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * A * ‖G‖ := by gcongr
-  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
-    calc
-      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
-      _ ≤ 3 * B * ‖G‖ * A := by gcongr
-      _ = _ := by ring
-  rw [ParabolicSolutionGraph.norm_eq]
-  change ‖f * G.u‖ + ‖f * G.ut‖ +
-    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
-    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
-      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
-  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
-  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
-    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
-  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
-  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
-  nlinarith
-
-/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
-theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
-    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
-        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
-        (C G).ddu (t,x) =
-          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
-          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
-            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
-  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
-  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
-  have hf := fun p hp => (heq p hp).1
-  have hdf := fun p hp => (heq p hp).2.1
-  have hddf := fun p hp => (heq p hp).2.2
-  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
-  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
-  let C := L.mkContinuous B hB
-  refine ⟨C, ?_, ?_⟩
-  · intro G p
-    change f p * G.u p = ψ p.2 * G.u p
-    by_cases hp : p ∈ cylinder T
-    · rw [hf p hp]
-    · simp [zero_off G.u hp]
-  · intro G t ht x
-    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
-    change f (t,x) * G.ut (t,x) = _ ∧
-      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
-        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
-    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
-    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp]
-    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
-      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
-        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
-      rfl
-
-end Poincare.ParabolicCutoffCommutator
-
-noncomputable section
-set_option maxHeartbeats 800000
-namespace Poincare.ParabolicCutoffCommutator
-open Set ParabolicHolder ParabolicSolutionGraph
-open scoped ContDiff
-variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
-
-/-- Evaluate a first derivative carrier on a unit direction. -/
-def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    Y (E := E) α T ℝ :=
-  ofFunction (fun p => H p v)
-    (fun p hp => by simp [zero_off H hp])
-    ⟨‖H‖, fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
-    ⟨‖H‖, fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
-
-/-- Evaluation is bounded in the full Hölder norm. -/
-theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
-    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
-  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
-    (norm_nonneg H) (norm_nonneg H)
-    (fun p _ => by
-      simpa [hv] using ((H p).le_opNorm v).trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
-    (fun p hp q hq => by
-      have h := (H p - H q).le_opNorm v
-      simpa [hv] using h.trans
-        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
-  linarith
-
-
-/-- The first-order forcing associated to the explicit commutator coefficients. -/
-def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) : Y (E := (ClosedSmoothModel 3)) α T ℝ :=
-  (∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c * G.u
-
-/-- The carrier evaluates to the first-order coefficient formula. -/
-theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) :
-    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p := by
-  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
-    derivativeEntry, ofFunction_apply]
-
-/-- The commutator uses only the value and gradient norms. -/
-theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) :
-    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
-  calc
-    ‖firstOrderForcing b c G‖ ≤
-        ‖∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ + ‖c * G.u‖ := norm_add_le _ _
-    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖) + ‖c‖ * ‖G.u‖ :=
-      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
-    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
-      apply add_le_add_left
-      apply Finset.sum_le_sum
-      intro i hi
-      exact (ParabolicHolder.norm_mul_le _ _).trans
-        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
-    _ = _ := by rw [← Finset.sum_mul]; ring
-
-/-- The commutator has separate positive time powers for its two coefficient families. -/
-theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
-  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
-  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
-  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
-  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
-  have h3 := norm_firstOrderForcing_le b c G
-  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
-
-/-- The common weaker time exponent controls both first-order terms. -/
-theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
-    ‖firstOrderForcing b c G‖ ≤
-      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
-  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
-    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
-  have h := firstOrder_time_bound b c G hα hα1 hT hT1
-  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
-
-/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
-def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
-    Graph (E := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ where
-  toFun := firstOrderForcing b c
-  map_add' G H := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [add_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) + H.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (G.u p + H.u p) = _
-    simp only [mul_add, Finset.sum_add_distrib]
-    ring
-  map_smul' r G := by
-    apply ParabolicHolder.ext
-    intro p hp
-    simp only [smul_apply, firstOrderForcing_apply]
-    change (∑ i : Fin 3, b i p * (r * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (r * G.u p) = _
-    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
-    ring
-
-/-- The frozen commutator operator target, with a universal constant. -/
-theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
-    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∀ (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ),
-    ∃ K : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ,
-      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p) ∧
-      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
-  intro α hα hα1
-  refine ⟨24, by norm_num, ?_⟩
-  intro T hT hT1 b c
-  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
-  let K := (firstOrderLinearMap b c).mkContinuous B
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
-  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
-    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
-
-set_option maxHeartbeats 4000000 in
-/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
-theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
-    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
-    (a : Fin 3 → Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (drift : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (potential : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
-    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
-      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)))
-    (hc : ∀ t ∈ Icc 0 T, ∀ x,
-      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) -
-        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
-    ∃ C : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Graph (E := (ClosedSmoothModel 3)) α T,
-      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
-      (∀ G t, t ∈ Icc 0 T → ∀ x,
-        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
-          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * (C G).u (t,x)) -
-        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
-          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * G.u (t,x)) =
-        (∑ i : Fin 3, b i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c (t,x) * G.u (t,x)) := by
-  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
-  refine ⟨C, hu, ?_⟩
-  intro G t ht x
-  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
-  rw [hut, hdu, hddu, hu G (t,x)]
-  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
-    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
-    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
-  ring
-
-end Poincare.ParabolicCutoffCommutator
+import Poincare.Global.ParabolicCutoffCommutator
+open Poincare
+#check ContDiff.RCLike
+#check ContDiff.lipschitzWith_of_hasCompactSupport
+#check ContinuousLinearMap.add_apply
+#check ContinuousLinearMap.lsmul
+#check ContinuousLinearMap.lsmul_apply
+#check ContinuousLinearMap.opNorm_le_bound
+#check ContinuousLinearMap.opNorm_le_of_unit_norm
+#check ContinuousLinearMap.opNorm_smul_le
+#check ContinuousLinearMap.smulRightL
+#check ContinuousLinearMap.smulRight_apply
+#check ContinuousLinearMap.smul_apply
+#check ContinuousLinearMap.sub_apply
+#check Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+#check Fin.sum_univ_succ
+#check Fin.sum_univ_zero
+#check Finset.sum_add_distrib
+#check Finset.sum_le_sum
+#check Finset.sum_mul
+#check Finset.sum_nonneg
+#check OrthonormalBasis.norm_eq_one
+#check ParabolicHolder.ext
+#check ParabolicHolder.holder_le
+#check ParabolicHolder.norm_le
+#check ParabolicHolder.norm_le_of_bounds
+#check ParabolicHolder.norm_mul_le
+#check ParabolicHolderMultiplier.sum_apply
+#check ParabolicSolutionGraph.norm_eq
+#check Real.norm_eq_abs
+#check Real.rpow_add
+#check Real.rpow_le_rpow
+#check Real.rpow_le_rpow_of_exponent_ge
+#check Real.rpow_mul
+#check Real.rpow_nonneg
+#check Real.rpow_one
+#check Real.sq_sqrt
+#check Real.sqrt
+#check Real.sqrt_eq_rpow
+#check Real.sqrt_nonneg
+#check Real.sqrt_pos
+#check EuclideanSpace.basisFun
+#check Poincare.ClosedSmoothModel
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/SymbolChecks.lean \n",
  "exit: 1\n",
  "/tmp/parabolic-cutoff-commutator/SymbolChecks.lean:3:7: error(lean.unknownIdentifier): Unknown constant `ContDiff.RCLike`\n",
  "ContDiff.lipschitzWith_of_hasCompactSupport.{u_1, u_2, u_3} {n : WithTop ℕ∞} {𝕂 : Type u_1} [RCLike 𝕂] {E' : Type u_2}\n",
  "  [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type u_3} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'}\n",
  "  (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : n ≠ 0) : ∃ C, LipschitzWith C f\n",
  "ContinuousLinearMap.add_apply.{u_1, u_2, u_4, u_6} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]\n",
  "  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]\n",
  "  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] [ContinuousAdd M₂] (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) :\n",
  "  (f + g) x = f x + g x\n",
  "ContinuousLinearMap.lsmul.{u_1, u_2, u_3} (𝕜 : Type u_1) {E : Type u_2} [NontriviallyNormedField 𝕜]\n",
  "  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (R : Type u_3) [SeminormedRing R] [NormedAlgebra 𝕜 R] [Module R E]\n",
  "  [IsBoundedSMul R E] [IsScalarTower 𝕜 R E] : R →L[𝕜] E →L[𝕜] E\n",
  "ContinuousLinearMap.lsmul_apply.{u_1, u_2, u_3} (𝕜 : Type u_1) {E : Type u_2} [NontriviallyNormedField 𝕜]\n",
  "  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (R : Type u_3) [SeminormedRing R] [NormedAlgebra 𝕜 R] [Module R E]\n",
  "  [IsBoundedSMul R E] [IsScalarTower 𝕜 R E] (c : R) (x : E) : ((ContinuousLinearMap.lsmul 𝕜 R) c) x = c • x\n",
  "ContinuousLinearMap.opNorm_le_bound.{u_1, u_2, u_4, u_5} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type u_5}\n",
  "  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]\n",
  "  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)\n",
  "  (hM : ∀ (x : E), ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M\n",
  "ContinuousLinearMap.opNorm_le_of_unit_norm.{u_1, u_2, u_4, u_5} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}\n",
  "  {F : Type u_5} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]\n",
  "  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]\n",
  "  [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ (x : E), ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C\n",
  "ContinuousLinearMap.opNorm_smul_le.{u_1, u_2, u_4, u_5, u_9} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}\n",
  "  {F : Type u_5} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]\n",
  "  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]\n",
  "  {𝕜' : Type u_9} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] [SeminormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F] (c : 𝕜')\n",
  "  (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖\n",
  "ContinuousLinearMap.smulRightL.{u_1, u_4, u_7} (𝕜 : Type u_1) (E : Type u_4) (Fₗ : Type u_7) [SeminormedAddCommGroup E]\n",
  "  [SeminormedAddCommGroup Fₗ] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] :\n",
  "  StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ\n",
  "ContinuousLinearMap.smulRight_apply.{u_4, u_6, u_9, u_10} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁]\n",
  "  {M₂ : Type u_6} [TopologicalSpace M₂] [AddCommMonoid M₂] {R : Type u_9} {S : Type u_10} [Semiring R] [Semiring S]\n",
  "  [Module R M₁] [Module R M₂] [Module R S] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]\n",
  "  [ContinuousSMul S M₂] {c : M₁ →L[R] S} {f : M₂} {x : M₁} : (c.smulRight f) x = c x • f\n",
  "ContinuousLinearMap.smul_apply.{u_1, u_2, u_4, u_6, u_9} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]\n",
  "  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]\n",
  "  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] {S₂ : Type u_9} [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂]\n",
  "  [ContinuousConstSMul S₂ M₂] (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x\n",
  "ContinuousLinearMap.sub_apply.{u_1, u_2, u_4, u_5} {R : Type u_1} [Ring R] {R₂ : Type u_2} [Ring R₂] {M : Type u_4}\n",
  "  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type u_5} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M]\n",
  "  [Module R₂ M₂] {σ₁₂ : R →+* R₂} [IsTopologicalAddGroup M₂] (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x\n",
  "Convex.norm_image_sub_le_of_norm_hasDerivWithin_le.{u_3, u_4} {𝕜 : Type u_3} {G : Type u_4} [RCLike 𝕜]\n",
  "  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜} {C : ℝ}\n",
  "  (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s)\n",
  "  (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖\n",
  "Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le.{u_1, u_3, u_4} {E : Type u_1} [NormedAddCommGroup E]\n",
  "  [NormedSpace ℝ E] {𝕜 : Type u_3} {G : Type u_4} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E]\n",
  "  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → G} {C : ℝ} {s : Set E} {x y : E} {f' : E → E →L[𝕜] G}\n",
  "  (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s)\n",
  "  (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖\n",
  "Fin.sum_univ_succ.{u_2} {M : Type u_2} [AddCommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) : ∑ i, f i = f 0 + ∑ i, f i.succ\n",
  "Fin.sum_univ_zero.{u_2} {M : Type u_2} [AddCommMonoid M] (f : Fin 0 → M) : ∑ i, f i = 0\n",
  "Finset.sum_add_distrib.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s : Finset ι} [AddCommMonoid M] {f g : ι → M} :\n",
  "  ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x\n",
  "Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f g : ι → N} {s : Finset ι}\n",
  "  [AddLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i\n",
  "Finset.sum_mul.{u_1, u_4} {ι : Type u_1} {R : Type u_4} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R)\n",
  "  (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a\n",
  "Finset.sum_nonneg.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f : ι → N} {s : Finset ι}\n",
  "  [AddLeftMono N] (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i\n",
  "OrthonormalBasis.norm_eq_one.{u_1, u_3, u_4} {ι : Type u_1} {𝕜 : Type u_3} [RCLike 𝕜] {E : Type u_4}\n",
  "  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ‖b i‖ = 1\n",
  "Poincare.ParabolicHolder.ext.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]\n",
  "  [NormedSpace ℝ F] {α T : ℝ} {f g : ParabolicHolder.Y α T F}\n",
  "  (h : ∀ p ∈ ParabolicHolder.cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p) : f = g\n",
  "Poincare.ParabolicHolder.holder_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]\n",
  "  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) {p q : ℝ × E}\n",
  "  (hp : p ∈ ParabolicHolder.cylinder T) (hq : q ∈ ParabolicHolder.cylinder T) :\n",
  "  ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * ParabolicHolder.parabolicDist p q ^ α\n",
  "Poincare.ParabolicHolder.norm_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]\n",
  "  [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) (p : ℝ × E) : ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖\n",
  "Poincare.ParabolicHolder.norm_le_of_bounds.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]\n",
  "  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)\n",
  "  (hb : ∀ p ∈ ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M)\n",
  "  (hh : ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f)) K) : ‖f‖ ≤ M + K\n",
  "Poincare.ParabolicHolder.norm_mul_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] {α T : ℝ}\n",
  "  (f g : ParabolicHolder.Y α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖\n",
  "Poincare.ParabolicHolderMultiplier.sum_apply.{u_1} {α T : ℝ} {ι : Type u_1} (s : Finset ι)\n",
  "  (f : ι → ParabolicHolder.Y α T ℝ) (p : ℝ × ClosedSmoothModel 3) :\n",
  "  ↑(WithLp.fst ↑(∑ i ∈ s, f i)) p = ∑ i ∈ s, ↑(WithLp.fst ↑(f i)) p\n",
  "Poincare.ParabolicSolutionGraph.norm_eq.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}\n",
  "  (g : ParabolicSolutionGraph.Graph α T) : ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖\n",
  "Real.norm_eq_abs (r : ℝ) : ‖r‖ = |r|\n",
  "Real.rpow_add {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z\n",
  "Real.rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z\n",
  "Real.rpow_le_rpow_of_exponent_ge {x y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z\n",
  "Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z\n",
  "Real.rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y\n",
  "Real.rpow_one (x : ℝ) : x ^ 1 = x\n",
  "Real.sq_sqrt {x : ℝ} (h : 0 ≤ x) : √x ^ 2 = x\n",
  "Real.sqrt (x : ℝ) : ℝ\n",
  "Real.sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / 2)\n",
  "Real.sqrt_nonneg (x : ℝ) : 0 ≤ √x\n",
  "Real.sqrt_pos {x : ℝ} : 0 < √x ↔ 0 < x\n",
  "EuclideanSpace.basisFun.{u_1, u_3} (ι : Type u_1) (𝕜 : Type u_3) [RCLike 𝕜] [Fintype ι] :\n",
  "  OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)\n",
  "Poincare.ClosedSmoothModel (n : ℕ) : Type\n"
]
```

</details>

<details>
<summary>run-056</summary>

Source SHA-256: `212b645f952257284ec45e9025b1d20bab0ac815998b6f7bc8aee5fc096465c2`.

```diff
--- preceding snapshot
+++ run-056.lean
@@ -1,44 +1,266 @@
 import Poincare.Global.ParabolicCutoffCommutator
+import Poincare.Global.NearIdentityParabolicRightInverse
+import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
+import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
+import Poincare.Global.DeTurckPrincipalIdentity
+import Poincare.Global.CompactCoefficientEllipticity
+import Mathlib.Analysis.Calculus.ContDiff.RCLike
+import Mathlib.Topology.MetricSpace.Contracting
+
+set_option autoImplicit false
+noncomputable section
+open Set
+open scoped Manifold ContDiff
+namespace FiniteAtlasSurvey
 open Poincare
-#check ContDiff.RCLike
-#check ContDiff.lipschitzWith_of_hasCompactSupport
-#check ContinuousLinearMap.add_apply
-#check ContinuousLinearMap.lsmul
-#check ContinuousLinearMap.lsmul_apply
-#check ContinuousLinearMap.opNorm_le_bound
-#check ContinuousLinearMap.opNorm_le_of_unit_norm
-#check ContinuousLinearMap.opNorm_smul_le
-#check ContinuousLinearMap.smulRightL
-#check ContinuousLinearMap.smulRight_apply
-#check ContinuousLinearMap.smul_apply
-#check ContinuousLinearMap.sub_apply
-#check Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
-#check Fin.sum_univ_succ
-#check Fin.sum_univ_zero
-#check Finset.sum_add_distrib
-#check Finset.sum_le_sum
-#check Finset.sum_mul
-#check Finset.sum_nonneg
-#check OrthonormalBasis.norm_eq_one
-#check ParabolicHolder.ext
-#check ParabolicHolder.holder_le
-#check ParabolicHolder.norm_le
-#check ParabolicHolder.norm_le_of_bounds
-#check ParabolicHolder.norm_mul_le
-#check ParabolicHolderMultiplier.sum_apply
-#check ParabolicSolutionGraph.norm_eq
-#check Real.norm_eq_abs
-#check Real.rpow_add
-#check Real.rpow_le_rpow
-#check Real.rpow_le_rpow_of_exponent_ge
-#check Real.rpow_mul
-#check Real.rpow_nonneg
-#check Real.rpow_one
-#check Real.sq_sqrt
-#check Real.sqrt
-#check Real.sqrt_eq_rpow
-#check Real.sqrt_nonneg
-#check Real.sqrt_pos
-#check EuclideanSpace.basisFun
-#check Poincare.ClosedSmoothModel
+local notation "E" => ClosedSmoothModel 3
+local notation "I" => closedSmoothModelWithCorners 3
+local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
+abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
+abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
+abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
+
+universe u
+variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
+  [IsManifold I ∞ M]
+
+structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
+    [IsManifold I ∞ M] where
+  cover : FiniteExtendedChartCover (n := 3) (M := M)
+  region : Fin cover.chartCount → Set M
+  region_open : ∀ i, IsOpen (region i)
+  region_cover : (⋃ i, region i) = univ
+  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
+  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
+  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
+  subordinate : partition.IsSubordinate region
+
+variable (A : AtlasData M)
+abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
+abbrev LocalProduct (H : Type*) := Index A → H
+
+def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
+def coordSupport (i : Fin A.cover.chartCount) : Set E :=
+  chart A i '' tsupport (A.partition i)
+def change (i j : Fin A.cover.chartCount) (z : E) : E :=
+  chart A j ((chart A i).symm z)
+def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
+  (fderiv ℝ (change A i j) (chart A i x) (e a)) c
+
+def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
+  ({ toFun := fun f => f p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
+
+def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
+  ({ toFun := fun G => G.u p
+     map_add' := fun _ _ => rfl
+     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
+    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)
+
+variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
+def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
+    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
+  (ev p).comp (ContinuousLinearMap.proj (i, a, b))
+
+def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
+    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
+  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
+    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
+      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)
+
+def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
+    ⨅ (z : {z : E // z ∉ coordSupport A i}),
+    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap
+
+def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
+    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap
+
+def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
+    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
+    LinearMap.ker (overlap A ev i j a b t x).toLinearMap
+
+def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
+  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
+abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
+abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
+
+structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
+  entries : LocalProduct A H
+  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
+  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
+  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
+    overlap A ev i j a b t x entries = 0
+
+-- Statement definitions, not proofs of closedness, completeness or equivalence.
+def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
+  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
+def carrierCompleteGoal (α T : ℝ) : Prop :=
+  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
+def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
+  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)
+
+-- Positive-time candidate strengthened norm functional; no norm instance claimed.
+def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
+  T ^ (-(1 - α / 2)) * ‖G.u‖ +
+  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖
+
+def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
+    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖
+
+-- Coefficients are the resulting commutator coefficients, already zero-extended.
+def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
+    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
+  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p
+
+def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
+  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
+  ∃ K : Jet α T →L[ℝ] Scalar α T,
+    (∀ G p, K G p = firstOrderValue b c G p) ∧
+    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)
+
+structure CutoffData (α T : ℝ) where
+  psi : E → ℝ
+  smooth : ContDiff ℝ ∞ psi
+  compact : HasCompactSupport psi
+  a : Fin 3 → Fin 3 → Scalar α T
+  drift : Fin 3 → Scalar α T
+  b : Fin 3 → Scalar α T
+  c : Scalar α T
+  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
+    b k (t,x) = -(∑ j : Fin 3,
+      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
+  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
+    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
+      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
+      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)
+
+def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
+    ∀ G p, (C G).u p = D.psi p.2 * G.u p
+
+structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
+  S : Scalar α T →L[ℝ] Jet α T
+  bound : ‖S‖ ≤ C_S
+  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
+    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
+      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)
+
+def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
+    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
+  0 < α → 0 < T →
+  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
+  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
+  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
+    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖
+
+-- Actual chart coefficient agreement is separate from the frozen analytic data.
+structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
+  cutoff : E → ℝ
+  smooth : ContDiff ℝ ∞ cutoff
+  compact : HasCompactSupport cutoff
+  one_on : ∀ z ∈ U, cutoff z = 1
+  b : Fin 3 → Fin 3 → Scalar α T
+  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
+    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))
+
+def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
+    (N : X_M A α T → Y_M A α T) : Prop :=
+  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
+    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
+  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
+def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
+    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
+    (G : Jet α T) (p : ℝ × E) : ℝ :=
+  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
+    a i j p * G.ddu p (e i) (e j)) -
+    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p
+
+def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
+    (potential : Scalar α T) : Prop :=
+  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
+    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
+    (∀ G t, t ∈ Icc 0 T → ∀ x,
+      localLinearValue D.a D.drift potential (C G) (t,x) -
+        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
+          firstOrderValue D.b D.c G (t,x))
+
+def oscillationExtensionGoal : Prop :=
+  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
+  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
+  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
+  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
+  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
+    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
+  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∃ b : Fin 3 → Fin 3 → Scalar α T,
+      (∀ t ∈ Icc 0 T, ∀ x i j,
+        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
+      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
+      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)
+
+def frozenCLMGoal : Prop :=
+  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
+  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
+  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
+  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)
+
+abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
+  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
+
+def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
+  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)
+
+def localizedValue {T : ℝ} (F : TensorField (M := M) T)
+    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
+  classical
+  exact if ht : p.1 ∈ Icc 0 T then
+    if p.2 ∈ (chart A i).target then
+      let x := (chart A i).symm p.2
+      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
+    else 0
+  else 0
+
+def reconstructionGoal (α T : ℝ) : Prop :=
+  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
+    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p
+
+abbrev Jet1 := E →L[ℝ] Bilin
+abbrev Jet2 := E →L[ℝ] Jet1
+
+def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
+    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
+  (∑ i : Fin 3, ∑ j : Fin 3,
+    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
+    DeTurckPrincipalIdentity.lowerTerm B DB G J
+
+set_option synthInstance.maxHeartbeats 400000 in
+def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
+    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
+    (z h : Bilin × Jet1 × Jet2) : Bilin :=
+  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
+    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
+    (∑ i : Fin 3, ∑ j : Fin 3,
+      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
+end FiniteAtlasSurvey
+
+example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation
+example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) : FiniteAtlasSurvey.cutoffGraphGoal D := by
+  intro hα hα1 hT hT1
+  obtain ⟨C, hu, _⟩ := Poincare.ParabolicCutoffCommutator.exists_cutoff_operator D.smooth D.compact hα hα1
+  exact ⟨C, hu⟩
+
+example : FiniteAtlasSurvey.commutatorGoal := Poincare.ParabolicCutoffCommutator.commutator
+example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) (potential : FiniteAtlasSurvey.Scalar α T) :
+    FiniteAtlasSurvey.cutoffIdentityGoal D potential := by
+  intro hα hα1 hT hT1
+  exact Poincare.ParabolicCutoffCommutator.cutoff_commutator_identity D.smooth D.compact hα hα1
+    D.a D.drift potential D.b D.c D.b_eq D.c_eq
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/FinalTargets.lean \n",
  "exit: 0\n"
]
```

</details>

<details>
<summary>run-057</summary>

Source SHA-256: `fa9b17a8529b0385b7717dd470984b87383aedc1856019cb8f4635acf547e764`.

```diff
--- preceding snapshot
+++ run-057.lean
@@ -1,266 +1,43 @@
 import Poincare.Global.ParabolicCutoffCommutator
-import Poincare.Global.NearIdentityParabolicRightInverse
-import Poincare.Global.ClosedLaplacianStokesGlobalCoefficients
-import Poincare.Global.FiniteFixedAnchorCutoffOneChartCover
-import Poincare.Global.DeTurckPrincipalIdentity
-import Poincare.Global.CompactCoefficientEllipticity
-import Mathlib.Analysis.Calculus.ContDiff.RCLike
-import Mathlib.Topology.MetricSpace.Contracting
-
-set_option autoImplicit false
-noncomputable section
-open Set
-open scoped Manifold ContDiff
-namespace FiniteAtlasSurvey
 open Poincare
-local notation "E" => ClosedSmoothModel 3
-local notation "I" => closedSmoothModelWithCorners 3
-local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
-abbrev Scalar (α T : ℝ) := ParabolicHolder.Y («E» := E) α T ℝ
-abbrev Jet (α T : ℝ) := ParabolicSolutionGraph.Graph («E» := E) α T
-abbrev Bilin := E →L[ℝ] E →L[ℝ] ℝ
-
-universe u
-variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
-  [IsManifold I ∞ M]
-
-structure AtlasData (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
-    [IsManifold I ∞ M] where
-  cover : FiniteExtendedChartCover (n := 3) (M := M)
-  region : Fin cover.chartCount → Set M
-  region_open : ∀ i, IsOpen (region i)
-  region_cover : (⋃ i, region i) = univ
-  closure_source : ∀ i, closure (region i) ⊆ (extChartAt I (cover.anchor i)).source
-  coordinate_compact : ∀ i, IsCompact ((extChartAt I (cover.anchor i)) '' closure (region i))
-  partition : SmoothPartitionOfUnity (Fin cover.chartCount) I M univ
-  subordinate : partition.IsSubordinate region
-
-variable (A : AtlasData M)
-abbrev Index := Fin A.cover.chartCount × Fin 3 × Fin 3
-abbrev LocalProduct (H : Type*) := Index A → H
-
-def chart (i : Fin A.cover.chartCount) := extChartAt I (A.cover.anchor i)
-def coordSupport (i : Fin A.cover.chartCount) : Set E :=
-  chart A i '' tsupport (A.partition i)
-def change (i j : Fin A.cover.chartCount) (z : E) : E :=
-  chart A j ((chart A i).symm z)
-def jac (i j : Fin A.cover.chartCount) (x : M) (c a : Fin 3) : ℝ :=
-  (fderiv ℝ (change A i j) (chart A i x) (e a)) c
-
-def evalY (α T : ℝ) (p : ℝ × E) : Scalar α T →L[ℝ] ℝ :=
-  ({ toFun := fun f => f p
-     map_add' := fun _ _ => rfl
-     map_smul' := fun _ _ => rfl } : Scalar α T →ₗ[ℝ] ℝ).mkContinuous 1
-    (fun f => by simpa only [one_mul] using ParabolicHolder.norm_le f p)
-
-def evalX (α T : ℝ) (p : ℝ × E) : Jet α T →L[ℝ] ℝ :=
-  ({ toFun := fun G => G.u p
-     map_add' := fun _ _ => rfl
-     map_smul' := fun _ _ => rfl } : Jet α T →ₗ[ℝ] ℝ).mkContinuous 1
-    (fun G => by simpa only [one_mul] using ParabolicSolutionGraph.sup_u_le G p)
-
-variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
-def evalLocal (ev : ℝ × E → H →L[ℝ] ℝ) (i : Fin A.cover.chartCount)
-    (a b : Fin 3) (p : ℝ × E) : LocalProduct A H →L[ℝ] ℝ :=
-  (ev p).comp (ContinuousLinearMap.proj (i, a, b))
-
-def overlap (ev : ℝ × E → H →L[ℝ] ℝ) (i j : Fin A.cover.chartCount)
-    (a b : Fin 3) (t : ℝ) (x : M) : LocalProduct A H →L[ℝ] ℝ :=
-  A.partition j x • evalLocal A ev i a b (t, chart A i x) -
-    A.partition i x • ∑ c : Fin 3, ∑ d : Fin 3,
-      (jac A i j x c a * jac A i j x d b) • evalLocal A ev j c d (t, chart A j x)
-
-def supportSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ),
-    ⨅ (z : {z : E // z ∉ coordSupport A i}),
-    LinearMap.ker (evalLocal A ev i a b (t, z)).toLinearMap
-
-def symmetrySubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (p : ℝ × E),
-    LinearMap.ker (evalLocal A ev i a b p - evalLocal A ev i b a p).toLinearMap
-
-def overlapSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  ⨅ (i : Fin A.cover.chartCount), ⨅ (j : Fin A.cover.chartCount),
-    ⨅ (a : Fin 3), ⨅ (b : Fin 3), ⨅ (t : ℝ), ⨅ (x : {x : M // x ∈ (chart A i).source ∩ (chart A j).source}),
-    LinearMap.ker (overlap A ev i j a b t x).toLinearMap
-
-def tensorSubmodule (ev : ℝ × E → H →L[ℝ] ℝ) : Submodule ℝ (LocalProduct A H) :=
-  supportSubmodule A ev ⊓ symmetrySubmodule A ev ⊓ overlapSubmodule A ev
-abbrev Y_M (α T : ℝ) := ↥(tensorSubmodule A (evalY α T))
-abbrev X_M (α T : ℝ) := ↥(tensorSubmodule A (evalX α T))
-
-structure CompatibleFields (ev : ℝ × E → H →L[ℝ] ℝ) where
-  entries : LocalProduct A H
-  supported : ∀ i a b t z, z ∉ coordSupport A i → evalLocal A ev i a b (t,z) entries = 0
-  symmetric : ∀ i a b p, evalLocal A ev i a b p entries = evalLocal A ev i b a p entries
-  transition : ∀ i j a b t x, x ∈ (chart A i).source ∩ (chart A j).source →
-    overlap A ev i j a b t x entries = 0
-
--- Statement definitions, not proofs of closedness, completeness or equivalence.
-def carrierClosedGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
-  IsClosed (tensorSubmodule A ev : Set (LocalProduct A H))
-def carrierCompleteGoal (α T : ℝ) : Prop :=
-  CompleteSpace (Y_M A α T) ∧ CompleteSpace (X_M A α T)
-def carrierFieldsGoal (ev : ℝ × E → H →L[ℝ] ℝ) : Prop :=
-  Nonempty (↥(tensorSubmodule A ev) ≃ CompatibleFields A ev)
-
--- Positive-time candidate strengthened norm functional; no norm instance claimed.
-def weightedSize (α T : ℝ) (G : Jet α T) : ℝ :=
-  T ^ (-(1 - α / 2)) * ‖G.u‖ +
-  T ^ (-((1 - α) / 2)) * ‖G.du‖ + ‖G.ut‖ + ‖G.ddu‖
-
-def interpolationGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Jet α T,
-    ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
-    ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖
-
--- Coefficients are the resulting commutator coefficients, already zero-extended.
-def firstOrderValue {α T : ℝ} (b : Fin 3 → Scalar α T)
-    (c : Scalar α T) (G : Jet α T) (p : ℝ × E) : ℝ :=
-  (∑ a : Fin 3, b a p * G.du p (e a)) + c p * G.u p
-
-def commutatorGoal : Prop := ∀ α : ℝ, 0 < α → α < 1 →
-  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-  ∀ (b : Fin 3 → Scalar α T) (c : Scalar α T),
-  ∃ K : Jet α T →L[ℝ] Scalar α T,
-    (∀ G p, K G p = firstOrderValue b c G p) ∧
-    ‖K‖ ≤ C * ((∑ a : Fin 3, ‖b a‖) + ‖c‖) * T ^ ((1 - α) / 2)
-
-structure CutoffData (α T : ℝ) where
-  psi : E → ℝ
-  smooth : ContDiff ℝ ∞ psi
-  compact : HasCompactSupport psi
-  a : Fin 3 → Fin 3 → Scalar α T
-  drift : Fin 3 → Scalar α T
-  b : Fin 3 → Scalar α T
-  c : Scalar α T
-  b_eq : ∀ t ∈ Icc 0 T, ∀ x k,
-    b k (t,x) = -(∑ j : Fin 3,
-      (a j k (t,x) + a k j (t,x)) * fderiv ℝ psi x (e j))
-  c_eq : ∀ t ∈ Icc 0 T, ∀ x,
-    c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3,
-      a j k (t,x) * fderiv ℝ (fderiv ℝ psi) x (e j) (e k)) -
-      ∑ j : Fin 3, drift j (t,x) * fderiv ℝ psi x (e j)
-
-def cutoffGraphGoal {α T : ℝ} (D : CutoffData α T) : Prop :=
-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
-    ∀ G p, (C G).u p = D.psi p.2 * G.u p
-
-structure FrozenSolver (α T C_S : ℝ) (A0 : Bilin) where
-  S : Scalar α T →L[ℝ] Jet α T
-  bound : ‖S‖ ≤ C_S
-  solves : ∀ f t, t ∈ Icc 0 T → ∀ x,
-    (S f).ut (t,x) = f (t,x) + ∑ a : Fin 3, ∑ b : Fin 3,
-      A0 (e a) (e b) * (S f).ddu (t,x) (e a) (e b)
-
-def frozenErrorGoal {α T C_S ε Λ : ℝ} {A0 : Bilin}
-    (S : FrozenSolver α T C_S A0) (b : Fin 3 → Fin 3 → Scalar α T) : Prop :=
-  0 < α → 0 < T →
-  (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) →
-  (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ) →
-  ∀ f, ‖ParabolicHolderMultiplier.forcing b (S.S f)‖ ≤
-    9 * C_S * (ε + Λ * T ^ (α / 2)) * ‖f‖
-
--- Actual chart coefficient agreement is separate from the frozen analytic data.
-structure OscillationData (α T : ℝ) (U : Set E) (a : E → Bilin) (anchor : E) where
-  cutoff : E → ℝ
-  smooth : ContDiff ℝ ∞ cutoff
-  compact : HasCompactSupport cutoff
-  one_on : ∀ z ∈ U, cutoff z = 1
-  b : Fin 3 → Fin 3 → Scalar α T
-  entry_eq : ∀ t ∈ Icc 0 T, ∀ x i j,
-    b i j (t,x) = cutoff x * (a x (e i) (e j) - a anchor (e i) (e j))
-
-def nonlinearGoal (α T r C_NL C_ref θ : ℝ)
-    (N : X_M A α T → Y_M A α T) : Prop :=
-  (∀ v w, ‖v‖ ≤ r → ‖w‖ ≤ r →
-    ‖N v - N w‖ ≤ C_NL * (r + T ^ θ) * ‖v - w‖) ∧
-  ‖N 0‖ ≤ C_ref * (T + T ^ (1 - α / 2))
-def localLinearValue {α T : ℝ} (a : Fin 3 → Fin 3 → Scalar α T)
-    (drift : Fin 3 → Scalar α T) (potential : Scalar α T)
-    (G : Jet α T) (p : ℝ × E) : ℝ :=
-  G.ut p - (∑ i : Fin 3, ∑ j : Fin 3,
-    a i j p * G.ddu p (e i) (e j)) -
-    (∑ i : Fin 3, drift i p * G.du p (e i)) - potential p * G.u p
-
-def cutoffIdentityGoal {α T : ℝ} (D : CutoffData α T)
-    (potential : Scalar α T) : Prop :=
-  0 < α → α < 1 → 0 < T → T ≤ 1 → ∃ C : Jet α T →L[ℝ] Jet α T,
-    (∀ G p, (C G).u p = D.psi p.2 * G.u p) ∧
-    (∀ G t, t ∈ Icc 0 T → ∀ x,
-      localLinearValue D.a D.drift potential (C G) (t,x) -
-        D.psi x * localLinearValue D.a D.drift potential G (t,x) =
-          firstOrderValue D.b D.c G (t,x))
-
-def oscillationExtensionGoal : Prop :=
-  ∀ α : ℝ, 0 < α → α < 1 → ∀ (U : Set E), IsOpen U →
-  ∀ (a : E → Bilin), ContDiffOn ℝ ∞ a U → ∀ (anchor : E), anchor ∈ U →
-  ∀ (ξ : E → ℝ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
-  (∀ x, ξ x ∈ Icc 0 1) → ∀ ε : ℝ, 0 ≤ ε →
-  (∀ x ∈ tsupport ξ, ∀ i j : Fin 3,
-    |a x (e i) (e j) - a anchor (e i) (e j)| ≤ ε) →
-  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
-    ∃ b : Fin 3 → Fin 3 → Scalar α T,
-      (∀ t ∈ Icc 0 T, ∀ x i j,
-        b i j (t,x) = ξ x * (a x (e i) (e j) - a anchor (e i) (e j))) ∧
-      (∀ i j, ParabolicHolder.supNorm (ParabolicHolder.cylinder T) (b i j) ≤ ε) ∧
-      (∀ i j, ParabolicHolder.holderSeminorm α (ParabolicHolder.cylinder T) (b i j) ≤ Λ)
-
-def frozenCLMGoal : Prop :=
-  ∀ α : ℝ, 0 < α → α < 1 → ∀ lam Λ : ℝ, 0 < lam → lam ≤ Λ →
-  ∃ C_S : ℝ, 0 < C_S ∧ ∀ A0 : Bilin, (∀ v w, A0 v w = A0 w v) →
-  (∀ v, lam * ‖v‖^2 ≤ A0 v v) → (∀ v, A0 v v ≤ Λ * ‖v‖^2) →
-  ∀ T : ℝ, 0 < T → T ≤ 1 → Nonempty (FrozenSolver α T C_S A0)
-
-abbrev TensorField (T : ℝ) := (t : Icc (0 : ℝ) T) →
-  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
-
-def inverseFrame (i : Fin A.cover.chartCount) (x : M) : E →L[ℝ] E :=
-  fderiv ℝ (fun z : E => extChartAt I x ((chart A i).symm z)) (chart A i x)
-
-def localizedValue {T : ℝ} (F : TensorField (M := M) T)
-    (i : Fin A.cover.chartCount) (a b : Fin 3) (p : ℝ × E) : ℝ := by
-  classical
-  exact if ht : p.1 ∈ Icc 0 T then
-    if p.2 ∈ (chart A i).target then
-      let x := (chart A i).symm p.2
-      A.partition i x * F ⟨p.1, ht⟩ x (inverseFrame A i x (e a)) (inverseFrame A i x (e b))
-    else 0
-  else 0
-
-def reconstructionGoal (α T : ℝ) : Prop :=
-  0 < T → ∀ f : Y_M A α T, ∃! F : TensorField (M := M) T,
-    ∀ i a b p, localizedValue A F i a b p = (f.val (i,a,b)) p
-
-abbrev Jet1 := E →L[ℝ] Bilin
-abbrev Jet2 := E →L[ℝ] Jet1
-
-def coordinateQ (B : E →L[ℝ] E →L[ℝ] E)
-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
-    (G : Bilin) (J : Jet1) (H2 : Jet2) : Bilin :=
-  (∑ i : Fin 3, ∑ j : Fin 3,
-    DeTurckPrincipalSecondJet.inverseEntries G i j • H2 (e i) (e j)) +
-    DeTurckPrincipalIdentity.lowerTerm B DB G J
-
-set_option synthInstance.maxHeartbeats 400000 in
-def linearizedJet (B : E →L[ℝ] E →L[ℝ] E)
-    (DB : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
-    (z h : Bilin × Jet1 × Jet2) : Bilin :=
-  fderiv ℝ (fun G : Bilin => coordinateQ B DB G z.2.1 z.2.2) z.1 h.1 +
-    fderiv ℝ (fun J : Jet1 => DeTurckPrincipalIdentity.lowerTerm B DB z.1 J) z.2.1 h.2.1 +
-    (∑ i : Fin 3, ∑ j : Fin 3,
-      DeTurckPrincipalSecondJet.inverseEntries z.1 i j • h.2.2 (e i) (e j))
-end FiniteAtlasSurvey
-
-example : FiniteAtlasSurvey.interpolationGoal := Poincare.ParabolicCutoffCommutator.interpolation
-example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) : FiniteAtlasSurvey.cutoffGraphGoal D := by
-  intro hα hα1 hT hT1
-  obtain ⟨C, hu, _⟩ := Poincare.ParabolicCutoffCommutator.exists_cutoff_operator D.smooth D.compact hα hα1
-  exact ⟨C, hu⟩
-
-example : FiniteAtlasSurvey.commutatorGoal := Poincare.ParabolicCutoffCommutator.commutator
-example {α T : ℝ} (D : FiniteAtlasSurvey.CutoffData α T) (potential : FiniteAtlasSurvey.Scalar α T) :
-    FiniteAtlasSurvey.cutoffIdentityGoal D potential := by
-  intro hα hα1 hT hT1
-  exact Poincare.ParabolicCutoffCommutator.cutoff_commutator_identity D.smooth D.compact hα hα1
-    D.a D.drift potential D.b D.c D.b_eq D.c_eq
+#check ContDiff.lipschitzWith_of_hasCompactSupport
+#check ContinuousLinearMap.add_apply
+#check ContinuousLinearMap.lsmul
+#check ContinuousLinearMap.lsmul_apply
+#check ContinuousLinearMap.opNorm_le_bound
+#check ContinuousLinearMap.opNorm_le_of_unit_norm
+#check ContinuousLinearMap.opNorm_smul_le
+#check ContinuousLinearMap.smulRightL
+#check ContinuousLinearMap.smulRight_apply
+#check ContinuousLinearMap.smul_apply
+#check ContinuousLinearMap.sub_apply
+#check Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+#check Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+#check Fin.sum_univ_succ
+#check Fin.sum_univ_zero
+#check Finset.sum_add_distrib
+#check Finset.sum_le_sum
+#check Finset.sum_mul
+#check Finset.sum_nonneg
+#check OrthonormalBasis.norm_eq_one
+#check ParabolicHolder.ext
+#check ParabolicHolder.holder_le
+#check ParabolicHolder.norm_le
+#check ParabolicHolder.norm_le_of_bounds
+#check ParabolicHolder.norm_mul_le
+#check ParabolicHolderMultiplier.sum_apply
+#check ParabolicSolutionGraph.norm_eq
+#check Real.norm_eq_abs
+#check Real.rpow_add
+#check Real.rpow_le_rpow
+#check Real.rpow_le_rpow_of_exponent_ge
+#check Real.rpow_mul
+#check Real.rpow_nonneg
+#check Real.rpow_one
+#check Real.sq_sqrt
+#check Real.sqrt
+#check Real.sqrt_eq_rpow
+#check Real.sqrt_nonneg
+#check Real.sqrt_pos
+#check EuclideanSpace.basisFun
+#check Poincare.ClosedSmoothModel
```

```json
[
  "$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/SymbolChecks.lean \n",
  "exit: 0\n",
  "ContDiff.lipschitzWith_of_hasCompactSupport.{u_1, u_2, u_3} {n : WithTop ℕ∞} {𝕂 : Type u_1} [RCLike 𝕂] {E' : Type u_2}\n",
  "  [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type u_3} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'}\n",
  "  (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : n ≠ 0) : ∃ C, LipschitzWith C f\n",
  "ContinuousLinearMap.add_apply.{u_1, u_2, u_4, u_6} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]\n",
  "  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]\n",
  "  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] [ContinuousAdd M₂] (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) :\n",
  "  (f + g) x = f x + g x\n",
  "ContinuousLinearMap.lsmul.{u_1, u_2, u_3} (𝕜 : Type u_1) {E : Type u_2} [NontriviallyNormedField 𝕜]\n",
  "  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (R : Type u_3) [SeminormedRing R] [NormedAlgebra 𝕜 R] [Module R E]\n",
  "  [IsBoundedSMul R E] [IsScalarTower 𝕜 R E] : R →L[𝕜] E →L[𝕜] E\n",
  "ContinuousLinearMap.lsmul_apply.{u_1, u_2, u_3} (𝕜 : Type u_1) {E : Type u_2} [NontriviallyNormedField 𝕜]\n",
  "  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (R : Type u_3) [SeminormedRing R] [NormedAlgebra 𝕜 R] [Module R E]\n",
  "  [IsBoundedSMul R E] [IsScalarTower 𝕜 R E] (c : R) (x : E) : ((ContinuousLinearMap.lsmul 𝕜 R) c) x = c • x\n",
  "ContinuousLinearMap.opNorm_le_bound.{u_1, u_2, u_4, u_5} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4} {F : Type u_5}\n",
  "  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]\n",
  "  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →SL[σ₁₂] F) {M : ℝ} (hMp : 0 ≤ M)\n",
  "  (hM : ∀ (x : E), ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M\n",
  "ContinuousLinearMap.opNorm_le_of_unit_norm.{u_1, u_2, u_4, u_5} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}\n",
  "  {F : Type u_5} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]\n",
  "  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]\n",
  "  [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ (x : E), ‖x‖ = 1 → ‖f x‖ ≤ C) : ‖f‖ ≤ C\n",
  "ContinuousLinearMap.opNorm_smul_le.{u_1, u_2, u_4, u_5, u_9} {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_4}\n",
  "  {F : Type u_5} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]\n",
  "  [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]\n",
  "  {𝕜' : Type u_9} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] [SeminormedAddCommGroup 𝕜'] [IsBoundedSMul 𝕜' F] (c : 𝕜')\n",
  "  (f : E →SL[σ₁₂] F) : ‖c • f‖ ≤ ‖c‖ * ‖f‖\n",
  "ContinuousLinearMap.smulRightL.{u_1, u_4, u_7} (𝕜 : Type u_1) (E : Type u_4) (Fₗ : Type u_7) [SeminormedAddCommGroup E]\n",
  "  [SeminormedAddCommGroup Fₗ] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] :\n",
  "  StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ\n",
  "ContinuousLinearMap.smulRight_apply.{u_4, u_6, u_9, u_10} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁]\n",
  "  {M₂ : Type u_6} [TopologicalSpace M₂] [AddCommMonoid M₂] {R : Type u_9} {S : Type u_10} [Semiring R] [Semiring S]\n",
  "  [Module R M₁] [Module R M₂] [Module R S] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]\n",
  "  [ContinuousSMul S M₂] {c : M₁ →L[R] S} {f : M₂} {x : M₁} : (c.smulRight f) x = c x • f\n",
  "ContinuousLinearMap.smul_apply.{u_1, u_2, u_4, u_6, u_9} {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]\n",
  "  {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6} [TopologicalSpace M₂]\n",
  "  [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] {S₂ : Type u_9} [DistribSMul S₂ M₂] [SMulCommClass R₂ S₂ M₂]\n",
  "  [ContinuousConstSMul S₂ M₂] (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x\n",
  "ContinuousLinearMap.sub_apply.{u_1, u_2, u_4, u_5} {R : Type u_1} [Ring R] {R₂ : Type u_2} [Ring R₂] {M : Type u_4}\n",
  "  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type u_5} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R M]\n",
  "  [Module R₂ M₂] {σ₁₂ : R →+* R₂} [IsTopologicalAddGroup M₂] (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x\n",
  "Convex.norm_image_sub_le_of_norm_hasDerivWithin_le.{u_3, u_4} {𝕜 : Type u_3} {G : Type u_4} [RCLike 𝕜]\n",
  "  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜} {C : ℝ}\n",
  "  (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s)\n",
  "  (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖\n",
  "Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le.{u_1, u_3, u_4} {E : Type u_1} [NormedAddCommGroup E]\n",
  "  [NormedSpace ℝ E] {𝕜 : Type u_3} {G : Type u_4} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E]\n",
  "  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → G} {C : ℝ} {s : Set E} {x y : E} {f' : E → E →L[𝕜] G}\n",
  "  (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s)\n",
  "  (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖\n",
  "Fin.sum_univ_succ.{u_2} {M : Type u_2} [AddCommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) : ∑ i, f i = f 0 + ∑ i, f i.succ\n",
  "Fin.sum_univ_zero.{u_2} {M : Type u_2} [AddCommMonoid M] (f : Fin 0 → M) : ∑ i, f i = 0\n",
  "Finset.sum_add_distrib.{u_1, u_4} {ι : Type u_1} {M : Type u_4} {s : Finset ι} [AddCommMonoid M] {f g : ι → M} :\n",
  "  ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x\n",
  "Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f g : ι → N} {s : Finset ι}\n",
  "  [AddLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i\n",
  "Finset.sum_mul.{u_1, u_4} {ι : Type u_1} {R : Type u_4} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R)\n",
  "  (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a\n",
  "Finset.sum_nonneg.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f : ι → N} {s : Finset ι}\n",
  "  [AddLeftMono N] (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i\n",
  "OrthonormalBasis.norm_eq_one.{u_1, u_3, u_4} {ι : Type u_1} {𝕜 : Type u_3} [RCLike 𝕜] {E : Type u_4}\n",
  "  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ‖b i‖ = 1\n",
  "Poincare.ParabolicHolder.ext.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]\n",
  "  [NormedSpace ℝ F] {α T : ℝ} {f g : ParabolicHolder.Y α T F}\n",
  "  (h : ∀ p ∈ ParabolicHolder.cylinder T, ↑(WithLp.fst ↑f) p = ↑(WithLp.fst ↑g) p) : f = g\n",
  "Poincare.ParabolicHolder.holder_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]\n",
  "  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) {p q : ℝ × E}\n",
  "  (hp : p ∈ ParabolicHolder.cylinder T) (hq : q ∈ ParabolicHolder.cylinder T) :\n",
  "  ‖↑(WithLp.fst ↑f) p - ↑(WithLp.fst ↑f) q‖ ≤ ‖f‖ * ParabolicHolder.parabolicDist p q ^ α\n",
  "Poincare.ParabolicHolder.norm_le.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedAddCommGroup F]\n",
  "  [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) (p : ℝ × E) : ‖↑(WithLp.fst ↑f) p‖ ≤ ‖f‖\n",
  "Poincare.ParabolicHolder.norm_le_of_bounds.{u_1, u_2} {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E]\n",
  "  [NormedAddCommGroup F] [NormedSpace ℝ F] {α T : ℝ} (f : ParabolicHolder.Y α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)\n",
  "  (hb : ∀ p ∈ ParabolicHolder.cylinder T, ‖↑(WithLp.fst ↑f) p‖ ≤ M)\n",
  "  (hh : ParabolicHolder.HasHolderBound α (ParabolicHolder.cylinder T) (↑(WithLp.fst ↑f)) K) : ‖f‖ ≤ M + K\n",
  "Poincare.ParabolicHolder.norm_mul_le.{u_1} {E : Type u_1} [NormedAddCommGroup E] {α T : ℝ}\n",
  "  (f g : ParabolicHolder.Y α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖\n",
  "Poincare.ParabolicHolderMultiplier.sum_apply.{u_1} {α T : ℝ} {ι : Type u_1} (s : Finset ι)\n",
  "  (f : ι → ParabolicHolder.Y α T ℝ) (p : ℝ × ClosedSmoothModel 3) :\n",
  "  ↑(WithLp.fst ↑(∑ i ∈ s, f i)) p = ∑ i ∈ s, ↑(WithLp.fst ↑(f i)) p\n",
  "Poincare.ParabolicSolutionGraph.norm_eq.{u_1} {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}\n",
  "  (g : ParabolicSolutionGraph.Graph α T) : ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖\n",
  "Real.norm_eq_abs (r : ℝ) : ‖r‖ = |r|\n",
  "Real.rpow_add {x : ℝ} (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z\n",
  "Real.rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z\n",
  "Real.rpow_le_rpow_of_exponent_ge {x y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z\n",
  "Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z\n",
  "Real.rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y\n",
  "Real.rpow_one (x : ℝ) : x ^ 1 = x\n",
  "Real.sq_sqrt {x : ℝ} (h : 0 ≤ x) : √x ^ 2 = x\n",
  "Real.sqrt (x : ℝ) : ℝ\n",
  "Real.sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / 2)\n",
  "Real.sqrt_nonneg (x : ℝ) : 0 ≤ √x\n",
  "Real.sqrt_pos {x : ℝ} : 0 < √x ↔ 0 < x\n",
  "EuclideanSpace.basisFun.{u_1, u_3} (ι : Type u_1) (𝕜 : Type u_3) [RCLike 𝕜] [Fintype ι] :\n",
  "  OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)\n",
  "Poincare.ClosedSmoothModel (n : ℕ) : Type\n"
]
```

</details>

## Symbol lookup evidence

The following are bounded grep excerpts from the pinned source tree. The Lean symbol-check probe above resolves the exact qualified names, including names generated by attributes.

<details>
<summary>DeclarationGrep.log</summary>

```text
$ rg -n declarations Poincare/Global/ParabolicCutoffCommutator.lean
exit: 0
19:theorem quadratic_remainder
57:theorem finite_difference_derivative
86:theorem derivative_norm_le_sqrt
111:theorem value_time_increment (G : Graph (E := E) α T)
120:theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
133:theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
141:theorem gradient_time_increment (G : Graph (E := E) α T)
156:theorem gradient_space_increment (G : Graph (E := E) α T)
164:theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
172:theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
184:theorem scale_interpolation {a L r R α : ℝ}
203:theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
210:theorem gradient_space_holder (G : Graph (E := E) α T)
225:theorem value_space_holder (G : Graph (E := E) α T)
251:theorem gradient_time_holder (G : Graph (E := E) α T)
266:theorem value_time_holder (G : Graph (E := E) α T)
280:theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
304:theorem gradient_holder (G : Graph (E := E) α T)
316:theorem value_holder (G : Graph (E := E) α T)
328:theorem interpolation_bounds (G : Graph (E := E) α T)
355:theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
363:theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
399:theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
422:theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
429:theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
440:theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
453:theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
481:def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
492:theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
506:local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
510:def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
555:theorem graph_ext_components {G H : Graph (E := E) α T}
563:def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
613:theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
701:theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
749:def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
762:theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
777:def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
782:theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
789:theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
806:theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
818:theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
828:def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
847:theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
865:theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
```

</details>

<details>
<summary>DependencyGrep.log</summary>

```text
$ rg -n -m 2 RCLike [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Data/Real/StarOrdered.lean:18:/-- Although the instance `RCLike.toStarOrderedRing` exists, it is locked behind the
.lake/packages/mathlib/Mathlib/Data/Real/StarOrdered.lean:23:`Mathlib/Analysis/RCLike/Basic.lean`. -/
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Binomial.lean:76:theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Binomial.lean:83:theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
.lake/packages/mathlib/Mathlib/Analysis/ConstantSpeed.lean:9:public import Mathlib.Analysis.RCLike.Basic
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:822:section RCLike
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:823:variable [RCLike 𝕜]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean:30:variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean:76:    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Hermitian.lean:28:open RCLike
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Hermitian.lean:32:variable {𝕜 m n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜]
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:308:theorem RCLike.hasTemperateGrowth_ofReal [RCLike 𝕜] : (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth :=

$ rg -n -m 2 lipschitzWith_of_hasCompactSupport [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean:227:      ContDiff.lipschitzWith_of_hasCompactSupport g_comp g_smooth (by simp)
.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean:156:theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' → F'}

$ rg -n -m 2 add_apply [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:151:  | @insert a s ha ih => simp only [Finset.sum_insert ha, add_apply, ih]
Poincare/Global/ParabolicHolderSpace.lean:208:@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean:51:    rw [Pi.add_apply, hf.finite _ ((le_max_left n m).trans hN),
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Balance.lean:40:  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:535:      prod_union hd, add_apply]
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean:289:@[simp] lemma add_apply {f g : E →SWOT[σ] F} (x : E) : (f + g) x = f x + g x := rfl
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:186:    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:456:  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:466:  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
.lake/packages/mathlib/Mathlib/Analysis/Seminorm.lean:182:theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:328:theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:1196:  mkCLMtoNormedSpace toBoundedContinuousFunction (by intro f g; ext; exact add_apply)

$ rg -n -m 2 lsmul [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:597:  (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strict.lean:252:  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Strict.lean:276:    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:23:For many applications we can take `L = ContinuousLinearMap.lsmul ℝ ℝ` or
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:72:* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:274:  hs.linear_image <| LinearMap.lsmul _ _ c
.lake/packages/mathlib/Mathlib/Analysis/Convex/Star.lean:281:  hs.linear_preimage (LinearMap.lsmul _ _ c)
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:270:  (ContinuousLinearMap.lsmul ℝ 𝕜).bilinear_hasTemperateGrowth hf hg
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:741:    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean:274:  integral_bilinear_deriv_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜)
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean:319:  integral_bilinear_lineDerivOp_right_eq_neg_left f g (ContinuousLinearMap.lsmul ℝ 𝕜) v
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:47:open ContinuousLinearMap (lsmul)

$ rg -n -m 2 lsmul_apply [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:477:  simp only [lsmul_apply, smul_eq_mul]
.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean:774:  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:195:theorem lsmul_apply (c : R) (x : E) : lsmul 𝕜 R c x = c • x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:360:  simp only [lsmul_apply, smul_eq_mul, integral_mul_const, w_integral E Dpos, Bx,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:378:  simp only [lsmul_apply, smul_eq_mul, Bx, mul_zero, integral_const]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean:59:  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean:116:  simp only [convolution_eq_swap, lsmul_apply]

$ rg -n -m 2 opNorm_le_bound [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Analytic/ChangeOrigin.lean:237:  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:315:  ContinuousMultilinearMap.opNorm_le_bound (by positivity) (compAlongComposition_bound _ _ _)
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:603:  refine (toCLM M).opNorm_le_bound (by simp) fun v ↦ ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:666:      refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:36:    (opNorm_le_bound _ (norm_nonneg _) fun b => by simpa only [mul_comm] using norm_mul_le b a) ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:39:  refine opNorm_le_bound _ (norm_nonneg _) fun b => ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Matrix.lean:236:  · refine T.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Unitization.lean:248:      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Basic.lean:55:  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Extend.lean:120:  refine opNorm_le_bound _ ?_ (isClosed_property h_dense (isClosed_le ?_ (by fun_prop)) fun x ↦ ?_)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Extend.lean:231:  (f.extendOfNorm e).opNorm_le_bound hC (norm_extendOfNorm_apply_le h_dense C h_norm)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Completeness.lean:80:    (squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_bound _ (hb₀ n) (this n)) hb_lim)

$ rg -n -m 2 opNorm_le_of_unit_norm [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:310:theorem opNorm_le_of_unit_norm [NormedAlgebra ℝ 𝕜] {f : E →SL[σ₁₂] F} {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/NNNorm.lean:63:  opNorm_le_of_unit_norm C.coe_nonneg fun x hx => hf x <| by rwa [← NNReal.coe_eq_one]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean:418:  refine opNorm_le_of_unit_norm hC fun x hx ↦ ?_

$ rg -n -m 2 opNorm_smul_le [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:439:theorem opNorm_smul_le (c : 𝕜') (f : ContinuousMultilinearMap 𝕜 E G) : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:451:  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f ↦ f.opNorm_smul_le c
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean:280:  ⟨fun c f ↦ f.1.opNorm_smul_le c⟩
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:334:theorem opNorm_smul_le {𝕜' : Type*} [DistribSMul 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean:353:  .ofSMulLE norm opNorm_zero opNorm_add_le opNorm_smul_le
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:813:  norm_smul_le r M := by simpa only [norm_def, map_smul] using (toCLM M).opNorm_smul_le r

$ rg -n -m 2 smulRightL [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean:872:          exact norm_iteratedFDeriv_le_of_bilinear_of_le_one (smulRightL ℝ G F)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean:397:  (smulRightL 𝕜 E F).isBoundedBilinearMap
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean:196:theorem norm_smulRightL (c : StrongDual 𝕜 E) [Nontrivial Fₗ] : ‖smulRightL 𝕜 E Fₗ c‖ = ‖c‖ :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean:199:lemma norm_smulRightL_le : ‖smulRightL 𝕜 E Fₗ‖ ≤ 1 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean:68:  set T := apply' _ (.id 𝕜) z ∘L f.toContinuousAlgHom.toContinuousLinearMap ∘L smulRightL 𝕜 _ _ v
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean:83:    smulRightL 𝕜 _ _ d
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/CompleteCodomain.lean:40:  let g : ℕ → (E →L[𝕜] F) := fun n ↦ ContinuousLinearMap.smulRightL 𝕜 E F φ (f n)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/CompleteCodomain.lean:41:  have : CauchySeq g := (ContinuousLinearMap.smulRightL 𝕜 E F φ).lipschitz.cauchySeq_comp hf
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:805:def smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 →L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:816:    smulRightL 𝕜 E G f z = f.smulRight z := rfl
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:413:`smulRightL (c : StrongDual 𝕜 E) (f : F) (x : E) = c x • f`.
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:418:def smulRightL : StrongDual 𝕜 E →L[𝕜] Fₗ →L[𝕜] E →L[𝕜] Fₗ :=

$ rg -n -m 2 smulRight_apply [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:176:  simp_rw [fourierSMulRight, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:799:    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean:65:      ContinuousLinearMap.ext_iff, not_forall, smulRight_apply, zero_apply,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:166:  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', _root_.id, one_smul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Mul.lean:167:  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean:423:        simp only [add_smul, coe_smulRightₗ, add_apply, smulRight_apply, LinearMap.add_apply]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exponential.lean:270:      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, zero_smul]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exponential.lean:281:    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:186:    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/UnitPartition.lean:365:    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean:792:    rw [smulRight_apply, nnnorm_smul]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Bases.lean:158:  simp [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

$ rg -n -m 2 smul_apply [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:214:@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Binomial.lean:189:    simp only [FormalMultilinearSeries.smul_apply, ContinuousMultilinearMap.smul_apply,
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:509:    simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
.lake/packages/mathlib/Mathlib/Analysis/Analytic/ConvergenceRadius.lean:307:  simp only [radius, smul_apply]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean:136:  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:202:@[simp] theorem smul_apply [SMul B A] (r : B) (M : CStarMatrix m n A) (i : m) (j : n) :
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:495:      WithCStarModule.equiv_symm_pi_apply, ContinuousLinearMap.smul_apply,
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:102:    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:123:      Unitization.fst_mul, Unitization.fst_star, Algebra.algebraMap_eq_smul_one, smul_apply,
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Multiplier.lean:147:          simp only [ContinuousLinearMap.smul_apply, mul_smul_comm, smul_mul_assoc, central] }
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Multiplier.lean:187:      simp only [← Nat.smul_one_eq_cast, smul_apply, one_apply, mul_smul_comm, smul_mul_assoc]⟩
.lake/packages/mathlib/Mathlib/Analysis/Complex/Conformal.lean:77:    simp only [LinearMap.smul_apply]

$ rg -n -m 2 sub_apply [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:211:@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
Poincare/Global/ParabolicHolderMultiplier.lean:69:  simp only [ContinuousLinearMap.sub_apply] at h
.lake/packages/mathlib/Mathlib/Data/Real/Basic.lean:544:  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:334:    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:339:    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean:246:    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/IsolatedZeros.lean:254:    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Balance.lean:43:  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean:200:      ← smul_sub, ← Pi.sub_apply]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Exp.lean:128:  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
.lake/packages/mathlib/Mathlib/Analysis/Fourier/FourierTransform.lean:117:    ← sub_eq_add_neg, ← LinearMap.sub_apply, map_sub, neg_sub]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/BoundedContinuousFunctionChar.lean:90:  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]

$ rg -n -m 2 norm_image_sub_le_of_norm_hasDerivWithin_le [pinned source roots]
exit: 0
Poincare/Global/ParabolicSolutionGraph.lean:167:  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
Poincare/Global/ParabolicSolutionGraph.lean:239:    apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:249:    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:312:    (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:692:theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:712:  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs

$ rg -n -m 2 norm_image_sub_le_of_norm_hasFDerivWithin_le [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:423:theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean:450:  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in
.lake/packages/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean:155:      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean:209:      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Partial.lean:48:  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'

$ rg -n -m 2 sum_univ_succ [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:606:        simp_rw [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean:655:        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Fin.lean:33:  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
.lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:77:  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
.lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean:160:  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:288:  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:295:  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bernstein.lean:162:  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:113:  · simpa [Fin.sum_univ_succ] using h
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:114:  · simp [hw', Fin.sum_univ_succ]
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean:405:      (by ext; simp [Fin.sum_univ_succ, Finset.mul_sum, mul_assoc, add_comm])
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:271:      simpa [Fin.sum_univ_succ] using

$ rg -n -m 2 sum_univ_zero [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Reflection.lean:203:  | 0 => return ⟨q((0 : $α)), q(Fin.sum_univ_zero $f)⟩

$ rg -n -m 2 sum_add_distrib [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Intervals.lean:181:    _ = ∑ i ∈ range n, (i + (n - 1 - i)) := sum_add_distrib.symm
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Expect.lean:153:  simp [expect, sum_add_distrib]
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Inner.lean:66:  simp [wInner, inner_add_left, smul_add, sum_add_distrib]
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Inner.lean:70:  simp [wInner, inner_add_right, smul_add, sum_add_distrib]
.lake/packages/mathlib/Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean:105:  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]
.lake/packages/mathlib/Mathlib/Analysis/Convex/StdSimplex.lean:46:    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
.lake/packages/mathlib/Mathlib/Analysis/Convex/Birkhoff.lean:140:  simp only [Pi.add_apply, add_smul, sum_add_distrib, hw', ite_smul, zero_smul,
.lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean:107:    simp only [← mul_sum, sum_add_distrib, mul_one, *]
.lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean:108:  simp only [Finset.centerMass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]
.lake/packages/mathlib/Mathlib/Analysis/Convex/Side.lean:872:    simp [w₃, lineMap_apply, Finset.sum_add_distrib, ← Finset.mul_sum, hw₁, hw₂]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Constructions.lean:236:  inner_add_right {x y z} := by simp [sum_add_distrib]
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:461:      rw [sum_add_distrib, sum_div, sum_div]

$ rg -n -m 2 sum_le_sum [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:214:      apply Finset.sum_le_sum
Poincare/Global/ParabolicHolderMultiplier.lean:217:      apply Finset.sum_le_sum
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:149:  replace hf := Finset.sum_le_sum hf
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:334:        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean:180:    apply Finset.sum_le_sum (fun i ih ↦ ht_max.2 i ih)
.lake/packages/mathlib/Mathlib/Analysis/PSeries.lean:65:    convert sum_le_sum this
.lake/packages/mathlib/Mathlib/Analysis/PSeries.lean:99:    convert sum_le_sum this
.lake/packages/mathlib/Mathlib/Analysis/Hofer.lean:66:            (sum_le_sum fun i i_in => (IH i <| Nat.lt_succ_iff.mp <| Finset.mem_range.mp i_in).1)
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:150:        apply Finset.sum_le_sum
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean:340:  refine Finset.sum_le_sum (fun i hi => ?_)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1439:    _ ≤ ∑ i ∈ s, C i * ‖B i x‖ := Finset.sum_le_sum (fun j hj ↦ hx j hj)
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1441:        refine Finset.sum_le_sum ?_

$ rg -n -m 2 sum_mul [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean:53:lemma sum_mul (s : Finset ι) (f : ι → R) (a : R) :
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean:61:  simp_rw [sum_mul, ← mul_sum]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Field.lean:27:    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Expect.lean:330:    (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:511:      rw [tsum_fintype, ← Finset.sum_mul]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:618:theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:619:    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]
.lake/packages/mathlib/Mathlib/Analysis/Hofer.lean:68:            rw [Finset.sum_mul]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:342:      simp_rw [← Finset.sum_mul, ← NNReal.finset_sup_mul]
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Inner.lean:113:    ⟪const _ a, f⟫_[𝕜, w] = (∑ i, w i • f i) * conj a := by simp [wInner, const_apply, sum_mul]
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Inner.lean:119:    ⟪const _ a, f⟫_[𝕜] = (∑ i, f i) * conj a := by simp [wInner_one_eq_sum, sum_mul]
.lake/packages/mathlib/Mathlib/Analysis/Polynomial/MahlerMeasure.lean:406:      rw [← Finset.sum_mul]

$ rg -n -m 2 sum_nonneg [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:489:    (sum_nonneg fun _ _ ↦ by positivity) _
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Constructions.lean:474:    ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ (C_pos i).le),
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Inner.lean:154:  sum_nonneg fun _ _ ↦ smul_nonneg (hw _) <| mul_nonneg (hg _) (star_nonneg_iff.2 (hf _))
.lake/packages/mathlib/Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean:47:    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/Convex/StdSimplex.lean:314:    exact Finset.sum_nonneg (by aesop)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Birkhoff.lean:67:    · exact sum_le_sum_of_subset_of_nonneg (by simp) fun _ _ _ => sum_nonneg fun j _ => hM.1 _ _
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:137:    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:768:    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add_le,
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1446:      congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean:1465:        exact Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
.lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean:208:      refine convex_iff_div.1 hs zi (ht hs₀ ?_ ?_) ?_ (sum_nonneg hs₀) hpos
.lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean:209:      · exact lt_of_le_of_ne (sum_nonneg hs₀) (Ne.symm hsum_t)

$ rg -n -m 2 norm_eq_one [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:157:    b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j)
Poincare/Global/ParabolicHolderMultiplier.lean:176:      b i j * entry G.ddu (e i) (e j) (OrthonormalBasis.norm_eq_one e i) (OrthonormalBasis.norm_eq_one e j) := by
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Finite.lean:30:protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Finite.lean:34:    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Positive.lean:159:    inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:454:lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:455:    ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:64:lemma Orthonormal.norm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:70:  simp [h.norm_eq_one]

$ rg -n -m 2 ext [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:41:  · have ht : p.1 ≠ q.1 := fun ht => h (Prod.ext ht hx)
Poincare/Global/ParabolicHolderSpace.lean:217:@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
Poincare/Global/ParabolicHolderMultiplier.lean:177:  apply ParabolicHolder.ext
.lake/packages/mathlib/Mathlib/Data/Real/Embedding.lean:111:  ext a
.lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:75:  ext; simp [mlconvolution]
.lake/packages/mathlib/Mathlib/Analysis/LConvolution.lean:81:  ext; simp [mlconvolution]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Intervals.lean:103:  apply Finset.ext
.lake/packages/mathlib/Mathlib/Data/Fin/Embedding.lean:153:  ext y
.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:373:  ext
.lake/packages/mathlib/Mathlib/Data/Real/Archimedean.lean:379:  ext
.lake/packages/mathlib/Mathlib/Data/Fin/Basic.lean:371:  Fin.ext <| val_cast_of_lt a.isLt
.lake/packages/mathlib/Mathlib/Data/Fin/Basic.lean:374:@[simp high] lemma natCast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp

$ rg -n -m 2 holder_le [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:134:theorem holder_le (f : Y (E := E) α T F) {p q : ℝ × E}
Poincare/Global/ParabolicHolderSpace.lean:154:    HasHolderBound α (cylinder T) f ‖f‖ := fun _ hp _ hq => holder_le f hp hq
Poincare/Global/ParabolicHolderMultiplier.lean:34:  have h := ParabolicHolder.holder_le G.ddu
Poincare/Global/ParabolicHolderMultiplier.lean:166:      exact ParabolicHolder.holder_le y hp hq⟩
Poincare/Global/ParabolicSolutionGraph.lean:128:  (ParabolicHolder.holder_le g.u hp hq).trans
Poincare/Global/ParabolicSolutionGraph.lean:139:  (ParabolicHolder.holder_le g.ut hp hq).trans

$ rg -n -m 2 norm_le [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:129:theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
Poincare/Global/ParabolicHolderSpace.lean:151:    ∃ M : ℝ, ∀ p ∈ cylinder T, ‖f p‖ ≤ M := ⟨‖f‖, fun p _ => norm_le f p⟩
Poincare/Global/ParabolicHolderMultiplier.lean:162:    ⟨‖y‖, fun p _ => by dsimp only; rw [← he p]; exact ParabolicHolder.norm_le y p⟩
Poincare/Global/ParabolicSolutionGraph.lean:123:  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)
Poincare/Global/ParabolicSolutionGraph.lean:134:  (ParabolicHolder.norm_le g.ut p).trans (norm_ut_le g)
.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean:90:  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
.lake/packages/mathlib/Mathlib/Analysis/ODE/PicardLindelof.lean:294:    exact hf.norm_le _ ht _ <| α.mem_closedBall hf.mul_max_le
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Extreme.lean:32:  refine ⟨fun he ↦ ⟨⟨he.nonneg, he.norm_le⟩,
.lake/packages/mathlib/Mathlib/Analysis/Fourier/PoissonSummation.lean:147:  rw [norm_norm, ContinuousMap.norm_le _ (by positivity)]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/PoissonSummation.lean:167:  rw [norm_norm, Function.comp_apply, norm_norm, ContinuousMap.norm_le _ (norm_nonneg _)]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean:72:      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using realPart.norm_le x)
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean:74:      (by simpa [norm_smul, inv_mul_le_one₀ (norm_pos_iff.2 hx)] using imaginaryPart.norm_le x)

$ rg -n -m 2 norm_le_of_bounds [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:290:theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
Poincare/Global/ParabolicHolderSpace.lean:394:    apply norm_le_of_bounds (f * g)
Poincare/Global/ParabolicHolderMultiplier.lean:99:  apply norm_le_of_bounds _ (supNorm_nonneg H) (holderSeminorm_nonneg H)
Poincare/Global/ParabolicHolderMultiplier.lean:138:  have hn := norm_le_of_bounds (b * h)

$ rg -n -m 2 norm_mul_le [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:390:theorem norm_mul_le (f g : Y (E := E) α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
Poincare/Global/ParabolicHolderSpace.lean:409:  ⟨mul_apply f g, norm_mul_le f g⟩
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:672:      apply norm_mul_le _ _ |>.trans
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean:758:  norm_mul_le _ _ := by simpa only [norm_def', map_mul] using norm_mul_le _ _
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:365:    norm_mul_le := linfty_opNorm_mul }
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:655:    norm_mul_le := frobenius_norm_mul
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:36:    (opNorm_le_bound _ (norm_nonneg _) fun b => by simpa only [mul_comm] using norm_mul_le b a) ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitization.lean:105:  refine (norm_mul_le _ _).trans ?_
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/lpSpace.lean:33:  norm_mul_le := norm_mul_le
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean:414:      apply (norm_mul_le _ _).trans
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt.lean:230:  norm_mul_le
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt.lean:236:      · apply norm_mul_le

$ rg -n -m 2 sum_apply [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:146:theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Y («E» := E) α T ℝ)
Poincare/Global/ParabolicHolderMultiplier.lean:159:    simp only [y, sum_apply, mul_apply, entry_apply]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/CPolynomialDef.lean:401:    simp_rw [changeOriginSeries, ContinuousMultilinearMap.sum_apply]; apply hasSum_fintype
.lake/packages/mathlib/Mathlib/Analysis/Analytic/ChangeOrigin.lean:281:      · simp only [changeOriginSeries, ContinuousMultilinearMap.sum_apply]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Pi.lean:49:@[to_additive (attr := push ←) /-- An 'unapplied' analogue of `Finset.sum_apply`. -/]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/IteratedFDeriv.lean:125:    ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousMultilinearMap.sum_apply,
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:259:theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean:278:  simpa only [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply, exists_prop]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:274:    ContinuousMultilinearMap.compAlongComposition_apply, ContinuousMultilinearMap.sum_apply]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Composition.lean:811:      ContinuousMultilinearMap.sum_apply]
.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Lemmas.lean:38:  /-- See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Inverse.lean:137:        ContinuousMultilinearMap.sum_apply]

$ rg -n -m 2 norm_eq [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:98:  rw [ParabolicHolder.norm_eq H]
Poincare/Global/ParabolicHolderMultiplier.lean:142:  rw [ParabolicHolder.norm_eq h]
Poincare/Global/ParabolicSolutionGraph.lean:83:theorem norm_eq (g : Graph (E := E) α T) :
Poincare/Global/ParabolicSolutionGraph.lean:90:  rw [norm_eq]
Poincare/Global/ParabolicHolderSpace.lean:286:theorem norm_eq (f : Y (E := E) α T F) :
Poincare/Global/ParabolicHolderSpace.lean:403:  rw [norm_eq f, norm_eq g]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean:195:    div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')), one_mul, norm_div, NNReal.norm_eq]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/OfScalars.lean:213:    simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:269:  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, PiLp.inner_apply, RCLike.inner_apply,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:314:  · simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, neg_mul, neg_inj, mul_eq_mul_left_iff]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean:641:theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/AddCircle.lean:16:`‖(x : AddCircle 1)‖ = |x - round x|` for any `x : ℝ` (see `UnitAddCircle.norm_eq`).

$ rg -n -m 2 norm_eq_abs [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:829:      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/Basic.lean:860:    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
.lake/packages/mathlib/Mathlib/Analysis/Fourier/Inversion.lean:70:    simp only [norm_eq_abs, abs_exp, exp_le_one_iff, Left.neg_nonpos_iff]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/Inversion.lean:154:    simp only [one_div, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, neg_inj,
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean:121:    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/Normed.lean:137:    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean:146:    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans x_one)]
.lake/packages/mathlib/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:395:    Real.norm_eq_abs, abs_of_nonneg pi_nonneg, norm_I, mul_one, smulRightL_apply, ge_iff_le]
.lake/packages/mathlib/Mathlib/Analysis/Polynomial/Basic.lean:380:  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:721:    rw [zsmul_eq_mul, norm_mul, ← ofReal_intCast, norm_ofReal, Int.norm_eq_abs]
.lake/packages/mathlib/Mathlib/Analysis/RCLike/Basic.lean:764:  norm_sq_eq_def_ax z := by simp only [sq, Real.norm_eq_abs, ← abs_mul, abs_mul_self z, add_zero,
.lake/packages/mathlib/Mathlib/Analysis/SumOverResidueClass.lean:56:  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this

$ rg -n -m 2 rpow_add [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:108:      rw [← rpow_add hx, hab']; congr 1; ring
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:396:    add_halves (1 : ℝ), Gamma_add_one (div_ne_zero hs two_ne_zero), rpow_add two_pos, rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:207:theorem rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:210:theorem rpow_add' (hx : 0 ≤ x) (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean:84:  rw [mul_sub, ← rpow_neg_one, ← rpow_add' (by grind) (by grind)]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean:140:  simpa using Eq.symm <| Real.rpow_add' hx (by aesop : (p - 1) + 1 ≠ 0)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:90:theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:91:  NNReal.eq <| Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:120:  exact mod_cast z.rpow_add' <| ne_of_gt (add_pos hx hy)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:459:lemma rpow_add {a : A} {x y : ℝ} (ha : IsUnit a) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:419:    nth_rw 1 [← add_sub_cancel 1 r, Real.rpow_add hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:127:    rw [← Real.rpow_natCast y (Module.finrank ℝ E - 1), ← Real.rpow_add hy]

$ rg -n -m 2 rpow_le_rpow [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:53:        (Real.rpow_le_rpow p.property.1.1 p.property.1.2 (by linarith))
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Monotone.lean:75:    convert rpow_le_rpow _ hz (le_of_lt ha) using 1
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:546:theorem rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:553:  fun _ ha _ _ hab => rpow_le_rpow ha hab hr
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:265:@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:266:  Real.rpow_le_rpow x.2 h₁ h₂
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:381:    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Multiplier.lean:536:    convert NNReal.rpow_le_rpow this two_pos.le
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean:146:lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:634:    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:767:  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
.lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/SmoothingSeminorm.lean:210:      · simpa [hnm1, pow_zero] using rpow_le_rpow (apply_nonneg μ _) hμ1 (one_div_cast_nonneg _)

$ rg -n -m 2 rpow_le_rpow_of_exponent_ge [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/SpecificLimits/FloorPow.lean:246:        exact Real.rpow_le_rpow_of_exponent_ge A C.le (Nat.sub_one_lt_floor _).le
.lake/packages/mathlib/Mathlib/Analysis/Complex/Hadamard.lean:176:      apply Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 0) (le_of_lt hM0_one) _
.lake/packages/mathlib/Mathlib/Analysis/Complex/Hadamard.lean:187:        neg_re, Real.rpow_le_rpow_of_exponent_ge (sSupNormIm_eps_pos f hε 1)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:645:theorem rpow_le_rpow_of_exponent_ge (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:691:  convert rpow_le_rpow_of_exponent_ge hx1 hx2 hz
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:342:theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:344:  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz
.lake/packages/mathlib/Mathlib/Analysis/MellinTransform.lean:365:        le_add_of_nonneg_of_le (rpow_pos_of_pos ht _).le (rpow_le_rpow_of_exponent_ge ht h.le ?_)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:245:      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hq.le hpq'

$ rg -n -m 2 rpow_mul [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:38:    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1]
.lake/packages/mathlib/Mathlib/Analysis/Analytic/RadiusLiminf.lean:45:        NNReal.rpow_one r, ← mul_inv_cancel₀ this.ne', NNReal.rpow_mul, ← NNReal.mul_rpow, ←
.lake/packages/mathlib/Mathlib/Analysis/Fourier/Inversion.lean:120:      rw [← rpow_natCast, ← rpow_natCast, ← rpow_sub pi_pos, ← rpow_mul pi_nonneg,
.lake/packages/mathlib/Mathlib/Analysis/Fourier/Inversion.lean:133:      rw [mul_rpow (by positivity) (by positivity), ← rpow_mul pi_nonneg,
.lake/packages/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean:324:        rw [← ENNReal.rpow_mul, hp.conjugate_eq]
.lake/packages/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean:449:    ← ENNReal.coe_rpow_of_nonneg _ h0p.le, eLpNormLESNormFDerivOneConst, ← NNReal.rpow_mul,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:76:    rw [mul_rpow (exp_pos _).le ((rpow_nonneg hx.le) _), ← exp_mul, ← rpow_mul hx.le]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Spectrum.lean:126:  rw [Function.comp_apply, ha.nnnorm_pow_two_pow, ENNReal.coe_pow, ← rpow_natCast, ← rpow_mul]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Spectrum.lean:143:    rw [Function.comp_apply, ← rpow_natCast, ← rpow_mul, mul_comm, rpow_mul, rpow_natCast, ←
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:640:  rw [← NNReal.rpow_le_rpow_iff one_half_pos, ← NNReal.rpow_mul,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Monotone.lean:70:  rw [← div_self (ne_of_lt ha).symm, div_eq_mul_one_div a a, rpow_mul y_pos.le, rpow_mul x_pos.le,
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:159:    rw [div_eq_mul_inv, rpow_mul (hz _ ih)]

$ rg -n -m 2 rpow_nonneg [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:140:    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
Poincare/Global/ParabolicHolderSpace.lean:348:    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
Poincare/Global/ParabolicHolderMultiplier.lean:49:  · exact mul_nonneg (Real.rpow_nonneg hT.le _) (norm_nonneg _)
Poincare/Global/ParabolicHolderMultiplier.lean:54:        (Real.rpow_nonneg p.property.1.1 _) (norm_nonneg G)
Poincare/Global/ParabolicSolutionGraph.lean:130:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
Poincare/Global/ParabolicSolutionGraph.lean:141:      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
.lake/packages/mathlib/Mathlib/Analysis/SumIntegralExpDecay.lean:36:        exact mul_nonneg (rpow_nonneg hx.le _) (exp_nonneg _)
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:157:  · rw [← finsetProd_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:397:      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one
.lake/packages/mathlib/Mathlib/Analysis/Distribution/TemperateGrowth.lean:530:      rw [Real.norm_of_nonneg (Real.rpow_nonneg (h_one_add x).le _)]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:396:        ← ENNReal.ofReal_rpow_of_nonneg] <;> simp [Real.rpow_nonneg, add_nonneg]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:477:    exact Real.rpow_nonneg (tsum_nonneg fun i ↦ by positivity) _

$ rg -n -m 2 rpow_one [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Analysis/Analytic/RadiusLiminf.lean:45:        NNReal.rpow_one r, ← mul_inv_cancel₀ this.ne', NNReal.rpow_mul, ← NNReal.mul_rpow, ←
.lake/packages/mathlib/Mathlib/Analysis/PSeries.lean:283:      nth_rw 1 [← rpow_one 2]
.lake/packages/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean:451:    inv_mul_cancel₀ h0p.ne', NNReal.rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:641:    mul_div_cancel₀ (1 : ℝ) two_ne_zero, NNReal.rpow_one, NNReal.mul_rpow]
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:175:      rw [← rpow_sum_of_nonneg _ hw, hw', rpow_one]
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalities.lean:497:  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.ne_zero, rpow_one,
.lake/packages/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean:55:  · simpa only [rpow_one] using concaveOn_id convex_univ
.lake/packages/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Pow.lean:87:  · simpa only [rpow_one] using concaveOn_id (convex_Ici _)
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/TrivSqZeroExt.lean:214:  simp only [WithLp.toLp_fst, ENNReal.toReal_one, Real.rpow_one, WithLp.toLp_snd, ne_eq,
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:297:  nth_rw 2 [← rpow_one (a : A)]
.lake/packages/mathlib/Mathlib/Analysis/Complex/PhragmenLindelof.lean:792:        _ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
.lake/packages/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean:82:  rw [← rpow_le_rpow_iff _ _ this, ← rpow_mul, one_div_mul_cancel (ne_of_gt this), rpow_one]

$ rg -n -m 2 sq_sqrt [pinned source roots]
exit: 0
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:49:@[simp] lemma sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x := sqrt.symm_apply_apply _
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:53:@[simp] lemma mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean:132:    inv_pow', CFC.sq_sqrt A]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:549:  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Multiplier.lean:537:    · simp only [NNReal.rpow_two, div_pow, sq_sqrt]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Multiplier.lean:539:    · simp only [NNReal.rpow_two, sq_sqrt]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:222:                          rw [Real.sq_sqrt]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:241:                simp only [norm_eq_sqrt_norm_inner_self (A := A), norm_nonneg, Real.sq_sqrt]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/GelfandMazur.lean:395:    rw [← sq_le_sq₀ M.sqrt_nonneg (norm_nonneg _), Real.sq_sqrt (norm_nonneg _), ← norm_pow,
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:385:    Real.sq_sqrt (x := 1 - x ^ 2) (by nlinarith [abs_le.mp hx])]
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/GelfandNaimarkSegal.lean:97:  simp [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt this.1, conj_eq_iff_re.mp this.star_eq]
.lake/packages/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean:49:    Real.sq_sqrt (by positivity)]

$ rg -n -m 2 sqrt [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:30:  ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|
Poincare/Global/ParabolicHolderMultiplier.lean:37:  have he : (Real.sqrt t) ^ α = t ^ (α / 2) := by
.lake/packages/mathlib/Mathlib/Data/Real/StarOrdered.lean:33:    refine ⟨sqrt d, ?_⟩
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:16:* `NNReal.sqrt` to be the square root of a nonnegative real number.
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:17:* `Real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.
.lake/packages/mathlib/Mathlib/Analysis/Analytic/RadiusLiminf.lean:14:$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
.lake/packages/mathlib/Mathlib/Analysis/Analytic/RadiusLiminf.lean:34:$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. The actual statement uses `ℝ≥0` and some
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:16:It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:26:**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean:20:This allows us to use more general results from C⋆-algebras, like `CFC.sqrt`.
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean:130:lemma inv_sqrt : (CFC.sqrt A)⁻¹ = CFC.sqrt A⁻¹ := by
.lake/packages/mathlib/Mathlib/Analysis/Matrix/PosDef.lean:110:/-- A positive semi-definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/

$ rg -n -m 2 sqrt_eq_rpow [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderMultiplier.lean:38:    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:549:  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Normed.lean:589:  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Stirling.lean:71:  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Monotone.lean:82:  simp_rw [sqrt_eq_rpow]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:988:theorem sqrt_eq_rpow (x : ℝ) : √x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:997:  rw [sqrt_eq_rpow, ← rpow_mul hx]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:185:theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:188:  exact Real.sqrt_eq_rpow x.1
.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean:804:  rw [prod_norm_eq_of_nat 2 (by norm_cast) _, Real.sqrt_eq_rpow]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:257:  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:261:  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg

$ rg -n -m 2 sqrt_nonneg [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:33:  exact add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
Poincare/Global/ParabolicHolderSpace.lean:45:      (Real.sqrt_nonneg _)
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:144:@[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:154:  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))
.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean:131:  rw [eq_comm, CFC.sqrt_eq_iff _ _ hA.inv.nonneg (CFC.sqrt_nonneg A).posSemidef.inv.nonneg, ← sq,
.lake/packages/mathlib/Mathlib/Analysis/Complex/Norm.lean:35:  Real.sqrt_nonneg _
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:321:      IsSelfAdjoint.of_nonneg (sqrt_nonneg a), IsSelfAdjoint.of_nonneg rpow_nonneg,
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:336:      _ ≤ b := conjugate_le_conjugate_of_nonneg h (sqrt_nonneg _) |>.trans <| by
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean:261:        using fun x _ ↦ Real.sqrt_nonneg x
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Unitary/Span.lean:62:  simp [IsSelfAdjoint.star_eq, ← sub_eq_add_neg, (CFC.sqrt_nonneg (1 - a ^ 2 : A)).isSelfAdjoint]
.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/GelfandMazur.lean:395:    rw [← sq_le_sq₀ M.sqrt_nonneg (norm_nonneg _), Real.sq_sqrt (norm_nonneg _), ← norm_pow,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:990:  · rw [← mul_self_inj_of_nonneg (sqrt_nonneg _) (rpow_nonneg h _), mul_self_sqrt h, ← sq,

$ rg -n -m 2 sqrt_pos [pinned source roots]
exit: 0
Poincare/Global/ParabolicHolderSpace.lean:43:      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.2 ht)))
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:97:@[simp] theorem sqrt_pos : 0 < sqrt x ↔ 0 < x := by simp [pos_iff_ne_zero]
.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:99:alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:39:  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean:55:  · have : ↑2 * √x ^ (2 - 1) ≠ 0 := by simp [(sqrt_pos.2 hx).ne', @two_ne_zero ℝ]
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/PolarCoord.lean:51:    simp only [prodMk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/InverseDeriv.lean:38:  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
.lake/packages/mathlib/Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean:155:      (mul_pos four_pos (pow_pos (sqrt_pos.mpr (zero_lt_one.trans hx)) 3))
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean:161:  refine ⟨Metric.ball 0 √r, Metric.ball_mem_nhds 0 (Real.sqrt_pos.mpr hr), ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean:162:  refine ⟨(s.sup p).ball 0 √r, p.basisSets_mem s (Real.sqrt_pos.mpr hr), ?_⟩
.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/Module/Defs.lean:185:  simp only [norm_eq_sqrt_norm_inner_self (A := A), Real.sqrt_pos, norm_pos_iff]
.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean:206:      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
```

</details>

<details>
<summary>FinSumGrep.log</summary>

```text
.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/Reflection.lean:203:  | 0 => return ⟨q((0 : $α)), q(Fin.sum_univ_zero $f)⟩
```

</details>

## Final proof diff from the recorded base

```diff
diff --git a/Poincare/Global/ParabolicCutoffCommutator.lean b/Poincare/Global/ParabolicCutoffCommutator.lean
new file mode 100644
index 00000000..8c2c5d02
--- /dev/null
+++ b/Poincare/Global/ParabolicCutoffCommutator.lean
@@ -0,0 +1,893 @@
+import Poincare.Global.ParabolicHolderMultiplier
+import Poincare.Global.DuhamelSolutionOperatorBound
+import Mathlib.Analysis.Calculus.MeanValue
+import Mathlib.Analysis.Calculus.ContDiff.RCLike
+
+noncomputable section
+
+set_option maxHeartbeats 800000
+set_option synthInstance.maxHeartbeats 200000
+
+namespace Poincare.ParabolicCutoffCommutator
+
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
+
+/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
+theorem quadratic_remainder
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
+    (x v : E) (hv : ‖v‖ = 1) :
+    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
+  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
+    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
+      convex_univ (mem_univ x) (mem_univ y)
+  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
+      (dh (x + s • v) v) s := by
+    simpa using (hd (x + s • v)).comp_hasDerivAt s
+      (((hasDerivAt_id s).smul_const v).const_add x)
+  have hdr (s : ℝ) : HasDerivAt
+      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
+      (dh (x + s • v) v - dh x v) s := by
+    simpa using ((hdline s).sub_const (h x)).sub
+      ((hasDerivAt_id s).mul_const (dh x v))
+  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
+    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
+    simp only [id_eq]
+    ring
+  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
+    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
+    (fun s _ => (hdr s).hasDerivWithinAt)
+    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
+    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
+  · exact hr
+  · calc
+      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
+      _ ≤ ‖dh (x + s • v) - dh x‖ := by
+        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
+      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)
+
+/-- The finite-difference estimate with an arbitrary positive step. -/
+theorem finite_difference_derivative
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
+    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
+    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
+  have hr := quadratic_remainder hd hdd hb hη.le x v hv
+  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
+    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
+  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
+    calc
+      |η * dh x v| = |(h (x + η • v) - h x) -
+          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
+      _ ≤ |h (x + η • v) - h x| +
+          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
+      _ ≤ _ := add_le_add hu hr
+  rw [abs_mul, abs_of_pos hη] at ht
+  apply (mul_le_mul_iff_right₀ hη).mp
+  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
+    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
+    calc
+      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
+      _ = _ := by rw [hc]
+  rw [he]
+  nlinarith
+
+/-- Optimizing the step gives a square-root bound on the full derivative. -/
+theorem derivative_norm_le_sqrt
+    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
+    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
+    (hd : ∀ x, HasFDerivAt h (dh x) x)
+    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
+    (hδ : 0 < δ) (hM : 0 ≤ M)
+    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
+    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
+  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
+  intro v hv
+  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
+  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
+      3 * Real.sqrt δ * M := by
+    have hs := Real.sq_sqrt hδ.le
+    have hp := Real.sqrt_pos.mpr hδ
+    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
+      apply (div_eq_iff (ne_of_gt hp)).2
+      nlinarith
+    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
+    ring
+  exact h.trans_eq he
+
+variable {α T : ℝ}
+
+/-- Time increments of the value are controlled by the stored time derivative. -/
+theorem value_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
+  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
+    (fun r hr => G.hasDeriv_time r hr x)
+    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
+  simpa only [Real.norm_eq_abs, mul_comm] using h
+
+/-- The gradient of any derivative graph is uniformly small at short times. -/
+theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
+    (norm_nonneg G) ?_ ?_ x
+  · intro y
+    calc
+      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
+      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
+  · intro y
+    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])
+
+/-- The supremum of the gradient has the same square-root gain. -/
+theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
+    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
+  apply csSup_le (insert_nonempty _ _)
+  rintro r (rfl | ⟨p, rfl⟩)
+  · positivity
+  · exact gradient_bound G hT p.property.1 p.val.2
+
+/-- Time differences of the gradient require no mixed time-space derivative. -/
+theorem gradient_time_increment (G : Graph (E := E) α T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
+  by_cases hst : t = s
+  · simp [hst]
+  · apply derivative_norm_le_sqrt
+      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
+      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
+      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
+      (value_time_increment G hs ht) ?_ x
+    intro y
+    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
+      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])
+
+/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
+theorem gradient_space_increment (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
+    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Spatial value increments inherit the improved gradient bound. -/
+theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
+  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
+    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
+    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)
+
+/-- Split a power at a larger positive scale. -/
+theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
+    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
+    r ^ b ≤ R ^ (b - a) * r ^ a := by
+  have he : r ^ b = r ^ (b - a) * r ^ a := by
+    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
+    congr 1
+    ring
+  rw [he]
+  exact mul_le_mul_of_nonneg_right
+    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)
+
+/-- Interpolate a Lipschitz bound and a bound at scale R. -/
+theorem scale_interpolation {a L r R α : ℝ}
+    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
+    (hl : a ≤ L * r) (hb : a ≤ L * R) :
+    a ≤ L * R ^ (1 - α) * r ^ α := by
+  by_cases h : r ≤ R
+  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
+    rw [Real.rpow_one] at hp
+    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
+  · have he : R ^ (1 - α) * R ^ α = R := by
+      rw [← Real.rpow_add hR]
+      convert Real.rpow_one R using 2
+      ring
+    calc
+      a ≤ L * R := hb
+      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
+      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
+        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)
+
+/-- The parabolic spatial scale is the square root of the time scale. -/
+theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
+    (Real.sqrt T) ^ p = T ^ (p / 2) := by
+  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
+  congr 1
+  ring
+
+/-- Spatial Hölder gradient increments carry the desired positive time power. -/
+theorem gradient_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    ‖G.du (t, x) - G.du (t, y)‖ ≤
+      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
+    (L := 6 * ‖G‖) (by positivity)
+    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
+    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
+      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
+  rw [sqrt_rpow hT.le] at h
+  nlinarith [h]
+
+/-- Spatial Hölder value increments gain one additional half power of time. -/
+theorem value_space_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
+    |G.u (t, x) - G.u (t, y)| ≤
+      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
+  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
+    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
+  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
+    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
+    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
+    (value_space_increment G hT ht x y)
+    ((abs_sub _ _).trans (by
+      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
+      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
+  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
+    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
+    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
+    rw [sqrt_rpow hT.le]
+    congr 1
+    ring
+  calc
+    |G.u (t,x) - G.u (t,y)| ≤ _ := h
+    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
+        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]
+
+/-- The temporal Hölder gradient bound follows from the square-root increment. -/
+theorem gradient_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    ‖G.du (t, x) - G.du (s, x)‖ ≤
+      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
+    (show (0 : ℝ) < 1 / 2 by norm_num)
+  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
+  have hi := gradient_time_increment G hs ht x
+  rw [Real.sqrt_eq_rpow] at hi
+  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]
+
+/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
+theorem value_time_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
+    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
+    |G.u (t, x) - G.u (s, x)| ≤
+      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
+  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
+  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
+    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
+  rw [Real.rpow_one] at hp
+  exact (value_time_increment G hs ht x).trans (by
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])
+
+omit [NormedSpace ℝ E] in
+/-- Split a mixed increment through the point with the first time and second position. -/
+theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
+    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
+    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
+      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
+    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
+      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
+    HasHolderBound α (cylinder T) f (Kx + Kt) := by
+  intro p hp q hq
+  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
+    Real.rpow_le_rpow (norm_nonneg _) (by
+      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
+  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
+    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
+    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
+      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
+  calc
+    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
+      norm_sub_le_norm_sub_add_norm_sub _ _ _
+    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
+      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
+    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
+      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]
+
+/-- Full gradient Hölder control, including mixed increments. -/
+theorem gradient_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
+  have h := holder_of_increments hα.le
+    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+    (fun t ht => gradient_space_holder G hα hα1 hT ht)
+    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
+  convert h using 1
+  ring
+
+/-- Full value Hölder control with its stronger time power. -/
+theorem value_holder (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
+    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
+  have h := holder_of_increments (f := G.u) hα.le
+    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
+    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
+    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
+    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
+  convert h using 1
+  ring
+
+/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
+theorem interpolation_bounds (G : Graph (E := E) α T)
+    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
+    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
+  constructor
+  · have h := ParabolicHolder.norm_le_of_bounds G.u
+      (show 0 ≤ T * ‖G‖ by positivity)
+      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
+      (fun p hp => (time_bound G hp.1 p.2).trans
+        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
+      (value_holder G hα hα1 hT)
+    have hp : T ≤ T ^ (1-α/2) := by
+      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
+      exact (Real.rpow_one T).symm
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
+      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
+  · have h := ParabolicHolder.norm_le_of_bounds G.du
+      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
+      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
+      (fun p hp => gradient_bound G hT hp.1 p.2)
+      (gradient_holder G hα hα1 hT)
+    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
+      rw [Real.sqrt_eq_rpow]
+      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]
+
+/-- A universal constant satisfies the frozen interpolation target. -/
+theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
+      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
+      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
+  intro α hα hα1
+  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩
+
+/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
+theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
+    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
+      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
+  classical
+  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
+  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
+  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
+  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
+    have h := scale_interpolation (L := 2*A+B) (R := 1)
+      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
+      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
+      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
+    simpa using h
+  refine ⟨A + (2*A+B), by positivity, ?_⟩
+  intro T
+  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
+  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
+    intro p hp; simp [f, hp]
+  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
+    intro p hp; simpa [f, hp] using hA p.2
+  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
+    intro p hp q hq
+    simp only [f, if_pos hp, if_pos hq]
+    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
+      (Real.rpow_le_rpow (norm_nonneg _) (by
+        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
+  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
+  refine ⟨fY, ?_, ?_⟩
+  · intro p hp
+    change f p = ψ p.2
+    simp [f, hp]
+  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder
+
+/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
+theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
+    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
+    (hα : 0 < α) (hα1 : α < 1) :
+    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
+      ∃ (f : Y (E := E) α T ℝ)
+        (df : Y (E := E) α T (E →L[ℝ] ℝ))
+        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
+      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
+        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
+      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
+  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
+  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
+  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
+  refine ⟨K0+K1+K2, by positivity, ?_⟩
+  intro T
+  obtain ⟨f, hf, hfb⟩ := h0 T
+  obtain ⟨df, hdf, hdfb⟩ := h1 T
+  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
+  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩
+
+/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
+theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z * G.u (t,z))
+      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
+  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)
+
+/-- The second spatial product rule includes both mixed Hessian terms. -/
+theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
+      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
+  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
+  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
+    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)
+
+/-- A spatial cutoff is constant in the within-time product rule. -/
+theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
+    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
+    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
+  (G.hasDeriv_time t ht x).const_mul (ψ x)
+
+section Bilinear
+variable {F H J : Type*}
+  [NormedAddCommGroup F] [NormedSpace ℝ F]
+  [NormedAddCommGroup H] [NormedSpace ℝ H]
+  [NormedAddCommGroup J] [NormedSpace ℝ J]
+
+omit [NormedSpace ℝ E] in
+/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
+theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
+  intro p hp q hq
+  have hf := ParabolicHolder.holder_le f hp hq
+  have hg := ParabolicHolder.holder_le g hp hq
+  have hf0 := ParabolicHolder.norm_le f p
+  have hg0 := ParabolicHolder.norm_le g q
+  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
+  calc
+    ‖B (f p) (g p) - B (f q) (g q)‖ =
+        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
+      congr 1
+      simp only [map_sub, ContinuousLinearMap.sub_apply]
+      abel
+    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
+    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
+      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
+    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
+        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
+      apply add_le_add
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
+          (norm_nonneg _) (by positivity)
+      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
+          (norm_nonneg _) (by positivity)
+    _ = _ := by ring
+
+/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
+def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
+  ofFunction (fun p => B (f p) (g p))
+    (fun p hp => by simp [zero_off f hp])
+    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
+    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩
+
+omit [NormedSpace ℝ E] in
+/-- The bilinear carrier norm has an explicit product bound. -/
+theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
+    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
+    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
+    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
+    (fun p _ => (B.le_opNorm₂ _ _).trans
+      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
+        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
+    (bilinear_holder B f g)
+  nlinarith [h]
+
+end Bilinear
+
+local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
+  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)
+
+/-- Assemble the cutoff graph from its three spatial carriers. -/
+def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
+    (G : Graph (E := E) α T) : Graph (E := E) α T where
+  u := f * G.u
+  ut := f * G.ut
+  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
+  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
+    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
+    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
+  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
+  hasFDeriv := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv hψ G ht x using 1
+    · funext z
+      simp only [mul_apply, hf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
+  hasFDeriv_du := by
+    intro t ht x
+    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
+    convert cutoff_hasFDeriv_du hψ G ht x using 1
+    · funext z
+      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
+      rfl
+  hasDeriv_time := by
+    intro t ht x
+    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
+      by_cases hs : (s,x) ∈ cylinder T
+      · simp [mul_apply, hf (s,x) hs]
+      · simp [mul_apply, zero_off G.u hs]
+    convert cutoff_hasDeriv_time ψ G ht x using 1
+    · funext s; exact he s
+    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]
+
+/-- Equality of the four stored carriers determines a derivative graph. -/
+theorem graph_ext_components {G H : Graph (E := E) α T}
+    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
+    G = H := by
+  cases G
+  cases H
+  simp_all
+
+/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
+def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
+  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
+  map_add' G H := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
+      simp only [map_add, ContinuousLinearMap.add_apply]
+      module
+  map_smul' c G := by
+    apply graph_ext_components
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.u p) = c • (f p * (G.u p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p * (c • G.ut p) = c • (f p * (G.ut p))
+      ring
+    · apply ParabolicHolder.ext
+      intro p hp
+      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
+      module
+    · apply ParabolicHolder.ext
+      intro p hp
+      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
+      simp only [map_smul, ContinuousLinearMap.smul_apply]
+      module
+
+
+set_option maxHeartbeats 4000000 in
+/-- The cutoff graph map is bounded in the original four-component norm. -/
+theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
+    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
+    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
+    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
+    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
+    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
+      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
+  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
+  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
+  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
+  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
+  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
+    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
+  let A := ‖f‖ + ‖df‖ + ‖ddf‖
+  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
+  have hA : 0 ≤ A := by dsimp [A]; positivity
+  have hB : 0 ≤ B := by dsimp [B]; positivity
+  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
+  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
+  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
+  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
+  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
+  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
+  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
+  refine ⟨20 * B * A, ?_⟩
+  intro G
+  have hGu := norm_u_le G
+  have hGut := norm_ut_le G
+  have hGdu := norm_du_le G
+  have hGddu := norm_ddu_le G
+  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
+    calc
+      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
+      _ ≤ B * A * ‖G‖ := by
+        calc
+          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
+          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
+  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * A * ‖G‖ := by gcongr
+  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
+    calc
+      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
+      _ ≤ 3 * B * ‖G‖ * A := by gcongr
+      _ = _ := by ring
+  rw [ParabolicSolutionGraph.norm_eq]
+  change ‖f * G.u‖ + ‖f * G.ut‖ +
+    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
+    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
+      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
+  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
+  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
+    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
+  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
+  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
+  nlinarith
+
+/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
+theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
+    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
+        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
+        (C G).ddu (t,x) =
+          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
+          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
+            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
+  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
+  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
+  have hf := fun p hp => (heq p hp).1
+  have hdf := fun p hp => (heq p hp).2.1
+  have hddf := fun p hp => (heq p hp).2.2
+  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
+  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
+  let C := L.mkContinuous B hB
+  refine ⟨C, ?_, ?_⟩
+  · intro G p
+    change f p * G.u p = ψ p.2 * G.u p
+    by_cases hp : p ∈ cylinder T
+    · rw [hf p hp]
+    · simp [zero_off G.u hp]
+  · intro G t ht x
+    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
+    change f (t,x) * G.ut (t,x) = _ ∧
+      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
+        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
+    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
+    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp]
+    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
+      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
+        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
+      rfl
+
+end Poincare.ParabolicCutoffCommutator
+
+noncomputable section
+set_option maxHeartbeats 800000
+namespace Poincare.ParabolicCutoffCommutator
+open Set ParabolicHolder ParabolicSolutionGraph
+open scoped ContDiff
+variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α T : ℝ}
+
+/-- Evaluate a first derivative carrier on a unit direction. -/
+def derivativeEntry (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    Y (E := E) α T ℝ :=
+  ofFunction (fun p => H p v)
+    (fun p hp => by simp [zero_off H hp])
+    ⟨‖H‖, fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v))⟩
+    ⟨‖H‖, fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v))⟩
+
+/-- Evaluation is bounded in the full Hölder norm. -/
+theorem norm_derivativeEntry_le (H : Y (E := E) α T (E →L[ℝ] ℝ)) (v : E) (hv : ‖v‖ = 1) :
+    ‖derivativeEntry H v hv‖ ≤ 2 * ‖H‖ := by
+  have h := ParabolicHolder.norm_le_of_bounds (derivativeEntry H v hv)
+    (norm_nonneg H) (norm_nonneg H)
+    (fun p _ => by
+      simpa [hv] using ((H p).le_opNorm v).trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.norm_le H p) (norm_nonneg v)))
+    (fun p hp q hq => by
+      have h := (H p - H q).le_opNorm v
+      simpa [hv] using h.trans
+        (mul_le_mul_of_nonneg_right (ParabolicHolder.holder_le H hp hq) (norm_nonneg v)))
+  linarith
+
+
+/-- The first-order forcing associated to the explicit commutator coefficients. -/
+def firstOrderForcing (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) : Y (E := (ClosedSmoothModel 3)) α T ℝ :=
+  (∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c * G.u
+
+/-- The carrier evaluates to the first-order coefficient formula. -/
+theorem firstOrderForcing_apply (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (p : ℝ × (ClosedSmoothModel 3)) :
+    firstOrderForcing b c G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p := by
+  simp only [firstOrderForcing, add_apply, ParabolicHolderMultiplier.sum_apply, mul_apply,
+    derivativeEntry, ofFunction_apply]
+
+/-- The commutator uses only the value and gradient norms. -/
+theorem norm_firstOrderForcing_le (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) :
+    ‖firstOrderForcing b c G‖ ≤ 2 * (∑ i : Fin 3, ‖b i‖) * ‖G.du‖ + ‖c‖ * ‖G.u‖ := by
+  calc
+    ‖firstOrderForcing b c G‖ ≤
+        ‖∑ i : Fin 3, b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖ + ‖c * G.u‖ := norm_add_le _ _
+    _ ≤ (∑ i : Fin 3, ‖b i * derivativeEntry G.du ((EuclideanSpace.basisFun (Fin 3) ℝ) i) (OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 3) ℝ) i)‖) + ‖c‖ * ‖G.u‖ :=
+      add_le_add (norm_sum_le _ _) (ParabolicHolder.norm_mul_le _ _)
+    _ ≤ (∑ i : Fin 3, ‖b i‖ * (2 * ‖G.du‖)) + ‖c‖ * ‖G.u‖ := by
+      apply add_le_add_left
+      apply Finset.sum_le_sum
+      intro i hi
+      exact (ParabolicHolder.norm_mul_le _ _).trans
+        (mul_le_mul_of_nonneg_left (norm_derivativeEntry_le G.du _ _) (norm_nonneg _))
+    _ = _ := by rw [← Finset.sum_mul]; ring
+
+/-- The commutator has separate positive time powers for its two coefficient families. -/
+theorem firstOrder_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      24 * ((∑ i : Fin 3, ‖b i‖) * T ^ ((1-α)/2) + ‖c‖ * T ^ (1-α/2)) * ‖G‖ := by
+  obtain ⟨hu, hdu⟩ := interpolation_bounds G hα hα1 hT hT1
+  have hb : 0 ≤ ∑ i : Fin 3, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
+  have h1 := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * ∑ i : Fin 3, ‖b i‖ by positivity)
+  have h2 := mul_le_mul_of_nonneg_left hu (norm_nonneg c)
+  have h3 := norm_firstOrderForcing_le b c G
+  nlinarith [mul_nonneg (norm_nonneg c) (mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G))]
+
+/-- The common weaker time exponent controls both first-order terms. -/
+theorem firstOrder_common_time_bound (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (G : Graph (E := (ClosedSmoothModel 3)) α T) (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
+    ‖firstOrderForcing b c G‖ ≤
+      (24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)) * ‖G‖ := by
+  have hp : T ^ (1-α/2) ≤ T ^ ((1-α)/2) :=
+    Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
+  have h := firstOrder_time_bound b c G hα hα1 hT hT1
+  nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) (norm_nonneg G))]
+
+/-- First-order coefficient multiplication is a linear map of derivative graphs. -/
+def firstOrderLinearMap (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ) :
+    Graph (E := (ClosedSmoothModel 3)) α T →ₗ[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ where
+  toFun := firstOrderForcing b c
+  map_add' G H := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [add_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i) + H.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (G.u p + H.u p) = _
+    simp only [mul_add, Finset.sum_add_distrib]
+    ring
+  map_smul' r G := by
+    apply ParabolicHolder.ext
+    intro p hp
+    simp only [smul_apply, firstOrderForcing_apply]
+    change (∑ i : Fin 3, b i p * (r * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i))) + c p * (r * G.u p) = _
+    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, smul_eq_mul, RingHom.id_apply]
+    ring
+
+/-- The frozen commutator operator target, with a universal constant. -/
+theorem commutator : ∀ α : ℝ, 0 < α → α < 1 →
+    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
+    ∀ (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ),
+    ∃ K : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Y (E := (ClosedSmoothModel 3)) α T ℝ,
+      (∀ G p, K G p = (∑ i : Fin 3, b i p * G.du p ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c p * G.u p) ∧
+      ‖K‖ ≤ C * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2) := by
+  intro α hα hα1
+  refine ⟨24, by norm_num, ?_⟩
+  intro T hT hT1 b c
+  let B := 24 * ((∑ i : Fin 3, ‖b i‖) + ‖c‖) * T ^ ((1-α)/2)
+  let K := (firstOrderLinearMap b c).mkContinuous B
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+  refine ⟨K, firstOrderForcing_apply b c, ?_⟩
+  exact ContinuousLinearMap.opNorm_le_bound _ (by dsimp [B]; positivity)
+    (fun G => firstOrder_common_time_bound b c G hα hα1 hT hT1)
+
+set_option maxHeartbeats 4000000 in
+/-- The nonsymmetric principal coefficients give both mixed cutoff terms. -/
+theorem cutoff_commutator_identity {ψ : (ClosedSmoothModel 3) → ℝ} (hψ : ContDiff ℝ ∞ ψ)
+    (hcompact : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1)
+    (a : Fin 3 → Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (drift : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (potential : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (b : Fin 3 → Y (E := (ClosedSmoothModel 3)) α T ℝ) (c : Y (E := (ClosedSmoothModel 3)) α T ℝ)
+    (hb : ∀ t ∈ Icc 0 T, ∀ x k,
+      b k (t,x) = -(∑ j : Fin 3, (a j k (t,x) + a k j (t,x)) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)))
+    (hc : ∀ t ∈ Icc 0 T, ∀ x,
+      c (t,x) = -(∑ j : Fin 3, ∑ k : Fin 3, a j k (t,x) * fderiv ℝ (fderiv ℝ ψ) x ((EuclideanSpace.basisFun (Fin 3) ℝ) j) ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) -
+        ∑ j : Fin 3, drift j (t,x) * fderiv ℝ ψ x ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) :
+    ∃ C : Graph (E := (ClosedSmoothModel 3)) α T →L[ℝ] Graph (E := (ClosedSmoothModel 3)) α T,
+      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
+      (∀ G t, t ∈ Icc 0 T → ∀ x,
+        ((C G).ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * (C G).ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * (C G).du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * (C G).u (t,x)) -
+        ψ x * (G.ut (t,x) - (∑ i : Fin 3, ∑ j : Fin 3, a i j (t,x) * G.ddu (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i) ((EuclideanSpace.basisFun (Fin 3) ℝ) j)) -
+          (∑ i : Fin 3, drift i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) - potential (t,x) * G.u (t,x)) =
+        (∑ i : Fin 3, b i (t,x) * G.du (t,x) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) + c (t,x) * G.u (t,x)) := by
+  obtain ⟨C, hu, hjets⟩ := exists_cutoff_operator hψ hcompact hα hα1
+  refine ⟨C, hu, ?_⟩
+  intro G t ht x
+  obtain ⟨hut, hdu, hddu⟩ := hjets G t ht x
+  rw [hut, hdu, hddu, hu G (t,x)]
+  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
+    ContinuousLinearMap.smulRight_apply, smul_eq_mul, hb t ht x, hc t ht x,
+    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
+  ring
+
+end Poincare.ParabolicCutoffCommutator
```

## Report whitespace verification

The initial report retained trailing spaces from compiler output and unified-diff context lines. The lossless JSON-line encoding above resolves that formatting issue. The original check is preserved here.

```json
[
  "$ git diff --cached --check\n",
  "exit: 2\n",
  "harness/reports/parabolic-cutoff-commutator_done.md:89: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:420: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/AppendixA.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:445: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:458: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:463: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:475: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:480: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:523: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:551: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:754: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:758: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:760: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:840: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:845: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:889: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:956: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:978: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:986: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item1Audit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1017: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1025: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1042: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1130: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1199: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1217: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1223: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1252: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1257: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1273: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1288: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/GradientAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1316: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1408: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1452: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1493: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1510: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1624: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1655: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1668: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1684: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1690: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1707: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1734: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1775: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1784: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1811: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1827: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1854: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1903: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:1905: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2176: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/InterpolationTarget.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2202: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2204: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2208: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2519: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2537: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2540: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2542: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2546: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2563: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2651: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2674: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2680: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2682: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2732: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2773: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2778: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2780: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2784: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2792: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2823: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2825: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2879: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/HessianInstance.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2914: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2916: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:2970: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3001: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3003: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3056: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/HessianInstanceDirect.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3071: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3073: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3128: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3145: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3188: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3242: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3247: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3740: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3745: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3749: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3751: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3776: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3778: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3813: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3815: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3839: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:3841: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4016: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4021: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4170: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4257: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4555: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4586: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4628: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4819: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4850: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4851: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4859: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4876: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4923: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:4958: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:5729: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:5956: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:5973: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:5975: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6052: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6057: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6061: trailing whitespace.\n",
  "+  \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6063: trailing whitespace.\n",
  "+    \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6247: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleDiagnostic.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:6662: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:7531: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:8309: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:8684: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:8706: trailing whitespace.\n",
  "+ \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:8714: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/Item4.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:10405: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:10707: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/FinalTargets.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:12808: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/ModuleAudit.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:13961: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ParabolicCutoffCommutator.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:14916: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/SymbolChecks.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:15339: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/FinalTargets.lean \n",
  "harness/reports/parabolic-cutoff-commutator_done.md:15664: trailing whitespace.\n",
  "+$ LEAN_NUM_THREADS=1 lake env lean /tmp/parabolic-cutoff-commutator/SymbolChecks.lean \n"
]
```
