# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-differential-transfer`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-differential-transfer_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-2.md` (the whole specification: its "Decisions and limits",
"Source and declaration index", and "Shared contract and verification convention" sections apply to you; your
task is reproduced below verbatim), the landed task 6 module `Poincare/Global/CartanSuppliedDifferentialSuccessor.lean`
(namespace `Poincare.CartanSuppliedDifferentialSuccessor`: `Interpretation`, `generic`, `patch`, `CoordinateData`,
`Data`, `Data.successor`, `anchor_laws`, `generic_map_eq`, `vector_eq`, `successor_fields`,
`eq_anchor_of_vector_eq_zero`) and its report `harness/reports/supplied-differential-successor_done.md`.

# Task supplied-differential-transfer

## Shared contract and verification convention

Task 6 starts at the recorded base. Each later implementation task freezes a new base containing its accepted predecessors. Tasks 6→7→8→9→10 are the requested dependency order; task 10's abstract recursion only needs tasks 6–7, while the later geometric dispatcher will need 8–9. Each task owns exactly the one new file named in its heading. All existing Lean files, `Poincare.lean`, audit wiring, and the other tasks' files are forbidden. This report-only attempt owns only this Markdown file; it does not update `HANDOFF.md`.

The following blocks give complete definitions and full theorem signatures. The signatures intentionally have no proof bodies. For declaration/type checking, each `theorem name : P` is transformed into `def name_spec : Prop := P`; no proof placeholder, axiom, or implementation of a target is introduced. Concatenating the blocks in order is the checked scratch contract. The broad existing import envelope below is for that scratch file. Each task's intended imports are specified separately.

```lean
import Poincare.Global.FixedChartUniformPreferredGermAgreement
import Poincare.Global.DifferentialSuccessorIntervalNaturality
import Poincare.Global.DifferentialSuccessorAdjacentContinuation
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

```


## 7. `Poincare/Global/CartanSuppliedDifferentialTransfer.lean`

Namespace: `Poincare.CartanSuppliedDifferentialTransfer`.
Imports: task 6, `Poincare.Global.DifferentialSuccessorIntervalNaturality`.

Objective: construct an actual differential-induced alignment from coordinate data; prove independence and cross-interpretation congruence; identify the generic instance and transfer fixed-anchor germs. No extra definitions are needed.

Reuse S5's derivative uniqueness and dependent-state equality arguments. S6.`inducedTangentAlignmentOfCoordinatePullback` is a model for the construction, **not** a direct instance for arbitrary fixed hosts: its `L₀` is aligned at its own old-chart anchors and its derivative factors through that `L₀`. Here `linear Q s` is an arbitrary framed equivalence. Re-prove the coordinate-pullback-to-reanchored-isometry construction for the displayed `CoordinateData`, using the invertible source/target chart-transition derivatives, and then construct `Data.alignment`. The metric-pullback hypothesis is retained verbatim in meaning, so this task adds no geometric isometry existence claim.

`ofGeneric` and `toGeneric` are existential adapter theorems, not definitions requiring a new selector. They preserve the normal vector and geometric successor, not equality of source sets or exact analytic witnesses. Use S1.`generic_map_eq` and local inverse-chart identities to move derivatives between the two coordinate presentations. `generic_interval_equality` is the generic consumer instance of S7 after these adapters, with a smaller open neighborhood to retain old and new sources. `local_equality_transfer` states precisely the extra neighborhood agreements needed to apply that instance to an arbitrary interpretation. S4 supplies the successor-anchor comparison when that anchor is retained; it does not by itself supply the predecessor comparison at the successor.

`patch_successor_at_anchor` retains the zero-step law used in S8's endpoint/ladder proofs, via S7.`anchorData_successor` and the patch germ comparison. Task 6's `eq_anchor_of_vector_eq_zero` reduces a zero vector to this anchor case. Do not assert the anchor-successor law for an arbitrary `Interpretation`: its normal charts and frames need not have anchor derivative equal to the stored predecessor alignment. The generic and geometric patch instances do have the needed comparison.

For `patch_germ_eventuallyEq_generic`, apply S4 on **both** retained patches, undo the target frame in the inverse-normal germ, and compose as in S2. The inverse-normal argument must use the partial inverse laws on their domains; do not claim equality of total inverses from S4.

```lean
namespace CartanSuppliedDifferentialTransfer
variable [T2Space M]
open CartanSuppliedDifferentialSuccessor
-- TARGET 7.1
theorem data_of_coordinateData : ∀ (Q : Interpretation g)
  (s : CartanChain.ChainState g) (z : M) (w : CoordinateData Q s z),
  ∃ d : Data Q s z, d.toCoordinateData = w
-- TARGET 7.2
theorem alignment_clm_eq_of_eventuallyEq :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z),
  reanchoredChartMap Q s z =ᶠ[𝓝 (extChartAt I z z)] reanchoredChartMap R t z →
  (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
    (e.alignment.toContinuousLinearEquiv : E →L[ℝ] E)
-- TARGET 7.3
theorem successor_eq_of_eqOn_open :
  ∀ (Q R : Interpretation g) (s t : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : Data R t z) (W : Set M),
    IsOpen W → z ∈ W → EqOn (map Q s) (map R t) W → d.successor = e.successor
-- TARGET 7.4
theorem successor_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d e : Data Q s z), d.successor = e.successor
-- TARGET 7.5
theorem ofGeneric : ∀ (s : CartanChain.ChainState g) (z : M)
    (d : DifferentialInducedSuccessor.Data s z),
    ∃ e : Data (generic g) s z, e.successor = d.successor ∧ e.v = d.v
-- TARGET 7.6
theorem toGeneric : ∀ (s : CartanChain.ChainState g) (z : M)
    (e : Data (generic g) s z),
    ∃ d : DifferentialInducedSuccessor.Data s z, d.successor = e.successor ∧ d.v = e.v
-- TARGET 7.7
theorem patch_germ_eventuallyEq_generic :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (s : CartanChain.ChainState g), s.anchor ∈ C.anchors → s.target ∈ D.anchors →
    map (patch C D) s =ᶠ[𝓝 s.anchor] s.map
-- TARGET 7.8
theorem generic_interval_equality :
  HasConstantSectionalCurvature3 g 1 → ∀ (x : M) (p : RoundSphere3),
  ∃ ρ > (0 : ℝ), ∀ (L : CartanMap.TangentAlignment g x p) (z : M)
    (d : Data (generic g) ⟨x, p, L⟩ z), ‖d.v‖ < ρ →
    ∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn (map (generic g) ⟨x, p, L⟩) (map (generic g) d.successor)
        (W ∩ ((germ (generic g) ⟨x, p, L⟩).source ∩
          (germ (generic g) d.successor).source))
-- TARGET 7.9
theorem local_equality_transfer :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z) (e : DifferentialInducedSuccessor.Data s z),
    d.successor = e.successor →
    map Q s =ᶠ[𝓝 z] s.map →
    map Q d.successor =ᶠ[𝓝 z] e.successor.map →
    (∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn s.germ e.successor.germ (W ∩ (s.germ.source ∩ e.successor.germ.source))) →
    ∃ W : Set M, IsOpen W ∧ z ∈ W ∧
      EqOn (map Q s) (map Q d.successor)
        (W ∩ ((germ Q s).source ∩ (germ Q d.successor).source))
-- TARGET 7.10
theorem patch_successor_at_anchor :
  ∀ (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V),
  U ⊆ IsometryInstantiate.cutoffOneLocus x₀ →
  V ⊆ IsometryInstantiate.cutoffOneLocus p₀ →
  ∀ (s : CartanChain.ChainState g)
    (d : Data (patch C D) s s.anchor), d.successor = s
end CartanSuppliedDifferentialTransfer
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialTransfer.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialTransfer.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All ten targets compile, including construction from `CoordinateData`, both generic adapters, and the two-patch germ comparison. Stop blocked at the first unclosed chart-transition, metric-pullback, or inverse-germ goal; retain its complete Lean context. Do not replace construction with an extra alignment premise or replace neighborhood equality with value equality.

