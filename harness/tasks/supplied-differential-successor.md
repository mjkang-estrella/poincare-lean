# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-differential-successor`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-differential-successor_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-2.md` (the whole specification: its "Decisions and limits",
"Source and declaration index", and "Shared contract and verification convention" sections apply to you; your
task is reproduced below verbatim), then `harness/reports/chain-parametrization-inventory.md`, then the five
landed modules it cites.

# Task supplied-differential-successor

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


## 6. `Poincare/Global/CartanSuppliedDifferentialSuccessor.lean`

Namespace: `Poincare.CartanSuppliedDifferentialSuccessor`.
Imports: `Poincare.Global.FixedChartUniformPreferredGermAgreement`, `Poincare.Global.DifferentialInducedSuccessor`.

Objective: make the actual supplied map, its coordinates, and its differential witnesses explicit, while retaining the geometric state. Reuse S1's composition formula and generic comparison, S3's exact endpoint/normal domains and anchor laws, S4's frame invertibility, S5's field layout, and S6's continuous-linear-equivalence constructor. `patchFrame` has an identity extension outside the anchors solely to define a total function. No regularity or geometric law is asserted there; quantitative tasks require anchor membership.

`sourceExp` and `targetExp` are the supplied endpoints expressed in explicitly stored host charts. They may have extra domain restrictions and are not definitionally the old exponential charts even for `generic`. `source_mem_oldChart` and `target_mem_oldChart` retain their consumer roles but now refer to those explicit hosts. For `patch C D` these hosts are fixed `x₀,p₀`, not the moving anchors. A port must use those hosts wherever the old proof used `s.anchor,s.target` as coordinate-chart centers. See S5.`Data` and S8.`successor_anchor_mem_coordinateControlledCommonSource`.

```lean
namespace CartanSuppliedDifferentialSuccessor
structure Interpretation (g : ClosedSmoothRiemannianMetric 3 M) where
  sourceAnchors : Set M
  targetAnchors : Set RoundSphere3
  sourceNormal : M → OpenPartialHomeomorph M E
  targetNormal : RoundSphere3 → OpenPartialHomeomorph RoundSphere3 E
  sourceFrame : M → E ≃L[ℝ] E
  targetFrame : RoundSphere3 → E ≃L[ℝ] E
  sourceHost : M → M
  targetHost : RoundSphere3 → RoundSphere3
  source_anchor_mem : ∀ x ∈ sourceAnchors, x ∈ (sourceNormal x).source
  source_anchor_zero : ∀ x ∈ sourceAnchors, sourceNormal x x = 0
  target_anchor_mem : ∀ p ∈ targetAnchors, p ∈ (targetNormal p).source
  target_anchor_zero : ∀ p ∈ targetAnchors, targetNormal p p = 0

def generic (g : ClosedSmoothRiemannianMetric 3 M) : Interpretation g where
  sourceAnchors := univ
  targetAnchors := univ
  sourceNormal := (CartanSourceExponential.genericFamily g).normal
  targetNormal := (CartanSourceExponential.genericFamily roundSphereMetric3).normal
  sourceFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  targetFrame := fun _ => ContinuousLinearEquiv.refl ℝ E
  sourceHost := id
  targetHost := id
  source_anchor_mem := fun x _ => (CartanSourceExponential.genericFamily g).anchor_mem_source x
  source_anchor_zero := fun x _ => (CartanSourceExponential.genericFamily g).normal_anchor x
  target_anchor_mem := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).anchor_mem_source p
  target_anchor_zero := fun p _ => (CartanSourceExponential.genericFamily roundSphereMetric3).normal_anchor p

def patchFrame {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U) (x : M) : E ≃L[ℝ] E :=
  @dite _ (x ∈ C.anchors) (Classical.propDecidable _) (fun hx =>
    InducedAlignment.continuousLinearEquivOfInvertible
      (FixedChartUniformPreferredGermAgreement.anchorFrame x₀ x)
      (FixedChartUniformPreferredGermAgreement.anchorFrame_isInvertible C x hx))
    (fun _ => ContinuousLinearEquiv.refl ℝ E)

def patch {x₀ : M} {p₀ : RoundSphere3} {U V : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V) :
    Interpretation g where
  sourceAnchors := C.anchors
  targetAnchors := D.anchors
  sourceNormal := C.normal
  targetNormal := D.normal
  sourceFrame := patchFrame C
  targetFrame := patchFrame D
  sourceHost := fun _ => x₀
  targetHost := fun _ => p₀
  source_anchor_mem := C.anchor_mem_normal_source
  source_anchor_zero := C.normal_anchor
  target_anchor_mem := D.anchor_mem_normal_source
  target_anchor_zero := D.normal_anchor

def linear (Q : Interpretation g) (s : CartanChain.ChainState g) : E ≃L[ℝ] E :=
  ((Q.sourceFrame s.anchor).trans s.alignment.toContinuousLinearEquiv).trans
    (Q.targetFrame s.target).symm

def germ (Q : Interpretation g) (s : CartanChain.ChainState g) :
    OpenPartialHomeomorph M RoundSphere3 :=
  (Q.sourceNormal s.anchor).trans
    ((linear Q s).toHomeomorph.toOpenPartialHomeomorph.trans
      (Q.targetNormal s.target).symm)

def map (Q : Interpretation g) (s : CartanChain.ChainState g) : M → RoundSphere3 :=
  germ Q s

def sourceExp (Q : Interpretation g) (x : M) : OpenPartialHomeomorph E E :=
  (Q.sourceNormal x).symm.trans (chartAt E (Q.sourceHost x))

def targetExp (Q : Interpretation g) (p : RoundSphere3) : OpenPartialHomeomorph E E :=
  (Q.targetNormal p).symm.trans (chartAt E (Q.targetHost p))

def chartMap (Q : Interpretation g) (s : CartanChain.ChainState g) : E → E :=
  fun z => targetExp Q s.target (linear Q s ((sourceExp Q s.anchor).symm z))

def chartDifferential (Q : Interpretation g) (s : CartanChain.ChainState g)
    (A B : E ≃L[ℝ] E) : E →L[ℝ] E :=
  ((A.symm.trans (linear Q s)).trans B : E ≃L[ℝ] E)

def reanchoredChartMap (Q : Interpretation g) (s : CartanChain.ChainState g)
    (z : M) : E → E :=
  fun w => extChartAt I (map Q s z) (map Q s ((extChartAt I z).symm w))

structure CoordinateData (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M) where
  source_anchor_valid : s.anchor ∈ Q.sourceAnchors
  target_anchor_valid : s.target ∈ Q.targetAnchors
  source_mem : z ∈ (germ Q s).source
  v : E
  A : E ≃L[ℝ] E
  B : E ≃L[ℝ] E
  source_vector_mem : v ∈ (sourceExp Q s.anchor).source
  target_vector_mem : linear Q s v ∈ (targetExp Q s.target).source
  source_mem_oldChart : z ∈ (extChartAt I (Q.sourceHost s.anchor)).source
  target_mem_oldChart : map Q s z ∈ (extChartAt I (Q.targetHost s.target)).source
  source_coordinate : extChartAt I (Q.sourceHost s.anchor) z = sourceExp Q s.anchor v
  target_coordinate : extChartAt I (Q.targetHost s.target) (map Q s z) =
    targetExp Q s.target (linear Q s v)
  source_exp_derivative : HasStrictFDerivAt (sourceExp Q s.anchor) (A : E →L[ℝ] E) v
  target_exp_derivative : HasStrictFDerivAt (targetExp Q s.target) (B : E →L[ℝ] E) (linear Q s v)
  cartan_chart_derivative : HasStrictFDerivAt (chartMap Q s)
    (chartDifferential Q s A B) (sourceExp Q s.anchor v)
  metric_pullback : ∀ u u' : E,
    CovariantDerivative.chartMetric roundSphereMetric3.inner (Q.targetHost s.target)
      (targetExp Q s.target (linear Q s v))
      (chartDifferential Q s A B u) (chartDifferential Q s A B u') =
    CovariantDerivative.chartMetric g.inner (Q.sourceHost s.anchor)
      (sourceExp Q s.anchor v) u u'

structure Data (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    extends CoordinateData Q s z where
  alignment : CartanMap.TangentAlignment g z (map Q s z)
  hasFDerivAt_reanchoredChartMap : HasFDerivAt (reanchoredChartMap Q s z)
    (alignment.toContinuousLinearEquiv : E →L[ℝ] E) (extChartAt I z z)

def Data.successor {Q : Interpretation g} {s : CartanChain.ChainState g} {z : M}
    (d : Data Q s z) : CartanChain.ChainState g :=
  ⟨z, map Q s z, d.alignment⟩

-- TARGET 6.1
theorem anchor_laws : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g),
  s.anchor ∈ Q.sourceAnchors → s.target ∈ Q.targetAnchors →
  s.anchor ∈ (germ Q s).source ∧ map Q s s.anchor = s.target
-- TARGET 6.2
theorem generic_map_eq : ∀ (s : CartanChain.ChainState g), map (generic g) s = s.map
-- TARGET 6.3
theorem vector_eq : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.v = Q.sourceNormal s.anchor z
-- TARGET 6.4
theorem successor_fields : ∀ (Q : Interpretation g) (s : CartanChain.ChainState g)
  (z : M) (d : Data Q s z), d.successor.anchor = z ∧
  d.successor.target = map Q s z ∧ z ∈ (germ Q s).source
-- TARGET 6.5
theorem eq_anchor_of_vector_eq_zero :
  ∀ (Q : Interpretation g) (s : CartanChain.ChainState g) (z : M)
    (d : Data Q s z), d.v = 0 → z = s.anchor
end CartanSuppliedDifferentialSuccessor
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedDifferentialSuccessor.lean
git diff --check
```

The Lean and diff commands must exit 0; the token scan must have no matches. Independently probe each named theorem at the frozen signature and inspect its axiom closure. A source-only gate assumes the accepted dependencies already have current oleans; the orchestrator builds those dependencies serially if needed.

Exact stop condition: All five targets and the displayed definitions compile. In particular, prove total forward-map equality for `generic`, and the stored-vector/source formulas for the supplied map. Stop blocked if a generic comparison can only be obtained by asserting equality of selected source sets; record the exact surviving map/domain goal.

