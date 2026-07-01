Read harness/worker_contract.md first and obey it strictly.

# Task M0-statement: Manifold-level statement of the Poincaré Conjecture

Create NEW file `Poincare/Global/Statement.lean` and add `import Poincare.Global.Statement` to `Poincare.lean`. This is the global statement layer this project structurally lacks (the existing single-chart model cannot express it).

Deliverable: compile-verified DEFINITIONS (no theorems required, no sorry allowed anywhere):

1. `def PoincareConjecture : Prop` — faithfully: every topological space M that is Hausdorff, second-countable, equipped with a smooth manifold structure modelled on `EuclideanSpace ℝ (Fin 3)` (use Mathlib: `IsManifold (𝓡 3) ⊤ M` or the appropriate current spelling — check `.lake/packages/mathlib` for the current API, e.g. `Mathlib/Geometry/Manifold/IsManifold/Basic.lean`), compact, connected, and simply connected (`SimplyConnectedSpace M`), is homeomorphic to the 3-sphere: `Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)`.
   - Quantify over the manifold via universe-polymorphic `∀ (M : Type u) [inst : ...]`.
   - CRITICAL vacuity check: the definition must unfold to the genuine mathematical statement. No auxiliary structures with Prop fields. An auditor will attempt to prove it with `trivial`-style instantiation; it must not be trivially provable NOR trivially false by type error.

2. `def SmoothClosed3Manifold`-style helper class or predicate bundling the hypotheses, only if it keeps things readable — otherwise inline.

3. Sanity checks in the same file (these ARE required to compile):
   - `example : PoincareConjecture ↔ (∀ ...)` restating it definitionally (`Iff.rfl`) to prove non-opacity.
   - A `#check` that `Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1` carries the expected charted-space instances from Mathlib (the sphere smooth structure exists in `Mathlib/Geometry/Manifold/Instances/Sphere.lean`).

4. `def RicciFlowProgramSkeleton` — SKIP for now (scope discipline): do NOT attempt to define Ricci flow on manifolds in this task.

Explore Mathlib under `.lake/packages/mathlib/Mathlib/Geometry/Manifold/` and `Mathlib/Topology/Homotopy/` (`SimplyConnectedSpace` is in `Mathlib/Topology/Homotopy/Contractible.lean` or nearby — verify) to get exact current names. Build with `lake build Poincare.Global.Statement` (first build of new imports may take several minutes — do not kill it). Commit when green.
