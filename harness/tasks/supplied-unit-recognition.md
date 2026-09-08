# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-unit-recognition`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-unit-recognition_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-unit-recognition
Landed prerequisites on main: tasks 11-18 (`CartanSuppliedFinitePatchCover.lean` (`Controlled`, `PatchCover`, `QuantitativeCover`, `exists_quantitativeCover`), `CartanSuppliedUniformPatchSwitch.lean` (`System`) + `CartanSuppliedBufferedPairAgreement.lean` (`exists_switchControl` unconditional), `CartanSuppliedPatchPolicy.lean`, `CartanSuppliedWholeCellRealization.lean` (`Realization`, `RootedRealization`, `exists_rootedRealization_with_wholeCellMesh`), `CartanSuppliedSubdivisionTransport.lean`, `CartanSuppliedHomotopyEndpoints.lean` (`endpoint_eq` under `SimplyConnectedSpace M`), `CartanSuppliedTerminalTransport.lean`, `CartanSuppliedRestrictedDevelopment.lean` (`RestrictedAtlas`, `terminalState`, `terminalGerm`, `development`, `development_eqOn_terminal_neighborhood`, `exists_restrictedAtlas`, `isLocalHomeomorph_diagonal`, `isLocalHomeomorph_development`)). Also landed: `ConnectionInstanceNaturality.exists_controlled_recognition_reduction'` (returns a finite sub-atlas `charts` with uniform ball sources, `hs : IsManifold I ∞ M` for it, and the recognition transfer to the original instance), `RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment`, `SphereTheorem.poincareConjecture_of_hamiltonConvergence_of_unitRecognition`, and `CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement`. Import and use them; do not re-prove landed theorems. Notes: `Controlled` is defined in `CartanSuppliedFinitePatchCover` as `charts.atlas.Finite ∧ (letI := d; ∃ δ > 0, ∀ x, ball x δ ⊆ (charts.chartAt x).source)`; the reduction theorem states its conclusion under `letI : MetricSpace M := d.replaceTopology hd.symm`, so match that metric when building `Controlled`. This is the FINAL task of the plan: if all five targets are proved, the reserved theorem `Poincare.poincare_conjecture` must STILL NOT be declared (the Hamilton premise remains open); report exactly what was proved.

## Two necessary qualifications

“One patch per chart” is not a consequence of S6 or S7. Starting with one arbitrarily chosen patch at a representative of each member of a finite atlas need not cover the other points of those charts. The executable contract below instead constructs a finite refinement: choose a patch centered at every point, then a finite subcover of smaller open anchor neighborhoods. On the controlled source, every host `chartAt E (center i)` still belongs to the given finite atlas, but a host chart may be used by several patches. On the sphere, use the existing sphere instance and take a finite patch subcover in the same way. If exactly one patch per original chart is a frozen requirement, stop at that coverage gap; do not assert `ball_cover` from S7. This qualification follows from the exact `exists_patch` and `Patch.anchors` types in S6.

Likewise, H1/H2 is uniform on compact anchor sets, not on their whole surrounding open patch. Use an operating core `core i` and a larger compact buffer with `core i ⊆ interior (buffer i) ⊆ buffer i ⊆ anchors`. The policy retains a label while both current anchors remain in its operating cores; when either leaves, it switches. This is the precise quantitative meaning of re-anchoring within a patch until leaving its operating anchor set. Waiting until the boundary of the full open `Patch.anchors` would have no uniform H1 justification. S3/S4 also only retain the target in an open set unless the stronger `exists_uniform_domain_radius_into_open` clause is used.

A policy of type `ℕ → ChainState → Interpretation` cannot read a previous label from `ChainState`. Task 13 gives it an external preferred-label schedule, constructed together with one chain by recursion. For off-history states it has a covering fallback, so `StepAvailable` still holds for every state anchored at the node, as S5 requires. No patch label is added to geometric state equality.


## Shared dispatch contract

Task 11 starts at the base above. For task `n > 11`, freeze a new exact commit containing its accepted prerequisites before dispatch; this report does not invent future hashes. Each task owns only its named new file. All existing Lean files, `Poincare.lean`, other tasks' files, audit wiring and source definitions are forbidden. Dependencies are `11 → 12 → 13 → 14 → 15 → 16`, with `17` using 13–15, `18` using 16–17, and `19` using 11–18 plus S7/S13/S14. A serial 11–19 dispatch is valid.

Each section specifies imports, proof templates, new work, and its stop condition. The common gate below means the exact command printed in that section plus a no-match prohibited-token scan and `git diff --check`. Require exit 0 for Lean and the diff check; require no matches, normally exit 1, for the scan. Independently probe every named target at its displayed signature and inspect its axiom closure. Only the standard logical dependencies are acceptable. Build accepted dependencies serially if their oleans are missing. These are worker gates, not acceptance or merge authority; root build/audits remain the orchestrator's integration checkpoint.

The Lean blocks are the complete proposed definitions and target signatures. A target has no proof body here. The reproducible probe converts each `theorem name : P` into a definition whose body is the proposition `P`; binder-bearing signatures are preserved. `autoImplicit false` prevents a misspelled interface from becoming an invented variable. The broad import envelope is only for the combined scratch probe. Each new implementation file uses the narrower imports listed in its task and the relevant common notation/variables.

```lean
import Poincare.Global.FixedChartMappedGeodesicAssembly
import Poincare.Global.CartanSuppliedReachableChain
import Poincare.Global.CartanTwoNeighborhoodDevelopment
import Poincare.Global.ConnectionInstanceNaturality

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain
```


## 19. `Poincare/Global/CartanSuppliedUnitRecognition.lean`

Namespace: `Poincare.CartanSuppliedUnitRecognition`.

Imports: task 18, `Poincare.Global.ConnectionInstanceNaturality`, `Poincare.Global.CartanTwoNeighborhoodDevelopment`.

Objective: discharge the unchanged developing-map and unit-recognition interfaces and expose the universal recognition theorem consumed by the Hamilton reduction.

For `controlled_globalLocalDevelopment`, introduce a metric `g` and its unit-curvature proof. Construct task 11's quantitative cover, task 12's switch control, S9's rooted skeleton, task 14's realization, and task 18's developing map. The supplied geometry can be stronger than needed and work for arbitrary chart instances; the public adapter still explicitly accepts the controlled instance with its compatible auxiliary metric. Its auxiliary chart-control distance `d` and the geometric chain distance `g.toMetricSpace` are distinct parameters. No equality of these distances is assumed. S4 uses the latter.

Apply S13.`RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment` for `controlled_unitRecognition`. The covering and sphere topology require no new proof and the conclusion is S14's literal `UnitConstantCurvatureSphereRecognition3`, not a renamed interface.

For `unitRecognition` on the original instance, first introduce its `g` and unit-curvature proof and use `d := g.toMetricSpace`, whose topology agrees by S17. Apply S7.`ConnectionInstanceNaturality.exists_controlled_recognition_reduction'`. It returns `charts`, a positive chart-source radius, atlas finiteness, a manifold instance `hs`, and the recognition implication back to the original instance. Install exactly `charts` and `hs`, invoke `controlled_unitRecognition` with the returned finite-atlas/ball clauses and compatible auxiliary metric, and apply the returned implication to obtain original-instance recognition; then evaluate it on the original `g`. This ordering avoids requiring a Riemannian metric before introducing the recognition input. The reduction uses `replaceTopology`; retain its exact instance when passing the ball clause. It does not require proving an equality between the transported metric distance and `d`.

The universal target reuses S14's existing `UniversalUnitConstantCurvatureSphereRecognitionStatement`. Its universe `u` and all nine binders match the displayed final Hamilton target. Apply S14.`poincareConjecture_of_hamiltonConvergence_of_unitRecognition` with this universal proof. The last target still assumes Hamilton convergence; it is not the reserved unconditional `Poincare.poincare_conjecture`. S14.`globalLocalDevelopment_of_two_neighborhoods` supplies the assembly pattern only: none of its legacy generic H1/H2 premises is asserted by this new route.

```lean
namespace CartanSuppliedUnitRecognition
open CartanSuppliedFinitePatchCover
variable [SecondCountableTopology M] [SimplyConnectedSpace M]

theorem controlled_globalLocalDevelopment : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M)

theorem controlled_unitRecognition : ∀ (d : MetricSpace M),
  d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace M) →
  Controlled inst d → UnitConstantCurvatureSphereRecognition3 M

theorem unitRecognition : UnitConstantCurvatureSphereRecognition3 M

theorem universal_unitRecognition :
  CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement.{u}

theorem poincare_of_hamiltonConvergence :
  (∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonConvergencePinchedLimit3 N) → PoincareConjecture.{u}
end CartanSuppliedUnitRecognition
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUnitRecognition.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedUnitRecognition.lean
git diff --check
```

Exact stop condition: All five targets compile with no extra patch-cover, switch, mesh, homotopy, atlas-compatibility or recognition premise. The final theorem may retain exactly the displayed Hamilton premise. Stop with the exact controlled-instance/metric/curvature transport type if adaptation fails; do not change the frozen recognition statement or claim unconditional Poincare completion.

```lean
end Poincare
```

