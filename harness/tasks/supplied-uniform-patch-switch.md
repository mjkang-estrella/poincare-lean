# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-uniform-patch-switch`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-uniform-patch-switch_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-uniform-patch-switch
Landed prerequisites on main: task 11 as `Poincare/Global/CartanSuppliedFinitePatchCover.lean` (namespace as specified; `PatchCover`, `QuantitativeCover`, `exists_patchCover`, `exists_quantitativeCover`); import and use it.

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


## 12. `Poincare/Global/CartanSuppliedUniformPatchSwitch.lean`

Namespace: `Poincare.CartanSuppliedUniformPatchSwitch`.

Imports: task 11. S2/S15 are already in its import graph.

Objective: close the quantitative comparison between different patch interpretations at the same geometric state, then combine it with H2 at a successor. This is an explicit new geometric obligation. The landed statements do not already provide `SwitchControl`.

`buffered_eventuallyEq` follows by comparing both patch maps to `s.map` using S2.`patch_germ_eventuallyEq_generic`, with membership supplied by the buffers. S15 explains the framed normal and inverse-normal comparisons behind that theorem. Their output is a neighborhood of `s.anchor` for this fixed state; it gives neither a radius uniform over states nor agreement around a different node.

The genuinely new target is `exists_switchControl`. It asks for a positive ball radius common to all finitely many patch pairs and all alignments at common buffer anchors. A prospective proof must compare the two fixed-host flows/normal inverses on common retained domains, control host-to-host frame changes, and obtain uniform comparison on compact intersections. S3.`exists_uniform_linear_bound` supplies a bound in each fixed pair of hosts. S15's ODE/frame proof is a template for local identification, not a theorem of uniform comparison. Taking a minimum of its pointwise neighborhoods is invalid. Neither equality of arbitrary total extensions nor agreement on entire source intersections is requested.

After this target, `transition_eqOn` is a quantitative consequence of S4 H2 and the switch bound. H1's predecessor lies in its operating core. `retained` puts the successor in the old buffers, while validity for the next label puts it in the new buffers. Apply H2 in the old interpretation, then the uniform same-state switch equality at `d.successor`. The displayed `/ 32` reserves more than the factor 4 used by this transition and the later two-edge comparisons. This task must not use task 16's global path independence to prove the switch bound.

```lean
namespace CartanSuppliedUniformPatchSwitch
open CartanSuppliedFinitePatchCover
structure SwitchControl (B : QuantitativeCover g) where
  radius : ℝ
  radius_pos : 0 < radius
  agreement : letI : MetricSpace M := g.toMetricSpace
    ∀ (a b : B.Label) (s : CartanChain.ChainState g),
      B.Buffered a s → B.Buffered b s →
      ball s.anchor radius ⊆ (germ (B.interp a) s).source ∩ (germ (B.interp b) s).source ∧
      EqOn (map (B.interp a) s) (map (B.interp b) s) (ball s.anchor radius)

structure System (g : ClosedSmoothRiemannianMetric 3 M) where
  cover : QuantitativeCover g
  switch : SwitchControl cover

def System.mesh (S : System g) : ℝ :=
  min S.cover.step (min S.cover.evaluation
    (min S.cover.retention S.switch.radius)) / 32

theorem buffered_eventuallyEq : ∀ (B : QuantitativeCover g)
    (a b : B.Label) (s : CartanChain.ChainState g),
  B.Buffered a s → B.Buffered b s →
  map (B.interp a) s =ᶠ[𝓝 s.anchor] map (B.interp b) s

theorem exists_switchControl : HasConstantSectionalCurvature3 g 1 →
  ∀ B : QuantitativeCover g, Nonempty (SwitchControl B)

theorem mesh_pos : ∀ S : System g, 0 < S.mesh

theorem transition_eqOn : ∀ (S : System g) (a b : S.cover.Label)
    (s : CartanChain.ChainState g) (z : M)
    (d : Data (S.cover.interp a) s z),
  S.cover.Valid a s → S.cover.Valid b d.successor →
  letI : MetricSpace M := g.toMetricSpace
  dist z s.anchor < 4 * S.mesh →
    ball z (4 * S.mesh) ⊆ (germ (S.cover.interp a) s).source ∩
      (germ (S.cover.interp b) d.successor).source ∧
    EqOn (map (S.cover.interp a) s) (map (S.cover.interp b) d.successor)
      (ball z (4 * S.mesh))
end CartanSuppliedUniformPatchSwitch
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedUniformPatchSwitch.lean
git diff --check
```

Exact stop condition: Prove all four targets with the displayed quantifier order and actual common-source ball. `buffered_eventuallyEq` alone is only a partial result. If uniform comparison cannot be established, record the exact resisting `SwitchControl.agreement` goal and strongest checked local statement; do not turn switch control into an extra hypothesis of final recognition.

