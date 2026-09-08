# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/supplied-patch-policy`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file as named below; no vacuous definitions; report actual command output; commit each verified lemma on the
branch; report to `harness/reports/supplied-patch-policy_{done|blocked}.md`. Stop conditions as in `harness/tasks/M5-glob-69.md`.
Read first: `harness/reports/parametrization-plan-3.md` (the whole specification; its "Verified source index",
"Two necessary qualifications", and "Shared dispatch contract" apply to you and are reproduced below; your task is
reproduced verbatim), then the cited landed modules.
# Task supplied-patch-policy
Landed prerequisites on main: task 11 (`CartanSuppliedFinitePatchCover.lean`), task 12 (`CartanSuppliedUniformPatchSwitch.lean` with its remainder proved in `CartanSuppliedBufferedPairAgreement.lean`: `CartanSuppliedUniformPatchSwitch.exists_switchControl` is unconditional under curvature 1). Import and use them; do not re-prove landed theorems.

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


## 13. `Poincare/Global/CartanSuppliedPatchPolicy.lean`

Namespace: `Poincare.CartanSuppliedPatchPolicy`.

Imports: task 12, `Poincare.Global.CartanSuppliedReachableChain`.

Objective: define the actual state-dependent policy and realize its sticky version. `fallback` selects the pair of cores containing the current source anchor and current sphere target, using the two `covers` witnesses. `select` keeps the preferred pair if both memberships hold, and otherwise uses that fallback. No continuity of this selection is claimed.

For any externally fixed schedule `a`, `policy B a n s` is exactly `B.interp (select B (a n) s)`. `select_valid` gives both core memberships, hence both buffer memberships. If the next-node distance is below `S.mesh`, it is below `B.step`; apply `B.h1` to the actual `s.alignment`, using `s.anchor = nodes n`. This proves S5.`StepAvailable` for all node-anchored states, including every possible target. H1 does not need to keep the next target in the same operating core, because the next policy call selects again.

For `exists_sticky_chain`, recurse jointly on the reached state and preferred pair. Start with `fallback initial`; choose a datum in the selected interpretation; pass its successor and the selected pair to the next recursion step. The resulting schedule satisfies `Sticky`, and the policy's off-history fallback makes it a total policy with the stated type. This is S5.`exists_reachableChain`'s dependent recursion template with one external recursion component. It is not circular choice of a policy from an already assumed realized chain.

For `chains_eq`, induct on equal prefix states. Task 12 switch control gives predecessor-map equality on the ball at that common anchor. The next node is inside that ball since the mesh is smaller than the switch radius. Restrict to an open neighborhood of the next node and apply S2.`successor_eq_of_eqOn_open`. The resulting open agreements discharge S5.`state_eq_of_open_agreement`; S5.`state_eq` handles witness choice for an identical policy. Its hypotheses do not directly compare different node sequences.

```lean
namespace CartanSuppliedPatchPolicy
open CartanSuppliedFinitePatchCover CartanSuppliedUniformPatchSwitch

def fallback (B : QuantitativeCover g) (s : CartanChain.ChainState g) : B.Label :=
  (B.source.pick s.anchor, B.target.pick s.target)

def select (B : QuantitativeCover g) (preferred : B.Label)
    (s : CartanChain.ChainState g) : B.Label :=
  @ite _ (B.Valid preferred s) (Classical.propDecidable _) preferred (fallback B s)

def policy (B : QuantitativeCover g) (preferred : ℕ → B.Label) :
    ℕ → CartanChain.ChainState g → Interpretation g :=
  fun n s => B.interp (select B (preferred n) s)

def Sticky (B : QuantitativeCover g) (preferred : ℕ → B.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (c : ReachableChain (policy B preferred) nodes initial) : Prop :=
  ∀ n, preferred (n + 1) = select B (preferred n) (c.state n)

theorem select_valid : ∀ (B : QuantitativeCover g) (a : B.Label)
  (s : CartanChain.ChainState g), B.Valid (select B a s) s

theorem stepAvailable : ∀ (S : System g) (a : ℕ → S.cover.Label) (nodes : ℕ → M),
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  StepAvailable (policy S.cover a) nodes

theorem exists_sticky_chain : ∀ (S : System g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g), initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∃ (a : ℕ → S.cover.Label)
    (c : ReachableChain (policy S.cover a) nodes initial),
    a 0 = fallback S.cover initial ∧ Sticky S.cover a nodes initial c

theorem chains_eq : ∀ (S : System g) (a b : ℕ → S.cover.Label)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g),
  initial.anchor = nodes 0 →
  (letI : MetricSpace M := g.toMetricSpace
   ∀ n, dist (nodes (n + 1)) (nodes n) < S.mesh) →
  ∀ (c : ReachableChain (policy S.cover a) nodes initial)
    (d : ReachableChain (policy S.cover b) nodes initial), ∀ n, c.state n = d.state n
end CartanSuppliedPatchPolicy
```

Gate:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/CartanSuppliedPatchPolicy.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/CartanSuppliedPatchPolicy.lean
git diff --check
```

Exact stop condition: All four targets compile. Require a schedule with the displayed retention recurrence and a policy valid on off-history states. A recursion requiring membership in a previously selected target core forever, or agreement only at the previous anchor when comparing next-step data, is failure.

