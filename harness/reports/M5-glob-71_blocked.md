# M5-glob-71 blocked: the frozen generic joint-regularity statement is false

Date: 2026-09-07. Branch: `worker/M5-glob-71`.
Base and proof-check HEAD: `d08f4a5252b0d14788d4558afb669b6f3ed8d19d`.

## Outcome

Stopped under Worker Contract hard rule 2. Lean checks a concrete smooth
Riemannian metric for which `CartanSourceExponential.GenericJointRegularity`
is false. The obstruction occurs in its first clause, joint source openness,
before any ODE comparison or continuity argument.

The complete checked counterexample is embedded below so this report is
self-contained. Only this report is added to the repository. The frozen
positive theorem has not been weakened or replaced, and
`Poincare/Global/ExponentialChartJointRegularity.lean` has not been created.
This is the contract's invalid-statement stop, rather than a partial-positive
result with a `target_of_<resisting>` theorem. The latter would conceal a
refuted premise here.

## Exact obstruction

The definition's instance context is:

```text
{M : Type u} [TopologicalSpace M]
[ChartedSpace (ClosedSmoothModel 3) M]
[IsManifold (closedSmoothModelWithCorners 3) ∞ M]
```

`ClosedSmoothRiemannianMetric` is an abbreviation for a smooth tangent-bundle
metric; it does not itself require `CompactSpace`. The frozen request says
to use the definition's instance context. The counterexample below uses
`M = ClosedSmoothModel 3`, with its usual Euclidean topology and a different
valid preferred-chart choice.

For every `g`, unfolding the actual generic family gives

```text
z ∈ ((genericFamily g).normal x).source
  → z ∈ (chartAt E x).source.
```

Its diagonal always belongs to its source. Consequently, joint source
openness forces the concrete necessary condition

```text
∀ x : M, {y : M | x ∈ (chartAt E y).source} ∈ 𝓝 x.
```

`preferred_chart_source_mem_nhds_of_joint` proves this using the continuous
map `y ↦ (y, x)` and the first component of the source intersection.

Choose the identity chart on all of `E` at `0`. At every nonzero anchor,
choose the identity chart restricted to `E \ {0}`. Every chart contains its
anchor. All chart transitions are identity restrictions, so this is a smooth
atlas. Equip it with the constant Euclidean inner product. The proof below
constructs the smooth metric explicitly, including its smoothness in this
atlas; metric existence is not an extra assumption.

The displayed necessary set at `x = 0` is exactly `{0}`, which is not a
neighborhood of `0` in `E`. Thus Lean proves both

```text
¬ GenericJointRegularity flatMetric
¬ (∀ g : ClosedSmoothRiemannianMetric 3 E, GenericJointRegularity g)
```

with this charted-space instance. No behavior of the chosen Picard–Lindelöf
flow, cutoff, inverse-function neighborhood, or exponential value is needed
for the contradiction.

Adding compactness would change the exact instance context checked here.
The same source-exclusion construction is available mathematically on a
positive-dimensional compact manifold: keep a chart at one point and remove
that point from every other preferred chart source. That compact variant is
not formalized in this report.

## Why the proposed route cannot prove this target

`ChartedSpace` requires only an atlas, a chart at each point, membership of
the point in that chart, and membership of the chart in the atlas.
`IsManifold` checks transition smoothness. Neither condition requires nearby
preferred charts to contain a fixed point.

The ODE transport lemmas require overlap and cutoff-one neighborhoods for
fixed charts. ODE uniqueness on such an overlap cannot insert a point into
an excluded preferred-chart source. A smooth family produced in a fixed
chart also does not make the domains of the already chosen generic family
jointly open. Independently, Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`
chooses an open neighborhood through `Classical.choose`; it supplies
per-function inverse data, not joint regularity of the selected domains.
The counterexample already settles the task without relying on this second
choice issue.

All supplied tool names were probed successfully in the current Lean cache:

- `GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc`
- `GeodesicTransport.exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn`
- `GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds`
- `GeodesicTransport.chartTransitionState_eventually_solves_of_initial_nhds`
- `GeodesicTransport.chartLeviCivita_eventuallyEq_closed`
- `GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero`
- `GeodesicTransport.expAt_injective_open_image_smallBall`
- `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`
- `ODE_solution_unique_of_mem_Icc`

The declaration types and axiom checks are in
`/tmp/M5-glob-71-evidence/probe-1.log`, produced by `probe.lean` in that directory.
The theorem names from `ChartTransitionGeodesicMap.lean` are in namespace
`Poincare.GeodesicTransport`.

Relevant source locations at the base commit:

- `Poincare/Global/CartanSourceExponentialFamily.lean:80`: the four clauses.
- `Poincare/Global/CartanSourceExponentialFamily.lean:91`: the generic source intersection.
- `Poincare/Global/RiemannianContext.lean:44`: the metric abbreviation.
- `.lake/packages/mathlib/Mathlib/Geometry/Manifold/ChartedSpace.lean:139`: charted-space fields.
- `Poincare/Global/ExponentialLocalHomeo.lean:417`: the chosen inverse-function chart.
- `.lake/packages/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean:113`: inverse-function neighborhood selection.

## Verification

Commands and actual results:

```text
LEAN_NUM_THREADS=1 lake env lean /tmp/M5-glob-71-evidence/probe.lean
exit 0; every supplied #check succeeds; both obstruction proofs have the allowed axioms.

LEAN_NUM_THREADS=1 lake env lean /tmp/M5-glob-71-evidence/counterexample.lean
exit 0; no warnings or errors; axiom output reproduced below.

LEAN_NUM_THREADS=1 lake build Poincare.Global.CartanSourceExponentialFamily
exit 0
Build completed successfully (3357 jobs).

rg -n '\b(sorry|admit|axiom)\b|native_decide' /tmp/M5-glob-71-evidence/counterexample.lean
exit 1; empty output, as required for no matches.

LEAN_NUM_THREADS=1 lake env lean /tmp/M5-glob-71-evidence/recheck.lean
exit 0; extracted verbatim from this report; identical allowed-axiom output.

git diff --check
git diff --cached --check
exit 0; empty output.
```

The build above validates the existing context module. The requested
`lake build Poincare.Global.ExponentialChartJointRegularity` gate is not
claimed: hard rule 2 stopped production of that positive-theorem module.
Full context-build output is retained in
`/tmp/M5-glob-71-evidence/build-context.log`; it replays existing upstream
warnings. Compiler attempts are retained as `counterexample-1.log` through
`counterexample-8.log` in the same directory. Attempts 2 through 7 failed
while constructing the metric, chiefly on tangent-fiber instance inference
and the hom-bundle trivialization calculation. Attempt 1 proved the atlas
and the obstruction conditional on a metric. Attempt 8 includes the explicit
metric and succeeds. No failed attempt is presented as verified code.

## Reproducible Lean evidence

Extract this single Lean block to `/tmp/M5-glob-71-evidence/recheck.lean`
and run `LEAN_NUM_THREADS=1 lake env lean` on it from the base checkout.
It is the exact source of the successful final counterexample check.

```lean
import Poincare.Global.CartanSourceExponentialFamily
import Poincare.Global.ChartTransitionGeodesicMap
open Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ExponentialChartJointRegularity
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
open CartanSourceExponential

theorem preferred_chart_source_mem_nhds_of_joint
    (g : ClosedSmoothRiemannianMetric 3 M) (h : GenericJointRegularity g) (x : M) :
    {y : M | x ∈ (chartAt E y).source} ∈ 𝓝 x := by
  have hdiag : (x, x) ∈ (genericFamily g).sourceLocus :=
    (genericFamily g).anchor_mem_source x
  have hn := h.isOpen_sourceLocus.mem_nhds hdiag
  have hc : Continuous (fun y : M => (y, x)) := continuous_id.prodMk continuous_const
  have hp := hc.continuousAt.preimage_mem_nhds hn
  apply Filter.mem_of_superset hp
  intro y hy
  change x ∈ (chartAt E y).source ∩ _ at hy
  exact hy.1

theorem not_joint_of_excluded_preferred_chart_source
    (g : ClosedSmoothRiemannianMetric 3 M) {x : M}
    (hx : ¬ IsOpen ({x} : Set M))
    (hexclude : ∀ y : M, y ≠ x → x ∉ (chartAt E y).source) :
    ¬ GenericJointRegularity g := by
  intro h
  have hn := preferred_chart_source_mem_nhds_of_joint g h x
  have hs : ({x} : Set M) ∈ 𝓝 x := by
    apply Filter.mem_of_superset hn
    intro y hy
    by_contra hne
    exact hexclude y hne hy
  apply hx
  rw [isOpen_iff_mem_nhds]
  intro y hy
  simpa only [Set.mem_singleton_iff.mp hy] using hs
end Poincare.ExponentialChartJointRegularity

noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ExponentialChartJointRegularity.Counterexample
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

def puncturedChart (x : E) : OpenPartialHomeomorph E E :=
  (OpenPartialHomeomorph.refl E).restrOpen
    (if x = 0 then Set.univ else {0}ᶜ)
    (by split <;> simp)

@[reducible] def puncturedChartedSpace : ChartedSpace E E where
  atlas := Set.range puncturedChart
  chartAt := puncturedChart
  mem_chart_source x := by
    simp only [puncturedChart, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_univ, true_and]
    split <;> simp_all
  chart_mem_atlas x := ⟨x, rfl⟩

local instance : ChartedSpace E E := puncturedChartedSpace

instance punctured_isManifold : IsManifold I ∞ E := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  change ContDiffOn ℝ ∞ (fun z : E => z) _
  exact contDiffOn_id

theorem not_genericJointRegularity (g : ClosedSmoothRiemannianMetric 3 E) :
    ¬ CartanSourceExponential.GenericJointRegularity g := by
  apply not_joint_of_excluded_preferred_chart_source g (not_isOpen_singleton (0 : E))
  intro y hy
  change 0 ∉ (puncturedChart y).source
  simp [puncturedChart, hy]

open Bundle Bornology
def flatInner : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
set_option backward.isDefEq.respectTransparency false in
def flatMetric : ClosedSmoothRiemannianMetric 3 E where
  inner _ := flatInner
  symm _ v w := @real_inner_comm E _ _ w v
  pos _ v hv := (@real_inner_self_pos E _ _ v).2 hv
  isVonNBounded _ := by
    change IsVonNBounded ℝ {v : E | inner ℝ v v < 1}
    have hball : Metric.ball (0 : E) 1 = {v : E | inner ℝ v v < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← hball]
    exact NormedSpace.isVonNBounded_ball ℝ E 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have hconst : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun _ : E => flatInner) x := contMDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
    have hsymm : (trivializationAt E (TangentSpace I) x).symmL ℝ y =
        ContinuousLinearMap.id ℝ E := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hy,
        tangentBundleCore_coordChange_achart]
      simp only [extChartAt_coe, extChartAt_coe_symm]
      change fderivWithin ℝ (id : E → E) (Set.range (id : E → E)) y = _
      rw [Set.range_id]
      exact fderivWithin_id uniqueDiffWithinAt_univ
    rw [hom_trivializationAt_apply]
    ext v w
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      hsymm]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem]
    · rw [hom_trivializationAt_apply]
      simp [ContinuousLinearMap.inCoordinates, hsymm]
      rfl
    · simpa using hy

theorem flatMetric_not_genericJointRegularity :
    ¬ CartanSourceExponential.GenericJointRegularity flatMetric :=
  not_genericJointRegularity flatMetric

theorem not_forall_genericJointRegularity :
    ¬ (∀ g : ClosedSmoothRiemannianMetric 3 E,
      CartanSourceExponential.GenericJointRegularity g) := by
  intro h
  exact flatMetric_not_genericJointRegularity (h flatMetric)

#print axioms Poincare.ExponentialChartJointRegularity.preferred_chart_source_mem_nhds_of_joint
#print axioms Poincare.ExponentialChartJointRegularity.not_joint_of_excluded_preferred_chart_source
#print axioms punctured_isManifold
#print axioms not_genericJointRegularity
#print axioms flatMetric_not_genericJointRegularity
#print axioms not_forall_genericJointRegularity
end Poincare.ExponentialChartJointRegularity.Counterexample
```

Actual final output:

```text
'Poincare.ExponentialChartJointRegularity.preferred_chart_source_mem_nhds_of_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ExponentialChartJointRegularity.not_joint_of_excluded_preferred_chart_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ExponentialChartJointRegularity.Counterexample.punctured_isManifold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ExponentialChartJointRegularity.Counterexample.not_genericJointRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ExponentialChartJointRegularity.Counterexample.flatMetric_not_genericJointRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ExponentialChartJointRegularity.Counterexample.not_forall_genericJointRegularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Handoff

The next action is to review the source-membership premise in
`CartanSourceExponential.LocalFamily.ControlsGenericNormal` against the
counterexample above before freezing a replacement task. A replacement
must address the selected chart domains explicitly, or formulate the
construction using compatible supplied local families and tangent-bundle
coordinates. Smooth geodesic dependence alone cannot supply the frozen
generic-family claim. No H1/H2 obligation is marked closed by this report.
