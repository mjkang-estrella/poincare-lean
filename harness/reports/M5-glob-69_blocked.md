# M5-glob-69 blocked: total preferred-chart extensions obstruct H2

Date: 2026-09-07. Base: `d08f4a5252b0d14788d4558afb669b6f3ed8d19d`.
Worktree: `/private/tmp/poincare-workers/M5-glob-69`.
Branch: `worker/M5-glob-69`.
Proof commits: `df566640`, followed by `8d1b76a7`.

The frozen theorem was NOT proved or changed. I stopped under Worker
Contract hard rule 2 because I believe the universally quantified statement
is false for the allowed arbitrary preferred charts and their total
extensions. This report supplies a checked necessary condition and a checked
conditional obstruction. It does NOT claim a fully instantiated Lean
counterexample on a recharted sphere.

The work is in the single new module
`Poincare/Global/SuccessorEqualityRadiusPersistence.lean`. No existing Lean
file, root import, mission, task, or ledger was changed. `HANDOFF.md` records
this worker result, without marking it accepted.

The failure appears before target-anchor motion: even at one fixed pair
`(x,p)`, H2 would require one output radius for all nearby successor anchors.
That is stronger than the existing datum-dependent equality neighborhood.

The key source facts are:

- `ActualSuccessorEqualityRadiusAdmissible` asks for `EqOn` on the WHOLE
  `Metric.ball z radius`. It does not intersect that ball with either germ's
  partial-homeomorphism source.
- `CartanChain.ChainState.germ` is an `OpenPartialHomeomorph`. Its coercion in
  `EqOn` is its total function, not an equivalence class of germs.
- `CartanMap.openPartialHomeomorph` begins with `(chartAt E anchor).trans`.
  Thus its total function factors through the total preferred chart even
  outside the chart's source. `CartanMap.lean` explicitly documents its
  off-source total extension as arbitrary.
- Mathlib `ChartedSpace` stores a preferred chart at each point, membership
  of the point in its source, and atlas membership. It supplies no common
  source neighborhood for nearby preferred charts. `OpenPartialHomeomorph`
  requires continuity only on source and target. Smooth compatibility of
  charts is likewise a condition on their honest overlap domains.

The following are the new checked theorems, all in namespace
`Poincare.SuccessorEqualityRadiusPersistence`:

1. `successor_germ_eq_of_chartAt_eq`: a successor's total map identifies any
   two points identified by the total chart at its anchor.
2. `injOn_chartAt_of_eqOn_successor`: equality with a predecessor on `U`
   forces chart injectivity on `predecessor.germ.source ∩ U`.
3. `exists_open_nhds_injOn_chartAt_of_constantCurvature_of_admissible`:
   curvature plus a positive admissible radius at fixed `(x,p)` implies
   `∃ V, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V, InjOn (chartAt E z) V`.
   The proof obtains actual successor data from the already verified
   curvature-only fixed-anchor producer, shrinks a ball inside the fixed
   predecessor's source, and uses the triangle inequality to put every pair
   of evaluation points in the required successor-centered ball. It keeps
   the target anchor and alignment fixed throughout.
4. `preferredChartCollisionAccumulation_of_shrinking_constant_extensions`:
   at a nonisolated anchor, constant total chart extensions outside balls
   `ball z (dist z x / 2)` produce the concrete collision obstruction below.
5. `not_admissible_of_constantCurvature_of_preferredChartCollisionAccumulation`:
   that obstruction excludes every positive admissible radius at `(x,p)`.
6. `not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation`:
   the same obstruction excludes the frozen persistence conclusion.

The exact obstruction, a geometric `Prop`, is:

```lean
def PreferredChartCollisionAccumulation (x : M) : Prop :=
  ∀ V : Set M, V ∈ 𝓝 x →
    ∃ z ∈ V, ∃ a ∈ V, ∃ b ∈ V,
      a ≠ b ∧ chartAt E z a = chartAt E z b
```

The sixth theorem has the checked type:

```lean
theorem not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (hcollision : PreferredChartCollisionAccumulation x) :
    ¬ DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence g
```

Here is the mathematical counterexample construction that needs independent
review and a concrete Lean realization. On the round three-sphere, retain
the usual smooth structure and intrinsic round metric. Fix `x`. At every
`z ≠ x`, choose a smooth coordinate chart restricted to a source contained in
`ball z (dist z x / 2)` and give its total forward function one constant value
outside that source. Keep any ordinary chart at `x`. Restriction and changing
the forward function outside its source leave each local chart and its
smooth overlap maps unchanged. These charts can be included in the atlas,
and `ChartedSpace` permits their pointwise selection as preferred charts.
Compactness, connectedness, and intrinsic constant curvature are unchanged.

Every neighborhood of `x` then contains some `z ≠ x` and another point `b ≠ x`
with `dist b x < dist z x / 4`. Both `x` and `b` lie outside the source of the
preferred chart at `z`; that total chart sends them to the same constant.
This is exactly the fourth theorem's checked collision criterion. The fifth
and sixth theorems show why those collisions are incompatible with H2,
regardless of how exponential-map values were extended.

The metric on the recharted sphere and its curvature have NOT been
constructed in this Lean file. The counterexample paragraph is mathematical
analysis, not a claimed theorem `¬ ∀ g, ...`. The checked result is the
conditional obstruction with the hypotheses displayed above. In particular,
merely failing to find a continuity theorem was not taken as proof of
unprovability.

The requested flow route was inspected before this obstruction was found.
All named input declarations passed `#check`, with the correct qualification
`GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds`
and the same namespace for both PL-flow declarations. The initial probe is
`/tmp/M5-glob-69-types.lean`, with output
`/tmp/M5-glob-69-types.log`, exit 0. The fixed-chart PL flow genuinely supports
moving initial positions. Existing
`CartanFixedChartGenericInverseEndpointODETailOverlapReduction.lean` also
proves automatic overlap continuation once preferred trajectory velocity
budgets hold. The issue is not a missing signed Christoffel law or ODE
uniqueness proof. Those arguments control honest chart domains; they cannot
force injectivity of unconstrained off-source total chart extensions.

No `target_of_<resisting>` theorem was added: this job invokes the explicit
wrong-statement stop rule, not stop condition (b) for a valid smaller proof
objective. Collision accumulation is an obstruction, not a sufficient
premise for the target. Deriving the target from contradictory curvature and
collision hypotheses would be a vacuous wrapper and was deliberately avoided.

Verification commands and actual results:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/SuccessorEqualityRadiusPersistence.lean
```

Final direct check: exit 0, no output. Log:
`/tmp/M5-glob-69-check-02.log`. The first direct check also exited 0 and
reported only an unused-section-variable warning; both affected declarations
now explicitly omit that variable. No failed Lean proof attempt was hidden.

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.SuccessorEqualityRadiusPersistence
```

Exit 0. Final module/build lines, omitting replayed dependency warnings:

```text
✔ [3579/3579] Built Poincare.Global.SuccessorEqualityRadiusPersistence (2.6s)
Build completed successfully (3579 jobs).
```

Full log: `/tmp/M5-glob-69-build-final.log`. The new module emitted no warning.
The earlier verified proof commit also built successfully, 3579 jobs.

```sh
grep -nE "\b(sorry|admit)\b|^\s*axiom\b|native_decide" Poincare/Global/SuccessorEqualityRadiusPersistence.lean
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/SuccessorEqualityRadiusPersistence.lean
git diff --check
```

Both scans: exit 1 with empty stdout and stderr, meaning no matches.
Diff check: exit 0 with empty stdout and stderr.

`/tmp/ax.lean` imports the new module and prints the axioms of all six new
theorems. Exact command:

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/ax.lean
```

Exit 0. Complete output follows:

```text
'Poincare.SuccessorEqualityRadiusPersistence.successor_germ_eq_of_chartAt_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.SuccessorEqualityRadiusPersistence.injOn_chartAt_of_eqOn_successor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.SuccessorEqualityRadiusPersistence.exists_open_nhds_injOn_chartAt_of_constantCurvature_of_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.SuccessorEqualityRadiusPersistence.preferredChartCollisionAccumulation_of_shrinking_constant_extensions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.SuccessorEqualityRadiusPersistence.not_admissible_of_constantCurvature_of_preferredChartCollisionAccumulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.SuccessorEqualityRadiusPersistence.not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The committed diff is durable proof evidence:
`git diff d08f4a52..8d1b76a7 -- Poincare/Global/SuccessorEqualityRadiusPersistence.lean`.

Exact next action: construct the recharted round sphere described above,
prove the displayed shrinking-constant-extension hypothesis for its preferred
charts, and apply the checked collision and non-persistence theorems. If the
orchestrator confirms the statement defect, it must review the frozen
contract and its downstream consumer together. This worker did not weaken
H2 to source-restricted equality or replace its selected germs.
