# Core existence construction, 2026-09-29

Central objective: `Poincare.UniversalHamiltonConvergenceStatement`.
It is equivalent to universal positive-Einstein metric existence. The separate
`Poincare.ExistsSmoothabilitySmoothManifoldStatement` remains necessary for the
frozen topological target. Neither complete core assumption is discharged.

## Exact completion boundary

The current proved consumer is
`poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`
in `Poincare/Global/HamiltonPoincareReduction.lean`. It takes exactly the two
universal statements above and returns `PoincareConjectureStatement`.
Cartan unit-curvature recognition is already proved.

Smoothability means, for every compact Hausdorff simply-connected topological
three-manifold M, selecting a possibly different compatible charted-space
instance and proving `IsManifold (modelWithCornersSelf ℝ E3) ∞ M`. No topology
is replaced. Its existing finite-nerve reduction still needs actual simultaneous
vertex corrections with smooth transition germs. Legacy Moise records that
start with one-point/sphere recognition cannot independently supply this.
Exact affine-germ/tangent-matching routes are stronger than smoothability and
are not accepted as a Moise construction.

Hamilton convergence means, in the exact compact connected simply-connected
Hausdorff second-countable smooth3 context:

```lean
∃ g : ClosedSmoothRiemannianMetric 3 M,
  (∀ x, g.tracelessRicciNormSqAt x = 0) ∧
  (∃ x, 0 < g.scalarAt x)
```

The equivalent positive-Einstein obligation is

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

These are existence obligations. Supplying a stationary Einstein flow or a
compact family already consisting of smooth nondegenerate metrics does not
construct their required metrics or limits.

## Non-circular route and first constructed input

The chosen construction route starts with arbitrary smooth initial metric data,
then genuine short-time Ricci/DeTurck evolution, and then the global continuation,
surgery and geometric reconstruction needed to produce a favorable Einstein
metric. A sphere identification may be used to transport the round metric only
when that identification has been independently constructed, never as an input
to the first metric/flow construction. Smoothability remains a separate
unresolved prerequisite for the final topological statement.

This is a construction program with explicit open stages, not a Lean proof of
those later stages. The finite-extinction route uses arbitrary initial metrics;
see Perelman's [surgery construction](https://arxiv.org/abs/math/0303109) and
[finite-extinction paper](https://arxiv.org/abs/math/0307245). The repository's
own surgery-source and topology-reconstruction existence obligations remain
open and are not filled by citing those papers.

The first missing input is now constructed:

```lean
∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (modelWithCornersSelf ℝ E3) ∞ M]
  [T2Space M] [CompactSpace M],
    Nonempty (ClosedSmoothRiemannianMetric 3 M)
```

`SmoothInitialMetricExistence.exists_initial_metric` constructs a real smooth
Riemannian metric without a supplied metric, curvature condition or sphere
recognition. Local Euclidean tangent pullbacks give positive symmetric sections
on their actual chart domains. The proved convex-cone and finite-dimensional
unit-ball lemmas feed Mathlib's partition-of-unity section gluing, which returns
an actual global smooth section. All five metric fields are established.

Each task names its core input and next proof consumer. The independently
proved local-pullback and positive-cone tasks both feed this existence theorem.
The existence theorem supplies g0 to the next unresolved construction:

```lean
∀ g0 : ClosedSmoothRiemannianMetric 3 M,
  ∃ T : ℝ, 0 < T ∧
  ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g0 ∧
    (∀ t ∈ Set.Ico 0 T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
    (∀ t ∈ Set.Ico 0 T, ∀ x, MetricEntriesJointContDiffAt gt t x 3)
```

This is the actual `ClosedRicciFlowNormalization.regularRicciFlowGoal`.
Its normalization consumer is already proved. The metric witness supplies no
positive Ricci curvature, all-forward flow, mean floor, finite energy, or
compact smooth-limit realization. These remain actual obligations.

## Next exact construction obstacle

The short-time route still lacks a metric-adapted finite buffered atlas and
constructed global operators L,P,R satisfying `L.comp P = id - R` and `‖R‖<1`.
`ParametrixNeumannCorrection.exists_right_inverse` consumes these actual
operators. It does not produce them. Standalone nonlinear Holder composition
was therefore deprioritized unless tied to a constructed buffered push and
this global operator.

The derivative adapter is also explicit: current graph carriers give within-
interval time derivatives. The regular flow goal asks for ordinary joint C3
entries at initial time zero. The graph's time-zero extension cannot be used as
the physical metric family without a compatible initial-jet extension and
regularity bootstrap. No ordinary derivative requirement was weakened.

## Verification and preserved attempts

All three proof tasks passed fresh source compilation and rigid exact frozen
contracts with permitted axiom footprints. Root independently reran the gates,
reviewed source-only diffs and integrated the actual witness. The local proof's
failed compiler attempts remain preserved. Existence Task revision1/draft and
the rejected branch-setup attempt are preserved; revision2 starts from the exact
base with independently accepted helper proofs. No unproved helper was used.
Earlier auxiliary drafts remain in ignored evidence and were not dispatched
after the user's strategy change. No branch, dirty worktree, model service or
remote harness was removed or changed.

## Concrete next input from the constructed metric

The next producer will take actual g0 and the positive anchor-dependent
solver tolerances already returned by
`BufferedFrozenParabolicSolver.exists_inverse_metric_chart_operator`. It must
construct `FiniteAtlasParabolicTensorSpace.AtlasData M`, a subordinate smooth
partition, and nested compactly supported coordinate cutoffs psi_i,xi_i. The
outer supports must lie in the actual chart target, the fixed-anchor cutoff-one
germ locus, and the coefficient-oscillation neighborhoods. The genuine inverse
Gram coefficients there must differ from their freezing values by at most the
selected solver tolerance. No AtlasData or error operator may be supplied as an
additional existence premise.

`exists_single_chart_parametrix` then consumes these constructed local inputs.
The finite common lifespan and bounds must be chosen from the finitely many
positive local values. Its local residual has sign `chartValue(P_i f)-f`;
the global Neumann consumer requires `L.comp P = id-R`, so that sign must be
proved in the actual global operator assembly.

The initial-time obstruction is already formal:
`DeTurckBUCInverseGaugeEvolution.not_differentiableAt_reconstructedCoordinateMetricPath_zero_of_rate_ne_zero`
proves the canonical zero-extended reconstruction fails ordinary
differentiability when its forward rate is nonzero. The future constructor
must build a compatible initial-jet extension and regularity bootstrap, not
pass that path into the stronger regular flow target.

The plain-BUC route is not a shortcut: its locally Lipschitz remainder package
is supplied, while the actual DeTurck remainder contains spatial derivatives
which are not bounded by the BUC supremum norm. The future actual nonlinear
producer must use a genuine parabolic graph/jet norm and prove its estimates.

The root integration checkpoint at source `9c01b8a0` passed every non-completion
gate, including fresh root import elaboration and allowed-axiom checks. Its
completion audit failed only for the absent reserved theorem. This validates
the constructed initial metric input; it does not mark either universal core
obligation as proved.
