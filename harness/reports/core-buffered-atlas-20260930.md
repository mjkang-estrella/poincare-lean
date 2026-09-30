# Constructed buffered geometry for Hamilton input existence

Date: 2026-09-29 America/Los_Angeles; source batch begun at
`21cdcfec507e622fbf1d52f9aca351249846a33a`.

The central objective remains `UniversalHamiltonConvergenceStatement`,
equivalently universal positive-Einstein existence. Neither this nor
`ExistsSmoothabilitySmoothManifoldStatement` is discharged. The frozen
`Poincare.poincare_conjecture` declaration is not supplied by this batch.

## Constructed input and proof consumer

The previous input witness constructs an actual initial Riemannian metric on
every compact Hausdorff smooth three-manifold. The present batch constructs
its solver geometry, with no supplied atlas, partition, curvature, flow,
operator, or limit witness:

```lean
forall (g0 : ClosedSmoothRiemannianMetric 3 M) (epsilon : M -> Real),
  (forall p, 0 < epsilon p) ->
  exists A : FiniteAtlasParabolicTensorSpace.AtlasData M,
  exists psi xi : Fin A.cover.chartCount -> ClosedSmoothModel 3 -> Real,
    -- smooth compact supports, nested one-sets,
    -- true target/cutoff-one germs and actual inverse-entry bounds
```

The actual exact type and source are
`MetricAdaptedBufferedAtlas.exists_metric_adapted_buffered_atlas` and its
schema-2.1 contract. The Gram field is covariant metric data in the inverse
chart; coefficients use its whole-matrix inverse. The output retains ambient
neighborhood germs for psi on coordinate support and for the anchor cutoff on
xi support. The equality xi=1 on psi support is pointwise, exactly as consumed
by the local solver.

Centered coordinate shrinking constructs precompact manifold regions inside
arbitrary coordinate neighborhoods. The refined-atlas proof selects a finite
subcover and constructs its actual smooth subordinate partition, preserving
centers and coordinate containment. The independent metric-neighborhood proof
constructs the target/cutoff-one/oscillation neighborhoods from g0. Its first
attempt exposed an unnecessary connectedness premise in the old radius
lemma; the final proof derives Gram entry smoothness, determinant
nonvanishing and inverse continuity locally. No premise was added.
The final proof constructs the nested compact cutoffs from those verified
inputs.

These proofs feed the actual
`BufferedFrozenParabolicSolver.exists_single_chart_parametrix`. Select its own
positive tolerance at each manifold anchor before constructing this atlas.
The tolerance from `exists_inverse_metric_chart_operator` is a different
existential choice and cannot silently replace it. The local consumer then
constructs actual P_i,R_i and positive time/bound constants, with residual
`R_i f = chartValue(actual_inverse_coefficients)(P_i f) - f`, on forcing
supported in coordSupport. No global R norm or unsupported residual-support
claim is inferred from those restricted estimates.

## Exact remaining core obligations

Smoothability still requires a compatible smooth atlas for every compact
Hausdorff simply-connected topological three-manifold, selected without using
sphere recognition. The selected-nerve correction producer remains open.

The Hamilton endpoint still requires, on every closed simply-connected smooth
three-manifold,

```lean
exists (g : ClosedSmoothRiemannianMetric 3 M) (lam : Real),
  0 < lam and forall x, g.IsEinsteinAt lam x
```

The first flow target consuming the initial metric and constructed geometry is
still unproved:

```lean
forall g0 : ClosedSmoothRiemannianMetric 3 M,
  ClosedRicciFlowNormalization.regularRicciFlowGoal g0
```

It requires a total metric family with the same initial metric, a positive
interval of the actual unnormalized equation, and ordinary joint C3 metric
entries including time zero. Global bounded tensor transport and actual L,P,R
with `L.comp P = id - R` and `norm R < 1` remain unconstructed. Their exact
consumer is `ParametrixNeumannCorrection.exists_right_inverse`. The stored
carrier entries are already partition weighted; global assembly must use
correct destination-only localization and prove the signed residual identity.

The local graph provides within-interval time derivatives. Its zero extension
cannot serve as the physical metric family at initial time when the actual
forward rate is nonzero; this obstruction is already a Lean theorem. A matched
initial-jet extension and higher regularity bootstrap are still required.
Neither the target nor ordinary derivative requirement was weakened. Global
continuation/surgery, favorable metric production, and actual smooth limits
also remain substantive open stages.

## Verification and next action

Every helper and the final constructor passed fresh source compilation,
exact reviewed type/axiom checks, scoped token/diff checks and
internal-inclusive emitted declaration scans. Root independently reran all
four scoped acceptance gates and reviewed the source-only diffs. All failed
compiler attempts remain preserved. Jobs are local Codex orchestrator helpers,
not registered Pi/Leanstral runtime jobs. No service or remote harness changed.

Next exact action: choose the positive tolerance returned by the actual
single-chart parametrix separately at each anchor, then apply the constructed
buffered atlas and produce a common positive lifespan and uniform local-family
bounds. This must construct the operators; assumed P/R packages or plain-BUC
remainder witnesses cannot replace them. The true DeTurck nonlinear remainder
contains spatial derivatives, so a parabolic graph/jet norm is needed.
