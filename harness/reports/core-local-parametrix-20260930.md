# Actual local operators toward universal Hamilton input existence

Date: 2026-09-29 America/Los_Angeles. Accepted constructor source:
`8890192d8f08ca7fb7f714da6b91a9ec72f2b625`.

## Core assumptions

Neither universal core assumption is discharged. The reserved
`Poincare.poincare_conjecture` remains absent. The existing checked final
consumer is
`poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`;
it needs precisely the following smoothability and Hamilton witnesses.

The exact smoothability obligation, over the same given topology, is:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
  ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M := charted
    IsManifold (𝓡 3) ∞ M
```

`∞` above denotes the smooth exponent, not the analytic exponent. The
source is `TopologicalCompletionBridge.lean`; the selected atlas may differ
from the given topological atlas. The selected finite-nerve smoothing route
still lacks actual simultaneous coordinate corrections. Recognition-based
smoothability records cannot produce this witness without a circular input.

The selected central Hamilton obligation is
`UniversalHamiltonConvergenceStatement`: for every compact connected simply
connected Hausdorff second-countable smooth three-manifold, produce an actual
`HamiltonConvergencePinchedLimit3 M`. Its verified reduced core is

```lean
∃ g : ClosedSmoothRiemannianMetric 3 M,
  (∀ x, g.tracelessRicciNormSqAt x = 0) ∧
  (∃ x, 0 < g.scalarAt x)
```

Equivalently, `UniversalPositiveEinsteinStatement` requires on every such M:

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

`UniversalHamiltonFrontInputsStatement.{u,v}` is the stronger universal
producer:

```lean
∀ (N : Type u) [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
  [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
    Nonempty (HamiltonFrontInputs.{u, v} N)
```

Its actual fields are:

- reaction: an actual forward normalized flow, compact smooth-metric
  parameterization, positive mean-scalar floor and reaction decay;
- compactTensorReferenceControl: continuous positive tensor/volume comparison
  against an actual reference metric;
- hequicontinuous: equicontinuity over all forward time of every scalar metric
  third-jet profile;
- hpointwiseCompact: for every slot and coordinate point an actual compact
  set containing all forward profile values;
- scalarSubordinateGeometry: finite subordinate Hausdorff Laplacian geometry
  for scalar curvature at every forward time.

These fields and their universal quantifiers in HamiltonFrontStatements are
still unconstructed. A supplied pinched flow, stationary Einstein metric or
conditional profile package cannot be substituted for their universal
existence. The endpoint itself has no measurable-space premise; the checked
front-input consumer derives canonical Borel instances.

## Constructed step and consumer

The non-circular construction program starts with the already verified initial
metric on any compact Hausdorff smooth M, then actual solver geometry and
operators, then general Ricci flow. Global continuation/surgery, independent
smooth reconstruction and favorable metric/limit construction are substantive
unproved stages. No step takes sphere recognition or the final theorem as an
input; this is a construction program, not a claim that all those stages are
already formalized.

This batch constructs, from g0 and 0<alpha<1 alone, an actual finite atlas,
compact nested buffers, chart-local bounded linear P_i/R_i, common constants
and one positive lifespan. The single-chart solver chooses epsilon(p) before
the atlas. Actual inverse-metric positivity/smoothness and finite aggregation
remove concrete prerequisites; the constructor consumes both proofs rather
than accepting their outputs as additional hypotheses.

For forcing supported in coordSupport A i it proves the actual signed
residual and estimates:

```text
R_i f = chartValue(actual inverse metric)(P_i f) - f
norm(R_i f) <= Cpsi*(T^((1-alpha)/2)+T^(1-alpha/2))*norm(f)
norm(P_i f) <= CP*norm(f)
```

P_i.u support is unconditional. R support and an unrestricted R_i operator
norm are not claimed. The signed local residual gives L_i P_i=id+R_i.
Subsequent global tensor assembly must account for that sign and preserve
support, symmetry and metric transition compatibility with actual jet norm
bounds. The stored source carrier is already partition weighted; multiplying
by another source partition is an incorrect reconstruction.

The exact next consumer `ParametrixNeumannCorrection.exists_right_inverse`
needs actual bounded maps on the atlas tensor/graph carriers:

```text
L : X_M ->L[Real] Y_M
P : Y_M ->L[Real] X_M
R : Y_M ->L[Real] Y_M
L.comp P = ContinuousLinearMap.id Real Y_M - R
norm R < 1
```

L must match the true DeTurck operator, including lower-order terms. These
maps/identity/contraction are not constructed here. Nonlinear inversion in
a parabolic graph/jet norm is also open; a plain-BUC sup-norm Lipschitz witness
does not bound the spatial derivatives of the real nonlinear remainder.

The still-open physical target is
`ClosedRicciFlowNormalization.regularRicciFlowGoal g0`:

```lean
∃ T : ℝ, 0 < T ∧
  ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g0 ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      IsClosedRicciFlowSolutionAt gt t x) ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x,
      MetricEntriesJointContDiffAt gt t x 3
```

The local Graph has within-[0,T] time derivatives and zero initial trace.
Its zero extension generally has no ordinary derivative at zero when the
forward rate is nonzero; that obstruction is already proved. Matched initial
jets and higher regularity are required, and the physical target was retained.

## Exact-type discrepancy and evidence

The original unaccepted a01 type accidentally selected entrywise Pi.inv under
chartValue's function-valued coefficient expectation. The actual solver's
identity instead contains Matrix.inv. The failed source, compiler output,
original approved-but-incorrect interpretation and frozen type are preserved.
A new reviewed Task explicitly fixes Matrix.inv without changing input
hypotheses, support, lifespan, sign or numerical estimates. Its corrected
constructor fresh-compiles and passes the exact frozen contract. A raw Lean
expression audit confirms all inverse occurrences in the previously accepted
coefficient-neighborhood/buffered-atlas/regularity exports already bind
Matrix.inv; those proofs did not need alteration.

Root independently reran all four scoped acceptance gates from each recorded
base and inspected the source-only diffs. Helper and corrected constructor
internal-inclusive axiom scans allow only propext, Classical.choice and
Quot.sound. All failed source/compiler evidence is preserved in the portable
gzip evidence directories. These are local Codex orchestrator helpers, not
registered Pi/Leanstral runtime Jobs. No model service or remote harness changed.

The integration checkpoint at `a2e17d41dc9ef166d6bd4ded73cb58514f71fac8`
passed fresh root source compilation, full Lake build, interface, mathlib-gap,
shape, theorem-contract, semantic, root-import and axiom audits. The independent
root internal scan of the corrected constructor passed with the three allowed
foundational axioms. Completion failed only because the reserved final
declaration is absent. Full outputs and receipt are preserved under the
integration evidence manifest. Both core assumptions remain open.

## Next concrete spatial construction

Read-only scoping identified an actual compact-overlap construction for the
next bounded transport proof. For destination i and source j, form
K_ij = chart_i '' (tsupport(partition_i) intersect chart_j.symm '' tsupport(xi_j)).
The verified outer buffers keep xi_j support in the true source chart target;
partition_i support is in the destination source. The next proof must construct
a smooth compact overlap gate theta_ij supported inside the true transition
domain and both cutoff-one germ loci, with theta=1 near K. It must then
construct a global smooth compact coordinate map F_ij agreeing germwise with
the actual chart change on all tsupport(theta), plus an actual Lipschitz bound.
Agreement throughout that gate prevents a global extension from creating
spurious source values. Smooth infinity supplies the higher derivatives needed
by Jacobian-weight jet norms. These new witnesses are not yet constructed.

The existing contDiffOn_ext_coord_change, buffered-cutoff and compact smooth
Lipschitz APIs provide a direct route: choose theta, then another cutoff eta
which is one near tsupport(theta), and extend eta times the true chart change
by zero. The next operator B transports source graph entries to one destination
chart, multiplies only the destination partition and the actual source outer
cutoff, and proves a T-uniform Graph norm bound. On P_j outputs xi_j equals one,
so the construction recovers the required tensor push without another source
partition. Graph.ext_of_u, exists_cutoff_operator and the verified Jacobian
cocycle can then establish the actual finite assembly. The nonlinear graph
composition and its bound remain open.
