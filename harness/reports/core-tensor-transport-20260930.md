# Constructed tensor Graph transport toward Hamilton existence

Date: 2026-09-30 America/Los_Angeles. Published starting commit:
`233be1e425f51d9e6c4a21990b2f25f82ade253d`.

## Core assumptions discharged

Neither universal core is discharged. The central objective remains
`UniversalHamiltonConvergenceStatement`; smoothability is a separate open
obligation. The exact kernel boundary was freshly inspected in
`core-boundary.lean`, including the final consumer and absence of the reserved
`Poincare.poincare_conjecture` declaration.

The smoothability obligation remains:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
    ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := charted
      IsManifold (𝓡 3) ∞ M
```

The topology is fixed; the atlas may be replaced. No compatible replacement
atlas for every such M has been constructed.

For every compact connected simply connected Hausdorff second-countable
smooth three-manifold M, the Hamilton endpoint still requires:

```lean
∃ g : ClosedSmoothRiemannianMetric 3 M,
  (∀ x, g.tracelessRicciNormSqAt x = 0) ∧ ∃ x, 0 < g.scalarAt x
```

Existing verified equivalences supply the omitted scalar differentiability
and identify this with the positive-Einstein payload:

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

The stronger `UniversalHamiltonFrontInputsStatement.{u,v}` still requires
`Nonempty (HamiltonFrontInputs.{u,v} M)` universally, for compatible Borel
structures. None of its universal fields was constructed in this batch:
actual normalized flow with compact metric parameterization, positive mean
floor and reaction decay (`reaction`); compact reference metric/volume
comparison (`compactTensorReferenceControl`); equicontinuity of all forward
scalar third-jet profiles (`hequicontinuous`); pointwise compact bounds
(`hpointwiseCompact`); and subordinate scalar geometry at every forward time
(`scalarSubordinateGeometry`).

## Concrete prerequisite removed

`BufferedTensorGraphTransport.exists_destination_entry_transport` constructs
an actual continuous linear operator from nine arbitrary source Graph entries
to one destination tensor-entry Graph. A nonnegative bound is chosen before
all `T` in `Ioc 0 1`. It uses the original finite-product supremum input norm
and the original four-carrier Graph output norm and certificates.

For destination i, source j and destination slots c,d, its actual coefficient
is

```text
W_ab(z) = theta(z) * (partition_i(chart_i.symm z) * xi_j(F z)
           * (DF_z e_c)_a * (DF_z e_d)_b).
B = sum_ab cutoffGraph(W_ab) composed with pullbackGraph(F)
           composed with source projection_(a,b).
```

The gate keeps the inverse chart in its genuine target and F in its true
chart-change agreement domain. The compact extension F can otherwise have
spurious off-chart values. Source entries already carry their own partition;
no extra source partition is inserted.

The actual all-point value and support identities are proved:

```text
(B w).u(t,z) = sum_ab W_ab(z) * w_ab.u(t,F z)
z outside coordSupport_i implies (B w).u(t,z) = 0
(B w).u(t,chart_i x) = partition_i(x) * indicator(source_j)(x)
  * sum_ab xi_j(chart_j x) * jac_ij[a,c] * jac_ij[b,d]
           * w_ab.u(t,chart_j x), for x in source_i.
```

The coefficient smoothness/compact-support proof and genuine chart/support
value proof independently remove concrete obstacles to this constructor.
The existing uniform cutoff estimate and nonlinear Graph pullback are reused
directly. Their bounds, rather than a supplied bound package, construct the
actual time-uniform operator norm.

An application check begins with the proved existence of an initial metric,
constructs its actual local-parametrix atlas and buffers, then constructs the
gated maps and these B operators for that same atlas. This check has no
metric, flow, operator, convergence, or recognition premise beyond the
original compact Hausdorff smooth-manifold context and 0<alpha<1.

`FiniteAtlasBufferedTensorValue.weighted_transition` proves the actual finite
buffered source sum satisfies the destination partition weighted overlap
law, using the existing genuine tensor cocycle. Arbitrary source arrays are
allowed. `symmetric` proves that source-slot symmetry produces symmetric
output. Both name core Hamilton existence and the immediate consumer:
finite sums of these actual Graph operators must belong to X_M. Their
support identities are already available; the codomain restriction and
actual global P construction remain the next step.

## Non-circular route and exact next obligations

The implemented producers start with general smooth geometry and actual
constructed metric/atlas/solver inputs. They do not take the Poincare theorem,
a sphere conclusion, a positive-Einstein metric, or an unproved flow/limit
witness as input. The final verified consumer is
`poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`;
both of its core premises still need independent proofs.

The next theorem must construct a positive lifespan and actual global
`P : Y_M A alpha T ->L X_M A alpha T` from the same produced local P_j and B_ij,
with a bound chosen before T. Apply the same local scalar P_j to all source
components; Y_M symmetry supplies source symmetry. Sum the B_ij outputs,
use the proved support/value/finite compatibility lemmas, then restrict the
actual continuous linear map to X_M. Retain the source buffers until their
removal is proved from the actual local output support and xi=1 there.

Still missing afterward: actual bounded global L and R for the full DeTurck
operator, including lower terms, with `L.comp P = id - R` and `norm R < 1`.
The local residual is `L_i P_i - id`, so its sign must be handled explicitly.
Nonlinear inversion needs a genuine derivative norm; a value-only Lipschitz
claim does not suffice. Matched initial-time jets and bootstrap must yield
ordinary joint C3 and an actual physical flow:

```lean
∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, MetricEntriesJointContDiffAt gt t x 3
```

The within-Icc Graph time certificate does not imply this ordinary initial
regularity. Continuation/surgery, independent smooth reconstruction,
favorable metric and limit existence remain substantive unproved stages.
This is a construction route with checked initial steps, not a claim that
those later stages are formalized. No core or frozen final target was weakened.

## Verification and evidence

Independent root acceptance reruns the recorded-base source gates and
inspects actual source-only diffs: fresh Lean, forbidden tokens, diff check,
exact reviewed type/universe and foundational axiom contracts. All attempted
source/failed compiler output and final diffs are retained; review preflight
failures concern notation/inference only, and no mathematical assumption was
introduced to fix them. Focused module dependency checks cover private
helpers without exporting expanded registry metadata.

Evidence is under `core-tensor-transport-20260930-evidence`; its gzip manifest
pins original and compressed bytes. Local Codex helpers are honestly recorded
as local attempts, not registered Pi/Leanstral runtime Jobs. Existing branches,
dirty work and historical failed attempts remain preserved.

The first integration checkpoint at `174e673c56ffbd16ef32db7e90b81c54b7e04d6d`
passed every non-completion gate except root-import coverage: new helper
modules were transitively available but lacked the required explicit root
imports. The failed receipt and full output are retained. Required direct
imports were added, preserving all proof types and bodies, before rerunning
the integration checkpoint.

The next global P contract must retain the same A,psi,xi, local P_j/R_j
residual/support witnesses and B_ij maps, with full Graph equality to their
actual finite assembly. Local CP estimates apply only to supported forcing;
use supported_entry for Y_M inputs rather than claim an unrestricted local
operator norm bound.
