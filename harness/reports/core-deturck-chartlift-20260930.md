# Actual global tensor lifts and genuine metric variations — 2026-09-30

The selected core is `UniversalHamiltonConvergenceStatement`. Neither it nor
`ExistsSmoothabilitySmoothManifoldStatement` is discharged; the reserved final
Poincare theorem is absent. This batch constructs the actual global smooth
tensor and positive metric family required to differentiate nonlinear
covariance. Positivity is positive definiteness of the metric tensor; it does
not supply the Hamilton scalar floor, a favorable metric or a flow.

## Exact universal obligations

The frozen topological consumer still requires:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
  ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    letI := charted
    IsManifold (𝓡 3) ∞ M
```

and

```lean
∀ (N : Type u) [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
  [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
  HamiltonConvergencePinchedLimit3 N
```

The Hamilton endpoint is equivalent to a smooth metric with zero traceless
Ricci everywhere and positive scalar somewhere. The stronger universal
HamiltonFrontInputs record is open too. Existing checked reductions permit
the smaller universal finite-energy normalized-flow existence boundary,
but its actual all-forward flow, energy integrability, compact metric
realization, continuous mean-energy pair and positive mean-scalar floor
witnesses are still unconstructed.

The non-circular intended route constructs genuine flow/energy/limit inputs,
uses the existing Hamilton endpoint and recognition, and independently proves
compatible smoothability. Short-time DeTurck analysis alone supplies no
all-forward or favorable-flow witness. Continuation/surgery and later universal
producers remain unproved links, not assumptions used to fill these gaps.

## Constructed obstacles and subsequent consumers

For c=extChartAt I anchor and smooth compact F:E->Bilin supported in c.target,
`chartLift` is the actual forward-differential pullback in both tangent slots
on c.source, and zero off the source. It uses topological CLM precomp/comp;
no new tangent seminorm is a constructor input.

`compact_source_support` derives actual K=c.symm''tsupportF, compactness,
K subsetsource, zero outsideK and neighborhood zero. Because tangent fibers
are dependent, it explicitly proves compactness and containment of
`closure {x | chartLift anchor F x != 0}`. Generic constant-codomain
HasCompactSupport/tsupport were ill-typed in the draft; that failure and prior
readback are retained. The corrected geometric support type was independently
reviewed and preflighted before any proof job.

`chartMetric_chartLift` proves whole-target equality with F from actual
forward/inverse chart differentials. `chartLift_symmetric` transfers actual
fiber symmetry; `chartLift_coordinates` proves nested Hom-bundle coordinates
without assuming a coordinate bridge. `chartLift_contMDiff` derives source
smoothness from those coordinates and F's smoothness, then glues the source
with compactK-complement using the actual zero section. These proofs supply
the real globally smooth compact symmetric section H for metric variation.
`chartMetric` itself has no cutoff; `blendedChartMetric` is separate.

`exists_coordinate_variation_radius` derives actual g0 chart positivity and
uniform coercivity on compact F support, bounds F in its original operator
norm, and chooses epsilon=c/(max C 0+1) before all signed real s. Throughout
the true target, |s|<epsilon preserves quadratic positivity; offsupport F=0.
No supplied positivity margin, norm replacement or candidate metric package.

`exists_actual_metric_variation` now constructs:

```lean
∃ ε : ℝ, 0 < ε ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ s, |s| < ε → ∀ x,
    (gt s).inner x = g0.inner x + s • chartLift anchor F x) ∧
  ∀ s, |s| < ε → ∀ z ∈ (extChartAt I anchor).target,
    CovariantDerivative.chartMetric (gt s).inner anchor z =
      CovariantDerivative.chartMetric g0.inner anchor z + s • F z
```

It fills actual symmetry, positivity, smoothness and bounded quadratic unit
balls. It returns g0 at zero and may return g0 outside the common interval;
no global smoothness in the parameter or flow equation is claimed. Temporary
canonical model-fiber bindings used solely for boundedness preserve topology,
scalar module and dual topology; fresh definitional equality probes confirm
that agreement. The consumer is an actual Riemannian variation along which
the existing nonlinear DeTurck tensor covariance can be differentiated.

A joint kernel application constructs g0 via initial metric existence, uses
the already proved compact symmetric two-jet realization of a C2 germ, then
constructs the genuine family and whole-target affine coefficients. No initial
metric, coordinate/support identity, margin or metric family is supplied as
an unproved package. The original nested operator norms and slots are retained.

## Exact next obligation

For actual G(s)=chartMetric(gt(s)).inner, derive the parameter two-jet:

```lean
HasDerivAt
 (fun s => ((G s z, fderiv ℝ (G s) z),
   fderiv ℝ (fderiv ℝ (G s)) z))
 ((F z, fderiv ℝ F z), fderiv ℝ (fderiv ℝ F) z) 0
```

The common open-target affine identity yields neighborhood equality before
both spatial derivative transports. Equality merely at z is insufficient.
The saved standalone prototype `parameter-jet-api-probe` passed at its
recorded earlier HEAD/time; it is labelled accurately as a prototype, not a
repository theorem. Reuse it in the next frozen proof task. Then compose the
full finite-jet derivative (retaining Da(G0)[h]:H0), differentiate nonlinear
covariance and transfer by exact two-jet matching to symmetric C2 Graph
germs. This last transfer must retain Jacobian derivatives through D3phi;
no full-Holder smooth-density claim is available or assumed.

Actual bounded global L/R, signed id-R contraction (local residuals are
id+R_j), nonlinear inversion, matched initial jets/ordinary jointC3, physical
Ricci flow and the later universal flow/limit/favorable-metric producers remain
open. Existing global P, actual compact coefficients, full cutoff corrections,
transport bounds and Graph C2/jet realization are reused.

## Acceptance and preserved evidence

Root independently reran all recorded scoped commands at each exact base and
reviewed actual source-only diffs before accepting support, coordinates,
positivity, smoothness and metric-family construction. Literal types,
universes, definition hashes and independent blind readbacks precede dispatch.
All emitted new constants, including helpers, pass unsafe/partial/allowed
foundational-axiom scans. Joint root imports and the genuine application pass.

All compiler sources/logs/exits, failed drafts/preflights, dependency/support
typing correction, field/topology probes, frozen reports, final diffs and
independent gates are preserved append-only. The parameter prototype includes
its original verification receipt and combined-output capture caveat. Local
Codex helpers are labelled as such, not registered Pi/Leanstral Jobs. No dirty
or unmerged historical worktree was removed. The complete goal remains active;
no core/final target, scalar action or topology was weakened.

## Sealed integration checkpoint

Clean source checkpoint: `76f07c68eb7ce3faf3637738ced24ee1f7af7ffa`.
Source-bound evidence: `harness/v2/state/verification/checkpoints/20260930T132636Z-0595f30e55c5452b870e50c169d6e078`.
Build and interface, mathlib, shape, theorem, semantic, root-import and axiom
phases returned 0. Completion returned 1 with exactly reserved-name absence
and the exact endpoint probe failure; completion is not certified.

Compressed append-only evidence is in
`core-deturck-chartlift-20260930-evidence/manifest.json`. Original and compressed
SHA-256 hashes were verified for every archived payload. It includes all
failed support/typing/compiler and topology-probe sources/logs, blind reports,
worker/root gates, genuine constructed-metric/twojet/family application and
saved parameter-derivative prototype with its original verification identity.
No universal core is discharged. The exact next action remains the actual
chart2jet parameter derivative, then full linearized covariance transfer.
