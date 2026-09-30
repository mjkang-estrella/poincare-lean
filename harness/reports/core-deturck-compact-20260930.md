# Actual compact DeTurck lower forcing — 2026-09-30

The selected core is `UniversalHamiltonConvergenceStatement`. Neither it nor
`ExistsSmoothabilitySmoothManifoldStatement` is discharged. The reserved
`Poincare.poincare_conjecture` remains absent. This batch constructs the actual
compact coefficient carriers and bounded local coupled lower-DQ operator,
plus its true spatial-jet interpretation, for the physical flow route.

## Core obligations and checked endpoint route

The frozen final consumer remains
`Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`.
Its two missing universal inputs are exactly:

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

The Hamilton payload is equivalent to
`∃ g : ClosedSmoothRiemannianMetric 3 N,
(∀ x, g.tracelessRicciNormSqAt x = 0) ∧ (∃ x, 0 < g.scalarAt x)`;
scalar differentiability for such smooth metrics is already proved.

The stronger universal `Nonempty (HamiltonFrontInputs.{u,v} N)` is still open.
Existing checked reductions instead permit
`UniversalHamiltonFiniteEnergyFlowExistenceStatement.{u,v}`. For each manifold
with a compatible Borel structure it requires an actual gt, compact K, metric
family and forward-time parameter realizing gt, such that:

```lean
(∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) ∧
(∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) ∧
0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
```

These universal witnesses remain unconstructed. The non-circular endpoint
route is to construct that sufficient flow/energy/limit input, apply the
checked Hamilton endpoint and existing recognition, and separately construct
compatible smoothability before the topological reduction. Short-time flow
from arbitrary g0 alone supplies neither the all-forward normalized flow nor
the positive scalar floor. Later continuation/surgery and favorable-flow
production remain actual proof obligations, not established links.

## Constructed inputs and their subsequent consumers

`exists_actual_compact_carriers` starts from the actual g0/bg jets and the
compact outer support already supplied by the metric-adapted local solver.
It constructs eta supported in the true chart/cutoff-one-germ zone and equal
one near all of tsupport xi. Every scalar coefficient is the actual
`eta * entry_cd(Z(tensor_ab))` or `eta * entry_cd(F(firstJet_pab))`.
It proves global smoothness, compact support and germ agreement, then
constructs their Y carriers for every real T. Common nonnegative row bounds
C0/C1 are chosen before T. No coefficient or bound package is supplied.
The zero-order field retains inverse variation contracted with D2g0.

`exists_actual_coupled_forcing` constructs K from those exact actual carriers
by summing scalar firstOrderLinearMap after the nine Pi projections and
mkContinuous. It retains the original Pi maximum and Graph sum norms, and:

```text
K W(q) = sum_ab [c0_ab(q) W_ab.u(q) + sum_p c1_pab(q) W_ab.du(q)(e_p)],
||K|| <= 24*(N1*T^((1-alpha)/2) + N0*T^(1-alpha/2)).
```

On the cylinder the value is exactly
`eta(z)*entry_cd(Z(tensorValue W)+F(tensorJet W))`, with every ordered source
slot and both actual fields. This is the positive lower action in DQ; the
later L subtracts it. The subsequent consumer is the actual full global
L=dt-DQ(g0), including covariance/localization and its signed residual.

`tensorJet_hasFDerivAt` reconstructs the whole ordinary spatial derivative
from the genuine Graph certificates:

```lean
∀ (α T : ℝ) (W : Inputs α T) (t : ℝ) (z : E), t ∈ Icc 0 T →
HasFDerivAt (fun y : E => tensorValue W (t,y)) (tensorJet W (t,z)) z
```

It adds no alpha/time positivity, support or symmetry premise. Its concrete
consumer identifies the preceding actual action as `Z(h)+F(Dh)`; within-time
Graph certificates still do not prove ordinary joint C3 at zero.

## Exact next obstacles

Stored entries are chi_i*h_i. Full localization requires principal mixed and
Hessian cutoff corrections plus `firstOrder((Dchi_i).smulRight h_i)`, with the
correct negative sign in L. Omitting the coupled first-order cutoff term gives
the wrong global residual. This product identity is the next frozen task.

Full linearized coordinate covariance remains open. Existing nonlinear
`deTurckChartMetricEvolutionBilin_chartTransitionDeriv` concerns actual smooth
metric families. The needed C2-germ law transforms DQ at actual g0/bg jets
under `h_i(y)(v,w)=h_j(phi y)(Dphi(y)v,Dphi(y)w)` and retains Jacobian
derivatives through D3phi. A possible route is compact smooth symmetric2jet
realization, a small actual Riemannian variation, differentiation of the
nonlinear law and transfer by jet matching. None of these missing producers
is filled by coefficient smoothness or an assumed full-Holder norm density.

Actual bounded global L/R and `L.comp P = id-R` with `||R||<1` remain open;
local solver residuals use id+R_j. Nonlinear inversion, matched initial jets,
ordinary joint regularity, physical Ricci flow and the later universal flow/
energy/compact-limit/favorable-metric producers remain unresolved. The actual
global P and its existing local solver/support witnesses are reused.

## Review and preserved evidence

Root independently reran the recorded scoped gates and reviewed each actual
source-only diff. Exact frozen types/universes/pins and allowed foundational
axioms are checked. Private helpers are included in the emitted-declaration
unsafe/partial/axiom scan. Canonical instances preserve norms and actions;
bounded scalar multiplication is proved for the existing Bilin norm.

A combined import exposed a compiler-generated instance-helper collision
between forcing and jet modules despite their separate scoped passes. All
failed integration sources/logs and the original proof are retained. A
superseding task changes only the three local instance identifiers and adds
an explicit combined-import gate; all five independent repair gates pass.
No target or proof is weakened.

A fresh kernel application first constructs g0 with exists_initial_metric,
then the actual atlas/psi/xi via exists_metric_adapted_local_parametrix. For each
actual chart buffer it constructs eta, pre-time C0/C1, the scalar carriers and
K. Its physical formula uses fderiv of tensorValue, replacing tensorJet through
the checked derivative certificate. The operator bound follows from the
constructed row budgets. Fresh root Lean and all-new-module dependency scans
pass jointly after the helper-name repair.

Every failed compiler attempt, contract preflight, readback, worker snapshot,
final diff and independent gate output is preserved append-only. Local Codex
helpers are labelled honestly, not registered Pi/Leanstral Jobs. Historical
and dirty worktrees remain intact. The complete-proof goal remains active.

## Sealed integration checkpoint

Clean source checkpoint: `5720eee4834ed98f7dacf3f3dbf18a5bdb690843`.
Source-bound evidence: `harness/v2/state/verification/checkpoints/20260930T112653Z-9ed1919ebedd41239b8fbd92d7332423`.
The build and interface, mathlib, shape, theorem, semantic, root-import and
axiom phases returned 0. Completion returned 1 with exactly the reserved-name
absence and exact endpoint probe failures; completion is not certified.
The constructed-metric/atlas/carrier/operator application, fresh root Lean,
whole-module dependency scan and live universal boundary probe passed.

Compressed append-only evidence is under
`core-deturck-compact-20260930-evidence/manifest.json`. Original and compressed
SHA-256 hashes were verified for every archived payload. It retains failed
preflights, the isolated jet proof and failed joint-import outputs, the
superseding name-only repair and its joint probe, worker/compiler/frozen
readback results, independent reviews and the next covariance findings.

Use unique local-instance names in shared namespaces: anonymous compiler
helpers collided despite individually passing modules in this batch.
The first next task remains the full actual DQ localization product identity
including the coupled first-order cutoff term. No universal core is discharged.
