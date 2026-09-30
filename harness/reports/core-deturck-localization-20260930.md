# Full localization and compact symmetric two-jets — 2026-09-30

The selected core is `UniversalHamiltonConvergenceStatement`. Neither that
universal existence statement nor `ExistsSmoothabilitySmoothManifoldStatement`
is discharged. The reserved final theorem is absent. This batch closes the
full local cutoff-product identity and actual derivative gates, then
constructs the compact smooth two-jet input for genuine metric variations.

## Exact universal obligations and route

The final topological consumer remains
`Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`.
It still requires:

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

The latter is equivalent to existence of a smooth metric with zero traceless
Ricci everywhere and positive scalar curvature somewhere. No such universal
producer is constructed here. The stronger universal HamiltonFrontInputs
record is also open. Its five fields are not all necessary: the checked
universal finite-energy normalized-flow reduction already suffices, but it
still requires actual all-forward flow, integrable traceless energy, compact
metric realization, continuous mean-energy pair and positive mean-scalar
floor. Short-time analysis alone produces none of these universal witnesses.

The intended non-circular route constructs real flow/energy/limit inputs,
applies the existing Hamilton endpoint and recognition, and independently
constructs compatible smoothability. Later continuation/surgery and favorable
metric/flow production remain unproved links, not assumptions to fill gaps.

## Proved obstacles and exact subsequent consumers

`DeTurckLocalization.differential_cutoff` gives the full bilinear identity:

```text
DQ(c*h, c*J+dc⊗h, cutoffSecond) = c*DQ(h,J,H)
 + sum_ij a_ij [dc(e_i)*J(e_j)+dc(e_j)*J(e_i)+ddc(e_i,e_j)*h]
 + firstOrder(dc⊗h).
```

Both ordered mixed terms remain; no symmetry of the principal matrix is
assumed. The full inverse variation `Da(G0)[h]:H0` and actual lower derivative
stay in the base DQ. The zero-order correction vanishes through true CLM
linearity. For L=dt-DQ the commutator correction has the opposite sign.
The consumer is correct weighted localization for stored chi_i*h_i and then
the actual signed global L/P/R residual. This identity alone does not
construct that global operator or prove its covariance.

`cutoff_hasFDerivAt_two` constructs actual first and second spatial product
certificates. Its input f has real first derivatives J everywhere and J has
real derivative H at the point; a C2 cutoff is enough. The proof identifies
the first derivative on a neighborhood before differentiating the actual
fderiv field. It does not equate a merely formal jet with an actual derivative.
Graph derivative certificates supply these inputs in the application.

`tensorHessian_hasFDerivAt` uses Graph.hasFDeriv_du and finite fixed-generator
maps to construct the ordinary derivative of tensorJet, with no alpha/time
positivity or symmetry premise beyond interval membership. The subsequent
`tensorValue_contDiff_two` derives global spatial C2 on each fixed-time slice
from the original Holder carriers when alpha>0. This supplies actual C2 germs
for compact realization and linearized covariance; it proves no ordinary
joint/time C3 or initial-time extension.

`exists_compact_symmetric_realization` constructs eta smooth compact inside U,
equal one near z, then the actual field

```text
F(y)=eta(y)*[h(z)+Dh(z)(y-z)+(1/2)*D²h(z)(y-z,y-z)].
```

For a C2 germ h with eventual tensor-slot symmetry it proves global tensor
symmetry and exact value/D/D2 matching at z. Hessian direction symmetry comes
from actual C2; differentiating the symmetry germ preserves covariant slots.
Every original ordered slot and nested operator norm remains. Matching a jet
is not equality of the original germ and implies no full-Holder norm density.
The next consumer is a GLOBAL smooth symmetric tangent-bilinear section,
then an actual positive metric variation and differentiated nonlinear
covariance. Those required inputs remain to be constructed.

A joint Lean application uses the genuine Graph first/second certificates to
localize actual fderiv jets and derive the full DQ correction. A second
application supplies the actual C2 Graph germ to the realization producer and
identifies its derivatives with tensorJet/tensorHessian. The generic base
jets in the algebraic identity can be instantiated at the previously checked
actual metric jets on their invertibility zone; no physical flow is inferred.

## First remaining genuine producer

For c=extChartAt I anchor and smooth compact symmetric F supported in c.target,
construct H zero off c.source and on it the pullback of F(c x) through the
forward chart differential in both tangent slots. Prove global smoothness,
symmetry, chartMetric H anchor z=F(z) throughout the target, and compact source
support K=c.symm''tsupportF. The bundle-coordinate identity must be proved,
not supplied as a premise. `chartMetric` itself has no cutoff; the separate
`blendedChartMetric` does. A point bump alone warrants only germ agreement.

Then derive coercivity from actual g0 on compact support and a bound on F,
choose a common epsilon>0, and construct genuine metrics whose inner forms
are g0.inner+s*H for |s|<epsilon. No supplied positivity margin/metric package
may replace this constructor. Differentiate the existing nonlinear covariance
along that actual family and transfer by exact two-jet matching to symmetric
C2 germs, retaining chart Jacobian derivatives through D3phi.

Actual global L/R, signed id-R contraction (local residuals are id+R_j),
nonlinear inversion, ordinary joint regularity/initial jets, physical Ricci
flow and all later universal flow/limit/favorable-metric producers remain
open. Existing constructed global P and coefficient/transport bounds are
reused. Source entries already contain their own partition; never multiply
that source weight a second time.

## Acceptance and evidence

Four disjoint proof tasks were independently rerun against their recorded
base e02105a51bd8ada40a512d66c4fceb0f4caf0feb. Root reviewed actual source-only
diffs and exact frozen-type/universe/pin and allowed-axiom gates before
acceptance. The joint root import, actual Graph application and all emitted
new-module constant scans passed, including public helpers and private
unsafe/partial/unexpected-axiom checks. Canonical instance caches and proved
bounded multiplication preserve the original norms; unique instance names
avoid the prior compiler-helper collision.

Every failed compiler source/log, preflight and intermediate readback is
preserved. An initial reviewer disclosed author-context exposure, wrote no
approval, and was replaced by a fresh blind reconstruction before dispatch.
A literal indentation error was repaired before any proof job started; both
versions are retained. All scoped sources and final diffs are append-only.
Local Codex helpers are labelled honestly, not registered Pi/Leanstral Jobs.
No historical dirty or unmerged worktree was removed. The complete goal
remains active; no core or final statement was weakened.

## Sealed integration checkpoint

Clean source checkpoint: `39dae92aa256a9daddb4c6d294760b80d099ba52`.
Source-bound evidence: `harness/v2/state/verification/checkpoints/20260930T121518Z-5f79cb02d5204e2ca8f351d8755c23ca`.
Build and interface, mathlib, shape, theorem, semantic, root-import and axiom
phases returned 0. Completion returned 1 with exactly reserved-name absence
and the exact endpoint probe failure. Completion is not certified.

Compressed append-only evidence is in
`core-deturck-localization-20260930-evidence/manifest.json`. Every original and
compressed SHA-256 hash was verified. The archive includes all failed sources/
logs, stopped-review exposure note, independent blind readbacks, worker and
root gates, actual joint applications and next chart-lift findings. Historical
worktrees and branches remain preserved. No universal core is discharged.
