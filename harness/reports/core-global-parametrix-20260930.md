# Constructed global parametrix and genuine DeTurck lower smoothness

Date: 2026-09-30 America/Los_Angeles. Published starting commit:
`977ffd610c60a79433cb7774fe0784f9916b5468`.

## Core assumptions remain open

Neither `ExistsSmoothabilitySmoothManifoldStatement` nor
`UniversalHamiltonConvergenceStatement` is discharged. The central objective
is still Hamilton existence. The fresh kernel boundary probe confirms the
exact quantified declarations and the absence of
`Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement`.

Smoothability requires a replacement charted-space structure on the SAME
topological compact Hausdorff simply connected three-manifold, with
`IsManifold (𝓡 3) ∞ M`. It cannot be obtained by assuming M already smooth.
Hamilton existence, for every target closed simply connected smooth M,
still requires the equivalent actual metric payload:

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x : M, g.IsEinsteinAt lam x
```

The reduced pinched-limit core is
`∃ g, (∀ x, g.tracelessRicciNormSqAt x = 0) ∧ ∃ x, 0 < g.scalarAt x`.
The stronger universal `Nonempty (HamiltonFrontInputs.{u,v} M)` still needs
actual normalized flow/reaction/compact parameterization, reference tensor
and volume comparison, third-jet equicontinuity and pointwise compact bounds,
and subordinate scalar geometry for the same forward flow. Local parametrix
construction does not provide these flow or limit witnesses.

## Actual global input constructed

`MetricAdaptedGlobalParametrix.exists_metric_adapted_global_parametrix` now
constructs the actual global continuous linear map from g0 and 0<alpha<1:

```lean
Pglobal : Y_M A alpha T →L[ℝ] X_M A alpha T
```

The atlas, nested buffers, genuine gated coordinate extensions, nonnegative
local/transport constants and positive lifespan are chosen before T. For
each `T ∈ Ioc 0 tau`, it constructs and RETAINS the same local S_j/R_j,
B_ijcd and Pglobal, rather than merely asserting an arbitrary operator exists.
The original subtype/Pi/Graph norms remain unchanged. Its global bound is
`CP * sum_i,j,c,d CB_i,j,c,d`, selected before time.

The local S_j support and actual residual remain linked to g0:

```text
S_j f.u is zero off tsupport(psi_j)
R_j f = chartValue(actual whole Matrix.inv of Gram(g0))(S_j f) - f
norm R_j f <= Cpsi * (T^((1-alpha)/2) + T^(1-alpha/2)) * norm f
norm S_j f <= CP * norm f
```

The last three assertions require f supported in coordSupport_j. The producer
does not strengthen them into an unrestricted local operator-norm estimate.
Global Y_M inputs supply that exact support. Each B retains its original raw
weighted pullback, true source-indicated chart value, destination support and
uniform norm certificate.

The full Graph equality is proved, so all genuine derivative certificates
belong to the actual finite construction:

```text
(Pglobal f).val(i,c,d) = sum_j B_ijcd
  (fun (a,b) => S_j(f.val(j,a,b))).
```

The true chart-u value is the actual destination-only buffered finite tensor
value, with source indicators and no additional source partition. The actual
ambient CLM is first formed by projections/pi/composition/finite sums, then
codomain-restricted using its proved membership in tensorSubmodule(evalX).

The independent range proof removes the support/symmetry/overlap obstacle.
It derives source symmetry from actual Y_M forcing equality and applies the
same S_j to both source slots. The independent norm proof consumes only the
producer's supported-input estimates. Both name core H and this actual
metric-derived constructor as their immediate subsequent proof.
An application check constructs an initial metric first, then produces the
actual global P with positive interval, bound and full Graph assembly for
the same resulting atlas. No metric, flow, inverse, or recognition package
was supplied to that check.

## Genuine coefficient prerequisite proved

`DeTurckLowerJetSmoothness.contDiffAt_lowerTerm` proves:

```lean
G0.IsInvertible → ContDiffAt ℝ ∞
  (fun p : Bilin × Jet1 =>
    DeTurckPrincipalIdentity.lowerTerm B DB p.1 p.2) (G0,J0)
```

Here B/DB are arbitrary fixed actual bilinear/trilinear background data and
J0 is arbitrary. No symmetry, realized metric jet, positive curvature, or
supplied lower-operator premise is required. The target is the ACTUAL
Bilin-valued lowerTerm, not the unspecified existential lower exported by
principalIdentity. Smoothness of actual CLM inversion and finite-dimensional
fixed-slot reconstruction prove the bundled conclusion.

Canonical Jet1 group/space bindings fix scalar/hom metavariable inference.
Independent probes verify Jet1 equals fresh E->L Bilin and its norm equals
actual CLM.opNorm by rfl. These bindings add no supplied hypothesis and change
no norm. Original failed preflights, failed custom readback wrapper, all
compiler/source attempts and final diffs remain preserved. The global bound
proof needs no added instances; its final inference repair uses the existing
transparency option only.

This coefficient theorem helps core H through the next actual finite-jet
linearization proof. It supplies metric/first-jet differentiability at fixed
background data, not joint spatial/background smoothness or the whole DQ.

## Exact next construction and remaining obligations

The genuine local expression to differentiate is

```text
Q_z(G,J,H) = inverseEntries(G):H + lowerTerm(B(z),DB(z),G,J).
DQ(g0)[h] = a(G0):D2h + Da(G0)[h]:H0
           + D_G lowerTerm[h] + D_J lowerTerm[Dh].
L = dt - DQ(g0).
```

The inverse-variation term contracted with H0 is a required zero-order
coefficient. It must not be omitted. The next exact first action is to define
actual scalar coefficient CLMs and prove, for G0.IsInvertible,

```text
HasFDerivAt (fun G:Bilin => inverseEntries G i j)
  (-(sum_k,l (a(G0)_ik * a(G0)_lj) smul entryCLM_k_l)) G0,
entryCLM_k_l(h) = h(basis3 k,basis3 l).
```

The nonsingularity proof can extract the existing raised-coordinate left
inverse from inverseEntries_eq_coordinates and use
Matrix.det_ne_zero_of_left_inverse. Mathlib hasFDerivAt_ringInverse supplies
H↦-(a*H*a) and Matrix.nonsing_inv_eq_ringInverse identifies the actual inverse.
Keep Matrix.Norms.Operator scoped internally; the public scalar derivative
avoids changing matrix or parabolic carrier norms.

Still unconstructed: the full finite-jet differential, joint coefficient
regularity, its differentiated covariance, and actual bounded global
`L : X_M ->L Y_M` and `R : Y_M ->L Y_M` with
`L.comp Pglobal = id - R` and `norm R < 1`. The old local residual has the
opposite error sign, so signed assembly requires a proof. Apply the physical
differential to reconstructed tensor fields and relocalize by the destination
partition; applying it directly to stored weighted entries introduces real
commutators. Supplied DeTurck linear/Lipschitz interfaces are not producers.

Then nonlinear inversion, matched initial jets and bootstrap must produce
ordinary joint C3 and actual Ricci flow. Within-Icc Graph time derivatives do
not provide ordinary initial-time regularity. The physical target remains:

```lean
∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, MetricEntriesJointContDiffAt gt t x 3
```

Continuation/surgery, independent smooth reconstruction, favorable metric
and actual Hamilton limit construction remain open. The existing final
consumer still requires independent smoothability and universal Hamilton
existence. Neither it nor a sphere conclusion was used as an input to the
new constructors. The complete proof goal and frozen endpoint are unchanged.

## Verification and preserved evidence

Root independently reviewed source-only diffs and reran the recorded-base
fresh Lean, forbidden-token, diff and exact frozen type/universe/foundational
axiom gates. Focused dependency scans cover every emitted declaration,
including private lower-term helpers, without expanded registry export.
Local Codex helpers are honestly recorded as local attempts, not registered
Pi/Leanstral runtime Jobs. Source/compiler failures, exact type diagnostics,
readback probes, final diffs and gate logs are archived in gzip manifests.
Existing dirty work and old branches were preserved. Root direct-import
coverage is checked before the single integration checkpoint.

The source-bound integration checkpoint at `5feae0855391338af7281ad9165f89e0db6bd7d6` passed
fresh root source and the full Lake build, interface, mathlib-gap, shape,
theorem-contract, semantic, root-import and axiom audits. Completion exited 1
only because the reserved final theorem is absent. Completion is not
certified; both universal cores and the complete proof goal remain open.
Evidence: `harness/v2/state/verification/checkpoints/20260930T084421Z-81c7bad93dfb4a109931295b29b3e56a`.
