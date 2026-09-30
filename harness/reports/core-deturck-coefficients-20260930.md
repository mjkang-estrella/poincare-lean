# Actual coupled DeTurck coefficient construction — 2026-09-30

The selected core is `UniversalHamiltonConvergenceStatement`. Neither that
universal existence statement nor compatible smoothability has been proved.
`Poincare.poincare_conjecture` remains absent. This batch removes actual
coefficient-regularity and finite tensor-reconstruction obstacles on the route
to a physical Ricci-flow producer; it does not supply a universal limit.

## Non-circular endpoint route and remaining universal obligations

`Poincare.poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence` consumes exactly these open types:

```lean
Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u}
Poincare.UniversalHamiltonConvergenceStatement.{u}
```

Smoothability expands to:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
  ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    letI := charted
    IsManifold (𝓡 3) ∞ M
```

Hamilton convergence quantifies over compact connected simply connected,
Hausdorff second-countable smooth three-manifolds and requires
`HamiltonConvergencePinchedLimit3 N`: an actual smooth metric with everywhere
differentiable scalar curvature, zero traceless Ricci and positive scalar
curvature somewhere.

The stronger `UniversalHamiltonFrontInputsStatement.{u,v}` requires
`Nonempty (HamiltonFrontInputs.{u,v} N)` with all five stored analytic fields;
it remains open. Existing checked reductions allow the smaller
`UniversalHamiltonFiniteEnergyFlowExistenceStatement.{u,v}` instead. Its actual
per-manifold witness type is:

```lean
∃ (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
  (metric : K → ClosedSmoothRiemannianMetric 3 M)
  (parameter : Ici (0 : ℝ) → K) (c : ℝ),
  (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
  IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) ∧
  (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
  Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) ∧
  0 < c ∧ (∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
```

Prove that universal producer, apply the checked finite-energy-to-Hamilton
reduction and existing unit-curvature recognition, and independently construct
compatible smoothability before the frozen topological reduction. This route
does not assume sphere recognition, positive Ricci, or a flow/limit package to
construct its inputs. The route's future producer stages remain unproved;
short-time flow from arbitrary g0 alone supplies neither an all-forward
normalized flow nor the positive mean-scalar floor. Continuation/surgery and
independent favorable-metric production still need proofs.

## Verified mathematical advance and its exact consumer

Each accepted task names the Hamilton core and the subsequent actual global
linear-operator consumer. The bridge identifies the metric partial derivative
of the actual jointly varying lowerTerm with the joint Frechet derivative
restricted by `(dG,dJ) ↦ ((0,0),(dG,dJ))`. Inverse-entry smoothness and joint
partial-coefficient smoothness then construct smooth actual spatial fields.

`DeTurckActualSpatialCoefficients.actual_spatial_coefficients` constructs, from
g0 and bg, the actual chart metric G, its DG and D2G, background Christoffel B
and DB. On the open chart/cutoff-germ zone it proves G invertible, all inverse
entries smooth, and both coefficient CLM fields smooth. Its full formula is

```text
DQ(G,J,H)[hG,hJ,hH] = a(G):hH + Z(hG) + F(hJ),
Z = Da(G)[·]:H + D_G(lowerTerm),  F = D_J(lowerTerm).
```

The inverse variation against the genuine D2g0 is retained. No curvature,
symmetry, realized-variation or supplied derivative package was introduced.
An application constructs g0 using `exists_initial_metric`, then applies the
actual coefficient producer with bg=g0.

`DeTurckTensorBasis.tensor_expansion`, `firstJet_expansion` and
`coefficient_action` prove whole CLM-valued reconstruction and scalar actions
using all nine tensor and 27 first-jet slots. Their next consumer constructs
actual scalar arrays `c0_abcd = entry_cd(Z(tensor_ab))` and
`c1_pabcd = entry_cd(F(firstJet_pab))`, compactly buffers them on the same atlas,
then constructs bounded coupled Graph forcing with values

```text
K_cd(W) = Σ_ab [c0_abcd W_ab.u + Σ_p c1_pabcd W_ab.du(e_p)].
```

These compact carriers, bounds and coupled Graph operator remain unproved.
Existing local scalar solvers and actual global P are reused. Next are
correct differentiated tensor covariance/localization, actual global L/R and
signed `L.comp P = id − R` with `‖R‖ < 1`; local residuals use `id + R_j`.
Nonlinear inversion, matched initial-time jets, ordinary joint C3 and physical
Ricci flow remain unresolved before the later universal flow/limit producers.

## Acceptance and evidence

Five disjoint tasks were checked against their recorded base commits in
isolated worktrees. Root independently reran each fresh source check,
forbidden-token scan, diff check and exact frozen-type/allowed-axiom gate, and
reviewed each source-only diff before acceptance. Canonical operator/product
instances retain the original norm and scalar action. An environment scan
checks every emitted declaration of the new modules for unsafe/partial code
and unexpected axioms, including private helpers. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed.

All failed compiler sources/logs, failed contract preflights, readbacks,
independent reviews and final diffs are preserved. The original full actual
application's default-heartbeat timeout is preserved; the final application
uses the same proof budget as the accepted producer. Local Codex helpers are
labelled as such, not registered Pi/Leanstral Jobs. No dirty or unmerged
worktree was removed. Batch checkpoint evidence will be recorded below.
