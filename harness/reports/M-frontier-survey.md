# M-frontier-survey: remaining walls and goal-7 recommendation

Read `harness/worker_contract.md` first. This is a survey-only task: no Lean
source files were changed, and no proof obligations or placeholder statements
were introduced.

Survey baseline:

- Harness ceiling: `HARNESS_STATUS.md` and `M4-audit-5_done.md` say the
  counted theorem-bearing surface is now Levi-Civita foundation, scalar and
  Ricci evolution, positivity/singularity algebra, pinching preservation, and
  pinching improvement. There is still no nontrivial closed-manifold Ricci-flow
  solution.
- Pinned Mathlib: `lake-manifest.json` pins Mathlib at
  `7175569c842f9164564bd76ff8b207e7b4705522`.
- Local Mathlib status: Euclidean/distributional Sobolev tools exist, but
  manifold integration, Riemannian volume/divergence/Stokes, geometric
  parabolic PDE, geodesics/injectivity radius, and space-form classification
  are absent or only statement-level.

## A. Hamilton sections 11-17 convergence chain

### What this repo already provides

The repo is strongest on pointwise and finite-dimensional estimate algebra:

- Canonical closed-manifold curvature vocabulary:
  `ClosedSmoothRiemannianMetric.leviCivita`, `ricciAt`, `scalarAt`,
  `ricciEndoAt`, `ricciNormSqAt`, `gradient`, `hessianAt`, `laplacianAt`.
- Scalar and Ricci evolution predicates and theorem routes:
  `SatisfiesHamiltonScalarEvolutionAt`,
  `SatisfiesRicciEvolutionAt`,
  `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow`,
  `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity`.
- Pinching algebra and maximum-principle wrappers:
  `SatisfiesPinchingQuotientEvolutionAt`,
  `SatisfiesTracelessPinchingImprovementEvolutionAt`,
  `hamilton_pinching_preserved`,
  `hamilton_pinching_improvement`,
  `hamilton_eigenvalue_pinching_floor_preserved`.
- Reaction and quotient algebra:
  `pinchingGradientSquareAt`,
  `pinchingGradientSquareAt_eq_completedSquareExpansion`,
  `pinchingReactionRemainderAt_nonpos_of_scalar_pos`,
  `TracelessPinchingEigenvalueImprovementLemma3_holds`.
- Einstein/equality local rigidity:
  `tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id`,
  `scalarAt_eq_nat_mul_of_isEinsteinAt`.
- Model/single-chart round-sphere and constant-curvature algebra in
  `ModelLaplacian.lean`, useful as coefficient sanity checks, but not a global
  closed-manifold convergence theorem.

This is exactly the surface needed for Hamilton-style reaction algebra and
quotient maximum principles. It is not yet enough for global convergence.

### What Mathlib provides

Useful pieces in the pinned Mathlib tree:

- Smooth manifolds, tangent bundles, smooth vector bundles, partitions of
  unity, and Riemannian path-length distance.
- Euclidean/distributional Sobolev material:
  `Mathlib/Analysis/Distribution/Sobolev.lean` and
  `Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`.
- Basic metric compactness/Gromov-Hausdorff files in topology, but not in a
  Ricci-flow compactness form.

Missing for this front:

- No manifold Riemannian integration layer: no Riemannian volume form API,
  manifold Stokes, or manifold divergence theorem.
- No manifold Sobolev/interpolation/Moser iteration stack.
- No geodesics, exponential map, conjugate radius, injectivity radius,
  Bonnet-Myers/Klingenberg/Cheeger estimates, or Hamilton compactness theorem.
- No Ricci-flow convergence, normalized-flow precompactness, or smooth
  Cheeger-Gromov convergence API.

### Keystone lemmas

The serious keystones are:

1. Moving-metric Bochner formula for scalar gradients:
   `(partial_t - Delta) |nabla R|^2` expressed in terms of Hessian, Ricci, and
   reaction terms under Ricci flow.
2. Higher-derivative regularity package for `R`, `nabla R`, `nabla^2 R`, and
   the Ricci tensor along the flow, strong enough to feed the Bochner formula.
3. Hamilton interpolation estimate for `|nabla R|^2`, using Sobolev/Moser or
   equivalent global analytic input. This is the first genuinely new-analysis
   wall, not just estimate algebra.
4. Improved pinching -> sectional/eigenvalue control in dimension 3, turning
   traceless-Ricci decay into nearly constant sectional curvature.
5. Diameter and injectivity control for normalized positively curved metrics.
6. Normalized-flow compactness and convergence to a constant-curvature metric.

### Honest difficulty

Very high. The estimate-algebra subfronts are tractable because they match the
repo's proven style: finite-dimensional traces, quotient calculus, reaction
signs, and maximum-principle wrappers. The global analytic subfronts are the
wall: interpolation/Sobolev on manifolds, integration by parts, injectivity
radius, and compactness are not locally available in Mathlib or this repo.

Classification:

- Estimate algebra: Bochner term expansion, quotient product rules, reaction
  signs, Ricci eigenvalue algebra, Einstein equality cases.
- New analysis: scalar-gradient interpolation, manifold Sobolev/Moser,
  diameter/injectivity estimates, compactness, normalized-flow convergence.

### Opening roadmap

1. Freeze an exact theorem inventory for Hamilton sections 11-17 in repo
   vocabulary: scalar-gradient estimate, pinching-to-roundness, normalized
   convergence, constant-curvature conclusion.
2. Define a bundled `ClosedRicciFlowGlobalRegularityOn` predicate collecting
   the already repeated `C2/C3` scalar, Ricci, gradient, Hessian, and time
   derivative hypotheses.
3. Prove the scalar-gradient Bochner identity pointwise, assuming that bundle.
4. Add finite-dimensional norm/trace lemmas needed to compare Hessian,
   `|nabla Ric|`, `|nabla R|`, and pinching quantities.
5. State a minimal interpolation theorem as an honest external theorem target,
   not as a Prop-field certificate; use it to derive the Hamilton
   `|nabla R|^2` estimate.
6. Prove the algebraic route from improved traceless pinching to pointwise
   near-Einstein and near-space-form curvature in dimension 3.
7. State diameter/injectivity control as a separate honest target, with exact
   dependencies on curvature bounds and positive lower eigenvalue pinching.
8. State normalized-flow compactness/convergence as a separate honest target.
9. Assemble conditional convergence: if the analytic estimates and compactness
   interfaces are supplied, the current pinching/evolution algebra gives the
   route to constant curvature.

## B. M2 short-time existence

### What this repo already provides

The repo has a real pointwise Ricci-flow equation and closed-metric wrapper:

- `CovariantDerivative.IsRicciFlowSolutionAt`: a pointwise PDE saying the
  metric time derivative equals `-2 Ric` against `C2` fields.
- `ClosedSmoothRiemannianMetric.IsClosedRicciFlowSolutionAt`: the same equation
  using the canonical closed Levi-Civita connection.
- `isClosedRicciFlowSolutionAt_of_metric`: reduces the closed wrapper to the
  genuine pointwise flow equation.
- Static examples:
  `euclidean_static_isRicciFlowSolutionAt` and
  `isClosedRicciFlowSolutionAt_const_of_ricciFlat`.
- Time shift/rescale/reparametrization lemmas in the older pointwise layer.
- Downstream evolution theorems consume a flow once given, but they do not
  construct one.

There are legacy proof-progress/package fields mentioning DeTurck background
compatibility. They should not be counted as analytic existence; the current
honest ceiling says no nontrivial closed-manifold Ricci-flow solution exists.

### What Mathlib provides

Useful but far from enough:

- Banach-space ODE/Picard-Lindelof material.
- Integral curves of vector fields on manifolds.
- Smooth manifold and bundle foundations.

Missing:

- No linear parabolic existence theory.
- No heat-equation semigroup, Schauder, Sobolev parabolic regularity, or
  quasilinear parabolic fixed-point theorem.
- No DeTurck trick, Lie-derivative PDE reduction, or PDE-on-vector-bundles
  infrastructure.

### Keystone lemmas

1. DeTurck vector field definition `W(g, gbar)` and Lie derivative
   `L_W g` in the current closed-metric/tensor vocabulary.
2. Coordinate calculation: Ricci-DeTurck has strictly parabolic principal
   symbol.
3. Linear parabolic existence and estimates for time-dependent sections of
   symmetric 2-tensors on a compact manifold.
4. Quasilinear parabolic fixed-point/existence theorem for Ricci-DeTurck.
5. ODE existence for the DeTurck diffeomorphism flow and regularity of its
   pullback action on metrics.
6. Gauge equivalence: pullback of a Ricci-DeTurck solution solves Ricci flow,
   with initial condition and uniqueness on a short interval.

### Minimal honest interface

The minimal interface should be a theorem-shaped existence statement with
concrete data and consequences, not a vacuous certificate. A good target shape:

```text
theorem exists_shortTime_closed_ricciFlow
    (g0 : ClosedSmoothRiemannianMetric 3 M) :
  exists T : R, 0 < T /\
  exists gt : R -> ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g0 /\
    FlowRegularOn gt (Icc 0 T) /\
    (forall t in Icc 0 T, forall x,
      IsClosedRicciFlowSolutionAt gt t x) /\
    (forall t in Icc 0 T, forall x,
      ClosedRicciFlowExtensionRegularAt gt t x)
```

The consequence layer should then prove, from this one theorem plus existing
evolution packages:

- scalar evolution holds on `(0,T)`,
- Ricci evolution holds on `(0,T)`,
- positive scalar/pinching hypotheses can be passed to the maximum-principle
  theorems when their initial hypotheses are supplied,
- the flow agrees with `g0` at time `0`.

This is still a frontier theorem. It is honest because the statement exposes
the actual metric family, interval, initial condition, PDE, and regularity
needed downstream. It avoids pretending to have the DeTurck construction.

### Honest difficulty

Extreme. This is the M2 wall because it demands a parabolic PDE library on
manifolds. The repo can state and consume the result cleanly, but proving it
means building linear and quasilinear parabolic existence from scratch.

### Opening roadmap

1. Write the exact non-vacuous short-time theorem interface, with no `Prop`
   fields that can be populated arbitrarily.
2. Bundle the downstream regularity classes already required by scalar/Ricci
   evolution into `FlowRegularOn`.
3. Define symmetric 2-tensor fields in the current dependent-family style, or
   first build the missing tensor-field abstraction.
4. Define Lie derivative of a metric along a time-dependent vector field.
5. Formalize the DeTurck vector field against a fixed background metric.
6. Prove the Ricci-DeTurck coordinate principal-symbol calculation.
7. State/prove linear parabolic existence on compact coordinate patches with
   partition-of-unity gluing.
8. Prove the quasilinear fixed-point theorem.
9. Use manifold ODE/integral-curve tools to build the DeTurck diffeomorphism.
10. Assemble short-time Ricci flow and immediately instantiate scalar/Ricci
    evolution consequences.

## C. Dark horse: sphere-recognition endgame

### What this repo already provides

This front has the most theorem-bearing local and topological material already
near the target:

- Pinching equality -> Einstein at a point:
  `tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id`.
- Einstein scalar trace:
  `scalarAt_eq_nat_mul_of_isEinsteinAt`.
- Local Schur lemma in the model layer:
  `schur_fderiv_coordScalar_eq_zero_of_einstein_field`.
- Sectional numerator vocabulary:
  `sectionalNumeratorAt`, `sectionalNumeratorAt_symm`,
  `sectionalNumeratorAt_self`.
- Dimension-3 Ricci-to-Riemann algebraic candidate:
  `riemannFromRicci3At`,
  `RiemannDeterminedByRicci3At`,
  `riemannFromRicci3At_spaceForm_coeff`, plus diagonal section checks.
- Constant-curvature model tensor algebra in `ModelLaplacian.lean`:
  `constCurvatureForm`, sectional/Ricci/scalar trace lemmas, and
  3D constant-curvature coefficient checks.
- Spherical quotient/topological recognition branch in
  `TopologyExtraction.lean`: if a space is already presented as a free
  properly discontinuous quotient of an `S3`-recognized total space, then
  simple connectedness collapses the deck group and gives a homeomorphism to
  `ThreeSphere`.

What is not present is the geometric bridge from "closed 3-manifold has
positive constant sectional curvature" to "it is a spherical space form
`S3/G` with the standard covering model."

### What Mathlib provides

Mathlib provides sphere manifold instances, homeomorphism/diffeomorphism
types, covering spaces, fundamental groups, and statement stubs for the
Poincare conjecture:

- `Geometry/Manifold/Instances/Sphere.lean`.
- `Topology/Compactification/OnePoint/Sphere.lean`.
- covering-space and simply-connected APIs.
- `Geometry/Manifold/PoincareConjecture.lean`, but its Poincare conclusions
  are `proof_wanted` statements, not proved classification tools.

Missing:

- No Riemannian geodesics, exponential map, universal Riemannian cover, or
  Killing/isometry group API for space-form classification.
- No theorem "complete simply connected positive constant sectional curvature
  manifold is isometric/diffeomorphic/homeomorphic to the round sphere."
- No theorem "closed positive constant-curvature 3-manifold is a spherical
  space form."

### Keystone lemmas

1. Limit pinched metric -> pointwise Einstein:
   `tracelessRicciNormSqAt = 0` implies
   `ricciEndoAt = (R/3) * id`, then `Ric = lambda g`.
2. Global/local Schur bridge: the closed-manifold Einstein condition in
   dimension 3 implies scalar curvature is constant, not just in the model
   coordinate lemma.
3. 3D Einstein -> actual Riemann tensor is the constant-curvature tensor:
   this needs the bridge from actual curvature to `riemannFromRicci3At`
   (`RiemannDeterminedByRicci3At`) and then to `constCurvatureForm`.
4. Positive scalar -> positive sectional constant for the limit metric.
5. Space-form recognition interface:
   positive constant sectional curvature on a closed connected 3-manifold
   gives a quotient-covering model with total space homeomorphic/diffeomorphic
   to `S3`.
6. Existing deck-collapse branch:
   simple connectedness of the original target kills the quotient group and
   gives `Nonempty (M ~= ThreeSphere)` or the smooth analogue after the
   existing smoothability bridge.

### Honest difficulty

Medium-to-high, but much lower than A or B if scoped correctly. The algebraic
half is well aligned with the repo's strengths. The hard missing piece is a
space-form classification theorem, but it can be isolated as a narrow,
honest interface. It does not require building parabolic PDE or manifold
Sobolev theory.

The key risk is overclaiming: the repo can prove "pinched limit -> Einstein
and constant-curvature algebra" much sooner than it can prove "constant
positive sectional curvature -> round sphere" from first principles.

### Opening roadmap

1. Define a closed-metric predicate for pointwise traceless-Ricci vanishing on
   all points, using `tracelessRicciNormSqAt`.
2. Prove global Einstein operator form from that predicate via
   `tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id`.
3. Bridge operator form to bilinear `IsEinsteinAt (R/3)` at every point.
4. Lift the local Schur lemma into the closed-manifold API, or state the exact
   coordinate-regularity bridge still needed.
5. Prove scalar constancy and set `kappa = R/6` in dimension 3.
6. Prove the actual curvature tensor is `constCurvatureForm kappa`, assuming
   or proving `RiemannDeterminedByRicci3At` for the canonical curvature tensor.
7. State the narrow non-vacuous space-form interface:
   positive constant sectional curvature on a closed connected 3-manifold
   supplies a free properly discontinuous quotient-covering model with total
   space recognized as `ThreeSphere`.
8. Feed that interface into the existing quotient-covering/simple-connected
   branch to get sphere recognition.
9. Add a smooth endpoint using the existing smoothability/Moise bridge only
   after the topological homeomorphism payload is real.

## Recommendation

Choose front C as goal 7.

Rationale:

- It has the best tractability-to-value ratio. A and B both run into missing
  global analytic foundations in Mathlib: Sobolev/interpolation/integration
  for A, and quasilinear parabolic PDE for B.
- C can produce theorem-bearing progress soon: pinched limit -> Einstein ->
  constant scalar -> constant sectional curvature is mostly local curvature
  algebra and API-bridging, which matches the repo's proven strengths.
- C directly advances the Poincare statement chain once Hamilton convergence
  is treated as an upstream input. It gives a clean endgame target:
  "constant positive curvature plus simple connectedness -> sphere."
- The genuinely hard part of C can be isolated as one honest interface:
  spherical space-form recognition. That interface is much narrower than the
  analytic interfaces needed by A or B and can reuse the existing
  quotient-covering deck-collapse work.

Suggested goal-7 shape:

```text
Goal 7: constant-curvature/spherical-space-form endgame.

Deliver:
1. pinched-limit equality -> global Einstein operator form;
2. global Schur bridge -> scalar constant;
3. dimension-3 Einstein -> constant sectional curvature, modulo the actual
   Riemann-from-Ricci bridge if necessary;
4. a narrow, non-vacuous `PositiveConstantCurvatureSpaceForm3` interface whose
   output plugs into existing quotient-covering recognition;
5. a conditional theorem:
      simplyConnected + closed + positive constant curvature
      + space-form interface
      -> Nonempty (M ~= ThreeSphere)
```

Do not choose A yet unless the task is explicitly to build manifold
Sobolev/integration infrastructure. Do not choose B yet unless the task is
explicitly to begin a multi-month parabolic PDE library. C gives the next
verifiable theorem-bearing frontier without pretending the analytic walls are
gone.

## Verification

Survey/read-only commands were run against the worktree and pinned Mathlib.
No Lean files were edited. This report was written as
`harness/reports/M-frontier-survey.md`.

Commands run after writing the report:

```bash
git diff --check
lake build Poincare.TopologyExtraction
lake build Poincare.Global.ScalarEvolution
```

Results: `git diff --check` passed. Both Lean builds completed successfully
with existing warnings only.
