# The Riemannian Foundation (2026-06-10)

This document records the genuine formalized layer added to this repository,
replacing reliance on the vacuous interface scaffold documented in
`INTEGRITY_ASSESSMENT.md`. Everything below is compile-verified
(toolchain `leanprover/lean4:v4.30.0-rc2`, full build green), with no
`sorry`, no axioms, and no opaque-`Prop` placeholders.

## Modules (in dependency order)

- `Poincare/RiemannCurvatureOperator.lean` — the Riemann curvature operator
  `R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` of a covariant derivative on
  the tangent bundle (absent from Mathlib); antisymmetry; pointwise
  tensoriality in `(X,Y)` via Leibniz cancellation; the pointwise curvature
  tensor (`TensorialAt.mkHom₂`); the Ricci trace; regularity discharge for
  `C¹` connections.
- `Poincare/FlatModelConnection.lean` — the flat connection on a normed
  space (first concrete `CovariantDerivative` instance anywhere); flatness
  of Euclidean space via Schwarz symmetry; torsion-freeness and
  inner-product compatibility (flat = Levi-Civita of Euclidean space).
- `Poincare/LeviCivitaUniqueness.lean` — pointwise `MetricCompatibleAt` /
  `TorsionFreeAt`; uniqueness of the Levi-Civita connection (S₃ argument);
  the Koszul formula for any compatible torsion-free connection.
- `Poincare/BianchiIdentity.lean` — the first Bianchi identity (global-C²
  form), including the cyclic Jacobi identity derived from Mathlib's Leibniz
  form.
- `Poincare/RicciFlowEquation.lean` — `IsLeviCivitaAt`; the Ricci flow
  equation `∂g/∂t = −2 Ric` with genuine content; Euclidean space as a
  verified static solution; canonical Ricci values of the model vanish.
- `Poincare/LocalConnectionRegularity.lean` — the local-regularity keystone
  (bump-function globalization + germ locality): `∇Z` differentiable at `x`
  for `Z` only `C²` *at* `x`; admissibility of canonical extensions; the
  canonical Ricci bilinear form; germ locality of curvature.
- `Poincare/ChartIdentification.lean` — chart formulas for the Lie bracket,
  `extDerivFun`, and pullbacks; the bracket-derivation identity
  `df([X,Y]) = X(Yf) − Y(Xf)` in chart and invariant forms (boundaryless
  manifolds), transferred from the model space through `extChartAt`.
- `Poincare/CurvatureTensoriality.lean` — full tensoriality of curvature in
  the field slot (smul/add/finite-sum/value-dependence via local frames);
  the genuine Ricci tensor (extension-independent, bilinear); localized
  Bianchi identity; Ricci antisymmetry identity; pair antisymmetry from
  compatibility; Ricci symmetry (g-skew operators are traceless); pair
  symmetry `g(R(a,b)c,d) = g(R(c,d)a,b)`; sectional numerator and scalar
  curvature.
- `Poincare/KoszulExistence.lean` — the Koszul functional with all six
  slot-laws (tensorial in direction and test slots, connection laws in the
  section slot) and value-dependence in both outer slots; the constructed
  `leviCivitaValueAt` with its defining Koszul property; verified
  torsion-freeness, metric compatibility, additivity, Leibniz; the pointwise
  fundamental theorem (`covDeriv_eq_leviCivitaValueAt`); the bundled
  `leviCivitaConnection : CovariantDerivative` with `IsLeviCivitaAt` at
  every point; the metric-only Ricci flow formulation.

- `Poincare/EuclideanLeviCivitaCheck.lean` — end-to-end model validation:
  the constructed Levi-Civita connection of the Euclidean metric *is* the
  flat connection (by bundled uniqueness), its curvature vanishes on
  `C²` fields through the whole pipeline, and the sectional numerator
  vanishes on all planes.
- `Poincare/CurvatureConditions.lean` — `IsEinsteinAt`, `HasNonnegRicciAt`,
  `HasPosRicciAt` against the genuine Ricci tensor; Euclidean space is
  Ricci-flat; scalar curvature of Einstein connections is `lam * dim`;
  Einstein metrics flow by linear scaling (exact Ricci flow solutions);
  the extinction time `1/(2 lam)` of the shrinking family, with vanishing
  at and negativity past it — the first quantitative extinction statements;
  Ricci agreement for coincident connections; scale invariance of the
  Levi-Civita connection; time-translation invariance and full parabolic
  rescaling of flow solutions; the fixed-point characterization (static
  solutions ⟺ Ricci-flat); the full affine symmetry group
  (`parabolic_reparam`); the representation-independence suite — curvature
  operator, sectional numerator, Ricci form, scalar curvature, and all
  condition classes transfer across connections agreeing on differentiable
  fields; the scalar-curvature scaling law and the
  blow-up of scalar curvature at the Einstein extinction time
  (`Tendsto … atTop`) — the first formal singularity-formation statement;
  positive Ricci curvature of shrinking Einstein connections.

Additions to earlier modules: bundled uniqueness
(`leviCivitaConnection_eq_of_isLeviCivita`), the `IsLeviCivitaAt` and
metric-only flow wiring in `KoszulExistence.lean`, the `C^k` instance for
the flat connection in `FlatModelConnection.lean`, and the canonical flat
Ricci vanishing in `RicciFlowEquation.lean`.

- `Poincare/ModelChristoffel.lean` — the Christoffel program on the model
  space: the corrector `Γ` (defined via the metric dual of the Koszul
  corrector functional) with its defining property, symmetry (via the
  CLM-composition transfer of metric symmetry to the derivative),
  bilinearity, and packaging as a continuous endomorphism-valued one-form;
  `modelLeviCivita = flat + Γ` via `addOneForm`; the trilinear product rule
  `fderiv_metric_pairing`; verified torsion-freeness and metric
  compatibility; and the identification with the canonical construction —
  the Levi-Civita connection in a form involving exactly one derivative of
  the metric; the closed form `Γ = G⁻¹ Φ` via operator inversion
  (`metric_isInvertible`, `christoffelAt_eq_inverse`); smoothness of the
  corrector (`contDiffAt_christoffelAt`, fixed directions) and along smooth
  sections (`contDiff_christoffel_apply_section`, by the per-vector
  evaluation criterion at both levels); and the stratum's first major
  theorem, `modelLeviCivita_contMDiff` — **the Levi-Civita connection of a
  `C^{k+1}` metric is a `C^k` covariant derivative** on the model space,
  putting every instance-gated theorem of the development at the disposal
  of smooth metrics; the concrete Ricci symmetry for `C²` metrics; the
  model-space Ricci flow as an honest PDE
  (`isRicciFlowSolutionAt_of_model_metric`); the consistency triangle
  (constant metrics have vanishing corrector, `modelLeviCivita` of a
  constant metric *is* the flat connection, and is Ricci-flat); and the
  complete static-solution family of the model flow
  (`const_metric_static_model_flow`).

- `Poincare/ChartTransport.lean` — the chart-transport stratum (opened):
  `chartMetric`, the pullback of a manifold metric through the tangent map
  of the inverse chart (built at the `LinearMap` level — `mk₂` over the
  tangent fibre + `compl₁₂` — since abstract tangent spaces carry no norm);
  its application formula, inherited symmetry, and nondegeneracy wherever
  the chart tangent map is invertible (with the centre-point corollary).
  positive-definiteness inheritance; the model-space anchoring
  (`chartMetric_model_space`); the scalar-reduction principle
  (`contDiff_chartMetric_iff`); the inverse-chart tangent-field smoothness
  (`contMDiffOn_inverseChart_tangentMap`); the target/range derivative
  bridge; and the globalized `blendedChartMetric` (cutoff-glued, with
  symmetry, positive-definiteness, and nondegeneracy). Remaining in this
  stratum: the hom-bundle pairing assembly of `chartMetric` smoothness,
  then the connection correspondence.

- `Poincare/MaximumPrinciple.lean` — the maximum-principle stratum
  (opened): the scalar ODE comparison backbone — `ode_comparison_nonpos` /
  `ode_comparison_nonneg` (sign persistence under `u' ≤ C u`, the scalar
  shadow of curvature-condition preservation), `riccati_lower_bound`
  (`u' ≥ a u²` forces the hyperbolic lower bound `u₀/(1 − a u₀ t)`), and
  `riccati_forces_finite_time` (explicit bound `T < 1/(a u₀)` on any
  interval of validity) — Hamilton's finite-time-singularity mechanism at
  its analytic core; `riccati_upper_bound` and `riccati_doubling_time`
  (blow-up control, the canonical-neighbourhood doubling mechanism); and
  the exact saturation of the Riccati engine by the verified Einstein
  scalar (`einstein_scalar_hasDerivAt_riccati`), cross-validating the
  analytic and flow strata.

- `Poincare/ModelLaplacian.lean` — the Laplacian stratum (opened):
  `modelLaplacian` (the trace of the Hessian against the inverse metric on
  the model space), linearity, and the anchoring computation
  `modelLaplacian_quadratic` (`Δ` of the metric's quadratic form is `2n`).
  The operator driving every evolution equation of the flow; affine
  functions are harmonic; **the spatial maximum principle**
  (`modelLaplacian_nonneg_of_isLocalMin`) — at a local minimum the
  Laplacian is nonnegative — assembled from the 1-d and multivariate
  second-derivative tests (both new beyond Mathlib, in
  `MaximumPrinciple.lean`) and trace positivity of PSD forms against
  positive metrics (`trace_dual_comp_nonneg`, via orthogonal bases);
  Hamilton's touching-point inequality; the first-crossing-time lemma; and
  **the parabolic maximum principle on compact domains**
  (`parabolic_min_principle_strict`) — strict reaction–diffusion
  supersolutions positive at time zero stay positive, by minimum-tracking
  through the first zero; the non-strict form (`parabolic_min_principle`,
  by ε-exponential perturbation); and the flow-shaped corollary
  `heat_supersolution_nonneg_preserved` — Hamilton's "nonnegative scalar
  curvature is preserved", modulo the evolution equation (the honest
  hypothesis awaiting commutation machinery). The centerpiece of
  Hamilton's analytic toolkit, complete in both variants, extended to
  **variable coefficients** (strict and non-strict), and culminating in
  **Hamilton's scalar comparison** (`hamilton_scalar_lower_bound`: `R`
  stays above the exact Riccati barrier under the evolution inequality)
  and **Hamilton's finite-time singularity theorem**
  (`hamilton_finite_time_singularity`: bounded solutions cannot persist to
  `1/(a m₀)`) — formal modulo the single hypothesis of the curvature
  evolution equation, with the trace Cauchy–Schwarz
  (`trace_sq_le_card_mul_trace_comp_self`) supplying `R² ≤ n|Ric|²`. The Bochner
  layer joins the strata: `covariantHessian` (the geometric second
  derivative of the Christoffel connection, symmetric by Schwarz +
  corrector symmetry), `curvedLaplacian` (the Laplace–Beltrami operator,
  trace of the covariant Hessian), and the anchor `curvedLaplacian_const`
  (= the flat Laplacian on constant metrics); `metricGradient` with its
  defining property; operator linearity and the constant/critical-point
  anchors; **the curved spatial maximum principle** (the corrector dies at
  critical points) and **the parabolic maximum principle on curved
  backgrounds** (`curved_parabolic_min_principle_strict`) — Hamilton's
  maximum principle in the geometric generality his estimates require;
  and the Laplacian product rule `Δ(fg) = fΔg + gΔf + 2b(∇f,∇g)` with its
  square form, the curved product rule (`curvedLaplacian_mul`, verbatim on
  any metric), and the Laplacian chain rule
  (`Δ(φ∘f) = φ'(f)Δf + φ''(f)|∇f|²`, global and local forms) and its
  dividends `Δ(log f) = Δf/f − |∇f|²/f²`, `Δ(e^f) = e^f(Δf + |∇f|²)`,
  and the L² inequalities — the complete functional calculus of
  Perelman's 𝓕/𝒲 computations; the heat equation (`IsHeatSolutionAt`)
  with its fundamental quadratic solution and the maximum principle wired
  end-to-end; the metric divergence with `div∘grad = Δ`; the
  conjugate-heat weight identity `Δ(e^{−f}) = e^{−f}(|∇f|²−Δf)`; and the
  entropy stratum: `perelmanFDensity` and `perelmanWDensity` (both
  integrands from verified components), and the Gaussian shrinking soliton
  in full — gradient `x/2τ`, Laplacian `n/2τ`, and the soliton equation
  `Hess(b(x,x)/4τ) = b/2τ` (with flat Ricci-flatness, exactly
  `Ric + Hess f = g/2τ`): the model self-similar singularity, verified;
  and the bundled soliton language `IsGradientSolitonAt` with both
  canonical inhabitants (`gaussian_isGradientSoliton`,
  `affine_isGradientSoliton`) — the formal vocabulary of Perelman's
  singularity-model classification, opened with verified instances.

- The commutation stratum (opened, in `ModelLaplacian.lean`):
  `flat_second_derivative_commutes`, `covariantSecondDerivative` (the
  `∇²_{v,w}X` of the Christoffel connection, whose antisymmetrization is
  the curvature) with its flat anchor and the constant-metric Ricci
  identity; plus the soliton trace identity `R + Δf = nλ`
  (`isGradientSolitonAt_trace`, via the `E`-typed trace bridge
  `scalarCurvatureAt_eq_trace_E`), flat scalar-flatness, and the
  three-strata Gaussian cross-check. **The curved Ricci identity is
  proved** (`ricci_identity` + `curvatureOp_modelLeviCivita_extend` in
  `ModelChristoffel.lean`): commuting covariant derivatives costs exactly
  one curvature term — the engine of the evolution equations, with
  `extend_model_space'` generalized to normed model spaces (the hidden
  `InnerProductSpace` instance-search was the melter of prior attempts);
  and the **`δΓ` variation theory** — `hasDerivAt_clm_inverse`
  (`d(A⁻¹) = −A⁻¹A′A⁻¹`), the functional slot-derivatives and
  finite-dimensional reconstruction, `hasDerivAt_christoffel_flow`
  (`∂Γ/∂t = G⁻¹Φ_{∂G} − G⁻¹(∂G)G⁻¹Φ_G`), the named `christoffelDeriv`
  with symmetry, and the flat-background linearization
  `christoffelDeriv_const_base = G₀⁻¹Φ_H` and its pairing form
  `b(δΓ(u,v),w) = Φ_H(u,v)(w)` — the opening objects of the DeTurck
  stratum. (The conformal-variation symbol is shelved: nested-CLM scalar
  actions hit instance-path mismatches in this Mathlib snapshot; three
  routes recorded in project memory.)

## What this layer provides

For any symmetric, nondegenerate, pairing-regular metric on a boundaryless
smooth finite-dimensional real manifold: the canonical Levi-Civita
connection (existence + uniqueness), the full Riemann curvature tensor with
all four classical symmetries, the symmetric bilinear Ricci tensor,
sectional and scalar curvature, and the Ricci flow equation posed purely in
terms of the metric family. The hypothesis classes of the
Hamilton–Perelman program (positive scalar/sectional curvature, the flow
equation itself) are now stateable as genuine mathematics.

## The honest remaining road

In order: the curvature evolution equations (the commutation machinery of
second covariant derivatives, discharging the heat-inequality hypotheses
of the now-proven maximum principle); parabolic PDE theory on manifolds and short-time existence of the
flow (DeTurck's trick); Hamilton's curvature evolution equations and
maximum principles; Perelman's entropy and reduced volume; κ-solutions and
canonical neighbourhoods; surgery; finite-time extinction; and the
topological endgame to the Poincaré conjecture. This is a multi-year
research program; no group worldwide has completed it. Future sessions
should continue from this foundation rather than the legacy interface
scaffold, whose vacuity is documented in `INTEGRITY_ASSESSMENT.md`.
