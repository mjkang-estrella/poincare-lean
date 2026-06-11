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
  Remaining in this stratum: smoothness of `chartMetric` from a smooth
  metric, then the connection correspondence.

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

In order: chart transport of the model-space smoothness theorem to general
manifolds; parabolic PDE theory on manifolds and short-time existence of the
flow (DeTurck's trick); Hamilton's curvature evolution equations and
maximum principles; Perelman's entropy and reduced volume; κ-solutions and
canonical neighbourhoods; surgery; finite-time extinction; and the
topological endgame to the Poincaré conjecture. This is a multi-year
research program; no group worldwide has completed it. Future sessions
should continue from this foundation rather than the legacy interface
scaffold, whose vacuity is documented in `INTEGRITY_ASSESSMENT.md`.
