# Constructed linearized covariance on the Hamilton route — 2026-09-30

The selected core is `Poincare.UniversalHamiltonConvergenceStatement`. No
universal core assumption was discharged. The exact smoothability and Hamilton
obligations remain open, and this batch supplies a necessary local geometric
input for the actual global DeTurck operator.

## Exact remaining core obligations

Lean's smoothability type is:

```lean
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [SimplyConnectedSpace M] [CompactSpace M],
  ∃ charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
    letI := charted
    IsManifold (𝓡 3) ∞ M
```

Its registered name is `Poincare.ExistsSmoothabilitySmoothManifoldStatement`.
The namespace is Poincare; the earlier wrong namespace probe is preserved.

The selected Hamilton type is:

```lean
∀ (N : Type u) [TopologicalSpace N] [T2Space N]
  [SecondCountableTopology N]
  [ChartedSpace (ClosedSmoothModel 3) N]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
  [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
  HamiltonConvergencePinchedLimit3 N
```

For each N its actual payload is a smooth Riemannian metric g with
MDifferentiable scalar curvature everywhere, tracelessRicciNormSqAt=0
everywhere, and scalarAt>0 somewhere. The sufficient finite-energy interface
still requires an actual all-forward normalized flow, integrable traceless
energy, a compact metric family realizing that flow, a continuous mean-energy
pair, and one positive mean-scalar lower bound for all forward times. None of
those universal producers is supplied by this batch.

## Non-circular route and discharged local obstacles

The intended route constructs actual initial metrics and local parametrices,
assembles the already constructed global P with actual coefficients and full
covariant linearization into global L/R, obtains the correctly signed id-R
contraction, and constructs a nonlinear solution/physical flow. Continuation,
surgery, favorable flow, finite energy and compact-limit production are still
unproved links. The existing unconditional recognition then consumes the
Hamilton metric. Independently constructed compatible smoothability and the
Hamilton endpoint feed
`poincareConjectureStatement_of_exists_smoothability_of_universalHamiltonConvergence`.
No Poincare/spherical witness is used to construct analytic inputs.

`DeTurckParameterJet.twoJet_hasDerivAt_of_affine_on_open` proves the parameter
derivative at zero of the actual value/first/second spatial-derivative tuple.
The common open-domain affine identity is transported to first derivatives on
a neighborhood before differentiating again. It consumes C2 base/variation
fields, no supplied jet derivative certificate. Its subsequent consumer is
the actual geometric-evolution derivative below.

`DeTurckPullbackTwoJet.pullback_twoJet_congr` proves that matched C2 two-jets
remain matched after the actual bilinear pullback in BOTH tensor slots. The
coordinate map is C3; its Jacobian is differentiated twice. No germ equality,
Holder density, symmetry or invertibility premise is added. Its subsequent
consumer is transfer of constructed smooth covariance to symmetric C2 Graph
germs, then global L/R.

`DeTurckActualEvolutionDerivative.hasDerivAt_chartEvolution_of_affine_inner`
derives C2 unblended chart coefficients from a smooth global tensor, derives
whole-domain affine coefficients from the common all-fiber affine inner germ,
and composes the complete finite-jet differential with the parameter two-jet.
A genuine explicit identification proves that this jet expression is actual
geometric -2 Ric + Lie_W g. The derivative retains inverse-metric variation
against D2g0 and the full lowerTerm differential. Its subsequent consumer is
the constructed covariance proof; chartLift/metricVariation supply its actual
smooth tensor and family hypotheses.

`DeTurckConstructedCovariance.chartLift_differential_covariance` constructs
that genuine Riemannian family internally from smooth compact symmetric F in
the actual lift chart target. It derives the smooth lift and common affine
inner germ, applies the actual derivative in BOTH anchors, and differentiates
the existing nonlinear tensor covariance. Its conclusion is whole Bilin
pullback equality for the full DQ. There is no metric-family, smooth-lift,
affine-identity, derivative or covariance certificate premise. True overlap
and cutoff-one germs in both charts remain explicit. Its subsequent consumer
is C2 germ transfer and actual global L/R.

A joint kernel application starts by constructing g0, constructs the compact
smooth symmetric F from a symmetric C2 germ's exact two-jet, and applies this
covariance theorem. Thus these inputs are actually produced in the checked
application, rather than hidden in a conditional package.

## Exact next local obligation

For the true chart transition phi from chart1 to chart2, let

```lean
T q y := pullbackBilinearForm (q (phi y)) (fderiv ℝ phi y)
```

and define D_a(q)(y) by the existing `DeTurckJetLinearization.differential`
applied to ((q y, fderiv ℝ q y), fderiv ℝ (fderiv ℝ q) y), at the ACTUAL chart
metric g0 jets and fixed background B/DB in chart a. The remaining target for
an arbitrary symmetric C2 germ q at phi z is:

```lean
pullbackBilinearForm (D_anchor2(q)(phi z)) (fderiv ℝ phi z) =
  D_anchor1(T q)(z)
```

with true overlap and both cutoff-one germs. Freeze its exact literal Lean
type next. Derive transition C3 and its actual Jacobian identities from the
true overlap; use compact two-jet realization, constructed lift covariance,
whole-target chart recovery, neighborhood chart transport and the proved
pullback_twoJet_congr. Never assume equality of q and its smooth realization
on a neighborhood. This target is not yet a repository theorem.

Actual bounded global L/R, signed contraction (local residuals are id+R_i),
nonlinear inversion, matched initial time jets/ordinary joint C3, physical
flow and the universal continuation/energy/limit producers remain open.

## Verification and evidence

Root independently checked each exact-base source-only diff and reran the
scoped Lean, token, diff and frozen literal/universe/axiom gates. Original
operator norms, scalar actions, topologies and frozen core types are intact.
The new modules are directly imported by the root. Whole-module dependency
checks include helpers and reject unsafe/partial constants or non-foundational
axioms. Workers are labelled local Codex helpers, not registered Pi Jobs.

The original actual-evolution audit parser lacked Manifold scope for the
literal 𝓘 notation. The same literal probe passed with that scope; the fixed
generator opens it only when selected types use the notation. Frozen bytes and
rigid expression comparison are unchanged. The regression suite passed.
Original failed probes and all compiler attempts are retained. Pullback worker
evidence written under primary state was also copied into integration state
without deleting the original. Dirty/unmerged historical worktrees remain.

## Sealed integration checkpoint

Clean checked source: `773b742d76e9adee76f8df959df8907f5c735600`.

Source SHA256: `ecdfba9888fd7c6adf10beeb1c97c803900e2d01f929b1c31cf8b5eefab7ddf0`.

The full build and all integration audits passed. Completion exited 1 only
for the absent local reserved name and failed exact final-theorem probe.
`Poincare.poincare_conjecture : Poincare.PoincareConjectureStatement` remains
absent. No completion claim follows from this checkpoint.

Every retained attempt and checkpoint artifact is compressed under
`core-deturck-covariance-20260930-evidence`; manifest SHA256 values for both
original and gzip bytes were independently rechecked against originals.
The final evidence commit changes only archived reports/generated status,
preserving the checked source identity.
