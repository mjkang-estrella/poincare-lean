# Actual finite-jet DeTurck differential toward Hamilton existence

Date: 2026-09-30 America/Los_Angeles. Published starting commit:
`f993ae914f2c705a1e89e12923860772e021f32c`.

## Core assumptions remain open

Neither compatible smoothability nor universal Hamilton/positive-Einstein
existence is discharged. The final reserved declaration remains absent.
The fresh kernel boundary probe inspects the actual quantified statements;
root elaboration and conditional final consumers do not prove completion.

Smoothability still requires, for every target topological M, an actual
replacement `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` over the SAME topology
carrying `IsManifold (𝓡 3) ∞ M`. Hamilton existence still requires, for every
closed simply connected smooth target M,

```lean
∃ (g : ClosedSmoothRiemannianMetric 3 M) (lam : ℝ),
  0 < lam ∧ ∀ x, g.IsEinsteinAt lam x
```

Equivalently, its reduced pinched-limit core is
`∃ g, (∀ x, g.tracelessRicciNormSqAt x = 0) ∧ ∃ x, 0 < g.scalarAt x`.
Actual normalized flow/reaction/compact parameterization, compact reference
metric/volume comparison, third-jet equicontinuity and pointwise compactness,
and subordinate scalar geometry remain universal Hamilton-front obligations.
No flow, positive-Einstein metric or limit was assumed to produce this batch.

## Actual finite-jet derivative constructed

`DeTurckJetLinearization.hasFDerivAt_evolution` proves the genuine derivative
of the explicit inverse-metric principal contraction plus actual lowerTerm:

```text
Q(B,DB,G,J,H) = sum_i,j a(G)_ij smul H(e_i)(e_j)
                + DeTurckPrincipalIdentity.lowerTerm B DB G J
```

The background is fixed while differentiating metric/first/second jets. At
invertible G0 and arbitrary J0/H0, the actual CLM differential is certified
by `HasFDerivAt`. Its complete scalar evaluation is:

```text
DQ(G0,J0,H0)[hG,hJ,hH](v,w)
 = sum_i,j a(G0)_ij * hH(e_i,e_j)(v,w)
   + sum_i,j [-sum_k,l a(G0)_ik * hG(e_k,e_l) * a(G0)_lj]
                 * H0(e_i,e_j)(v,w)
   + D(lowerTerm B DB)(G0,J0)[hG,hJ](v,w).
```

Both inverse factors, the minus sign and the contraction with H0 remain.
The latter is a required zero-order coefficient when H0=D2g0. It is not
replaced by a scalar heat operator. The lower differential is the actual
Frechet derivative of the explicit lowerTerm, whose differentiability is
proved; it is not an assumed lower-operator package or the unconstrained
existential lower from principalIdentity.

The derivative proof reconstructs CLM-valued derivative certificates from
finite-dimensional scalar slot evaluations, using the real scalar product
rule and actual inverse-entry derivative. This avoids expensive generic
vector-smul dictionary normalization. The unchanged canonical CLM/product
norms and additive structures are explicitly cached where inference needs
it; no norm, scalar action or supplied hypothesis was added.

A genuine-metric application check supplies G0, DG0 and D2G0 from the actual
chart metric, with background Christoffel B and DB, under actual chart-target
membership and the existing cutoff-one germ. It proves invertibility, equality
of this Q with the actual chart evolution, and the derivative certificate
at those same metric jets. Background bg stays arbitrary. This confirms the
new expression is linked to the physical evolution before global assembly.

## Independent prerequisites and their consumers

`DeTurckMetricJetNonsingular.coordinate_matrix_isUnit` constructs the actual
coordinate matrix unit from G0.IsInvertible via the raised-coordinate left
inverse N*M=1. Its immediate consumer is inverse-entry differentiation.
`DeTurckInverseEntryDerivative.hasFDerivAt_inverseEntry` constructs the real
scalar coefficient derivative
`h ↦ -sum_k,l a(G0)_ik*h(e_k,e_l)*a(G0)_lj`. Matrix operator norms stay internal;
public Bilin/real norms remain unchanged. This supplies Da:h for full DQ.

`DeTurckLowerJointSmoothness.contDiffAt_lowerTerm_joint` proves smoothness of
actual Bilin-valued lowerTerm with B/DB/G/J all varying, at invertible G0.
Its subsequent consumer is the spatially varying partial differential and
zero/first-order coefficient maps of the actual L. Fixed-background
smoothness alone would not provide that dependence. Every Task explicitly
helps core H through these named consumers.

## Exact next construction

The full finite-jet derivative is proved, but actual global L is still absent.
First construct the partial-derivative bridge. Let

```text
BG = Background × BackgroundDerivative
V = Bilin × Jet1
F ((B,DB),(G,J)) = lowerTerm B DB G J
inr(hG,hJ) = ((0,0),(hG,hJ)).
```

Prove at invertible G:

```text
lowerDifferential B DB G J = (fderiv R F ((B,DB),(G,J))).comp inr.
```

Then prove joint smoothness of the partial differential using actual joint
smoothness, `ContDiffAt.fderiv_right` and composition with constant inr.
Compose with actual spatial z↦((B(z),DB(z)),(G0(z),DG0(z))) to construct
coefficient regularity. The invertible-G domain is the open range of continuous
linear equivalences E→dualE, pulled back by the metric projection; it must not
be mistaken for units in an endomorphism ring.

Still unproved: those spatial coefficient maps and quantitative compact-buffer
bounds, differentiated tensor covariance, and actual bounded global
`L : X_M ->L Y_M` and `R : Y_M ->L Y_M` with
`L.comp Pglobal = id - R`, `norm R < 1`. The actual Pglobal and linked local
residuals already exist. Apply L to reconstructed tensor fields and relocalize
by destination partition; applying it directly to stored weighted entries
introduces real localization commutators. Local R_j=L_j S_j-id has the opposite
error sign, which signed assembly must handle explicitly.

Nonlinear inversion, matched initial jets, ordinary joint C3 and actual
physical Ricci flow remain unproved:

```lean
∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
  gt 0 = g0 ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, IsClosedRicciFlowSolutionAt gt t x) ∧
  ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, MetricEntriesJointContDiffAt gt t x 3
```

Within-Icc derivative graphs do not supply ordinary initial-time regularity.
Continuation/surgery, independent smooth reconstruction, favorable metrics
and actual Hamilton limits remain open. Existing final reduction still needs
independent proofs of both universal cores. The new inputs do not use that
reduction, a sphere conclusion or the final theorem as a premise.

## Preserved failed contract and verification evidence

The original unit Task accidentally elaborated bare IsUnit of a function
as `Pi.monoid`; the approved readback incorrectly treated it as matrix
multiplication. That target is false for ordinary invertible diagonal matrices
with zero off-diagonal entries. It was not forced or accepted. The worker's
actual left-inverse proof exposed the mismatch. Original contract, incorrect
readback, failed source/compiler output and dirty worktree remain preserved.

A superseding independently reviewed contract explicitly uses
`@IsUnit (Matrix (Fin 3) (Fin 3) R) Matrix.semiring.toMonoidWithZero.toMonoid`.
Raw-expression and kernel-rfl checks confirm actual matrix multiplication and
identity. The repaired proof and all independent scoped gates passed. The
frozen Poincare target and universal cores were not altered.

Failed joint/default-scope product probes are also preserved. Canonical Jet,
background and product bindings are checked against actual operator norms and
stored module/additive dictionaries. Successful full literal preflight rejects
recovered placeholders and unresolved term/level metavariables. Every compiler
attempt, including bounded normalization timeouts and successful scalar
reconstruction, is retained with final diffs.

Root independently reviews actual source-only diffs and reruns recorded-base
fresh Lean, forbidden tokens, diff and exact type/universe/foundational axiom
gates. Focused private-inclusive dependency scans avoid expanded registry
metadata. Local Codex helpers are local attempts, not registered Pi/Leanstral
runtime Jobs. Gzip manifests pin original and compressed bytes. No existing
dirty branch/worktree or failed evidence was deleted.
