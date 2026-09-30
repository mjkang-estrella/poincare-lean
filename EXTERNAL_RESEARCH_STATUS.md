# External Research Status

## 2026-09-30 Published endpoint comparison

The May research below is historical and no longer describes public availability.
Two public projects now provide claimed completed Poincare endpoints:

- FrenzyMath: https://github.com/frenzymath/PoincareConjecture at
  `3d7318c32025ccb30465dd29850e95a9e2aa1526`, Lean4.33.1. Statement/Main and
  Comparator/Solution were inspected. Comparator config names the two real
  endpoint proofs, permits propext/Classical.choice/Quot.sound and enables
  Nanoda. Their September28 announcement reports successful checking; we have
  NOT yet reproduced that build or independent-kernel check. The older
  frenzymath/Poincare-Conjecture repository is a different active workspace.
- DifferentialGeometry: https://github.com/qinz1yang/differential-geometry at
  `777299070a5529e96345e0033979706fd00c7e62`, development Lean4.35rc3. Its
  Topology/ThreeManifold/Poincare endpoint structurally matches our frozen
  topological statement and literal standard sphere. Moise352Producer produces
  a replacement compatible smooth atlas, matching our existence-shaped core.
  README reports a full build/standard axiom footprint; we have NOT yet
  reproduced these checks. Stable v0.1.3 was fetched at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`;
  its toolchain is Lean4.33.1 and its source contains the matching endpoint.

Our toolchain remains Lean4.30rc2. Reuse needs isolated version alignment and
exact statement/axiom validation before any production endpoint or core closure.
Frenzy adds second countability, derivable here from compactness plus the
Euclidean charted space, as our existing topological bridge already does.
Do not map Moise into the older arbitrary-ambient-atlas smoothability predicate,
which our MoiseSmoothabilityTarget explicitly identifies as a false frontier.

First action: reproduce a pinned compatible upstream smoothing producer and
exact endpoint in an isolated comparison project, check allowed axioms and
statement identity, then build the smallest credited adapter to the existing
frozen target. Preserve independent proof work; do not call upstream reuse
a newly completed independent proof. See docs/PROOF_STRATEGY_REVIEW.md.


Date: 2026-05-02

This note records external research performed while assessing whether a complete
Lean proof of the Poincare Conjecture could be imported or adapted.

## Findings

- Mathlib has a canonical statement file for the Poincare conjecture, but the
  local checkout still marks the 3D statements as `proof_wanted`.
- Public search did not find a complete Lean formalization of Perelman's proof
  or of Ricci flow with surgery.
- The visible Lean-related Poincare material found externally is statement-level
  or placeholder-based, not a full proof.
- Contemporary Lean/mathlib material confirms mathlib is broad and growing, but
  does not indicate a completed Ricci-flow-with-surgery proof stack.

## Fresh Check: 2026-05-02

Searches run:

- `Lean Poincare conjecture formalization Ricci flow with surgery Lean theorem prover`
- `site:github.com Lean Poincare conjecture Ricci flow formalization`
- `mathlib PoincareConjecture proof_wanted nonempty_homeomorph_sphere_three`
- `Lean formalization Ricci curvature Ricci flow mathlib`

Result: no importable Lean proof artifact was found. The most relevant current
results still point to:

- mathlib statement/documentation surfaces for the generalized Poincare
  conjecture;
- non-formal mathematical references for Ricci flow with surgery and finite
  extinction;
- broad mathlib capability descriptions, not a completed Ricci-flow-with-surgery
  formalization.

## Refresh Check: 2026-05-02

Additional searches run:

- `Lean formalization Poincare conjecture Ricci flow Perelman mathlib proof_wanted nonempty_homeomorph_sphere_three`
- `site:leanprover-community.github.io mathlib PoincareConjecture Lean SimplyConnectedSpace nonempty_homeomorph_sphere_three`
- `GitHub Lean Poincare Conjecture Ricci flow formalization Perelman`

Result: the current public mathlib documentation still exposes
`Mathlib.Geometry.Manifold.PoincareConjecture` as the canonical Lean statement
surface, and external mathematical references still point to Perelman/Morgan-Tian
Ricci-flow proof sources rather than an importable Lean proof. No public
completed Lean artifact for Ricci flow with surgery, finite extinction, and the
3-dimensional Poincare conclusion was found in this refresh.

## Relevant External References

- Lean/mathlib overview:
  <https://lean-lang.org/use-cases/mathlib/>
- Mathlib `PoincareConjecture` documentation:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/PoincareConjecture.html>
- Mathlib simply-connected-space documentation:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.html>
- Mathlib spectral-analysis snapshot showing scale of current mathlib:
  <https://proofgraph.org/post/2026-03-29-proofgraph-findings/>
- Mathlib-adjacent formal-conjectures project:
  <https://reservoir.lean-lang.org/%40google-deepmind/formal_conjectures>
- Clay Mathematics Institute reference for Morgan-Tian's Ricci-flow proof:
  <https://www.claymath.org/resource/ricci-flow-and-the-poincare-conjecture/>
- John Lott's Perelman/Ricci-flow reference page:
  <https://math.berkeley.edu/~lott/ricciflow/perelman>
- MathWorld summary of Ricci flow:
  <https://mathworld.wolfram.com/RicciFlow.html>

## Conclusion

No complete Lean proof artifact was found to import. The honest project state is
therefore:

1. Build and audit the precise statement layer.
2. Track missing dependencies.
3. Avoid claiming completion until a proof-bearing theorem exists and the
   completion audit passes.
