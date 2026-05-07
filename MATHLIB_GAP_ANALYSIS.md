# Mathlib Gap Analysis For Poincare Formalization

This file records evidence from the local mathlib checkout used by this project.

## Existing Useful Surface

The project can import and build against:

- `Mathlib.Geometry.Manifold.PoincareConjecture`
  - Contains canonical statements for the generalized, topological 3D, and
    smooth 3D Poincare conjectures.
  - The 3D statements are currently `proof_wanted`.
  - In this local checkout, those `proof_wanted` names are visible in the source
    file but are not exposed as ordinary Lean constants for `#check`; the audit
    therefore treats the source-level `proof_wanted` entries as the authoritative
    gap evidence.
- `Mathlib.Geometry.Manifold.Instances.Sphere`
  - Provides charted-space and analytic-manifold structure for unit spheres.
  - In particular, the 3-sphere target can be represented as
    `Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1`.
- `Mathlib.Geometry.Manifold.Riemannian.Basic`
  - Defines a Prop-valued `IsRiemannianManifold` class on top of an emetric
    structure and a Riemannian tangent bundle.
  - Provides the standard Riemannian metric on an inner product vector space.
  - Constructs a distance from a Riemannian structure.
- `Mathlib.Analysis.ODE.PicardLindelof`
  - Provides local existence of integral curves and local flows for
    time-dependent vector fields in Banach spaces.

These are real formalized dependencies and are useful starting points.

## Missing Surface For A Perelman Proof

Searches of the local mathlib checkout did not find a formalized stack for:

- Ricci curvature as a tensor attached to a Riemannian manifold.
- Scalar curvature and sectional curvature API at the level needed by Ricci
  flow.
- Ricci flow equation on closed manifolds.
- Parabolic PDE existence/regularity theory suitable for Ricci flow.
- Singular-time analysis for Ricci flow.
- Perelman reduced length, reduced volume, and non-collapsing.
- Canonical-neighborhood theorem.
- Ricci flow with surgery.
- Long-time existence with surgery.
- Finite extinction for compact simply connected 3-manifolds.
- The topological extraction theorem from finite extinction to homeomorphism
  with `S^3`.

## Consequence

The current project can honestly formalize the statement layer and maintain a
precise dependency ledger, but it cannot complete the Poincare proof without a
large new formalization of differential geometry, geometric analysis, and
3-manifold topology.

The next proof-bearing milestone would be much smaller than Poincare itself:
define a minimal Ricci-curvature API compatible with mathlib's current
Riemannian manifold classes, then prove elementary consistency lemmas for a
known example such as Euclidean space.

## Local Interface Progress

`Poincare/RicciFlowInterface.lean` now exposes the split between:

- finite extinction under Ricci flow with surgery; and
- the topological extraction theorem from finite extinction to a homeomorphism
  with `S^3`.

It proves that those two future theorem inputs imply
`PoincareConjectureStatement`. This is not the missing Ricci-flow proof, but it
does define the Lean boundary at which that proof should connect to the final
Poincare statement.

`Poincare/RicciFlow.lean` adds a minimal typed API around mathlib's
`ContMDiffRiemannianMetric`, representing time-dependent Riemannian metrics,
candidate Ricci tensor fields, Ricci-identification evidence, and the Ricci-flow
equation as future theorem interfaces. It does not construct Ricci curvature
from a connection, since that surface is still absent from the local mathlib
checkout. It now also proves the algebraic zero-candidate consistency layer:
given future evidence that the zero derivative and zero Ricci candidates are the
correct derivative and Ricci tensor for a metric, the explicit equation payload
verifies `∂ₜ g = -2 Ricci` by reducing both sides to zero. The same explicit
inputs now build zero Ricci-flow data and an analytic equation-boundary package,
so the flat/stationary candidate route reaches the existing boundary statement
without inventing any constructor for the missing equation interface.

`Poincare/Surgery.lean` adds the next typed boundary: Ricci flow with surgery,
Perelman singularity control, and derivation of finite extinction. These are
interfaces only; the local mathlib checkout still lacks the geometric-analysis
theorems that would inhabit them.

`Poincare/TopologyExtraction.lean` adds the post-extinction topology boundary:
decomposition data, 3-sphere recognition, and the extraction package that
supplies `ExtinctionImpliesSphereStatement`. These remain interfaces because the
needed 3-manifold classification theorem is not present locally.

`Poincare/Smoothability.lean` adds the bridge from the topological target
statement to the smooth model used by Ricci flow with surgery. It remains an
interface because the needed smoothability/compatibility theorem is not supplied
locally.

`Poincare/FullAssembly.lean` verifies that these interfaces compose into the
project's target proposition once explicit smoothability, surgery, and topology
packages are supplied. It is conditional assembly, not a replacement for the
missing dependencies.

`Poincare/Dependencies.lean` packages those future inputs into a single
`PoincareProofDependencies` structure. This is the current executable target for
future formalization work: fill that package with real proof terms, then the
project-level statement and completion criterion follow.

`Poincare/DependencyCrosswalk.lean` maps the data-only dependency milestones to
the concrete package layers. This keeps the missing-work ledger aligned with the
executable proof spine.

`Poincare/CompletionTarget.lean` records the canonical completion target and the
remaining dependency package that would imply it. It deliberately does not define
the missing theorem `poincare_conjecture`.

`scripts/mathlib_gap_audit.sh` makes the local checkout status executable: it
finds the mathlib `proof_wanted` 3D Poincare statements, confirms the
Riemannian metric infrastructure used locally, checks whether the canonical
3D Poincare names are exposed as Lean constants, and reports that Ricci-specific
and Ricci-flow-with-surgery declarations are absent from the local manifold
surface.
