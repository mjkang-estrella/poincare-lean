Read harness/worker_contract.md first and obey it strictly (rules 1-3 concern Lean code; your deliverable here is a report, so the honesty rules 4-6 are the binding ones).

# Task M0-gap-survey: Mathlib gap survey for the manifold-level Perelman program

Deliverable: `harness/reports/mathlib_gaps.md`, committed. Survey the ACTUAL pinned Mathlib in `.lake/packages/mathlib/` (grep/read it directly — do not rely on memory of Mathlib, it moves fast).

For each area below, report: status (EXISTS / PARTIAL / ABSENT), the exact module paths and key declaration names found, and a 1-3 sentence assessment of what's missing for our use:

1. Smooth manifolds: `IsManifold`, charted spaces, smooth maps, partitions of unity.
2. Vector bundles: tangent bundle, cotangent, tensor bundles, smooth sections, bundle metrics.
3. Riemannian metrics on manifolds: any `RiemannianMetric`/`RiemannianManifold` structure? Levi-Civita connection? Geodesics? Curvature on manifolds (not just our single-chart model)?
4. Connections/covariant derivatives on bundles.
5. Integration on manifolds: volume forms, Stokes, divergence theorem.
6. Algebraic topology: fundamental group, `SimplyConnectedSpace`, covering spaces, Betti numbers/homology, sphere characterizations (e.g. is there ANY homeomorphism-classification machinery?).
7. PDE: elliptic/parabolic theory, Sobolev spaces, semigroups, anything usable toward short-time existence of a geometric flow.
8. The sphere: smooth structure on `Metric.sphere`, its simply-connectedness, `≃ₜ` machinery.
9. Gromov-Hausdorff / metric geometry (needed for blow-up limits): `GromovHausdorff` namespace contents.
10. Prior art: grep for any Ricci-flow, mean-curvature-flow, or geometric-analysis files.

End with a ranked list: the 5 cheapest high-value bridge tasks (things nearly in Mathlib that unlock our M1 tier), and the 3 biggest walls with effort estimates. Commit the report.
