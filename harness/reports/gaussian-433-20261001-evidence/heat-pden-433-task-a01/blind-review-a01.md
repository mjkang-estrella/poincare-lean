# Independent blind mathematical read-back

Reviewer: /root/workflow_bottlenecks, distinct from the statement/task author.
Review date: 2026-09-30.
Verdict: PASS for the literal mathematical meaning of the six frozen declarations, subject to fresh compiler/type/axiom acceptance by the orchestrator. This report makes no core-closure claim.

## Frozen identity and review scope

The supplied snapshot is:
`/Users/mjkang/.codex/worktrees/incremental-verification/poincare/harness/v2/state/upstream-verification-20260930/heat-pden-433-task-a01/blind-snapshot.json`.

Its recorded snapshot digest is exactly:
`00653a6fedf1d8c7319ace7e7d58e051d67dd309f1bd0d517df64bcb804a6ead`.

The JSON file's raw SHA-256 is:
`af20b9bf415301cea6fe3cb93e0072617db48fb3ebc8f30ed82daddf0b75d1f5`.
These are different identity fields; I have not assumed an undocumented canonicalization algorithm for the recorded snapshot digest.

I read the frozen declaration types, the pinned HeatKernel and HeatKernelPDE definitions, and the relevant Mathlib derivative, innerSL and Laplacian definitions. I did not read the task wording or the HeatKernelPDEn proof implementation, run Lean/builds, or edit Lean/Task files.

Relative pin resolution against the directory containing the state artifact initially reached the old Lean 4.30 checkout. Three of its four definition-file hashes did not match the snapshot. I then resolved all four pins against:
`/Users/mjkang/.codex/worktrees/upstream-integration-433/poincare`.
All four hashes there matched exactly:

| Definition file | Verified SHA-256 |
| --- | --- |
| lean-toolchain | 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71 |
| lake-manifest.json | 1d7b430e56fad6141cc360d6684f8259ec40e8412bb9017a34e741e78dea4411 |
| Poincare/Global/HeatKernel.lean | 719c7249148724e351cfd069d4235387fb8b37c53a04e190af6ed2cd1133099a |
| Poincare/Global/HeatKernelPDE.lean | 888f20603ac61654678f2e7c54b6adf821e5ef81db39fde46fb1fa82672877e7 |

The matched toolchain is Lean 4.33.1; the matched manifest pins Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The manifest also includes DifferentialGeometry, but no supplied declaration type or the heat-kernel definition contains a DifferentialGeometry theorem premise.

## Common parameters and operator meaning

Every declaration quantifies over a real inner-product space E, with `NormedAddCommGroup E` and `InnerProductSpace Real E`. E is an implicit type parameter in an arbitrary universe: u_1 for the first five declarations and u_2 for the sixth. Real is in universe 0. The repeated instance names in the snapshot are implicit typeclass binders, not additional mathematical hypotheses.

The first three declarations do not require finite dimension or completeness. The last three require `FiniteDimensional Real E`; zero-dimensional E is included. The dimension is not fixed at three.

Write
`q_t(x) = -||x||^2/(4t)`,
`G_t(x) = exp(q_t(x))`,
and `n = finrank Real E`.
The real continuous linear functional `innerSL Real x` maps v to the real inner product <x,v>. Thus scalar multiples of it in the first two types are actual specified Frechet derivatives.

Mathlib's scalar `deriv` and `iteratedFDeriv` are total derivative operators. An equality involving them is not syntactically a separate `HasDerivAt` or regularity certificate. The first two declarations explicitly assert `HasFDerivAt`, so they do assert derivative existence.

The Laplacian in the snapshot is the canonical inner-product-space Laplacian on E. For a scalar function it is the trace of the second Frechet derivative, equivalently the sum of the diagonal second derivatives in any orthonormal basis. Its sign is the positive sum-of-second-derivatives convention. No manifold Laplace-Beltrami operator or evolving metric is supplied.

## Literal assertions

1. `Poincare.hasFDerivAt_neg_norm_sq_div`

For every real t with t != 0 and every x in E, the function y -> -||y||^2/(4t) has Frechet derivative at x equal to the continuous linear map
`v -> -<x,v>/(2t)`.
The statement applies also when t is negative. Its only non-instance assumption is t != 0.

2. `Poincare.hasFDerivAt_exp_neg_norm_sq_div`

For every real t with t != 0 and every x in E, G_t has Frechet derivative at x equal to
`v -> G_t(x) * (-<x,v>/(2t))`.
Again t may be negative and finite dimension is not assumed.

3. `Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply`

For every real t with t != 0 and every x,v in E, the second iterated Frechet derivative of G_t at x evaluated on the ordered pair (v,v) equals
`G_t(x) * (<x,v>^2/(4t^2) - ||v||^2/(2t))`.
This is a diagonal Hessian evaluation for an arbitrary direction v. It does not state the mixed two-direction formula as a separate deliverable, nor a time derivative. Negative t is allowed.

4. `Poincare.sum_sq_inner_stdOrthonormalBasis`

For finite-dimensional E and every x in E,
`sum_{i in Fin(n)} <x,e_i>^2 = ||x||^2`,
where e_i is Mathlib's chosen standard orthonormal basis of E. This is a finite Parseval identity. There is no time parameter and no nonzero-dimension assumption.

5. `Poincare.laplacian_exp_neg_norm_sq_div`

For finite-dimensional E, every real t with t != 0 and every x in E,
`Delta G_t(x) = G_t(x) * (||x||^2/(4t^2) - n/(2t))`.
Here n is coerced from its natural-number finrank to Real. This is the spatial Laplacian of the unnormalized exponential factor. It holds at negative time as a calculus identity; it is not itself a positive-time heat-kernel existence theorem.

6. `Poincare.heatKernel_heatEquation_laplacian`

For finite-dimensional E, every positive real t and every x in E,
`deriv (tau -> heatKernel tau x) t = Delta (y -> heatKernel t y)(x)`.

The pinned definition is exactly
`heatKernel t x = (4*pi*t)^(-n/2) * exp(-||x||^2/(4t))`,
using real exponentiation for the normalization. Thus the declaration is the pointwise positive-time heat equation for this explicit normalized Gaussian on an arbitrary finite-dimensional real inner-product space.

The frozen type asserts this derivative-operator equality. It does not separately package a joint spacetime regularity theorem, mass-one integral, delta initial condition, convolution solution, boundary value problem, uniqueness theorem, or manifold heat kernel.

## Supplied assumptions, geometry and closure boundary

All six assertions are local/model-space scalar calculus or finite-dimensional inner-product identities. Their supplied assumptions are the real inner-product-space structures, finite dimension where listed, and the stated time restrictions. There is no supplied global flow, global existence certificate, charted-manifold structure, smooth atlas, compact manifold, curvature hypothesis, surgery trace, recognition map, PDE solution package, or universal Hamilton witness.

These statements do not weaken their claims by assuming the desired Gaussian PDE identity: the final declaration asks for an identity of the explicitly defined Gaussian, with only t > 0 beyond the space instances. The first five concern explicit expressions or the canonical orthonormal basis.

The read-back reveals no change of domain, dimension restriction to a special sphere, concealed manifold-flow premise, or replacement of a global construction by a supplied global witness within these six types. They are useful model-space analytic lemmas. Even successful proof-preserving compiler migration of all six does not construct compatible smoothing, Ricci flow on arbitrary closed manifolds, Hamilton convergence, or the canonical Poincare endpoint.

## Acceptance boundary

PASS means the six frozen types have the literal mathematical content described above and form coherent Gaussian-calculus assertions. I have not verified the current proof terms, their transitive axiom/unsafe dependencies, compilation on Lean 4.33.1, or equality with an earlier compiled theorem type. Those remain independent orchestrator gates. Preserve the exact original types and pinned definitions during migration.

