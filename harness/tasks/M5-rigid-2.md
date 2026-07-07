Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-2: tangent alignment exists — the Cartan map becomes unconditional

Context: `harness/reports/M5-rigid-1_blocked.md` (READ FIRST). `Poincare/Global/CartanMap.lean` has the full `cartanMap` opener (source-target homeomorphism, anchor lemmas) PARAMETERIZED by a `TangentAlignment g x₀ p₀` (a linear equivalence of `E = EuclideanSpace ℝ (Fin 3)` intertwining the two anchor chart metrics — read its exact fields). The single blocker: `Nonempty (TangentAlignment g x₀ p₀)` — pure linear algebra: any two positive-definite symmetric bilinear forms on a finite-dimensional real space admit a linear map taking one to the other (orthonormal bases for each — Mathlib: `LinearMap.BilinForm`/inner-product-space machinery; e.g. build the inner-product-space structures `InnerProductSpace.ofCore` from each form, use `LinearIsometryEquiv` between finite-dim inner product spaces of equal dimension — `LinearIsometryEquiv.ofInnerProductSpace` / `finDimVectorspaceEquiv`-adjacent, or orthonormal bases via `stdOrthonormalBasis` on each core structure and map basis to basis).

Deliverables, in a NEW file `Poincare/Global/TangentAlignmentExists.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE EXISTENCE: `theorem tangentAlignment_nonempty … : Nonempty (TangentAlignment g x₀ p₀)` (exact hypotheses per the structure's context; the two forms' positivity/symmetry lemmas are already in `CartanMap.lean`).
2. THE UNCONDITIONAL OPENER: instantiate — `∃` a Cartan source-target homeomorphism with `cartanMap x₀ = p₀` (compose with rigid-1's parameterized results).
3. Report `harness/reports/M5-rigid-2_{done|blocked}.md` + confirm the Jacobi sin-comparison roadmap from rigid-1's report as the next tasks.

No vacuous wrappers. Verify: `lake build Poincare.Global.TangentAlignmentExists` and report the actual result. Commit your work.
