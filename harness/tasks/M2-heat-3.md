Read harness/worker_contract.md first and obey it strictly.

# Task M2-heat-3: the n-dimensional heat equation

Context: `Poincare/Global/HeatKernelPDE.lean` (report `harness/reports/M2-heat-2_done.md`, READ FIRST) proved the 1D heat equation and isolated the n-dimensional target verbatim:
`deriv (fun τ ↦ heatKernel τ x) t = (Δ fun y ↦ heatKernel t y) x` for `t > 0`,
with the route named: compute the spatial second Fréchet derivative of `x ↦ Real.exp (-(‖x‖²)/(4t))`, contract via `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis` (Mathlib HAS `Δ` for inner-product spaces — mine its API: `laplacian_exp`? `laplacian_comp`? check what composition/chain-rule lemmas exist; the Gaussian is `exp ∘ (negative scaled norm-square)`, and `‖x‖²` has known `Δ ‖x‖² = 2n`; the product/chain expansion `Δ(f∘g)` may exist for real compositions — if not, the orthonormal-basis coordinate route: `‖x‖² = Σ ⟨x,eᵢ⟩²` reduces everything to 1D second derivatives along coordinates, where the 1D machinery from HeatKernelPDE.lean is reusable).

Deliverable, in a NEW file `Poincare/Global/HeatKernelPDEn.lean` (do NOT edit existing files, incl. `Poincare.lean`): the theorem `heatKernel_heatEquation_laplacian` exactly as isolated (spelling adaptations documented), plus whatever second-derivative/Laplacian helper lemmas it needs (standalone, reusable). Strict-partial with ONE isolated sub-lemma remains valid. Report `harness/reports/M2-heat-3_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.HeatKernelPDEn` and report the actual result. Commit your work.
