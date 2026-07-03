Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-11: the two K-slot product-rule bridges → finish the tensor Ricci identity

Read `harness/reports/M4-prep-10_blocked.md` — it displays the EXACT two target shapes (the left-slot and right-slot moving-K product rules for a raw (0,2) tensor h, with the exact hypothesis list: Tensor2Add/SMul slots, `CovTensor2ExtContMDiffAt h x 2`, K MDifferentiable).

Route — the finite-frame expansion (the pattern that closed every such bridge): expand `K y = Σᵢ kᵢ(y) · extend E (bᵢ) y` in the anchored frame near x (the coefficients kᵢ are scalar functions, differentiable since K is; the gramFrameBasis machinery gives the expansion); then `h y (K y) (extend E q y) = Σᵢ kᵢ(y) · h y (ext bᵢ)(ext q)` — a finite sum of products of differentiable scalars — differentiate by the product rule; recognize `covTensor2DerivAt` + the two Levi-Civita correction terms (K's derivative decomposes as ∇K-value + Christoffel action; the extend-calculus lemmas identify the pieces). Commit: left-slot bridge, right-slot bridge, then:

1. Instantiate with K = the connection-value fields per the report's closing instructions.
2. Combine with `closedChristoffel_antisymm_deriv_eq_curvature` + `covTensor2SecondDerivAt_antisymm_expansion` + `..._pure_schwarz_cancel` (all on main) → **THE CLOSED TENSOR RICCI IDENTITY**.
3. Specialize to `ricciVariationField g`.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
