Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-12: the moving-K coefficient contraction → K-slot bridges → tensor Ricci identity

Read `harness/reports/M4-prep-11_blocked.md`. ONE reusable lemma remains before the whole chain fires: differentiate the coefficient block
`fun y => (gramMatrix g x y)⁻¹ i j * g.inner y (K y) (gramFrame x y j)`
and contract back to `g.leviCivita K x u` — the moving-K generalization of `gram_inv_deriv_contraction_eq_leviCivita_corrections` (on main; READ ITS PROOF — the generalization replaces the fixed trace slots with K, whose derivative contributes the ∇K term that BECOMES the `g.leviCivita K x u` value; the metric-compatibility cancellations are identical).

Steps (each its own commit):
1. Scalar derivative of `y ↦ g.inner y (K y) (gramFrame x y j)`: product rule (K MDifferentiable + the metric/frame smoothness — the entry machinery), giving g(∇K-ish, frame) + corrections. NOTE: the honest derivative of K appears as the connection-value `g.leviCivita K x u` PLUS Christoffel corrections by ∇'s definition — the extend/frame calculus identifies the pieces.
2. The inverse-Gram derivative contraction: exactly the existing proof with the K-slot carried through (the −G⁻¹(∂G)G⁻¹ terms cancel the frame Christoffel corrections; the K corrections survive as the connection value).
3. Assemble the LEFT-slot bridge (the M4-prep-10 report's displayed shape), then the RIGHT-slot analogue (symmetric).
4. Instantiate K = connection-value fields → combine with the merged bridges → **THE CLOSED TENSOR RICCI IDENTITY** → specialize to `ricciVariationField g`.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
