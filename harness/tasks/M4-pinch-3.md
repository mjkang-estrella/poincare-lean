Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-3: the 3D Weyl-vanishing fiber lemma (pure multilinear algebra)

Read `harness/reports/M4-pinch-2_blocked.md` — its "Next atom" is this task, self-contained finite-dimensional multilinear algebra (no manifolds):

**The lemma**: over a 3-dimensional real inner-product space (work with `EuclideanSpace ℝ (Fin 3)` directly, or abstractly with `FiniteDimensional ℝ V`, `finrank = 3`, an inner product — pick what instantiates cleanest against the closed curvature entries), a 4-linear form W with (i) antisymmetry in the first pair, (ii) antisymmetry in the second pair, (iii) pair-exchange symmetry, (iv) the first Bianchi cyclic identity, and (v) zero Ricci trace (Σᵢ W(eᵢ, u, eᵢ, w) = 0 for an orthonormal basis) is identically zero.

Proof (classical dimension count / direct): in 3D, index over an orthonormal basis e₁e₂e₃; the symmetries reduce W to the 6 components W(eᵢeⱼ, eₖeₗ) with {i<j}, {k<l} ranging over the 3 pairs (a symmetric 3×3 matrix under pair-exchange); the trace-zero condition gives 6 linear equations (Ricci is symmetric 3×3) in those 6 unknowns and forces all to vanish (the classical Λ²(3D) ≅ 3D so Riemann ↔ symmetric bilinear on Λ², and trace-zero kills it — verify the rank claim by the explicit 6×6 elimination in the proof, `decide`/`Finset` case analysis or plain linear algebra). Commit: (1) the 4-slot basis extensionality/reconstruction lemma the report asks for, (2) the vanishing lemma.

Then instantiate: the difference [closed curvature entry − riemannFromRicci3At] satisfies (i)-(v) — (i)-(iv) from the merged curvature symmetry lemmas + `riemannFromRicci3At`'s construction; (v) because both have the same Ricci trace (that's the decomposition's defining property) → **step 1 of the pinching roadmap: the 3D decomposition theorem**. If budget: re-attempt step 2 (now unblocked).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation`, report names.
