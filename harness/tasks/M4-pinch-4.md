Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-4: the trace bridge + bundled difference → the 3D decomposition theorem

Read `harness/reports/M4-pinch-3_blocked.md` (the "Next atom"). On main: `Poincare.PinchingAlgebra.fourLinearEuclidean3_eq_zero_of_riemann_symm_and_trace` (the Weyl-vanishing core, orthonormal-Euclidean-trace form), plus the closed curvature symmetry lemmas and `riemannFromRicci3At` with its Kulkarni-Nomizu form.

Deliverables (each its own commit):
1. **Trace-convention bridge**: either (a) generalize the vanishing lemma's trace hypothesis to the closed library's contraction `Σᵢ W(bᵢ, u, w, ♯bⁱ)` (basis-invariance: the g-contraction over finBasis+dual = the orthonormal trace after a Gram–Schmidt/congruence argument — OR restate the lemma over an abstract 3D inner-product space where the trace is basis-free via `LinearMap.trace`, then both conventions instantiate), or (b) prove the numeric bridge directly for the Euclidean fiber (the metric at x is a general inner product on E, NOT the standard one — mind this: the closed fiber's g-inner ≠ EuclideanSpace's standard inner; route (a)-abstract handles it, route (b) needs the congruence transport). RECOMMEND the abstract-space restatement.
2. **Bundled difference**: package `⟨curvatureOp ... , ·⟩ − riemannFromRicci3At` as a `FourLinear`-shape with the five hypotheses: symmetries from the merged closed curvature lemmas + the KN-form algebra; the trace condition from `ricciAt_eq_curvature_contraction` + `riemannFromRicci3At`'s trace (compute it — the decomposition was BUILT to have Ricci trace = ricciAt; prove that lemma if missing).
3. **`RiemannDeterminedByRicci3At`**: apply the vanishing lemma → the 3D decomposition theorem (n = 3). Space-form sanity check.
4. If budget: pinching roadmap step 2 (now unblocked — rewrite 2·Lich via the decomposition into the PINNED reaction coefficients already on main).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation`, report names.
