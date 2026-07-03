Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-13: the extension-independence bridge → THE TENSOR RICCI IDENTITY

Read `harness/reports/M4-prep-12_blocked.md` — it displays the ONE remaining bridge (the outer `extDerivFun` expansion of `covTensor2DerivAt` with moving-anchor extensions) and the 5-step direct assembly that follows.

Route options (probe both quickly, pick one):
(a) **Tensoriality**: prove `covTensor2DerivAt g h y v p q` depends only on the VALUES (v, p, q at y), not the extension choice — from the slot-linearity lemmas + the structure of the definition (flat derivative of the scalar entry + pointwise Christoffel corrections; the flat-derivative term is the only extension-sensitive piece and its extension-dependence cancels against... verify against the definition; the model has the corresponding congr lemmas — `covTensor2Deriv_congr`-shapes). Then the moving-anchor expression = the anchored one, and the displayed bridge follows from the already-proven fixed-anchor expansions.
(b) **Direct expansion**: prove the displayed bridge directly by the K-slot bridges just merged (the moving extensions ARE K-fields — `K y = extend E p y` anchored at x is MDifferentiable; apply the left/right-slot bridges with those K's; the `g.leviCivita (extend E p) y (extend E v y)` correction fields match the displayed RHS terms).

Then the 5-step assembly per the report → **THE CLOSED TENSOR RICCI IDENTITY** → specialize to `ricciVariationField g` → (if budget) trace it per the M4-prep-8 plan slices 3-4 toward `RicciSecondDerivCurvatureCommutationAt`.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
