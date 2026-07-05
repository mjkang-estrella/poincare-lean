Read harness/worker_contract.md first and obey it strictly.

# Task M5-sphere-2: EXECUTE the Schur bridge list → constant sectional curvature

Read `harness/reports/M5-sphere-1_blocked.md` — its "Recommended next interfaces" list is this task, each as its own commit:

1. `covTensor2DerivAt_scalar_metric`: ∇ of the field `f·g` (variable scalar times the metric) — the Leibniz form `(∇ᵥ(f·g))(p,q) = (df·v)·g(p,q)` (metric compatibility kills the ∇g term; the scalar-times-tensor derivative machinery from the pinch-8 product-rule layer is the template).
2. `tensorDivergenceOneFormAt_scalar_metric`: div of f·g = df (the trace of 1 over the contracted slot — the divergence/trace machinery on main).
3. `extDerivFun_scalarAt_eq_zero_of_isEinstein3`: THE SCHUR STEP — substitute Ric = (R/3)·g into the PROVEN contracted Bianchi `div Ric = ½·dR` (on main; the exact export was located in the M4-prep-15 campaign — `eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt_canonical`-family): LHS = dR/3 by 1+2, so dR/3 = dR/2 ⟹ dR = 0.
4. `scalarAt_constant_of_extDerivFun_eq_zero_connected`: vanishing extDerivFun everywhere ⟹ scalarAt constant on the connected closed manifold — through the chart representative (extDerivFun is the fderiv of the chart rep; `fderiv = 0` on a preconnected chart domain ⟹ locally constant; Mathlib: `IsLocallyConstant.iff_continuous`... use `IsLocallyConstant` + `PreconnectedSpace` ⟹ constant; the manifold-level lemma may exist as `IsLocallyConstant.of_mdifferentiableAt_zero`-shape — search Mathlib first: `Manifold.IsLocallyConstant`, `mdifferentiable`... or prove via `constant_of_fderivWithin_eq_zero`-analog through charts + connectedness).
5. `HasConstantSectionalCurvature3` predicate + `hasConstantSectionalCurvature3_of_isEinstein3_of_scalar_const` via the 3D decomposition collapse (`closedCurvatureFourLinearAt_spaceForm_coeff` machinery — derive its hypotheses from Einstein + constant R). Pin on space form + refute on a non-Einstein pattern.
6. **The chain theorem**: `tracelessRicciNormSqAt ≡ 0 → HasConstantSectionalCurvature3 g (R₀/6)`-form. Done-report + items 4-5 outlook (space-form interface + conditional sphere theorem).

Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
