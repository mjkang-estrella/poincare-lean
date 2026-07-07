Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-21: ⚠️ PIN THE CHART-DEPENDENCE FIRST — is the source-weight claim even true?

Context: `harness/reports/M5-rigid-20_blocked.md` (READ FIRST). Proven: the fixed-vector derivative identity, scalar ODE uniqueness, and the sphere weight pin (`cos⁴(t/2)` solves `κ' = −2·tan(t/2)·κ` — in the SPHERE'S STEREOGRAPHIC chart). ⚠️ ORCHESTRATOR SUSPICION (mandatory check BEFORE any proof attempt): the demanded source expansion uses the SPHERE's weight function, but the source manifold's `extChartAt` is an ARBITRARY atlas chart — the metric-coefficient evolution along geodesics is CHART-DEPENDENT, so "source weight = sphere weight" is likely FALSE for general atlases. PIN: consider the round sphere ITSELF as the source but with a DIFFERENT chart convention (e.g. the chart at a different anchor point composed with a rotation, or examine whether `extChartAt` for `RoundSphere3` at `p₀` vs the map-composed weight differ — any concrete mismatch suffices), or argue abstractly (a chart rescaling `z ↦ 2z` changes the coefficient evolution but not the geometry). IF FALSE: the consumer needs the RATIO-INVARIANT reshape — the pullback identity's actual requirement is `weight_target(Φ(v)) / weight_source(v) = (the Jacobian/alignment factor)²`-shaped, or equivalently the expansion should be stated with a SOURCE-OWNED weight function (existentially quantified or defined from `g`'s own coefficient evolution) and the pullback proof adjusted to cancel the two weights (both sides' sin factors and radial parts are chart-invariant statements; the weights must appear symmetrically). Reshape via sanctioned ADDITIVE edits (`CartanLocalIsometry.lean`/`CartanExpansionBridge.lean`/`CartanPunctured.lean` — new defs/variants only).

Deliverables, in a NEW file `Poincare/Global/CartanWeightInvariant.lean` (+ additive edits as needed):
1. THE PIN VERDICT with the computation/argument recorded.
2. The (reshaped, if needed) source expansion statement that is TRUE + as much of its proof as the session closes (the source-owned weight EXISTS by solving the coefficient ODE — rigid-20's uniqueness machinery constructs it).
3. The correspondingly adjusted pullback consumer (weights canceling), preserving all existing names.
4. Report `harness/reports/M5-rigid-21_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge Poincare.Global.CartanPunctured Poincare.Global.CartanWeightInvariant` (ALL must pass) and report the actual result. Commit your work.
