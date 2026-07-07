Read harness/worker_contract.md first and obey it strictly.

# Task M5-glob-28: instantiate LC naturality — the F-transition law

Context: `harness/reports/M5-glob-27_done.md` (READ FIRST). PROVEN: the field (`exists_cartanChartDifferential_field_on_punctured_ball`, `DifferentialField.lean` — `DF` invertible + strict derivative + pointwise pullback on the ball) + the generic algebra (`LCNaturality.christoffelAt_map_eq_signed_transport_of_differentiated_pullback` — READ its exact hypotheses). THE INSTANTIATION: (1) THE DIFFERENTIATED PULLBACK — the pointwise pullback identity holds ON THE OPEN BALL; differentiate it (the `PullbackDifferentiate.lean` abstract pattern with `sigma := cartanChartMap`, derivative facts = the field's strict derivatives — strict ⟹ `HasFDerivAt` ⟹ the composite differentiable; `EventuallyEq`-differentiation on the open set); note DF's own differentiability may be demanded — if `LCNaturality` needs the DERIVATIVE OF DF (second derivative of F), derive from F's smoothness (F = exp∘L∘exp⁻¹ — compositions of smooth maps; the exp smoothness from the germ machinery `HdiffInstantiate.lean` pattern) OR check whether the algebraic form only needs the first-order data; (2) apply the algebra pointwise → 🎯 THE F-TRANSITION LAW: target Christoffels pull back under F (signed) on the ball. Strict-partial; ONE isolated statement max. Report `harness/reports/M5-glob-28_{done|blocked}.md`.

Deliverables in a NEW file `Poincare/Global/FTransition.lean` (do NOT edit existing files, incl. `Poincare.lean`).

No vacuous wrappers. Verify: `lake build Poincare.Global.FTransition` and report the actual result. Commit your work.
