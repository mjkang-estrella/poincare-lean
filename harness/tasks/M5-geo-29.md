Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-29: the fiber-norm identification, the length formula, the sharp bound

Context: `harness/reports/M5-geo-28_blocked.md` (READ FIRST) isolates the ONE remaining bridge: identify `‖mfderiv% c s 1‖ₑ` (the Riemannian fiber e-norm of the curve velocity, as Mathlib's `pathELength` integrand measures it, under `g.toRiemannianBundle`/the installed `RiemannianBundle` instance where `inner = g.inner`, `RiemannianContext.lean:147 fiber_inner_eq`) with the chart-metric speed of the flow curve (position-derivative = velocity component, constant speed — all proven in `Poincare/Global/GeodesicPathLength.lean`). The identification runs through: `mfderiv` of `c = (extChartAt).symm ∘ γ₁` via the chain rule (chart-inverse mfderiv composed with the chart derivative of the position — `mfderiv_comp`, and the chart/tangent identification at points of the source), then `fiber_inner_eq` converts the fiber norm to `g.inner`, then the chart-metric transport (`chartMetric` lemmas in `GeodesicReanchorLaw.lean` / cutoff-1 lemmas) converts `g.inner` at the curve point applied to transported vectors into the chart pairing.

Deliverables, in a NEW file `Poincare/Global/GeodesicLength.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE INTEGRAND IDENTIFICATION (the isolated statement from the report; spelling adaptations documented).
2. THE LENGTH FORMULA: `pathELength` of the radial curve on `[0, t]` = `ENNReal.ofReal (t * Real.sqrt (chart speed at 0))`-shaped, via constant speed.
3. THE SHARP UPPER BOUND: `dist x₀ (expAt g x₀ v) ≤ t·√(speed)`-shaped through `induced_edist_le_pathELength` (`GeodesicDistance.lean`).
4. Report `harness/reports/M5-geo-29_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicLength` and report the actual result. Commit your work.
