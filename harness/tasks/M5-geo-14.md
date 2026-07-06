Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-14: GOAL 10 opener — geodesics have constant speed (Gauss-lemma prerequisite 1)

Context: the geodesic layer (`Poincare/Global/{GeodesicChart,GeodesicTransport,GeodesicGerm,ExponentialGerm,ExponentialFixedTime}.lean`, namespace `Poincare.GeodesicTransport`) has chart geodesics driven by `chartChristoffelField g x₀` (= `christoffelOneForm` of the blended chart metric). The first metric property needed for the Gauss lemma / rigidity road: CONSTANT SPEED — along a chart geodesic `γ`, the blended-chart-metric pairing `G (γ t).1 (γ t).2 (γ t).2` is constant in `t`. Classically: `d/dt G(c', c') = (∂G along c')(c',c') + 2·G(c'', c') = 0` using `c'' = −Γ(c')(c')` and the Koszul/compatibility identity relating `∂G` and `Γ` (the pairing characterization `chartChristoffelField_pairing_eq_chartMetric_…` in `Poincare/Global/GeodesicReanchor.lean` is exactly this identity on cutoff-1 germs; the blended metric's own compatibility with its christoffelOneForm should hold everywhere — check the `CovariantDerivative` chart machinery for the metric-compatibility lemma of `christoffelOneForm`/`chartBilin` and use the general form if available).

Deliverables, in a NEW file `Poincare/Global/GeodesicSpeed.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE DERIVATIVE IDENTITY: for a solution `γ` of the chart geodesic system on an interval, `HasDerivAt (fun t ↦ (blended chart metric at (γ t).1) (γ t).2 (γ t).2) 0 t` (i.e. derivative zero) — via chain rule + the compatibility identity. State against the exact metric object the Christoffel field is built from (the blended chart metric of `g` at anchor `x₀`); spelling free, semantics frozen.
2. CONSTANT SPEED: the pairing is constant on the interval (`Constant`/`EqOn` form via `hasDerivAt_zero`→constancy, e.g. `is_const_of_deriv_eq_zero`-style Mathlib lemma).
3. GERM COROLLARY: along `geodesicGermAt g x₀ v₀`'s chosen chart solution, the speed equals its initial value `G (chart x₀) v₀ v₀` eventually near `0`.
4. Report `harness/reports/M5-geo-14_{done|blocked}.md`: signatures + next Gauss-lemma decomposition (radial fields, the polar variation, `⟨d exp(v), v⟩` identity).

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicSpeed` and report the actual result. Commit your work.
