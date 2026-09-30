import Poincare.MaximumPrinciple
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``RicciFlow.ode_comparison_nonpos, ``RicciFlow.ode_comparison_nonneg, ``RicciFlow.riccati_lower_bound, ``RicciFlow.riccati_forces_finite_time, ``RicciFlow.einstein_scalar_hasDerivAt_riccati, ``RicciFlow.riccati_upper_bound, ``RicciFlow.riccati_doubling_time, ``RicciFlow.secondDeriv_nonneg_of_isLocalMin, ``RicciFlow.hessian_nonneg_of_isLocalMin, ``RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt, ``RicciFlow.exists_first_zero, ``RicciFlow.ode_comparison_nonpos_eq, ``RicciFlow.ode_comparison_nonneg_eq, ``RicciFlow.riccati_lower_bound_eq, ``RicciFlow.riccati_forces_finite_time_eq, ``RicciFlow.einstein_scalar_hasDerivAt_riccati_eq, ``RicciFlow.riccati_upper_bound_eq, ``RicciFlow.riccati_doubling_time_eq, ``RicciFlow.secondDeriv_nonneg_of_isLocalMin_eq, ``RicciFlow.hessian_nonneg_of_isLocalMin_eq, ``RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq, ``RicciFlow.exists_first_zero_eq] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
