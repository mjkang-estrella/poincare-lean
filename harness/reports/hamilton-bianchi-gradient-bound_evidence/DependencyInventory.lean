import Poincare.Global.HamiltonScalarGradientEstimate
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HamiltonScalarGradientEstimate
    | throwError "module missing"
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      logInfo m!"{n}: {axs}"
