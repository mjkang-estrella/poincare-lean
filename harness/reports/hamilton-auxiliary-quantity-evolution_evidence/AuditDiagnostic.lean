import Poincare.Global.HamiltonScalarGradientEstimate
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Poincare.Global.HamiltonScalarGradientEstimate
    | throwError "module missing"
  let mut count := 0
  for (n, _) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n == some idx then
      let axs ← liftCoreM (collectAxioms n)
      unless axs.size == 3 && axs.contains ``propext &&
          axs.contains ``Classical.choice && axs.contains ``Quot.sound do
        logWarning m!"Unexpected dependencies: {n}: {axs}"
      elabCommand (← `(command| #print axioms $(mkIdent n)))
      count := count + 1
  logInfo m!"EXACT_DEPENDENCIES_PASS declarations={count}"
