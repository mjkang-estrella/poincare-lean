import DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import Lean
open scoped Manifold ContDiff
universe u
#check DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
#print axioms DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
-- Literal unapplied producer contract on the existing underlying topology.
example : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
      ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI := C
        IsManifold (𝓡 3) ∞ M := by
  intro M _ _ _ _
  exact DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
open Lean Elab Command Meta in
run_cmd do
  let name := ``DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
  let env := (← getEnv).setExporting false
  let mut pending : List Name := [name]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    if !seen.contains current then
      seen := seen.insert current
      let some info := env.find? current | throwError "missing dependency {current}"
      if info.isUnsafe || info.isPartial then throwError "unsafe/partial {current}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
  let axs ← collectAxioms name
  unless axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
    throwError "unexpected axiom footprint: {name}: {axs}"
  logInfo m!"UPSTREAM_AXIOM_CONTRACT_OK: {name}"
