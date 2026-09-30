import DifferentialGeometry.Topology.ThreeManifold.Poincare
import Lean
open scoped Manifold ContDiff
universe u
#check DifferentialGeometry.Topology.poincare_conjecture
#check DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
#print axioms DifferentialGeometry.Topology.poincare_conjecture
#print axioms DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
-- Literal compatibility comparison only; this is not the project's declaration.
example : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  intro M _ _ _ _ _
  exact DifferentialGeometry.Topology.poincare_conjecture M
example : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
      ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI := C
        IsManifold (𝓡 3) ∞ M := by
  intro M _ _ _ _ _
  exact DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three
open Lean Elab Command Meta in
run_cmd do
  for name in #[``DifferentialGeometry.Topology.poincare_conjecture,
      ``DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three] do
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
