import Poincare.ProofProgress.FiniteExtinctionSweepoutInterfaceBundle

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- A concrete sweepout payload supplies the abstract sweepout witness. -/
theorem finite_extinction_sweepout_existence_of_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    {fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M}
    (payload : FiniteExtinctionSweepoutPayload M fundamentalGroup) :
    HasFiniteExtinctionSweepoutExistence M fundamentalGroup :=
  HasFiniteExtinctionSweepoutExistence.of_sweepout_payload payload

/-- A concrete target sweepout payload supplies the target sweepout witness. -/
theorem finite_extinction_sweepout_existence_of_target_payload_boundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target :=
  finite_extinction_sweepout_existence_of_target_payload payload

/--
The full finite-extinction sub-obligation payload is exactly strong enough to
supply the target sweepout witness, after replacing its stored finite
fundamental-group input by the simply-connected target input.
-/
theorem finite_extinction_sweepout_existence_of_subobligations_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload :
      ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
        FiniteExtinctionSubobligationsStatement flow surgery control) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target := by
  rcases payload with ⟨_n, _flow, _surgery, _control, statement⟩
  exact finite_extinction_sweepout_existence_of_subobligations_statement
    statement

/--
A completed finite-extinction surgery package carries a sweepout witness; this
bridge transports it to the canonical simply-connected target
fundamental-group input.
-/
theorem finite_extinction_sweepout_existence_of_surgery_package_target
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target := by
  have hfg :
      finite_extinction_fundamental_group_input_of_surgery_package package =
        finite_extinction_fundamental_group_input_of_target := by
    apply Subsingleton.elim
  exact hfg ▸ finite_extinction_sweepout_existence_of_surgery_package package

/--
The package-layer payload used by the dependency crosswalk is sufficient to
produce the target finite-extinction sweepout witness.
-/
theorem finite_extinction_sweepout_existence_of_surgery_package_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target := by
  rcases payload with ⟨⟨_n, package⟩⟩
  exact finite_extinction_sweepout_existence_of_surgery_package_target package

/--
Pointwise crosswalk form: the finite-extinction package-layer requirement
discharges the target sweepout-existence subgoal for each target manifold.
-/
theorem finite_extinction_sweepout_existence_of_finiteExtinctionPackage_requirement
    (requirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target :=
  finite_extinction_sweepout_existence_of_surgery_package_payload
    (requirement M)

/--
The target sweepout-existence blocker has moved to the concrete sweepout
payload: once that payload is supplied, the target sweepout-frontier bundle is
available by construction.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_payload_boundary
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M :=
  target_finite_extinction_sweepout_interface_bundle_of_payload payload

end Poincare
