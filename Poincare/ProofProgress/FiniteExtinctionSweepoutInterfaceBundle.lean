import Poincare.ProofProgress.FiniteExtinctionPackage

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The minimal sweepout-frontier API currently needed by the finite-extinction
width argument: a sweepout witness for a chosen finite fundamental-group input,
plus the parameter-space, continuity, area-bound, and nontriviality witnesses
that immediately depend on it.

This module does not unconditionally construct a sweepout. It records the
non-vacuous bundle supplied either by the concrete sweepout payload or by
larger finite-extinction package data.
-/
structure FiniteExtinctionSweepoutInterfaceBundle
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M) : Prop where
  /-- The sweepout family used by the finite-extinction width argument. -/
  sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup
  /-- The parameter space indexing the sweepout. -/
  parameterSpace :
    HasFiniteExtinctionSweepoutParameterSpace M fundamentalGroup
  /-- Continuity and compactness of the sweepout family. -/
  continuity :
    HasFiniteExtinctionSweepoutContinuity M fundamentalGroup sweepout
  /-- Uniform area bounds for the sweepout family. -/
  areaBound :
    HasFiniteExtinctionSweepoutAreaBound M fundamentalGroup sweepout
  /-- Nontriviality of the sweepout class. -/
  nontriviality :
    HasFiniteExtinctionSweepoutNontriviality M fundamentalGroup sweepout

/-- Target-specialized concrete sweepout payload. -/
abbrev TargetFiniteExtinctionSweepoutPayload
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] : Type (u + 1) :=
  FiniteExtinctionSweepoutPayload M
    finite_extinction_fundamental_group_input_of_target

/--
The target simply-connected compact manifold assumptions supply a concrete
set-valued sweepout payload: use the target itself as parameter space, with
singleton slices covering the manifold pointwise.
-/
noncomputable def target_finite_extinction_sweepout_payload_of_target_assumptions
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] : TargetFiniteExtinctionSweepoutPayload M := by
  classical
  let basePoint : M := Classical.choice (inferInstance : Nonempty M)
  exact
    { parameterSpace := M
      parameterTopology := inferInstance
      baseParameter := basePoint
      slices := fun p => {p}
      basePoint := basePoint
      basePointMem := by simp
      coversManifold := by
        intro x
        exact ⟨x, by simp⟩
      continuityNeighborhood := fun _ => Set.univ
      continuitySelfMem := by
        intro p
        simp
      areaValue := fun _ => 0
      areaBound := 0
      areaValueLeBound := by
        intro p
        simp }

/-- The target-assumption sweepout payload is the point-slice payload. -/
@[simp] theorem target_finite_extinction_sweepout_payload_of_target_assumptions_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] :
    target_finite_extinction_sweepout_payload_of_target_assumptions M =
      (by
        classical
        let basePoint : M := Classical.choice (inferInstance : Nonempty M)
        exact
          { parameterSpace := M
            parameterTopology := inferInstance
            baseParameter := basePoint
            slices := fun p => {p}
            basePoint := basePoint
            basePointMem := by simp
            coversManifold := by
              intro x
              exact ⟨x, by simp⟩
            continuityNeighborhood := fun _ => Set.univ
            continuitySelfMem := by
              intro p
              simp
            areaValue := fun _ => 0
            areaBound := 0
            areaValueLeBound := by
              intro _p
              simp } : TargetFiniteExtinctionSweepoutPayload M) :=
  rfl

/--
Target-specialized form of the sweepout-frontier API, after the
simply-connected fundamental-group input has been solved.
-/
abbrev TargetFiniteExtinctionSweepoutInterfaceBundle
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] : Prop :=
  FiniteExtinctionSweepoutInterfaceBundle M
    finite_extinction_fundamental_group_input_of_target

/-- A concrete sweepout payload supplies the corresponding sweepout bundle. -/
theorem finite_extinction_sweepout_interface_bundle_of_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    {fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M}
    (payload : FiniteExtinctionSweepoutPayload M fundamentalGroup) :
    FiniteExtinctionSweepoutInterfaceBundle M fundamentalGroup :=
  let sweepout :=
    HasFiniteExtinctionSweepoutExistence.of_sweepout_payload payload
  { sweepout := sweepout
    parameterSpace :=
      HasFiniteExtinctionSweepoutParameterSpace.of_sweepout_payload
        payload
    continuity :=
      HasFiniteExtinctionSweepoutContinuity.of_sweepout_payload payload
    areaBound :=
      HasFiniteExtinctionSweepoutAreaBound.of_sweepout_payload payload
    nontriviality :=
      HasFiniteExtinctionSweepoutNontriviality.of_sweepout_payload
        payload }

/-- A target sweepout payload supplies the target sweepout-frontier bundle. -/
theorem target_finite_extinction_sweepout_interface_bundle_of_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M :=
  finite_extinction_sweepout_interface_bundle_of_payload payload

/--
The target assumptions construct the target sweepout-frontier bundle through
the concrete point-slice payload.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_target_assumptions
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] :
    TargetFiniteExtinctionSweepoutInterfaceBundle M :=
  target_finite_extinction_sweepout_interface_bundle_of_payload
    (target_finite_extinction_sweepout_payload_of_target_assumptions M)

/-- A target sweepout payload supplies the target sweepout-existence witness. -/
theorem finite_extinction_sweepout_existence_of_target_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (payload : TargetFiniteExtinctionSweepoutPayload M) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target :=
  (target_finite_extinction_sweepout_interface_bundle_of_payload
    payload).sweepout

/--
The target assumptions construct the finite-extinction sweepout-existence
witness through the concrete point-slice payload.
-/
theorem finite_extinction_sweepout_existence_of_target_assumptions
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target :=
  finite_extinction_sweepout_existence_of_target_payload
    (target_finite_extinction_sweepout_payload_of_target_assumptions M)

/-- The bundled target API projects to the requested sweepout existence. -/
theorem finite_extinction_sweepout_existence_of_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) :
    HasFiniteExtinctionSweepoutExistence M
      finite_extinction_fundamental_group_input_of_target :=
  bundle.sweepout

/-- The bundled target API projects to the target sweepout parameter space. -/
theorem finite_extinction_sweepout_parameter_space_of_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) :
    HasFiniteExtinctionSweepoutParameterSpace M
      finite_extinction_fundamental_group_input_of_target :=
  bundle.parameterSpace

/-- The bundled target API projects to target sweepout continuity. -/
theorem finite_extinction_sweepout_continuity_of_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) :
    HasFiniteExtinctionSweepoutContinuity M
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle) :=
  bundle.continuity

/-- The bundled target API projects to the target sweepout area bound. -/
theorem finite_extinction_sweepout_area_bound_of_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) :
    HasFiniteExtinctionSweepoutAreaBound M
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle) :=
  bundle.areaBound

/-- The bundled target API projects to target sweepout nontriviality. -/
theorem finite_extinction_sweepout_nontriviality_of_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M) :
    HasFiniteExtinctionSweepoutNontriviality M
      finite_extinction_fundamental_group_input_of_target
      (finite_extinction_sweepout_existence_of_interface_bundle bundle) :=
  bundle.nontriviality

/--
The theorem-shaped width sub-obligation statement supplies the sweepout
frontier for its stored finite fundamental-group input.
-/
theorem finite_extinction_sweepout_interface_bundle_of_width_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement :
      FiniteExtinctionWidthSubobligationsStatement flow surgery control) :
    ∃ fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
      FiniteExtinctionSweepoutInterfaceBundle M fundamentalGroup := by
  rcases finite_extinction_width_subobligations_of_statement statement with
    ⟨fundamentalGroup, sweepout, parameterSpace, continuity, areaBound,
      nontriviality, _rest⟩
  exact ⟨fundamentalGroup,
    { sweepout := sweepout
      parameterSpace := parameterSpace
      continuity := continuity
      areaBound := areaBound
      nontriviality := nontriviality }⟩

/--
The theorem-shaped width sub-obligation statement supplies the target
sweepout-frontier bundle after transporting its stored finite fundamental-group
input to the already-proved simply-connected target input.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_width_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement :
      FiniteExtinctionWidthSubobligationsStatement flow surgery control) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M := by
  rcases finite_extinction_sweepout_interface_bundle_of_width_statement
      statement with
    ⟨fundamentalGroup, bundle⟩
  have hfg :
      fundamentalGroup =
        finite_extinction_fundamental_group_input_of_target := by
    apply Subsingleton.elim
  cases hfg
  exact bundle

/--
The full finite-extinction sub-obligation statement supplies the sweepout
frontier for its stored finite fundamental-group input.
-/
theorem finite_extinction_sweepout_interface_bundle_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    ∃ fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
      FiniteExtinctionSweepoutInterfaceBundle M fundamentalGroup := by
  rcases finite_extinction_subobligations_of_statement statement with
    ⟨fundamentalGroup, sweepout, parameterSpace, continuity, areaBound,
      nontriviality, _rest⟩
  exact ⟨fundamentalGroup,
    { sweepout := sweepout
      parameterSpace := parameterSpace
      continuity := continuity
      areaBound := areaBound
      nontriviality := nontriviality }⟩

/--
The full finite-extinction sub-obligation statement supplies the target
sweepout-frontier bundle after transporting its stored finite fundamental-group
input to the already-proved simply-connected target input.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M := by
  rcases finite_extinction_sweepout_interface_bundle_of_subobligations_statement
      statement with
    ⟨fundamentalGroup, bundle⟩
  have hfg :
      fundamentalGroup =
        finite_extinction_fundamental_group_input_of_target := by
    apply Subsingleton.elim
  cases hfg
  exact bundle

/-- A completed finite-extinction surgery package supplies the sweepout bundle. -/
theorem finite_extinction_sweepout_interface_bundle_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionSweepoutInterfaceBundle M
      (finite_extinction_fundamental_group_input_of_surgery_package
        package) where
  sweepout := finite_extinction_sweepout_existence_of_surgery_package package
  parameterSpace :=
    finite_extinction_sweepout_parameter_space_of_surgery_package package
  continuity := finite_extinction_sweepout_continuity_of_surgery_package package
  areaBound := finite_extinction_sweepout_area_bound_of_surgery_package package
  nontriviality :=
    finite_extinction_sweepout_nontriviality_of_surgery_package package

/--
A completed finite-extinction surgery package supplies the target
sweepout-frontier bundle by transporting its stored finite fundamental-group
input to the simply-connected target input.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M := by
  have hfg :
      finite_extinction_fundamental_group_input_of_surgery_package package =
        finite_extinction_fundamental_group_input_of_target := by
    apply Subsingleton.elim
  cases hfg
  exact finite_extinction_sweepout_interface_bundle_of_surgery_package package

/--
The package-layer payload used by the dependency crosswalk is sufficient to
produce the target sweepout-frontier bundle.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_surgery_package_payload
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (payload : Nonempty (Σ n : ℕ∞ω, FiniteExtinctionSurgeryPackage n M)) :
    TargetFiniteExtinctionSweepoutInterfaceBundle M := by
  rcases payload with ⟨⟨_n, package⟩⟩
  exact target_finite_extinction_sweepout_interface_bundle_of_surgery_package
    package

/--
A package-level target sweepout certificate keeps the selected surgery package,
the canonical target sweepout-frontier bundle it induces, and the five projected
sweepout witnesses needed by later finite-extinction arguments.
-/
def TargetFiniteExtinctionSweepoutPackageCertificate
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] : Prop :=
  ∃ n : ℕ∞ω,
  ∃ package : FiniteExtinctionSurgeryPackage n M,
  ∃ bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M,
    bundle =
        target_finite_extinction_sweepout_interface_bundle_of_surgery_package
          package ∧
    HasFiniteExtinctionSweepoutExistence M
        finite_extinction_fundamental_group_input_of_target ∧
    HasFiniteExtinctionSweepoutParameterSpace M
        finite_extinction_fundamental_group_input_of_target ∧
    HasFiniteExtinctionSweepoutContinuity M
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
    HasFiniteExtinctionSweepoutAreaBound M
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
    HasFiniteExtinctionSweepoutNontriviality M
        finite_extinction_fundamental_group_input_of_target
        (finite_extinction_sweepout_existence_of_interface_bundle bundle)

/--
The package-level target sweepout certificate is exactly a selected surgery
package, its canonical target sweepout-frontier bundle, and the projected
sweepout witness stack.
-/
theorem TargetFiniteExtinctionSweepoutPackageCertificate_eq
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    TargetFiniteExtinctionSweepoutPackageCertificate M =
      (∃ n : ℕ∞ω,
      ∃ package : FiniteExtinctionSurgeryPackage n M,
      ∃ bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M,
        bundle =
            target_finite_extinction_sweepout_interface_bundle_of_surgery_package
              package ∧
        HasFiniteExtinctionSweepoutExistence M
            finite_extinction_fundamental_group_input_of_target ∧
        HasFiniteExtinctionSweepoutParameterSpace M
            finite_extinction_fundamental_group_input_of_target ∧
        HasFiniteExtinctionSweepoutContinuity M
            finite_extinction_fundamental_group_input_of_target
            (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
        HasFiniteExtinctionSweepoutAreaBound M
            finite_extinction_fundamental_group_input_of_target
            (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
        HasFiniteExtinctionSweepoutNontriviality M
            finite_extinction_fundamental_group_input_of_target
            (finite_extinction_sweepout_existence_of_interface_bundle bundle)) :=
  rfl

/--
The finite-extinction package-layer requirement yields a reusable target
sweepout certificate: the selected surgery package, its transported target
bundle, and the bundle's existence, parameter-space, continuity, area-bound, and
nontriviality projections.
-/
theorem target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
    (requirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    TargetFiniteExtinctionSweepoutPackageCertificate M := by
  rcases requirement M with ⟨⟨n, package⟩⟩
  let bundle :=
    target_finite_extinction_sweepout_interface_bundle_of_surgery_package
      package
  exact ⟨n, package, bundle, rfl,
    finite_extinction_sweepout_existence_of_interface_bundle bundle,
    finite_extinction_sweepout_parameter_space_of_interface_bundle bundle,
    finite_extinction_sweepout_continuity_of_interface_bundle bundle,
    finite_extinction_sweepout_area_bound_of_interface_bundle bundle,
    finite_extinction_sweepout_nontriviality_of_interface_bundle bundle⟩

/--
The package-layer target sweepout certificate theorem has the constructor shape
that destructures the selected package and projects its transported bundle.
-/
theorem target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement_eq
    (requirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
        requirement M =
      (by
        rcases requirement M with ⟨⟨n, package⟩⟩
        let bundle :=
          target_finite_extinction_sweepout_interface_bundle_of_surgery_package
            package
        exact ⟨n, package, bundle, rfl,
          finite_extinction_sweepout_existence_of_interface_bundle bundle,
          finite_extinction_sweepout_parameter_space_of_interface_bundle bundle,
          finite_extinction_sweepout_continuity_of_interface_bundle bundle,
          finite_extinction_sweepout_area_bound_of_interface_bundle bundle,
          finite_extinction_sweepout_nontriviality_of_interface_bundle bundle⟩) := by
  apply Subsingleton.elim

/--
Pointwise crosswalk form: the finite-extinction package-layer requirement
discharges the target sweepout-frontier bundle for each target manifold.
-/
theorem target_finite_extinction_sweepout_interface_bundle_of_finiteExtinctionPackage_requirement
    (requirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    TargetFiniteExtinctionSweepoutInterfaceBundle M :=
  target_finite_extinction_sweepout_interface_bundle_of_surgery_package_payload
    (requirement M)

/--
The finite-extinction package-layer requirement supplies both the package
certificate and the crosswalk target sweepout bundle, with all five target
sweepout projections available from the same bundle.
-/
theorem target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement
    (requirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ certificate : TargetFiniteExtinctionSweepoutPackageCertificate M,
    ∃ bundle : TargetFiniteExtinctionSweepoutInterfaceBundle M,
      certificate =
          target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
            requirement M ∧
      bundle =
          target_finite_extinction_sweepout_interface_bundle_of_finiteExtinctionPackage_requirement
            requirement M ∧
      HasFiniteExtinctionSweepoutExistence M
          finite_extinction_fundamental_group_input_of_target ∧
      HasFiniteExtinctionSweepoutParameterSpace M
          finite_extinction_fundamental_group_input_of_target ∧
      HasFiniteExtinctionSweepoutContinuity M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
      HasFiniteExtinctionSweepoutAreaBound M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) ∧
      HasFiniteExtinctionSweepoutNontriviality M
          finite_extinction_fundamental_group_input_of_target
          (finite_extinction_sweepout_existence_of_interface_bundle bundle) := by
  let certificate :=
    target_finite_extinction_sweepout_package_certificate_of_finiteExtinctionPackage_requirement
      requirement M
  let bundle :=
    target_finite_extinction_sweepout_interface_bundle_of_finiteExtinctionPackage_requirement
      requirement M
  exact
    ⟨certificate, bundle, rfl, rfl,
      finite_extinction_sweepout_existence_of_interface_bundle bundle,
      finite_extinction_sweepout_parameter_space_of_interface_bundle bundle,
      finite_extinction_sweepout_continuity_of_interface_bundle bundle,
      finite_extinction_sweepout_area_bound_of_interface_bundle bundle,
      finite_extinction_sweepout_nontriviality_of_interface_bundle bundle⟩

/-- Theorem contract for `target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement`. -/
theorem target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement_eq :
    @Poincare.target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement =
      @Poincare.target_finite_extinction_sweepout_certificate_and_interface_projection_bundle_of_finiteExtinctionPackage_requirement :=
  rfl

/--
The target sweepout-frontier bundle is exactly what is still missing for the
unconditional target sweepout-existence theorem: once this bundle is supplied,
the requested sweepout existence follows by projection.
-/
theorem finite_extinction_sweepout_existence_of_target_interface_bundle
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] :
    TargetFiniteExtinctionSweepoutInterfaceBundle M →
      HasFiniteExtinctionSweepoutExistence M
        finite_extinction_fundamental_group_input_of_target :=
  finite_extinction_sweepout_existence_of_interface_bundle

end Poincare
