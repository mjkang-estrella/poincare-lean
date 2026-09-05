import Poincare.DependencyCrosswalk

open scoped Manifold ContDiff

namespace Poincare

/--
A conditional dependency implication: a single finite-extinction surgery package
already contains the fixed-flow Ricci-flow-with-surgery construction package
and Perelman singularity-control package required by the package-layer
dependency crosswalk.

This does not construct those packages directly; it only projects them from the
strictly stronger finite-extinction package.
-/
theorem surgery_perelman_package_payload_of_finite_extinction_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
      PerelmanSingularityControlPackage (n := n) (M := M) flow := by
  let flow := ricci_flow_data_of_surgery_package package
  exact
    ⟨flow,
      surgery_construction_package_of_surgery_package package,
      perelman_control_package_of_surgery_package package⟩

/--
A conditional dependency implication: a completed finite-extinction surgery
package for one target supplies the exact `∃ n, ∃ flow, construction package ∧
Perelman package` target used for the surgery package layer.

This records projection from a stronger package, not completion of the
surgery/Perelman construction.
-/
theorem surgery_perelman_package_target_of_finite_extinction_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
      PerelmanSingularityControlPackage (n := n) (M := M) flow := by
  exact
    ⟨n,
      surgery_perelman_package_payload_of_finite_extinction_surgery_package
        package⟩

/--
Conditional dependency implication: the finite-extinction package-layer
requirement strictly subsumes the Ricci-flow-with-surgery plus
Perelman-control package-layer requirement.

This is useful for dependency bookkeeping, but it assumes the stronger
finite-extinction package-layer requirement and therefore does not fill the
surgery/Perelman blocker.
-/
theorem surgeryPackage_requirement_of_finiteExtinctionPackage_requirement
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage) :
    dependencyPackageLayerRequirement.{u}
      DependencyPackageLayer.surgeryPackage := by
  intro M _ _ _ _ _ _
  rcases finiteExtinctionRequirement M with ⟨⟨_n, package⟩⟩
  exact
    surgery_perelman_package_target_of_finite_extinction_surgery_package
      package

/--
Pointwise conditional form of the package-layer implication: for any target
manifold, a finite-extinction package family selects a flow carrying both the
surgery construction package and the Perelman-control package.
-/
theorem surgery_perelman_package_target_at_of_finiteExtinctionPackage_requirement
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] [IsManifold ThreeManifoldModelWithCorners 1 M] :
    ∃ n : ℕ∞ω,
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow ∧
      PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  surgeryPackage_requirement_of_finiteExtinctionPackage_requirement
    finiteExtinctionRequirement M

/--
The finite-extinction package layer discharges the Ricci-flow-with-surgery
milestone requirement because that milestone asks for the same fixed-flow
construction package plus Perelman package.
-/
theorem ricciFlowWithSurgery_milestone_requirement_of_finiteExtinctionPackage_requirement
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.ricciFlowWithSurgery :=
  surgeryPackage_requirement_of_finiteExtinctionPackage_requirement
    finiteExtinctionRequirement

/--
The finite-extinction package layer also discharges the Perelman-control
milestone requirement; both milestones share the same package-layer target.
-/
theorem perelmanSingularityControl_milestone_requirement_of_finiteExtinctionPackage_requirement
    (finiteExtinctionRequirement :
      dependencyPackageLayerRequirement.{u}
        DependencyPackageLayer.finiteExtinctionPackage) :
    dependencyMilestoneRequirement.{u}
      DependencyMilestone.perelmanSingularityControl :=
  surgeryPackage_requirement_of_finiteExtinctionPackage_requirement
    finiteExtinctionRequirement

/-- Concrete surgery-scale payloads produce the first construction-package field. -/
theorem surgery_scale_function_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (payload : SurgeryScaleFunctionPayload flow) :
    HasSurgeryScaleFunction flow :=
  HasSurgeryScaleFunction.of_scale_function_payload payload

/--
Concrete continuity payloads for a selected surgery-scale function produce the
second construction-package field.
-/
theorem surgery_scale_continuity_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    (payload : SurgeryScaleContinuityPayload scalePayload) :
    HasSurgeryScaleContinuity flow :=
  HasSurgeryScaleContinuity.of_scale_continuity_payload payload

/--
Concrete separation payloads for a selected continuous surgery-scale function
produce the third construction-package field.
-/
theorem surgery_scale_separation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    (payload : SurgeryScaleSeparationPayload continuityPayload) :
    HasSurgeryScaleSeparation flow :=
  HasSurgeryScaleSeparation.of_scale_separation_payload payload

/--
Concrete cutoff-control payloads for a separated surgery-scale package produce
the fourth construction-package field.
-/
theorem surgery_cutoff_parameter_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    (payload : SurgeryCutoffParameterControlPayload separationPayload) :
    HasSurgeryCutoffParameterControl flow :=
  HasSurgeryCutoffParameterControl.of_cutoff_parameter_control_payload payload

/--
Concrete smooth-bump payloads for controlled cutoff parameters produce the fifth
construction-package field.
-/
theorem surgery_cutoff_smooth_bump_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    (payload : SurgeryCutoffSmoothBumpPayload cutoffPayload) :
    HasSurgeryCutoffSmoothBumpFunction flow :=
  HasSurgeryCutoffSmoothBumpFunction.of_cutoff_smooth_bump_payload payload

/--
Concrete parameter-selection payloads for smooth cutoff packages produce the
sixth construction-package field.
-/
theorem surgery_parameter_selection_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    (payload : SurgeryParameterSelectionPayload smoothBumpPayload) :
    HasSurgeryParameterSelection flow :=
  HasSurgeryParameterSelection.of_parameter_selection_payload payload

/--
Concrete strong delta-neck detection payloads for selected surgery parameters
produce the seventh construction-package field.
-/
theorem surgery_strong_delta_neck_detection_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    (payload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload) :
    HasStrongDeltaNeckDetection flow :=
  HasStrongDeltaNeckDetection.of_strong_delta_neck_detection_payload payload

/--
Concrete neck-separation payloads for detected strong delta-necks produce the
eighth construction-package field.
-/
theorem surgery_neck_separation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    (payload : SurgeryNeckSeparationPayload strongDeltaPayload) :
    HasSurgeryNeckSeparation flow :=
  HasSurgeryNeckSeparation.of_neck_separation_payload payload

/--
Concrete neck-parametrization payloads for separated surgery necks produce the
ninth construction-package field.
-/
theorem surgery_neck_parametrization_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    (payload :
      SurgeryNeckParametrizationPayload neckSeparationPayload) :
    HasSurgeryNeckParametrization flow :=
  HasSurgeryNeckParametrization.of_neck_parametrization_payload payload

/--
Concrete canonical-coordinate payloads for parametrized surgery necks produce
the tenth construction-package field.
-/
theorem surgery_neck_canonical_coordinates_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    (payload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload) :
    HasSurgeryNeckCanonicalCoordinates flow :=
  HasSurgeryNeckCanonicalCoordinates.of_neck_canonical_coordinates_payload
    payload

/--
Concrete neck-decomposition payloads for canonical-coordinate surgery necks
produce the next construction-package field.
-/
theorem surgery_neck_decomposition_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    (payload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload) :
    HasSurgeryNeckDecomposition flow :=
  HasSurgeryNeckDecomposition.of_neck_decomposition_payload payload

/--
Concrete standard-cap-model payloads for decomposed surgery necks produce the
next construction-package field.
-/
theorem standard_cap_model_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    (payload : StandardCapModelPayload neckDecompositionPayload) :
    HasStandardCapModel flow :=
  HasStandardCapModel.of_standard_cap_model_payload payload

/--
Concrete cap-gluing smoothness payloads for standard cap models produce the
next construction-package field.
-/
theorem cap_gluing_smoothness_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    (payload : CapGluingSmoothnessPayload standardCapModelPayload) :
    HasCapGluingSmoothness flow :=
  HasCapGluingSmoothness.of_cap_gluing_smoothness_payload payload

/--
Concrete cap metric interpolation payloads for cap-gluing data produce the next
construction-package field.
-/
theorem surgery_cap_metric_interpolation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    (payload :
      SurgeryCapMetricInterpolationPayload capGluingSmoothnessPayload) :
    HasSurgeryCapMetricInterpolation flow :=
  HasSurgeryCapMetricInterpolation.of_cap_metric_interpolation_payload
    payload

/--
Concrete cap curvature estimate payloads for cap metric interpolation data
produce the next construction-package field.
-/
theorem surgery_cap_curvature_estimates_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    (payload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload) :
    HasSurgeryCapCurvatureEstimates flow :=
  HasSurgeryCapCurvatureEstimates.of_cap_curvature_estimates_payload
    payload

/--
Concrete cap construction payloads for cap curvature estimate data produce the
next construction-package field.
-/
theorem surgery_cap_construction_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    (payload :
      SurgeryCapConstructionPayload
        capCurvatureEstimatesPayload) :
    HasSurgeryCapConstruction flow :=
  HasSurgeryCapConstruction.of_cap_construction_payload payload

/--
Concrete post-surgery curvature pinching payloads for cap construction data
produce the next construction-package field.
-/
theorem post_surgery_curvature_pinching_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    (payload :
      PostSurgeryCurvaturePinchingPayload
        capConstructionPayload) :
    HasPostSurgeryCurvaturePinching flow :=
  HasPostSurgeryCurvaturePinching.of_post_surgery_curvature_pinching_payload
    payload

/--
Concrete post-surgery noncollapsing payloads for curvature pinching data
produce the next construction-package field.
-/
theorem post_surgery_noncollapsing_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    (payload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload) :
    HasPostSurgeryNoncollapsingControl flow :=
  HasPostSurgeryNoncollapsingControl.of_post_surgery_noncollapsing_payload
    payload

/--
Concrete post-surgery derivative-bound payloads for noncollapsing data produce
the next construction-package field.
-/
theorem post_surgery_derivative_bounds_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    (payload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload) :
    HasPostSurgeryDerivativeBounds flow :=
  HasPostSurgeryDerivativeBounds.of_post_surgery_derivative_bounds_payload
    payload

/--
Concrete post-surgery canonical-neighborhood persistence payloads for
derivative-bound data produce the next construction-package field.
-/
theorem post_surgery_canonical_neighborhood_persistence_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    (payload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload) :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow :=
  HasPostSurgeryCanonicalNeighborhoodPersistence.of_post_surgery_canonical_neighborhood_persistence_payload
    payload

/--
Concrete post-surgery metric-control payloads for canonical-neighborhood
persistence data produce the next construction-package field.
-/
theorem post_surgery_metric_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    (payload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload) :
    HasPostSurgeryMetricControl flow :=
  HasPostSurgeryMetricControl.of_post_surgery_metric_control_payload
    payload

/--
Concrete surgery-time-discreteness payloads for post-surgery metric-control data
produce the next construction-package field.
-/
theorem surgery_time_discreteness_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    (payload :
      SurgeryTimeDiscretenessPayload
        postSurgeryMetricControlPayload) :
    HasSurgeryTimeDiscreteness flow :=
  HasSurgeryTimeDiscreteness.of_surgery_time_discreteness_payload
    payload

/--
Concrete surgery-time-local-finiteness payloads for surgery-time-discreteness
data produce the next construction-package field.
-/
theorem surgery_time_local_finiteness_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    (payload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload) :
    HasSurgeryTimeLocalFiniteness flow :=
  HasSurgeryTimeLocalFiniteness.of_surgery_time_local_finiteness_payload
    payload

/--
Concrete long-time existence iteration payloads for surgery-time-local-
finiteness data produce the next construction-package field.
-/
theorem long_time_existence_iteration_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    (payload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload) :
    HasLongTimeExistenceIteration flow :=
  HasLongTimeExistenceIteration.of_long_time_existence_iteration_payload
    payload

/--
Concrete long-time surgery-parameter coherence payloads for long-time
existence-iteration data produce the next construction-package field.
-/
theorem long_time_surgery_parameter_coherence_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    (payload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload) :
    HasLongTimeSurgeryParameterCoherence flow :=
  HasLongTimeSurgeryParameterCoherence.of_long_time_surgery_parameter_coherence_payload
    payload

/--
Concrete long-time nonaccumulation payloads for long-time surgery-parameter
coherence data produce the next construction-package field.
-/
theorem long_time_nonaccumulation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    (payload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload) :
    HasLongTimeNonaccumulation flow :=
  HasLongTimeNonaccumulation.of_long_time_nonaccumulation_payload
    payload

/--
Concrete long-time surgery-continuation payloads for long-time
nonaccumulation data produce the next construction-package field.
-/
theorem long_time_surgery_continuation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    {longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload}
    (payload :
      LongTimeSurgeryContinuationPayload
        longTimeNonaccumulationPayload) :
    HasLongTimeSurgeryContinuation flow :=
  HasLongTimeSurgeryContinuation.of_long_time_surgery_continuation_payload
    payload

/--
Concrete aggregate Ricci-flow-with-surgery payloads produce the final
construction-package field.
-/
theorem ricci_flow_with_surgery_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    {longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload}
    {longTimeSurgeryContinuationPayload :
      LongTimeSurgeryContinuationPayload
        longTimeNonaccumulationPayload}
    (payload :
      RicciFlowWithSurgeryPayload
        longTimeSurgeryContinuationPayload) :
    HasRicciFlowWithSurgery n M :=
  HasRicciFlowWithSurgery.of_ricci_flow_with_surgery_payload payload

/--
The remaining Ricci-flow-with-surgery construction fields after the surgery
scale function has been selected.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Continuity and controlled variation of the surgery scale function. -/
  scaleContinuity : HasSurgeryScaleContinuity flow
  /-- Separation among surgery, cutoff, and canonical-neighborhood scales. -/
  scaleSeparation : HasSurgeryScaleSeparation flow
  /-- Cutoff parameter control for surgery. -/
  cutoffParameterControl : HasSurgeryCutoffParameterControl flow
  /-- Smooth cutoff bump functions used in the metric transition region. -/
  cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow
  /-- Surgery parameter and cutoff selection. -/
  parameterSelection : HasSurgeryParameterSelection flow
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery-scale
continuity has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Separation among surgery, cutoff, and canonical-neighborhood scales. -/
  scaleSeparation : HasSurgeryScaleSeparation flow
  /-- Cutoff parameter control for surgery. -/
  cutoffParameterControl : HasSurgeryCutoffParameterControl flow
  /-- Smooth cutoff bump functions used in the metric transition region. -/
  cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow
  /-- Surgery parameter and cutoff selection. -/
  parameterSelection : HasSurgeryParameterSelection flow
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery-scale
separation has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Cutoff parameter control for surgery. -/
  cutoffParameterControl : HasSurgeryCutoffParameterControl flow
  /-- Smooth cutoff bump functions used in the metric transition region. -/
  cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow
  /-- Surgery parameter and cutoff selection. -/
  parameterSelection : HasSurgeryParameterSelection flow
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after smooth cutoff
bump functions have been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Surgery parameter and cutoff selection. -/
  parameterSelection : HasSurgeryParameterSelection flow
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery
parameter selection has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
Assemble the smooth-bump remainder from surgery parameter selection plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump_of_parameter_selection_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (parameterSelection : HasSurgeryParameterSelection flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
        flow where
  parameterSelection := parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the smooth-bump remainder from concrete parameter-selection payload data
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump_of_parameter_selection_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump_of_parameter_selection_and_remainder
    (surgery_parameter_selection_of_payload parameterSelectionPayload)
    remainder

/--
The remaining Ricci-flow-with-surgery construction fields after strong
delta-neck detection has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery neck
separation has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery neck
parametrization has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after canonical neck
coordinates have been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery neck
decomposition has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after the standard
cap model has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after smooth cap
gluing has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after cap metric
interpolation has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after cap curvature
estimates have been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after cap construction
has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after post-surgery
curvature pinching has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after post-surgery
noncollapsing control has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after post-surgery
derivative bounds have been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after post-surgery
canonical-neighborhood persistence has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after post-surgery
metric control has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery-time
discreteness has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after surgery-time
local finiteness has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after long-time
existence iteration has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after long-time
surgery-parameter coherence has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after long-time
nonaccumulation has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
The remaining Ricci-flow-with-surgery construction fields after long-time
surgery continuation has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
Assemble the final long-time-continuation remainder from concrete aggregate
Ricci-flow-with-surgery payload data.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation_of_ricci_flow_with_surgery_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    {longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload}
    {longTimeSurgeryContinuationPayload :
      LongTimeSurgeryContinuationPayload
        longTimeNonaccumulationPayload}
    (payload :
      RicciFlowWithSurgeryPayload
        longTimeSurgeryContinuationPayload) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation
        flow where
  withSurgery := ricci_flow_with_surgery_of_payload payload

/--
Assemble the long-time-nonaccumulation remainder from long-time continuation
plus the aggregate surgery-flow construction.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation_of_continuation_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (longTimeContinuation : HasLongTimeSurgeryContinuation flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
        flow where
  longTimeContinuation := longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the long-time-nonaccumulation remainder from concrete long-time
surgery-continuation payload data plus the aggregate surgery-flow construction.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation_of_continuation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    {longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload}
    (longTimeSurgeryContinuationPayload :
      LongTimeSurgeryContinuationPayload
        longTimeNonaccumulationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation_of_continuation_and_remainder
    (long_time_surgery_continuation_of_payload
      longTimeSurgeryContinuationPayload)
    remainder

/--
Assemble the long-time-surgery-parameter-coherence remainder from
nonaccumulation plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence_of_nonaccumulation_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (longTimeNonaccumulation : HasLongTimeNonaccumulation flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
        flow where
  longTimeNonaccumulation := longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the long-time-surgery-parameter-coherence remainder from concrete
long-time nonaccumulation payload data plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence_of_nonaccumulation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    {longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload}
    (longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence_of_nonaccumulation_and_remainder
    (long_time_nonaccumulation_of_payload longTimeNonaccumulationPayload)
    remainder

/--
Assemble the long-time-existence-iteration remainder from parameter coherence
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration_of_parameter_coherence_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (longTimeParameterCoherence :
      HasLongTimeSurgeryParameterCoherence flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
        flow where
  longTimeParameterCoherence := longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the long-time-existence-iteration remainder from concrete
long-time surgery-parameter coherence payload data plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration_of_parameter_coherence_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    {longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload}
    (longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration_of_parameter_coherence_and_remainder
    (long_time_surgery_parameter_coherence_of_payload
      longTimeSurgeryParameterCoherencePayload)
    remainder

/--
Assemble the surgery-time-local-finiteness remainder from long-time existence
iteration plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness_of_long_time_existence_iteration_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (longTimeExistenceIteration :
      HasLongTimeExistenceIteration flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
        flow where
  longTimeExistenceIteration := longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the surgery-time-local-finiteness remainder from concrete long-time
existence iteration payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness_of_long_time_existence_iteration_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    {surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload
        surgeryTimeDiscretenessPayload}
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload
        surgeryTimeLocalFinitenessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness_of_long_time_existence_iteration_and_remainder
    (long_time_existence_iteration_of_payload
      longTimeExistenceIterationPayload)
    remainder

/--
Assemble the surgery-time-discreteness remainder from surgery-time local
finiteness plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness_of_local_finiteness_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (surgeryTimeLocalFiniteness :
      HasSurgeryTimeLocalFiniteness flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
        flow where
  surgeryTimeLocalFiniteness := surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the surgery-time-discreteness remainder from concrete
surgery-time-local-finiteness payload data plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness_of_local_finiteness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    {surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload}
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness_of_local_finiteness_and_remainder
    (surgery_time_local_finiteness_of_payload
      surgeryTimeLocalFinitenessPayload)
    remainder

/--
Assemble the post-surgery-metric-control remainder from surgery-time
discreteness plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl_of_surgery_time_discreteness_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
        flow where
  surgeryTimeDiscreteness := surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the post-surgery-metric-control remainder from concrete
surgery-time-discreteness payload data plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl_of_surgery_time_discreteness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    {postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload}
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl_of_surgery_time_discreteness_and_remainder
    (surgery_time_discreteness_of_payload
      surgeryTimeDiscretenessPayload)
    remainder

/--
Assemble the post-surgery-canonical-neighborhood-persistence remainder from
metric control plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence_of_metric_control_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (metricControl : HasPostSurgeryMetricControl flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
        flow where
  metricControl := metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the post-surgery-canonical-neighborhood-persistence remainder from
concrete metric-control payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence_of_metric_control_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    {postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload}
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence_of_metric_control_and_remainder
    (post_surgery_metric_control_of_payload
      postSurgeryMetricControlPayload)
    remainder

/--
Assemble the post-surgery-derivative-bounds remainder from canonical-
neighborhood persistence plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds_of_canonical_neighborhood_persistence_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (postSurgeryCanonicalNeighborhoodPersistence :
      HasPostSurgeryCanonicalNeighborhoodPersistence flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
        flow where
  postSurgeryCanonicalNeighborhoodPersistence :=
    postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the post-surgery-derivative-bounds remainder from concrete canonical-
neighborhood persistence payload data plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds_of_canonical_neighborhood_persistence_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    {postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload
        postSurgeryNoncollapsingPayload}
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds_of_canonical_neighborhood_persistence_and_remainder
    (post_surgery_canonical_neighborhood_persistence_of_payload
      postSurgeryCanonicalNeighborhoodPersistencePayload)
    remainder

/--
Assemble the post-surgery-noncollapsing remainder from derivative bounds plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing_of_derivative_bounds_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
        flow where
  postSurgeryDerivativeBounds := postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the post-surgery-noncollapsing remainder from concrete derivative-bound
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing_of_derivative_bounds_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    {postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload}
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing_of_derivative_bounds_and_remainder
    (post_surgery_derivative_bounds_of_payload
      postSurgeryDerivativeBoundsPayload)
    remainder

/--
Assemble the post-surgery-curvature-pinching remainder from noncollapsing
control plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching_of_noncollapsing_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (postSurgeryNoncollapsing :
      HasPostSurgeryNoncollapsingControl flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
        flow where
  postSurgeryNoncollapsing := postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the post-surgery-curvature-pinching remainder from concrete
noncollapsing payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching_of_noncollapsing_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    {postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload}
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching_of_noncollapsing_and_remainder
    (post_surgery_noncollapsing_control_of_payload
      postSurgeryNoncollapsingPayload)
    remainder

/--
Assemble the cap-construction remainder from post-surgery curvature pinching
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction_of_post_surgery_curvature_pinching_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (postSurgeryCurvaturePinching :
      HasPostSurgeryCurvaturePinching flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
        flow where
  postSurgeryCurvaturePinching := postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the cap-construction remainder from concrete post-surgery curvature
pinching payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction_of_post_surgery_curvature_pinching_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    {capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload}
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction_of_post_surgery_curvature_pinching_and_remainder
    (post_surgery_curvature_pinching_of_payload
      postSurgeryCurvaturePinchingPayload)
    remainder

/--
Assemble the cap-curvature-estimates remainder from cap construction plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates_of_cap_construction_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (capConstruction : HasSurgeryCapConstruction flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
        flow where
  capConstruction := capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the cap-curvature-estimates remainder from concrete cap construction
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates_of_cap_construction_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    {capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload}
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates_of_cap_construction_and_remainder
    (surgery_cap_construction_of_payload capConstructionPayload)
    remainder

/--
Assemble the cap-metric-interpolation remainder from cap curvature estimates
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation_of_cap_curvature_estimates_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
        flow where
  capCurvatureEstimates := capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the cap-metric-interpolation remainder from concrete cap curvature
estimate payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation_of_cap_curvature_estimates_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    {capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload}
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation_of_cap_curvature_estimates_and_remainder
    (surgery_cap_curvature_estimates_of_payload
      capCurvatureEstimatesPayload)
    remainder

/--
Assemble the cap-gluing-smoothness remainder from cap metric interpolation plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness_of_cap_metric_interpolation_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (capMetricInterpolation : HasSurgeryCapMetricInterpolation flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
        flow where
  capMetricInterpolation := capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the cap-gluing-smoothness remainder from concrete cap metric
interpolation payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness_of_cap_metric_interpolation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    {capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload}
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload capGluingSmoothnessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness_of_cap_metric_interpolation_and_remainder
    (surgery_cap_metric_interpolation_of_payload
      capMetricInterpolationPayload)
    remainder

/--
Assemble the standard-cap-model remainder from cap-gluing smoothness plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel_of_cap_gluing_smoothness_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (capGluingSmoothness : HasCapGluingSmoothness flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
        flow where
  capGluingSmoothness := capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the standard-cap-model remainder from concrete cap-gluing smoothness
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel_of_cap_gluing_smoothness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    {standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload}
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel_of_cap_gluing_smoothness_and_remainder
    (cap_gluing_smoothness_of_payload capGluingSmoothnessPayload)
    remainder

/--
Assemble the neck-decomposition remainder from the standard cap model plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition_of_standard_cap_model_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (standardCapModel : HasStandardCapModel flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
        flow where
  standardCapModel := standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the neck-decomposition remainder from concrete standard-cap-model
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition_of_standard_cap_model_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    {neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload}
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition_of_standard_cap_model_and_remainder
    (standard_cap_model_of_payload standardCapModelPayload)
    remainder

/--
Assemble the canonical-coordinate remainder from surgery neck decomposition
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates_of_neck_decomposition_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (neckDecomposition : HasSurgeryNeckDecomposition flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
        flow where
  neckDecomposition := neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the canonical-coordinate remainder from concrete neck-decomposition
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates_of_neck_decomposition_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    {neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload}
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates_of_neck_decomposition_and_remainder
    (surgery_neck_decomposition_of_payload neckDecompositionPayload)
    remainder

/--
Assemble the neck-parametrization remainder from canonical neck coordinates plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization_of_neck_canonical_coordinates_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
        flow where
  neckCanonicalCoordinates := neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the neck-parametrization remainder from concrete canonical-coordinate
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization_of_neck_canonical_coordinates_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    {neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload}
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization_of_neck_canonical_coordinates_and_remainder
    (surgery_neck_canonical_coordinates_of_payload
      neckCanonicalCoordinatesPayload)
    remainder

/--
Assemble the neck-separation remainder from surgery neck parametrization plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation_of_neck_parametrization_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (neckParametrization : HasSurgeryNeckParametrization flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
        flow where
  neckParametrization := neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the neck-separation remainder from concrete neck-parametrization
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation_of_neck_parametrization_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    {neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload}
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation_of_neck_parametrization_and_remainder
    (surgery_neck_parametrization_of_payload neckParametrizationPayload)
    remainder

/--
Assemble the strong-delta-neck-detection remainder from surgery neck separation
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection_of_neck_separation_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (neckSeparation : HasSurgeryNeckSeparation flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
        flow where
  neckSeparation := neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the strong-delta-neck-detection remainder from concrete neck-separation
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection_of_neck_separation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    {strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload}
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection_of_neck_separation_and_remainder
    (surgery_neck_separation_of_payload neckSeparationPayload)
    remainder

/--
Assemble the parameter-selection remainder from strong delta-neck detection plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection_of_strong_delta_neck_detection_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
        flow where
  strongDeltaNeckDetection := strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the parameter-selection remainder from concrete strong delta-neck
detection payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection_of_strong_delta_neck_detection_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    {smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload}
    {parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload}
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection_of_strong_delta_neck_detection_and_remainder
    (surgery_strong_delta_neck_detection_of_payload strongDeltaPayload)
    remainder

/--
The remaining Ricci-flow-with-surgery construction fields after surgery cutoff
parameter control has been supplied.
-/
structure RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Smooth cutoff bump functions used in the metric transition region. -/
  cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow
  /-- Surgery parameter and cutoff selection. -/
  parameterSelection : HasSurgeryParameterSelection flow
  /-- Detection of strong delta-necks. -/
  strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow
  /-- Separation of selected surgery necks. -/
  neckSeparation : HasSurgeryNeckSeparation flow
  /-- Parametrization of selected necks by standard cylindrical models. -/
  neckParametrization : HasSurgeryNeckParametrization flow
  /-- Canonical neck coordinates with controlled metric errors. -/
  neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow
  /-- Neck detection and decomposition. -/
  neckDecomposition : HasSurgeryNeckDecomposition flow
  /-- Standard cap model used in the surgery replacement. -/
  standardCapModel : HasStandardCapModel flow
  /-- Smooth cap gluing into neck regions. -/
  capGluingSmoothness : HasCapGluingSmoothness flow
  /-- Metric interpolation between the neck and the inserted cap. -/
  capMetricInterpolation : HasSurgeryCapMetricInterpolation flow
  /-- Curvature estimates on the inserted standard cap. -/
  capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow
  /-- Standard cap construction. -/
  capConstruction : HasSurgeryCapConstruction flow
  /-- Post-surgery curvature pinching estimates. -/
  postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow
  /-- Post-surgery noncollapsing control. -/
  postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow
  /-- Post-surgery derivative bounds for restarting the flow. -/
  postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow
  /-- Persistence of canonical-neighborhood control after surgery. -/
  postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow
  /-- Post-surgery metric estimates. -/
  metricControl : HasPostSurgeryMetricControl flow
  /-- Discreteness of surgery times. -/
  surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow
  /-- Local finiteness of surgery times on bounded intervals. -/
  surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow
  /-- Iteration of the continuation argument for all time. -/
  longTimeExistenceIteration : HasLongTimeExistenceIteration flow
  /-- Coherence of parameter choices through the long-time iteration. -/
  longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow
  /-- Exclusion of finite-time accumulation in the long-time construction. -/
  longTimeNonaccumulation : HasLongTimeNonaccumulation flow
  /-- Long-time continuation after surgery. -/
  longTimeContinuation : HasLongTimeSurgeryContinuation flow
  /-- Aggregate Ricci-flow-with-surgery construction. -/
  withSurgery : HasRicciFlowWithSurgery n M

/--
Assemble the cutoff-parameter-control remainder from smooth cutoff bump
functions plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl_of_cutoff_smooth_bump_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
        flow where
  cutoffSmoothBump := cutoffSmoothBump
  parameterSelection := remainder.parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the cutoff-parameter-control remainder from concrete smooth-bump
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl_of_cutoff_smooth_bump_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    {cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload}
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl_of_cutoff_smooth_bump_and_remainder
    (surgery_cutoff_smooth_bump_of_payload smoothBumpPayload) remainder

/--
Assemble the scale-separation remainder from cutoff parameter control plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation_of_cutoff_parameter_control_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (cutoffParameterControl : HasSurgeryCutoffParameterControl flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
        flow where
  cutoffParameterControl := cutoffParameterControl
  cutoffSmoothBump := remainder.cutoffSmoothBump
  parameterSelection := remainder.parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the scale-separation remainder from concrete cutoff-control payload data
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation_of_cutoff_parameter_control_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    {separationPayload : SurgeryScaleSeparationPayload continuityPayload}
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation_of_cutoff_parameter_control_and_remainder
    (surgery_cutoff_parameter_control_of_payload cutoffPayload) remainder

/--
Assemble the scale-continuity remainder from surgery-scale separation plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity_of_scale_separation_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scaleSeparation : HasSurgeryScaleSeparation flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity
        flow where
  scaleSeparation := scaleSeparation
  cutoffParameterControl := remainder.cutoffParameterControl
  cutoffSmoothBump := remainder.cutoffSmoothBump
  parameterSelection := remainder.parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble the scale-continuity remainder from concrete surgery-scale separation
payload data plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity_of_scale_separation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {scalePayload : SurgeryScaleFunctionPayload flow}
    {continuityPayload : SurgeryScaleContinuityPayload scalePayload}
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity
        flow :=
  ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity_of_scale_separation_and_remainder
    (surgery_scale_separation_of_payload separationPayload) remainder

/--
Assemble the scale-function remainder from surgery-scale continuity plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction_of_scale_continuity_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scaleContinuity : HasSurgeryScaleContinuity flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity
        flow) :
    RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction
        flow where
  scaleContinuity := scaleContinuity
  scaleSeparation := remainder.scaleSeparation
  cutoffParameterControl := remainder.cutoffParameterControl
  cutoffSmoothBump := remainder.cutoffSmoothBump
  parameterSelection := remainder.parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble a construction package from a selected surgery-scale function and the
remaining construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_function_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scaleFunction : HasSurgeryScaleFunction flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow where
  scaleFunction := scaleFunction
  scaleContinuity := remainder.scaleContinuity
  scaleSeparation := remainder.scaleSeparation
  cutoffParameterControl := remainder.cutoffParameterControl
  cutoffSmoothBump := remainder.cutoffSmoothBump
  parameterSelection := remainder.parameterSelection
  strongDeltaNeckDetection := remainder.strongDeltaNeckDetection
  neckSeparation := remainder.neckSeparation
  neckParametrization := remainder.neckParametrization
  neckCanonicalCoordinates := remainder.neckCanonicalCoordinates
  neckDecomposition := remainder.neckDecomposition
  standardCapModel := remainder.standardCapModel
  capGluingSmoothness := remainder.capGluingSmoothness
  capMetricInterpolation := remainder.capMetricInterpolation
  capCurvatureEstimates := remainder.capCurvatureEstimates
  capConstruction := remainder.capConstruction
  postSurgeryCurvaturePinching := remainder.postSurgeryCurvaturePinching
  postSurgeryNoncollapsing := remainder.postSurgeryNoncollapsing
  postSurgeryDerivativeBounds := remainder.postSurgeryDerivativeBounds
  postSurgeryCanonicalNeighborhoodPersistence :=
    remainder.postSurgeryCanonicalNeighborhoodPersistence
  metricControl := remainder.metricControl
  surgeryTimeDiscreteness := remainder.surgeryTimeDiscreteness
  surgeryTimeLocalFiniteness := remainder.surgeryTimeLocalFiniteness
  longTimeExistenceIteration := remainder.longTimeExistenceIteration
  longTimeParameterCoherence := remainder.longTimeParameterCoherence
  longTimeNonaccumulation := remainder.longTimeNonaccumulation
  longTimeContinuation := remainder.longTimeContinuation
  withSurgery := remainder.withSurgery

/--
Assemble a construction package from concrete surgery-scale payload data plus
the remaining construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_function_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_function_and_remainder
    (surgery_scale_function_of_payload scalePayload) remainder

/--
Assemble a construction package from concrete scale-function and
scale-continuity payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_function_payload_and_remainder
    scalePayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleFunction_of_scale_continuity_and_remainder
      (surgery_scale_continuity_of_payload continuityPayload) remainder)

/--
Assemble a construction package from concrete scale-function, continuity, and
separation payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_and_remainder
    scalePayload continuityPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleContinuity_of_scale_separation_payload_and_remainder
      separationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, and cutoff-control payloads plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_and_remainder
    scalePayload continuityPayload separationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterScaleSeparation_of_cutoff_parameter_control_payload_and_remainder
      cutoffPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, and smooth-bump payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffParameterControl_of_cutoff_smooth_bump_payload_and_remainder
      smoothBumpPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, and parameter-selection payloads plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCutoffSmoothBump_of_parameter_selection_payload_and_remainder
      parameterSelectionPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, and strong
delta-neck detection payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterParameterSelection_of_strong_delta_neck_detection_payload_and_remainder
      strongDeltaPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, and neck-separation payloads plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterStrongDeltaNeckDetection_of_neck_separation_payload_and_remainder
      neckSeparationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, and neck-parametrization payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckSeparation_of_neck_parametrization_payload_and_remainder
      neckParametrizationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, and canonical-coordinate
payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckParametrization_of_neck_canonical_coordinates_payload_and_remainder
      neckCanonicalCoordinatesPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate, and
neck-decomposition payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckCanonicalCoordinates_of_neck_decomposition_payload_and_remainder
      neckDecompositionPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, and standard-cap-model payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterNeckDecomposition_of_standard_cap_model_payload_and_remainder
      standardCapModelPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, and cap-gluing-smoothness payloads plus
the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterStandardCapModel_of_cap_gluing_smoothness_payload_and_remainder
      capGluingSmoothnessPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, and cap metric
interpolation payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCapGluingSmoothness_of_cap_metric_interpolation_payload_and_remainder
      capMetricInterpolationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, and cap curvature estimate payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCapMetricInterpolation_of_cap_curvature_estimates_payload_and_remainder
      capCurvatureEstimatesPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, and cap construction payloads plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCapCurvatureEstimates_of_cap_construction_payload_and_remainder
      capConstructionPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, and post-surgery
curvature pinching payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterCapConstruction_of_post_surgery_curvature_pinching_payload_and_remainder
      postSurgeryCurvaturePinchingPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, and post-surgery noncollapsing payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCurvaturePinching_of_noncollapsing_payload_and_remainder
      postSurgeryNoncollapsingPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, and post-surgery derivative-bound payloads
plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryNoncollapsing_of_derivative_bounds_payload_and_remainder
      postSurgeryDerivativeBoundsPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound, and
post-surgery canonical-neighborhood persistence payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryDerivativeBounds_of_canonical_neighborhood_persistence_payload_and_remainder
      postSurgeryCanonicalNeighborhoodPersistencePayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, and post-surgery metric-control
payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryCanonicalNeighborhoodPersistence_of_metric_control_payload_and_remainder
      postSurgeryMetricControlPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
and surgery-time-discreteness payloads plus the later construction-package
fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterPostSurgeryMetricControl_of_surgery_time_discreteness_payload_and_remainder
      surgeryTimeDiscretenessPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
surgery-time-discreteness, and surgery-time-local-finiteness payloads plus the
later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeDiscreteness_of_local_finiteness_payload_and_remainder
      surgeryTimeLocalFinitenessPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
surgery-time-discreteness, surgery-time-local-finiteness, and long-time
existence iteration payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload surgeryTimeLocalFinitenessPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    surgeryTimeLocalFinitenessPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterSurgeryTimeLocalFiniteness_of_long_time_existence_iteration_payload_and_remainder
      longTimeExistenceIterationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
surgery-time-discreteness, surgery-time-local-finiteness, long-time existence
iteration, and long-time surgery-parameter coherence payloads plus the later
construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload surgeryTimeLocalFinitenessPayload)
    (longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    surgeryTimeLocalFinitenessPayload longTimeExistenceIterationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeExistenceIteration_of_parameter_coherence_payload_and_remainder
      longTimeSurgeryParameterCoherencePayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
surgery-time-discreteness, surgery-time-local-finiteness, long-time existence
iteration, long-time surgery-parameter coherence, and long-time nonaccumulation
payloads plus the later construction-package fields.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_long_time_nonaccumulation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload surgeryTimeLocalFinitenessPayload)
    (longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload)
    (longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    surgeryTimeLocalFinitenessPayload longTimeExistenceIterationPayload
    longTimeSurgeryParameterCoherencePayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryParameterCoherence_of_nonaccumulation_payload_and_remainder
      longTimeNonaccumulationPayload remainder)

/--
Assemble a construction package from concrete scale-function, continuity,
separation, cutoff-control, smooth-bump, parameter-selection, strong delta-neck
detection, neck-separation, neck-parametrization, canonical-coordinate,
neck-decomposition, standard-cap-model, cap-gluing-smoothness, cap metric
interpolation, cap curvature estimate, cap construction, post-surgery curvature
pinching, post-surgery noncollapsing, post-surgery derivative-bound,
post-surgery canonical-neighborhood persistence, post-surgery metric-control,
surgery-time-discreteness, surgery-time-local-finiteness, long-time existence
iteration, long-time surgery-parameter coherence, long-time nonaccumulation,
and long-time surgery-continuation payloads plus aggregate surgery-flow
evidence.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_long_time_nonaccumulation_payload_long_time_continuation_payload_and_remainder
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload surgeryTimeLocalFinitenessPayload)
    (longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload)
    (longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload)
    (longTimeSurgeryContinuationPayload :
      LongTimeSurgeryContinuationPayload longTimeNonaccumulationPayload)
    (remainder :
      RicciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation
        flow) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_long_time_nonaccumulation_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    surgeryTimeLocalFinitenessPayload longTimeExistenceIterationPayload
    longTimeSurgeryParameterCoherencePayload longTimeNonaccumulationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeNonaccumulation_of_continuation_payload_and_remainder
      longTimeSurgeryContinuationPayload remainder)

/--
Assemble a construction package from the complete surgery payload chain,
including the aggregate Ricci-flow-with-surgery payload.
-/
theorem ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_long_time_nonaccumulation_payload_long_time_continuation_payload_ricci_flow_with_surgery_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (scalePayload : SurgeryScaleFunctionPayload flow)
    (continuityPayload : SurgeryScaleContinuityPayload scalePayload)
    (separationPayload : SurgeryScaleSeparationPayload continuityPayload)
    (cutoffPayload : SurgeryCutoffParameterControlPayload separationPayload)
    (smoothBumpPayload : SurgeryCutoffSmoothBumpPayload cutoffPayload)
    (parameterSelectionPayload :
      SurgeryParameterSelectionPayload smoothBumpPayload)
    (strongDeltaPayload :
      SurgeryStrongDeltaNeckDetectionPayload parameterSelectionPayload)
    (neckSeparationPayload :
      SurgeryNeckSeparationPayload strongDeltaPayload)
    (neckParametrizationPayload :
      SurgeryNeckParametrizationPayload neckSeparationPayload)
    (neckCanonicalCoordinatesPayload :
      SurgeryNeckCanonicalCoordinatesPayload
        neckParametrizationPayload)
    (neckDecompositionPayload :
      SurgeryNeckDecompositionPayload
        neckCanonicalCoordinatesPayload)
    (standardCapModelPayload :
      StandardCapModelPayload neckDecompositionPayload)
    (capGluingSmoothnessPayload :
      CapGluingSmoothnessPayload standardCapModelPayload)
    (capMetricInterpolationPayload :
      SurgeryCapMetricInterpolationPayload
        capGluingSmoothnessPayload)
    (capCurvatureEstimatesPayload :
      SurgeryCapCurvatureEstimatesPayload
        capMetricInterpolationPayload)
    (capConstructionPayload :
      SurgeryCapConstructionPayload capCurvatureEstimatesPayload)
    (postSurgeryCurvaturePinchingPayload :
      PostSurgeryCurvaturePinchingPayload capConstructionPayload)
    (postSurgeryNoncollapsingPayload :
      PostSurgeryNoncollapsingControlPayload
        postSurgeryCurvaturePinchingPayload)
    (postSurgeryDerivativeBoundsPayload :
      PostSurgeryDerivativeBoundsPayload postSurgeryNoncollapsingPayload)
    (postSurgeryCanonicalNeighborhoodPersistencePayload :
      PostSurgeryCanonicalNeighborhoodPersistencePayload
        postSurgeryDerivativeBoundsPayload)
    (postSurgeryMetricControlPayload :
      PostSurgeryMetricControlPayload
        postSurgeryCanonicalNeighborhoodPersistencePayload)
    (surgeryTimeDiscretenessPayload :
      SurgeryTimeDiscretenessPayload postSurgeryMetricControlPayload)
    (surgeryTimeLocalFinitenessPayload :
      SurgeryTimeLocalFinitenessPayload surgeryTimeDiscretenessPayload)
    (longTimeExistenceIterationPayload :
      LongTimeExistenceIterationPayload surgeryTimeLocalFinitenessPayload)
    (longTimeSurgeryParameterCoherencePayload :
      LongTimeSurgeryParameterCoherencePayload
        longTimeExistenceIterationPayload)
    (longTimeNonaccumulationPayload :
      LongTimeNonaccumulationPayload
        longTimeSurgeryParameterCoherencePayload)
    (longTimeSurgeryContinuationPayload :
      LongTimeSurgeryContinuationPayload longTimeNonaccumulationPayload)
    (ricciFlowWithSurgeryPayload :
      RicciFlowWithSurgeryPayload longTimeSurgeryContinuationPayload) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow :=
  ricciFlowWithSurgeryConstructionPackage_of_scale_payload_continuity_payload_separation_payload_cutoff_payload_smooth_bump_payload_parameter_selection_payload_strong_delta_payload_neck_separation_payload_neck_parametrization_payload_neck_canonical_coordinates_payload_neck_decomposition_payload_standard_cap_model_payload_cap_gluing_smoothness_payload_cap_metric_interpolation_payload_cap_curvature_estimates_payload_cap_construction_payload_post_surgery_curvature_pinching_payload_post_surgery_noncollapsing_payload_post_surgery_derivative_bounds_payload_post_surgery_canonical_neighborhood_persistence_payload_post_surgery_metric_control_payload_surgery_time_discreteness_payload_surgery_time_local_finiteness_payload_long_time_existence_iteration_payload_long_time_parameter_coherence_payload_long_time_nonaccumulation_payload_long_time_continuation_payload_and_remainder
    scalePayload continuityPayload separationPayload cutoffPayload
    smoothBumpPayload parameterSelectionPayload strongDeltaPayload
    neckSeparationPayload neckParametrizationPayload
    neckCanonicalCoordinatesPayload neckDecompositionPayload
    standardCapModelPayload capGluingSmoothnessPayload
    capMetricInterpolationPayload capCurvatureEstimatesPayload
    capConstructionPayload postSurgeryCurvaturePinchingPayload
    postSurgeryNoncollapsingPayload postSurgeryDerivativeBoundsPayload
    postSurgeryCanonicalNeighborhoodPersistencePayload
    postSurgeryMetricControlPayload surgeryTimeDiscretenessPayload
    surgeryTimeLocalFinitenessPayload longTimeExistenceIterationPayload
    longTimeSurgeryParameterCoherencePayload longTimeNonaccumulationPayload
    longTimeSurgeryContinuationPayload
    (ricciFlowWithSurgeryConstructionPackageRemainderAfterLongTimeSurgeryContinuation_of_ricci_flow_with_surgery_payload
      ricciFlowWithSurgeryPayload)

/--
Concrete aggregate Perelman singularity-control payloads produce the final
Perelman package field.
-/
theorem perelman_singularity_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {noLocalCollapsing : HasPerelmanNoLocalCollapsing flow}
    {reducedVolume : HasPerelmanReducedVolumeMonotonicity flow}
    {canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow}
    {singularityModelClassification :
      HasSingularityModelClassification flow}
    {singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow}
    (payload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    HasPerelmanSingularityControl flow :=
  HasPerelmanSingularityControl.of_perelman_singularity_control_payload
    payload

/--
Assemble the Perelman singularity-control package from its component inputs and
the aggregate singularity-control payload.
-/
theorem perelmanSingularityControlPackage_of_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalSetup : HasPerelmanFFunctionalSetup flow)
    (entropyNormalization : HasPerelmanEntropyNormalization flow)
    (entropyMinimizerExistence : HasPerelmanEntropyMinimizerExistence flow)
    (entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow)
    (conjugateHeatEquation : HasConjugateHeatEquationTheory flow)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow where
  fFunctionalSetup := fFunctionalSetup
  entropyNormalization := entropyNormalization
  entropyMinimizerExistence := entropyMinimizerExistence
  entropyLogSobolevControl := entropyLogSobolevControl
  conjugateHeatEquation := conjugateHeatEquation
  adjointHeatKernel := adjointHeatKernel
  conjugateHeatKernelEstimates := conjugateHeatKernelEstimates
  wFunctionalSetup := wFunctionalSetup
  entropyGradientFormula := entropyGradientFormula
  entropyFirstVariation := entropyFirstVariation
  entropyMonotonicity := entropyMonotonicity
  entropyLowerBoundPropagation := entropyLowerBoundPropagation
  entropyFunctional := entropyFunctional
  reducedLengthFirstVariation := reducedLengthFirstVariation
  reducedDistanceExistence := reducedDistanceExistence
  reducedDistanceDifferentialInequality :=
    reducedDistanceDifferentialInequality
  reducedDistanceEstimates := reducedDistanceEstimates
  reducedDistanceCutLocusControl := reducedDistanceCutLocusControl
  reducedJacobianComparison := reducedJacobianComparison
  reducedDistance := reducedDistance
  reducedVolumeDefinition := reducedVolumeDefinition
  reducedVolumeDerivativeFormula := reducedVolumeDerivativeFormula
  reducedVolumeRigidity := reducedVolumeRigidity
  reducedVolumePositiveLowerBound := reducedVolumePositiveLowerBound
  reducedVolumeLimitRigidity := reducedVolumeLimitRigidity
  reducedVolumeNonincreasing := reducedVolumeNonincreasing
  kappaNoncollapsingFromReducedVolume := kappaNoncollapsingFromReducedVolume
  noLocalCollapsingContradictionSetup :=
    noLocalCollapsingContradictionSetup
  collapsedBallBlowup := collapsedBallBlowup
  volumeRatioContradiction := volumeRatioContradiction
  noLocalCollapsingVolumeLowerBound := noLocalCollapsingVolumeLowerBound
  kappaNoncollapsing := kappaNoncollapsing
  hamiltonCompactness := hamiltonCompactness
  ancientKappaSolutionLimitExtraction := ancientKappaSolutionLimitExtraction
  kappaSolutionPointedRescaling := kappaSolutionPointedRescaling
  kappaSolutionCurvatureNormalization := kappaSolutionCurvatureNormalization
  kappaSolutionStructure := kappaSolutionStructure
  kappaSolutionNonnegativeCurvatureOperator :=
    kappaSolutionNonnegativeCurvatureOperator
  kappaSolutionAsymptoticSoliton := kappaSolutionAsymptoticSoliton
  ancientKappaSolutionCompactness := ancientKappaSolutionCompactness
  canonicalNeighborhoodScaleControl := canonicalNeighborhoodScaleControl
  canonicalNeighborhoodStability := canonicalNeighborhoodStability
  canonicalNeighborhoodPersistenceAcrossScales :=
    canonicalNeighborhoodPersistenceAcrossScales
  canonicalNeighborhoodNeckCapDichotomy :=
    canonicalNeighborhoodNeckCapDichotomy
  canonicalNeighborhoodClassification := canonicalNeighborhoodClassification
  noLocalCollapsing := noLocalCollapsing
  reducedVolume := reducedVolume
  canonicalNeighborhood := canonicalNeighborhood
  singularityModelClassification := singularityModelClassification
  singularityModelBlowupClassification :=
    singularityModelBlowupClassification
  control := perelman_singularity_control_of_payload controlPayload

/--
Concrete F-functional setup payloads produce the first Perelman package field.
-/
theorem perelman_f_functional_setup_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (payload : PerelmanFFunctionalSetupPayload flow) :
    HasPerelmanFFunctionalSetup flow :=
  HasPerelmanFFunctionalSetup.of_f_functional_setup_payload payload

/--
Assemble the Perelman singularity-control package from concrete F-functional
setup payload data, the remaining component inputs, and aggregate
singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalization : HasPerelmanEntropyNormalization flow)
    (entropyMinimizerExistence : HasPerelmanEntropyMinimizerExistence flow)
    (entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow)
    (conjugateHeatEquation : HasConjugateHeatEquationTheory flow)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_components_and_control_payload
    (perelman_f_functional_setup_of_payload fFunctionalPayload)
    entropyNormalization entropyMinimizerExistence entropyLogSobolevControl
    conjugateHeatEquation adjointHeatKernel conjugateHeatKernelEstimates
    wFunctionalSetup entropyGradientFormula entropyFirstVariation
    entropyMonotonicity entropyLowerBoundPropagation entropyFunctional
    reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume noLocalCollapsingContradictionSetup
    collapsedBallBlowup volumeRatioContradiction
    noLocalCollapsingVolumeLowerBound kappaNoncollapsing
    hamiltonCompactness ancientKappaSolutionLimitExtraction
    kappaSolutionPointedRescaling kappaSolutionCurvatureNormalization
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Concrete entropy-normalization payloads produce the next Perelman package field.
-/
theorem perelman_entropy_normalization_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    (payload : PerelmanEntropyNormalizationPayload fFunctionalPayload) :
    HasPerelmanEntropyNormalization flow :=
  HasPerelmanEntropyNormalization.of_entropy_normalization_payload payload

/--
Concrete entropy-minimizer payloads produce the next Perelman package field.
-/
theorem perelman_entropy_minimizer_existence_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    (payload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload) :
    HasPerelmanEntropyMinimizerExistence flow :=
  HasPerelmanEntropyMinimizerExistence.of_entropy_minimizer_existence_payload
    payload

/--
Concrete entropy log-Sobolev payloads produce the next Perelman package field.
-/
theorem perelman_entropy_log_sobolev_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    (payload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload) :
    HasPerelmanEntropyLogSobolevControl flow :=
  HasPerelmanEntropyLogSobolevControl.of_entropy_log_sobolev_control_payload
    payload

/--
Concrete conjugate heat equation payloads produce the next Perelman package
field.
-/
theorem conjugate_heat_equation_theory_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    (payload :
      ConjugateHeatEquationTheoryPayload
        entropyLogSobolevPayload) :
    HasConjugateHeatEquationTheory flow :=
  HasConjugateHeatEquationTheory.of_conjugate_heat_equation_theory_payload
    payload

/--
Concrete adjoint heat-kernel payloads produce the next Perelman package field.
-/
theorem adjoint_heat_kernel_construction_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    (payload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload) :
    HasAdjointHeatKernelConstruction flow :=
  HasAdjointHeatKernelConstruction.of_adjoint_heat_kernel_construction_payload
    payload

/--
Concrete adjoint/conjugate heat-kernel estimate payloads produce the next
Perelman package field.
-/
theorem perelman_conjugate_heat_kernel_estimates_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    (payload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload) :
    HasPerelmanConjugateHeatKernelEstimates flow :=
  HasPerelmanConjugateHeatKernelEstimates.of_conjugate_heat_kernel_estimates_payload
    payload

/--
Concrete W-functional setup payloads produce the next Perelman package field.
-/
theorem perelman_w_functional_setup_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    (payload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload) :
    HasPerelmanWFunctionalSetup flow :=
  HasPerelmanWFunctionalSetup.of_w_functional_setup_payload payload

/--
Concrete entropy-gradient formula payloads produce the next Perelman package
field.
-/
theorem perelman_entropy_gradient_formula_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    (payload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload) :
    HasPerelmanEntropyGradientFormula flow :=
  HasPerelmanEntropyGradientFormula.of_entropy_gradient_formula_payload
    payload

/--
Concrete entropy first-variation payloads produce the next Perelman package
field.
-/
theorem perelman_entropy_first_variation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    (payload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload) :
    HasPerelmanEntropyFirstVariation flow :=
  HasPerelmanEntropyFirstVariation.of_entropy_first_variation_payload
    payload

/--
Concrete entropy monotonicity payloads produce the next Perelman package field.
-/
theorem perelman_entropy_monotonicity_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    (payload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload) :
    HasPerelmanEntropyMonotonicity flow :=
  HasPerelmanEntropyMonotonicity.of_entropy_monotonicity_payload
    payload

/--
Concrete entropy lower-bound propagation payloads produce the next Perelman
package field.
-/
theorem perelman_entropy_lower_bound_propagation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    (payload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload) :
    HasPerelmanEntropyLowerBoundPropagation flow :=
  HasPerelmanEntropyLowerBoundPropagation.of_entropy_lower_bound_propagation_payload
    payload

/--
Concrete entropy-functional payloads produce the next Perelman package field.
-/
theorem perelman_entropy_functional_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    (payload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload) :
    HasPerelmanEntropyFunctional flow :=
  HasPerelmanEntropyFunctional.of_entropy_functional_payload payload

/--
Concrete reduced-length first-variation payloads produce the next Perelman
package field.
-/
theorem perelman_reduced_length_first_variation_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    (payload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload) :
    HasPerelmanReducedLengthFirstVariation flow :=
  HasPerelmanReducedLengthFirstVariation.of_reduced_length_first_variation_payload
    payload

/--
Concrete reduced-distance existence payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_distance_existence_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    (payload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload) :
    HasPerelmanReducedDistanceExistence flow :=
  HasPerelmanReducedDistanceExistence.of_reduced_distance_existence_payload
    payload

/--
Concrete reduced-distance differential-inequality payloads produce the next
Perelman package field.
-/
theorem perelman_reduced_distance_differential_inequality_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    (payload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload) :
    HasPerelmanReducedDistanceDifferentialInequality flow :=
  HasPerelmanReducedDistanceDifferentialInequality.of_reduced_distance_differential_inequality_payload
    payload

/--
Concrete reduced-distance estimates payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_distance_estimates_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    (payload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload) :
    HasPerelmanReducedDistanceEstimates flow :=
  HasPerelmanReducedDistanceEstimates.of_reduced_distance_estimates_payload
    payload

/--
Concrete reduced-distance cut-locus and barrier-control payloads produce the
next Perelman package field.
-/
theorem perelman_reduced_distance_cut_locus_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    (payload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload) :
    HasPerelmanReducedDistanceCutLocusControl flow :=
  HasPerelmanReducedDistanceCutLocusControl.of_reduced_distance_cut_locus_control_payload
    payload

/--
Concrete reduced-Jacobian comparison payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_jacobian_comparison_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    (payload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload) :
    HasPerelmanReducedJacobianComparison flow :=
  HasPerelmanReducedJacobianComparison.of_reduced_jacobian_comparison_payload
    payload

/--
Concrete reduced-distance theory payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_distance_theory_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    (payload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload) :
    HasPerelmanReducedDistanceTheory flow :=
  HasPerelmanReducedDistanceTheory.of_reduced_distance_theory_payload
    payload

/--
Concrete reduced-volume definition payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_volume_definition_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    (payload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload) :
    HasPerelmanReducedVolumeDefinition flow :=
  HasPerelmanReducedVolumeDefinition.of_reduced_volume_definition_payload
    payload

/--
Concrete reduced-volume derivative-formula payloads produce the next Perelman
package field.
-/
theorem perelman_reduced_volume_derivative_formula_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    (payload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload) :
    HasPerelmanReducedVolumeDerivativeFormula flow :=
  HasPerelmanReducedVolumeDerivativeFormula.of_reduced_volume_derivative_formula_payload
    payload

/--
Concrete reduced-volume rigidity payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_volume_rigidity_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    (payload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload) :
    HasPerelmanReducedVolumeRigidity flow :=
  HasPerelmanReducedVolumeRigidity.of_reduced_volume_rigidity_payload
    payload

/--
Concrete reduced-volume positive lower-bound payloads produce the next Perelman
package field.
-/
theorem perelman_reduced_volume_positive_lower_bound_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    (payload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload) :
    HasPerelmanReducedVolumePositiveLowerBound flow :=
  HasPerelmanReducedVolumePositiveLowerBound.of_reduced_volume_positive_lower_bound_payload
    payload

/--
Concrete reduced-volume limit-rigidity payloads produce the next Perelman
package field.
-/
theorem perelman_reduced_volume_limit_rigidity_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    (payload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload) :
    HasPerelmanReducedVolumeLimitRigidity flow :=
  HasPerelmanReducedVolumeLimitRigidity.of_reduced_volume_limit_rigidity_payload
    payload

/--
Concrete reduced-volume nonincreasing payloads produce the next Perelman package
field.
-/
theorem perelman_reduced_volume_nonincreasing_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    (payload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload) :
    HasPerelmanReducedVolumeNonincreasing flow :=
  HasPerelmanReducedVolumeNonincreasing.of_reduced_volume_nonincreasing_payload
    payload

/--
Concrete reduced-volume monotonicity payloads produce the high-level
reduced-volume monotonicity interface.
-/
theorem perelman_reduced_volume_monotonicity_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {nonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    (payload :
      PerelmanReducedVolumeMonotonicityPayload
        nonincreasingPayload) :
    HasPerelmanReducedVolumeMonotonicity flow :=
  HasPerelmanReducedVolumeMonotonicity.of_reduced_volume_monotonicity_payload
    payload

/--
Concrete kappa-from-reduced-volume payloads produce the next Perelman package
field.
-/
theorem perelman_kappa_noncollapsing_from_reduced_volume_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    (payload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload) :
    HasPerelmanKappaNoncollapsingFromReducedVolume flow :=
  HasPerelmanKappaNoncollapsingFromReducedVolume.of_kappa_noncollapsing_from_reduced_volume_payload
    payload

/--
Reduced-volume kappa-noncollapsing evidence supplies the quantified
kappa-noncollapsing interface used by the no-local-collapsing package.
-/
theorem perelman_kappa_noncollapsing_quantification_of_kappa_noncollapsing_from_reduced_volume
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow) :
    HasPerelmanKappaNoncollapsingQuantification flow :=
  HasPerelmanKappaNoncollapsingQuantification.of_kappa_noncollapsing_from_reduced_volume
    kappaNoncollapsingFromReducedVolume

/--
Concrete reduced-volume kappa payloads produce quantified kappa-noncollapsing
through the accepted kappa-from-reduced-volume interface.
-/
theorem perelman_kappa_noncollapsing_quantification_of_kappa_noncollapsing_from_reduced_volume_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    (payload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload) :
    HasPerelmanKappaNoncollapsingQuantification flow :=
  perelman_kappa_noncollapsing_quantification_of_kappa_noncollapsing_from_reduced_volume
    (perelman_kappa_noncollapsing_from_reduced_volume_of_payload payload)

/--
Concrete no-local-collapsing contradiction-setup payloads produce the next
Perelman package field.
-/
theorem perelman_no_local_collapsing_contradiction_setup_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    (payload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload) :
    HasPerelmanNoLocalCollapsingContradictionSetup flow :=
  HasPerelmanNoLocalCollapsingContradictionSetup.of_no_local_collapsing_contradiction_setup_payload
    payload

/--
Concrete no-local-collapsing payloads produce Perelman's no-local-collapsing
interface.
-/
theorem perelman_no_local_collapsing_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    (payload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload) :
    HasPerelmanNoLocalCollapsing flow :=
  HasPerelmanNoLocalCollapsing.of_no_local_collapsing_payload
    payload

/--
Concrete collapsed-ball blowup payloads produce the next Perelman package
field.
-/
theorem perelman_collapsed_ball_blowup_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    (payload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload) :
    HasPerelmanCollapsedBallBlowup flow :=
  HasPerelmanCollapsedBallBlowup.of_collapsed_ball_blowup_payload payload

/--
Collapsed-ball blowup payloads carry the recorded volume-ratio contradiction.
-/
theorem perelman_volume_ratio_contradiction_of_collapsed_ball_blowup_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    (payload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload) :
    HasPerelmanVolumeRatioContradiction flow :=
  HasPerelmanVolumeRatioContradiction.of_collapsed_ball_blowup_payload
    payload

/--
Collapsed-ball blowup payloads also provide the local volume lower-bound
interface used after the volume-ratio contradiction step.
-/
theorem no_local_collapsing_volume_lower_bound_of_collapsed_ball_blowup_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    (payload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload) :
    HasNoLocalCollapsingVolumeLowerBound flow :=
  HasNoLocalCollapsingVolumeLowerBound.of_collapsed_ball_blowup_payload
    payload

/--
Concrete Hamilton compactness payloads produce the Hamilton compactness
interface for the collapsed-ball blowup sequence.
-/
theorem hamilton_compactness_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    (payload : HamiltonCompactnessPayload collapsedBallBlowupPayload) :
    HasHamiltonCompactnessTheorem flow :=
  HasHamiltonCompactnessTheorem.of_hamilton_compactness_payload payload

/--
Build ancient kappa-solution limit-extraction evidence from explicit
Hamilton-compactness extraction payload data.
-/
theorem ancient_kappa_solution_limit_extraction_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    (payload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload) :
    HasAncientKappaSolutionLimitExtraction flow :=
  HasAncientKappaSolutionLimitExtraction.of_ancient_kappa_solution_limit_extraction_payload
    payload

/--
Build ancient kappa-solution compactness evidence from explicit Hamilton-backed
ancient compactness payload data.
-/
theorem ancient_kappa_solution_compactness_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    (payload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload) :
    HasAncientKappaSolutionCompactness flow :=
  HasAncientKappaSolutionCompactness.of_ancient_kappa_solution_compactness_payload
    payload

/--
Build canonical-neighborhood scale-control evidence from explicit scale-control
payload data tied to ancient kappa-solution compactness.
-/
theorem canonical_neighborhood_scale_control_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    (payload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload) :
    HasCanonicalNeighborhoodScaleControl flow :=
  HasCanonicalNeighborhoodScaleControl.of_canonical_neighborhood_scale_control_payload
    payload

/--
Build canonical-neighborhood stability evidence from explicit stability payload
data tied to canonical-neighborhood scale control.
-/
theorem canonical_neighborhood_stability_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    (payload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload) :
    HasCanonicalNeighborhoodStability flow :=
  HasCanonicalNeighborhoodStability.of_canonical_neighborhood_stability_payload
    payload

/--
Build cross-scale canonical-neighborhood persistence evidence from explicit
persistence payload data tied to canonical-neighborhood stability.
-/
theorem canonical_neighborhood_persistence_across_scales_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    {stabilityPayload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload}
    (payload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        stabilityPayload) :
    HasCanonicalNeighborhoodPersistenceAcrossScales flow :=
  HasCanonicalNeighborhoodPersistenceAcrossScales.of_canonical_neighborhood_persistence_across_scales_payload
    payload

/--
Build canonical-neighborhood neck/cap dichotomy evidence from explicit
dichotomy payload data tied to cross-scale canonical-neighborhood persistence.
-/
theorem canonical_neighborhood_neck_cap_dichotomy_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    {stabilityPayload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload}
    {persistencePayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        stabilityPayload}
    (payload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        persistencePayload) :
    HasCanonicalNeighborhoodNeckCapDichotomy flow :=
  HasCanonicalNeighborhoodNeckCapDichotomy.of_canonical_neighborhood_neck_cap_dichotomy_payload
    payload

/--
Build canonical-neighborhood classification evidence from explicit
classification payload data tied to the neck/cap dichotomy payload.
-/
theorem canonical_neighborhood_classification_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    {stabilityPayload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload}
    {persistencePayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        stabilityPayload}
    {neckCapPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        persistencePayload}
    (payload :
      CanonicalNeighborhoodClassificationPayload
        neckCapPayload) :
    HasCanonicalNeighborhoodClassification flow :=
  HasCanonicalNeighborhoodClassification.of_canonical_neighborhood_classification_payload
    payload

/--
Build canonical-neighborhood theorem evidence from explicit theorem payload
data tied to the classification payload.
-/
theorem canonical_neighborhood_theorem_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    {stabilityPayload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload}
    {persistencePayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        stabilityPayload}
    {neckCapPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        persistencePayload}
    {classificationPayload :
      CanonicalNeighborhoodClassificationPayload neckCapPayload}
    (payload :
      CanonicalNeighborhoodTheoremPayload
        classificationPayload) :
    HasCanonicalNeighborhoodTheorem flow :=
  HasCanonicalNeighborhoodTheorem.of_canonical_neighborhood_theorem_payload
    payload

/--
Build singularity-model classification evidence from explicit classification
payload data tied to asymptotic solitons and canonical neighborhoods.
-/
theorem singularity_model_classification_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    {pointedRescalingPayload :
      KappaSolutionPointedRescalingPayload limitExtractionPayload}
    {curvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload pointedRescalingPayload}
    {structurePayload :
      KappaSolutionStructureTheoryPayload curvatureNormalizationPayload}
    {nonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload structurePayload}
    {asymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        nonnegativeCurvatureOperatorPayload}
    {ancientCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload}
    {scaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientCompactnessPayload}
    {stabilityPayload :
      CanonicalNeighborhoodStabilityPayload scaleControlPayload}
    {persistencePayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        stabilityPayload}
    {neckCapPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        persistencePayload}
    {classificationPayload :
      CanonicalNeighborhoodClassificationPayload neckCapPayload}
    {canonicalNeighborhoodTheoremPayload :
      CanonicalNeighborhoodTheoremPayload classificationPayload}
    (payload :
      SingularityModelClassificationPayload
        asymptoticSolitonPayload
        canonicalNeighborhoodTheoremPayload) :
    HasSingularityModelClassification flow :=
  HasSingularityModelClassification.of_singularity_model_classification_payload
    payload

/--
Build pointed kappa-solution rescaling evidence from explicit pointed
rescaling payload data.
-/
theorem kappa_solution_pointed_rescaling_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    (payload : KappaSolutionPointedRescalingPayload limitExtractionPayload) :
    HasKappaSolutionPointedRescaling flow :=
  HasKappaSolutionPointedRescaling.of_kappa_solution_pointed_rescaling_payload
    payload

/--
Build kappa-solution curvature-normalization evidence from explicit
curvature-normalization payload data.
-/
theorem kappa_solution_curvature_normalization_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    {pointedRescalingPayload :
      KappaSolutionPointedRescalingPayload limitExtractionPayload}
    (payload :
      KappaSolutionCurvatureNormalizationPayload pointedRescalingPayload) :
    HasKappaSolutionCurvatureNormalization flow :=
  HasKappaSolutionCurvatureNormalization.of_kappa_solution_curvature_normalization_payload
    payload

/--
Build kappa-solution structure-theory evidence from explicit structure-theory
payload data.
-/
theorem kappa_solution_structure_theory_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    {pointedRescalingPayload :
      KappaSolutionPointedRescalingPayload limitExtractionPayload}
    {curvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload pointedRescalingPayload}
    (payload :
      KappaSolutionStructureTheoryPayload curvatureNormalizationPayload) :
    HasKappaSolutionStructureTheory flow :=
  HasKappaSolutionStructureTheory.of_kappa_solution_structure_theory_payload
    payload

/--
Build kappa-solution nonnegative curvature-operator evidence from explicit
curvature-operator payload data.
-/
theorem kappa_solution_nonnegative_curvature_operator_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    {pointedRescalingPayload :
      KappaSolutionPointedRescalingPayload limitExtractionPayload}
    {curvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload pointedRescalingPayload}
    {structurePayload :
      KappaSolutionStructureTheoryPayload curvatureNormalizationPayload}
    (payload :
      KappaSolutionNonnegativeCurvatureOperatorPayload structurePayload) :
    HasKappaSolutionNonnegativeCurvatureOperator flow :=
  HasKappaSolutionNonnegativeCurvatureOperator.of_kappa_solution_nonnegative_curvature_operator_payload
    payload

/--
Build kappa-solution asymptotic-soliton evidence from explicit
asymptotic-soliton payload data.
-/
theorem kappa_solution_asymptotic_soliton_of_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {fFunctionalPayload : PerelmanFFunctionalSetupPayload flow}
    {entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload}
    {entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload}
    {entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload}
    {conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload}
    {adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload}
    {conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload}
    {wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload}
    {entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload}
    {entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload}
    {entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload}
    {entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload}
    {entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload}
    {reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload}
    {reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload}
    {reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload}
    {reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload}
    {reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload}
    {reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload}
    {reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload}
    {reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload}
    {reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload}
    {reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload}
    {reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload}
    {reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload}
    {reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload}
    {kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload}
    {noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload}
    {collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload}
    {hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload}
    {limitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload}
    {pointedRescalingPayload :
      KappaSolutionPointedRescalingPayload limitExtractionPayload}
    {curvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload pointedRescalingPayload}
    {structurePayload :
      KappaSolutionStructureTheoryPayload curvatureNormalizationPayload}
    {nonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload structurePayload}
    (payload :
      KappaSolutionAsymptoticSolitonPayload
        nonnegativeCurvatureOperatorPayload) :
    HasKappaSolutionAsymptoticSoliton flow :=
  HasKappaSolutionAsymptoticSoliton.of_kappa_solution_asymptotic_soliton_payload
    payload

/--
Assemble the Perelman singularity-control package from concrete F-functional
setup and entropy-normalization payload data, the remaining component inputs,
and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerExistence : HasPerelmanEntropyMinimizerExistence flow)
    (entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow)
    (conjugateHeatEquation : HasConjugateHeatEquationTheory flow)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_and_components_and_control_payload
    fFunctionalPayload
    (perelman_entropy_normalization_of_payload entropyNormalizationPayload)
    entropyMinimizerExistence entropyLogSobolevControl conjugateHeatEquation
    adjointHeatKernel conjugateHeatKernelEstimates wFunctionalSetup
    entropyGradientFormula entropyFirstVariation entropyMonotonicity
    entropyLowerBoundPropagation entropyFunctional reducedLengthFirstVariation
    reducedDistanceExistence reducedDistanceDifferentialInequality
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, and entropy-minimizer payload data, the remaining
component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow)
    (conjugateHeatEquation : HasConjugateHeatEquationTheory flow)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload
    (perelman_entropy_minimizer_existence_of_payload
      entropyMinimizerPayload)
    entropyLogSobolevControl conjugateHeatEquation adjointHeatKernel
    conjugateHeatKernelEstimates wFunctionalSetup entropyGradientFormula
    entropyFirstVariation entropyMonotonicity entropyLowerBoundPropagation
    entropyFunctional reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, and entropy log-Sobolev payload data,
the remaining component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatEquation : HasConjugateHeatEquationTheory flow)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    (perelman_entropy_log_sobolev_control_of_payload
      entropyLogSobolevPayload)
    conjugateHeatEquation adjointHeatKernel conjugateHeatKernelEstimates
    wFunctionalSetup entropyGradientFormula entropyFirstVariation
    entropyMonotonicity entropyLowerBoundPropagation entropyFunctional
    reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, and conjugate
heat equation payload data, the remaining component inputs, and aggregate
singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatKernel : HasAdjointHeatKernelConstruction flow)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload
    (conjugate_heat_equation_theory_of_payload conjugateHeatPayload)
    adjointHeatKernel conjugateHeatKernelEstimates wFunctionalSetup
    entropyGradientFormula entropyFirstVariation entropyMonotonicity
    entropyLowerBoundPropagation entropyFunctional reducedLengthFirstVariation
    reducedDistanceExistence reducedDistanceDifferentialInequality
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, and adjoint heat-kernel payload data, the remaining component inputs,
and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimates :
      HasPerelmanConjugateHeatKernelEstimates flow)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload
    (adjoint_heat_kernel_construction_of_payload adjointHeatPayload)
    conjugateHeatKernelEstimates wFunctionalSetup entropyGradientFormula
    entropyFirstVariation entropyMonotonicity entropyLowerBoundPropagation
    entropyFunctional reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, and heat-kernel estimate payload data, the
remaining component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalSetup : HasPerelmanWFunctionalSetup flow)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    (perelman_conjugate_heat_kernel_estimates_of_payload
      conjugateHeatKernelEstimatesPayload)
    wFunctionalSetup entropyGradientFormula entropyFirstVariation
    entropyMonotonicity entropyLowerBoundPropagation entropyFunctional
    reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, and W-functional payload
data, the remaining component inputs, and aggregate singularity-control payload
data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientFormula : HasPerelmanEntropyGradientFormula flow)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload
    (perelman_w_functional_setup_of_payload wFunctionalPayload)
    entropyGradientFormula entropyFirstVariation entropyMonotonicity
    entropyLowerBoundPropagation entropyFunctional reducedLengthFirstVariation
    reducedDistanceExistence reducedDistanceDifferentialInequality
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, and entropy
gradient formula payload data, the remaining component inputs, and aggregate
singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariation : HasPerelmanEntropyFirstVariation flow)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    (perelman_entropy_gradient_formula_of_payload entropyGradientPayload)
    entropyFirstVariation entropyMonotonicity entropyLowerBoundPropagation
    entropyFunctional reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, and entropy first-variation payload data, the remaining
component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicity : HasPerelmanEntropyMonotonicity flow)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload
    (perelman_entropy_first_variation_of_payload
      entropyFirstVariationPayload)
    entropyMonotonicity entropyLowerBoundPropagation entropyFunctional
    reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, and entropy monotonicity payload data,
the remaining component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagation :
      HasPerelmanEntropyLowerBoundPropagation flow)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    (perelman_entropy_monotonicity_of_payload
      entropyMonotonicityPayload)
    entropyLowerBoundPropagation entropyFunctional reducedLengthFirstVariation
    reducedDistanceExistence reducedDistanceDifferentialInequality
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, and entropy
lower-bound propagation payload data, the remaining component inputs, and
aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctional : HasPerelmanEntropyFunctional flow)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload
    (perelman_entropy_lower_bound_propagation_of_payload
      entropyLowerBoundPropagationPayload)
    entropyFunctional reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, and entropy-functional payload data, the remaining
component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariation :
      HasPerelmanReducedLengthFirstVariation flow)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    (perelman_entropy_functional_of_payload entropyFunctionalPayload)
    reducedLengthFirstVariation reducedDistanceExistence
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, and reduced-length first-variation
payload data, the remaining component inputs, and aggregate singularity-control
payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload
    (perelman_reduced_length_first_variation_of_payload
      reducedLengthFirstVariationPayload)
    reducedDistanceExistence reducedDistanceDifferentialInequality
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
and reduced-distance existence payload data, the remaining component inputs,
and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequality :
      HasPerelmanReducedDistanceDifferentialInequality flow)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    (perelman_reduced_distance_existence_of_payload
      reducedDistanceExistencePayload)
    reducedDistanceDifferentialInequality reducedDistanceEstimates
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, and reduced-distance differential-inequality
payload data, the remaining component inputs, and aggregate
singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    (perelman_reduced_distance_differential_inequality_of_payload
      reducedDistanceDifferentialInequalityPayload)
    reducedDistanceEstimates reducedDistanceCutLocusControl
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality, and
reduced-distance estimates payload data, the remaining component inputs, and
aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControl :
      HasPerelmanReducedDistanceCutLocusControl flow)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    (perelman_reduced_distance_estimates_of_payload
      reducedDistanceEstimatesPayload)
    reducedDistanceCutLocusControl reducedJacobianComparison reducedDistance
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, and reduced-distance cut-locus/barrier-control
payload data, the remaining component inputs, and aggregate singularity-control
payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload
    (perelman_reduced_distance_cut_locus_control_of_payload
      reducedDistanceCutLocusControlPayload)
    reducedJacobianComparison reducedDistance reducedVolumeDefinition
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control, and
reduced-Jacobian comparison payload data, the remaining component inputs, and
aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistance : HasPerelmanReducedDistanceTheory flow)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload
    reducedDistanceCutLocusControlPayload
    (perelman_reduced_jacobian_comparison_of_payload
      reducedJacobianComparisonPayload)
    reducedDistance reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, and reduced-distance-theory payload data, the
remaining component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload
    (perelman_reduced_distance_theory_of_payload
      reducedDistanceTheoryPayload)
    reducedVolumeDefinition reducedVolumeDerivativeFormula
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, and reduced-volume
definition payload data, the remaining component inputs, and aggregate
singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormula :
      HasPerelmanReducedVolumeDerivativeFormula flow)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    (perelman_reduced_volume_definition_of_payload
      reducedVolumeDefinitionPayload)
    reducedVolumeDerivativeFormula reducedVolumeRigidity
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, and reduced-volume derivative-formula payload data, the remaining
component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload
    (perelman_reduced_volume_derivative_formula_of_payload
      reducedVolumeDerivativeFormulaPayload)
    reducedVolumeRigidity reducedVolumePositiveLowerBound
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, and reduced-volume rigidity
payload data, the remaining component inputs, and aggregate singularity-control
payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBound :
      HasPerelmanReducedVolumePositiveLowerBound flow)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    (perelman_reduced_volume_rigidity_of_payload
      reducedVolumeRigidityPayload)
    reducedVolumePositiveLowerBound reducedVolumeLimitRigidity
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity, and
reduced-volume positive lower-bound payload data, the remaining component
inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidity :
      HasPerelmanReducedVolumeLimitRigidity flow)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload
    (perelman_reduced_volume_positive_lower_bound_of_payload
      reducedVolumePositiveLowerBoundPayload)
    reducedVolumeLimitRigidity reducedVolumeNonincreasing
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, and reduced-volume limit-rigidity payload
data, the remaining component inputs, and aggregate singularity-control payload
data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasing :
      HasPerelmanReducedVolumeNonincreasing flow)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    (perelman_reduced_volume_limit_rigidity_of_payload
      reducedVolumeLimitRigidityPayload)
    reducedVolumeNonincreasing kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity, and
reduced-volume nonincreasing payload data, the remaining component inputs, and
aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolume :
      HasPerelmanKappaNoncollapsingFromReducedVolume flow)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload
    (perelman_reduced_volume_nonincreasing_of_payload
      reducedVolumeNonincreasingPayload)
    kappaNoncollapsingFromReducedVolume
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, and kappa-from-reduced-volume payload data, the
remaining component inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetup :
      HasPerelmanNoLocalCollapsingContradictionSetup flow)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    (perelman_kappa_noncollapsing_from_reduced_volume_of_payload
      kappaNoncollapsingFromReducedVolumePayload)
    noLocalCollapsingContradictionSetup collapsedBallBlowup
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume, and
no-local-collapsing contradiction-setup payload data, the remaining component
inputs, and aggregate singularity-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    (perelman_no_local_collapsing_contradiction_setup_of_payload
      noLocalCollapsingContradictionSetupPayload)
    collapsedBallBlowup volumeRatioContradiction
    noLocalCollapsingVolumeLowerBound kappaNoncollapsing
    hamiltonCompactness ancientKappaSolutionLimitExtraction
    kappaSolutionPointedRescaling kappaSolutionCurvatureNormalization
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, and collapsed-ball blowup payload
data, the remaining component inputs, and aggregate singularity-control payload
data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    (perelman_collapsed_ball_blowup_of_payload
      collapsedBallBlowupPayload)
    volumeRatioContradiction noLocalCollapsingVolumeLowerBound
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, and collapsed-ball blowup payload
data, deriving the volume-ratio contradiction from that blowup payload.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (noLocalCollapsingVolumeLowerBound :
      HasNoLocalCollapsingVolumeLowerBound flow)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload
    (perelman_volume_ratio_contradiction_of_collapsed_ball_blowup_payload
      collapsedBallBlowupPayload)
    noLocalCollapsingVolumeLowerBound kappaNoncollapsing
    hamiltonCompactness ancientKappaSolutionLimitExtraction
    kappaSolutionPointedRescaling kappaSolutionCurvatureNormalization
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, and collapsed-ball blowup payload
data, deriving both the volume-ratio contradiction and local volume lower-bound
interfaces from that blowup payload.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_volume_lower_bound_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload
    (no_local_collapsing_volume_lower_bound_of_collapsed_ball_blowup_payload
      collapsedBallBlowupPayload)
    kappaNoncollapsing hamiltonCompactness
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, and collapsed-ball blowup payload
data, deriving the quantified kappa-noncollapsing interface from the
reduced-volume kappa payload.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_volume_lower_bound_kappa_quantification_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactness : HasHamiltonCompactnessTheorem flow)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_volume_lower_bound_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload
    (perelman_kappa_noncollapsing_quantification_of_kappa_noncollapsing_from_reduced_volume_payload
      kappaNoncollapsingFromReducedVolumePayload)
    hamiltonCompactness ancientKappaSolutionLimitExtraction
    kappaSolutionPointedRescaling kappaSolutionCurvatureNormalization
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, and Hamilton
compactness payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtraction :
      HasAncientKappaSolutionLimitExtraction flow)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_volume_ratio_contradiction_volume_lower_bound_kappa_quantification_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload
    (hamilton_compactness_of_payload hamiltonCompactnessPayload)
    ancientKappaSolutionLimitExtraction kappaSolutionPointedRescaling
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, and ancient kappa-solution limit-extraction payload
data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    (ancient_kappa_solution_limit_extraction_of_payload
      ancientKappaSolutionLimitExtractionPayload)
    kappaSolutionPointedRescaling kappaSolutionCurvatureNormalization
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution limit-extraction payload data,
and pointed kappa-solution rescaling payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalization :
      HasKappaSolutionCurvatureNormalization flow)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    (kappa_solution_pointed_rescaling_of_payload
      kappaSolutionPointedRescalingPayload)
    kappaSolutionCurvatureNormalization kappaSolutionStructure
    kappaSolutionNonnegativeCurvatureOperator kappaSolutionAsymptoticSoliton
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution limit-extraction payload data,
pointed kappa-solution rescaling payload data, and kappa-solution
curvature-normalization payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructure : HasKappaSolutionStructureTheory flow)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    (kappa_solution_curvature_normalization_of_payload
      kappaSolutionCurvatureNormalizationPayload)
    kappaSolutionStructure kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution limit-extraction payload data,
pointed kappa-solution rescaling payload data, curvature-normalization payload
data, and kappa-solution structure-theory payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperator :
      HasKappaSolutionNonnegativeCurvatureOperator flow)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    (kappa_solution_structure_theory_of_payload kappaSolutionStructurePayload)
    kappaSolutionNonnegativeCurvatureOperator
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution limit-extraction payload data,
pointed kappa-solution rescaling payload data, curvature-normalization payload
data, structure-theory payload data, and nonnegative curvature-operator payload
data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSoliton :
      HasKappaSolutionAsymptoticSoliton flow)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    (kappa_solution_nonnegative_curvature_operator_of_payload
      kappaSolutionNonnegativeCurvatureOperatorPayload)
    kappaSolutionAsymptoticSoliton ancientKappaSolutionCompactness
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution limit-extraction payload data,
pointed kappa-solution rescaling payload data, curvature-normalization payload
data, structure-theory payload data, nonnegative curvature-operator payload
data, and asymptotic-soliton payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (ancientKappaSolutionCompactness :
      HasAncientKappaSolutionCompactness flow)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    (kappa_solution_asymptotic_soliton_of_payload
      kappaSolutionAsymptoticSolitonPayload)
    ancientKappaSolutionCompactness canonicalNeighborhoodScaleControl
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, and
asymptotic-soliton payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControl :
      HasCanonicalNeighborhoodScaleControl flow)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    (ancient_kappa_solution_compactness_of_payload
      ancientKappaSolutionCompactnessPayload)
    canonicalNeighborhoodScaleControl canonicalNeighborhoodStability
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, asymptotic-soliton
payload data, and canonical-neighborhood scale-control payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    (canonical_neighborhood_scale_control_of_payload
      canonicalNeighborhoodScaleControlPayload)
    canonicalNeighborhoodStability canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, asymptotic-soliton
payload data, canonical-neighborhood scale-control payload data, and
canonical-neighborhood stability payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScales :
      HasCanonicalNeighborhoodPersistenceAcrossScales flow)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    (canonical_neighborhood_stability_of_payload
      canonicalNeighborhoodStabilityPayload)
    canonicalNeighborhoodPersistenceAcrossScales
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, asymptotic-soliton
payload data, canonical-neighborhood scale-control payload data,
canonical-neighborhood stability payload data, and cross-scale persistence
payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomy :
      HasCanonicalNeighborhoodNeckCapDichotomy flow)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    (canonical_neighborhood_persistence_across_scales_of_payload
      canonicalNeighborhoodPersistenceAcrossScalesPayload)
    canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, asymptotic-soliton
payload data, canonical-neighborhood scale-control payload data,
canonical-neighborhood stability payload data, cross-scale persistence payload
data, and canonical-neighborhood neck/cap dichotomy payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassification :
      HasCanonicalNeighborhoodClassification flow)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    (canonical_neighborhood_neck_cap_dichotomy_of_payload
      canonicalNeighborhoodNeckCapDichotomyPayload)
    canonicalNeighborhoodClassification
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from concrete F-functional,
entropy-normalization, entropy-minimizer, entropy log-Sobolev, conjugate heat
equation, adjoint heat-kernel, heat-kernel estimate, W-functional, entropy
gradient formula, entropy first-variation, entropy monotonicity, entropy
lower-bound propagation, entropy-functional, reduced-length first-variation,
reduced-distance existence, reduced-distance differential-inequality,
reduced-distance estimates, reduced-distance cut-locus/barrier-control,
reduced-Jacobian comparison, reduced-distance-theory, reduced-volume
definition, reduced-volume derivative-formula, reduced-volume rigidity,
reduced-volume positive lower-bound, reduced-volume limit-rigidity,
reduced-volume nonincreasing, kappa-from-reduced-volume,
no-local-collapsing contradiction-setup, collapsed-ball blowup, Hamilton
compactness payload data, ancient kappa-solution compactness payload data,
ancient kappa-solution limit-extraction payload data, pointed kappa-solution
rescaling payload data, curvature-normalization payload data, structure-theory
payload data, nonnegative curvature-operator payload data, asymptotic-soliton
payload data, canonical-neighborhood scale-control payload data,
canonical-neighborhood stability payload data, cross-scale persistence payload
data, canonical-neighborhood neck/cap dichotomy payload data, and
canonical-neighborhood classification payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (noLocalCollapsing : HasPerelmanNoLocalCollapsing flow)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow noLocalCollapsing
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    canonicalNeighborhoodNeckCapDichotomyPayload
    (canonical_neighborhood_classification_of_payload
      canonicalNeighborhoodClassificationPayload)
    noLocalCollapsing reducedVolume canonicalNeighborhood
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from payload-backed
no-local-collapsing data after the canonical-neighborhood classification route.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (noLocalCollapsingPayload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload)
    (reducedVolume : HasPerelmanReducedVolumeMonotonicity flow)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow
        (perelman_no_local_collapsing_of_payload noLocalCollapsingPayload)
        reducedVolume canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    canonicalNeighborhoodNeckCapDichotomyPayload
    canonicalNeighborhoodClassificationPayload
    (perelman_no_local_collapsing_of_payload noLocalCollapsingPayload)
    reducedVolume canonicalNeighborhood singularityModelClassification
    singularityModelBlowupClassification controlPayload

/--
Assemble the Perelman singularity-control package from payload-backed
reduced-volume monotonicity after no-local-collapsing has also been derived
from payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (reducedVolumeMonotonicityPayload :
      PerelmanReducedVolumeMonotonicityPayload
        reducedVolumeNonincreasingPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (noLocalCollapsingPayload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload)
    (canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow
        (perelman_no_local_collapsing_of_payload noLocalCollapsingPayload)
        (perelman_reduced_volume_monotonicity_of_payload
          reducedVolumeMonotonicityPayload)
        canonicalNeighborhood singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    canonicalNeighborhoodNeckCapDichotomyPayload
    canonicalNeighborhoodClassificationPayload
    noLocalCollapsingPayload
    (perelman_reduced_volume_monotonicity_of_payload
      reducedVolumeMonotonicityPayload)
    canonicalNeighborhood singularityModelClassification
    singularityModelBlowupClassification controlPayload

/--
Assemble the Perelman singularity-control package from payload-backed
canonical-neighborhood theorem data after no-local-collapsing and
reduced-volume monotonicity have also been derived from payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_canonical_neighborhood_theorem_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (reducedVolumeMonotonicityPayload :
      PerelmanReducedVolumeMonotonicityPayload
        reducedVolumeNonincreasingPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (canonicalNeighborhoodTheoremPayload :
      CanonicalNeighborhoodTheoremPayload
        canonicalNeighborhoodClassificationPayload)
    (noLocalCollapsingPayload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload)
    (singularityModelClassification :
      HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow
        (perelman_no_local_collapsing_of_payload noLocalCollapsingPayload)
        (perelman_reduced_volume_monotonicity_of_payload
          reducedVolumeMonotonicityPayload)
        (canonical_neighborhood_theorem_of_payload
          canonicalNeighborhoodTheoremPayload)
        singularityModelClassification
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    reducedVolumeMonotonicityPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    canonicalNeighborhoodNeckCapDichotomyPayload
    canonicalNeighborhoodClassificationPayload
    noLocalCollapsingPayload
    (canonical_neighborhood_theorem_of_payload
      canonicalNeighborhoodTheoremPayload)
    singularityModelClassification singularityModelBlowupClassification
    controlPayload

/--
Assemble the Perelman singularity-control package from payload-backed
singularity-model classification after canonical neighborhoods have been
derived from payload data.
-/
theorem perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_canonical_neighborhood_theorem_payload_singularity_model_classification_payload_and_components_and_control_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (reducedVolumeMonotonicityPayload :
      PerelmanReducedVolumeMonotonicityPayload
        reducedVolumeNonincreasingPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (canonicalNeighborhoodTheoremPayload :
      CanonicalNeighborhoodTheoremPayload
        canonicalNeighborhoodClassificationPayload)
    (singularityModelClassificationPayload :
      SingularityModelClassificationPayload
        kappaSolutionAsymptoticSolitonPayload
        canonicalNeighborhoodTheoremPayload)
    (noLocalCollapsingPayload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (controlPayload :
      PerelmanSingularityControlPayload flow
        (perelman_no_local_collapsing_of_payload noLocalCollapsingPayload)
        (perelman_reduced_volume_monotonicity_of_payload
          reducedVolumeMonotonicityPayload)
        (canonical_neighborhood_theorem_of_payload
          canonicalNeighborhoodTheoremPayload)
        (singularity_model_classification_of_payload
          singularityModelClassificationPayload)
        singularityModelBlowupClassification) :
    PerelmanSingularityControlPackage (n := n) (M := M) flow :=
  perelmanSingularityControlPackage_of_f_functional_payload_entropy_normalization_payload_entropy_minimizer_payload_log_sobolev_payload_conjugate_heat_payload_adjoint_heat_payload_conjugate_heat_kernel_estimates_payload_w_functional_payload_entropy_gradient_payload_entropy_first_variation_payload_entropy_monotonicity_payload_entropy_lower_bound_payload_entropy_functional_payload_reduced_length_first_variation_payload_reduced_distance_existence_payload_reduced_distance_differential_inequality_payload_reduced_distance_estimates_payload_reduced_distance_cut_locus_payload_reduced_jacobian_payload_reduced_distance_theory_payload_reduced_volume_definition_payload_reduced_volume_derivative_formula_payload_reduced_volume_rigidity_payload_reduced_volume_positive_lower_bound_payload_reduced_volume_limit_rigidity_payload_reduced_volume_nonincreasing_payload_kappa_noncollapsing_from_reduced_volume_payload_no_local_collapsing_contradiction_setup_payload_collapsed_ball_blowup_payload_hamilton_compactness_payload_ancient_kappa_solution_compactness_payload_ancient_kappa_solution_limit_extraction_payload_kappa_solution_pointed_rescaling_payload_kappa_solution_curvature_normalization_payload_kappa_solution_structure_payload_kappa_solution_nonnegative_curvature_operator_payload_kappa_solution_asymptotic_soliton_payload_canonical_neighborhood_scale_control_payload_canonical_neighborhood_stability_payload_canonical_neighborhood_persistence_across_scales_payload_canonical_neighborhood_neck_cap_dichotomy_payload_canonical_neighborhood_classification_payload_no_local_collapsing_payload_reduced_volume_monotonicity_payload_canonical_neighborhood_theorem_payload_and_components_and_control_payload
    fFunctionalPayload entropyNormalizationPayload entropyMinimizerPayload
    entropyLogSobolevPayload conjugateHeatPayload adjointHeatPayload
    conjugateHeatKernelEstimatesPayload wFunctionalPayload
    entropyGradientPayload entropyFirstVariationPayload
    entropyMonotonicityPayload entropyLowerBoundPropagationPayload
    entropyFunctionalPayload reducedLengthFirstVariationPayload
    reducedDistanceExistencePayload
    reducedDistanceDifferentialInequalityPayload
    reducedDistanceEstimatesPayload reducedDistanceCutLocusControlPayload
    reducedJacobianComparisonPayload reducedDistanceTheoryPayload
    reducedVolumeDefinitionPayload reducedVolumeDerivativeFormulaPayload
    reducedVolumeRigidityPayload reducedVolumePositiveLowerBoundPayload
    reducedVolumeLimitRigidityPayload reducedVolumeNonincreasingPayload
    reducedVolumeMonotonicityPayload
    kappaNoncollapsingFromReducedVolumePayload
    noLocalCollapsingContradictionSetupPayload
    collapsedBallBlowupPayload hamiltonCompactnessPayload
    ancientKappaSolutionCompactnessPayload
    ancientKappaSolutionLimitExtractionPayload
    kappaSolutionPointedRescalingPayload
    kappaSolutionCurvatureNormalizationPayload
    kappaSolutionStructurePayload
    kappaSolutionNonnegativeCurvatureOperatorPayload
    kappaSolutionAsymptoticSolitonPayload
    canonicalNeighborhoodScaleControlPayload
    canonicalNeighborhoodStabilityPayload
    canonicalNeighborhoodPersistenceAcrossScalesPayload
    canonicalNeighborhoodNeckCapDichotomyPayload
    canonicalNeighborhoodClassificationPayload
    canonicalNeighborhoodTheoremPayload
    noLocalCollapsingPayload
    (singularity_model_classification_of_payload
      singularityModelClassificationPayload)
    singularityModelBlowupClassification controlPayload

/--
A classification source supplies blow-up classification exactly when its
classified models cover every pointed rescaling index.
-/
theorem perelman_singularity_model_blowup_classification_of_payload_source_and_coverage
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (source : SingularityModelClassificationPayloadSource flow)
    (hCoverage :
      Function.Surjective source.singularityModelToPointedRescalingIndex) :
    HasSingularityModelBlowupClassification flow :=
  HasSingularityModelBlowupClassification.of_classification_payload_source
    source hCoverage

/--
Payload-backed surgery construction plus the available Perelman control legs
give the finite-extinction-facing certificate once classified singularity
models cover every pointed rescaling index. The certificate contains a
theorem-shaped surgery construction statement, its sub-obligation payload, the
aggregate surgery witness, no-local-collapsing, reduced-volume monotonicity,
canonical-neighborhood control, singularity-model classification, and the
resulting blow-up classification.
-/
theorem surgery_perelman_finite_extinction_control_certificate_of_payloads
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (constructionPackage :
      RicciFlowWithSurgeryConstructionPackage (n := n) (M := M) flow)
    (fFunctionalPayload : PerelmanFFunctionalSetupPayload flow)
    (entropyNormalizationPayload :
      PerelmanEntropyNormalizationPayload fFunctionalPayload)
    (entropyMinimizerPayload :
      PerelmanEntropyMinimizerExistencePayload
        entropyNormalizationPayload)
    (entropyLogSobolevPayload :
      PerelmanEntropyLogSobolevControlPayload
        entropyMinimizerPayload)
    (conjugateHeatPayload :
      ConjugateHeatEquationTheoryPayload entropyLogSobolevPayload)
    (adjointHeatPayload :
      AdjointHeatKernelConstructionPayload conjugateHeatPayload)
    (conjugateHeatKernelEstimatesPayload :
      PerelmanConjugateHeatKernelEstimatesPayload adjointHeatPayload)
    (wFunctionalPayload :
      PerelmanWFunctionalSetupPayload
        conjugateHeatKernelEstimatesPayload)
    (entropyGradientPayload :
      PerelmanEntropyGradientFormulaPayload wFunctionalPayload)
    (entropyFirstVariationPayload :
      PerelmanEntropyFirstVariationPayload entropyGradientPayload)
    (entropyMonotonicityPayload :
      PerelmanEntropyMonotonicityPayload
        entropyFirstVariationPayload)
    (entropyLowerBoundPropagationPayload :
      PerelmanEntropyLowerBoundPropagationPayload
        entropyMonotonicityPayload)
    (entropyFunctionalPayload :
      PerelmanEntropyFunctionalPayload
        entropyLowerBoundPropagationPayload)
    (reducedLengthFirstVariationPayload :
      PerelmanReducedLengthFirstVariationPayload
        entropyFunctionalPayload)
    (reducedDistanceExistencePayload :
      PerelmanReducedDistanceExistencePayload
        reducedLengthFirstVariationPayload)
    (reducedDistanceDifferentialInequalityPayload :
      PerelmanReducedDistanceDifferentialInequalityPayload
        reducedDistanceExistencePayload)
    (reducedDistanceEstimatesPayload :
      PerelmanReducedDistanceEstimatesPayload
        reducedDistanceDifferentialInequalityPayload)
    (reducedDistanceCutLocusControlPayload :
      PerelmanReducedDistanceCutLocusControlPayload
        reducedDistanceEstimatesPayload)
    (reducedJacobianComparisonPayload :
      PerelmanReducedJacobianComparisonPayload
        reducedDistanceCutLocusControlPayload)
    (reducedDistanceTheoryPayload :
      PerelmanReducedDistanceTheoryPayload
        reducedJacobianComparisonPayload)
    (reducedVolumeDefinitionPayload :
      PerelmanReducedVolumeDefinitionPayload
        reducedDistanceTheoryPayload)
    (reducedVolumeDerivativeFormulaPayload :
      PerelmanReducedVolumeDerivativeFormulaPayload
        reducedVolumeDefinitionPayload)
    (reducedVolumeRigidityPayload :
      PerelmanReducedVolumeRigidityPayload
        reducedVolumeDerivativeFormulaPayload)
    (reducedVolumePositiveLowerBoundPayload :
      PerelmanReducedVolumePositiveLowerBoundPayload
        reducedVolumeRigidityPayload)
    (reducedVolumeLimitRigidityPayload :
      PerelmanReducedVolumeLimitRigidityPayload
        reducedVolumePositiveLowerBoundPayload)
    (reducedVolumeNonincreasingPayload :
      PerelmanReducedVolumeNonincreasingPayload
        reducedVolumeLimitRigidityPayload)
    (reducedVolumeMonotonicityPayload :
      PerelmanReducedVolumeMonotonicityPayload
        reducedVolumeNonincreasingPayload)
    (kappaNoncollapsingFromReducedVolumePayload :
      PerelmanKappaNoncollapsingFromReducedVolumePayload
        reducedVolumeNonincreasingPayload)
    (noLocalCollapsingContradictionSetupPayload :
      PerelmanNoLocalCollapsingContradictionSetupPayload
        kappaNoncollapsingFromReducedVolumePayload)
    (collapsedBallBlowupPayload :
      PerelmanCollapsedBallBlowupPayload
        noLocalCollapsingContradictionSetupPayload)
    (hamiltonCompactnessPayload :
      HamiltonCompactnessPayload collapsedBallBlowupPayload)
    (ancientKappaSolutionCompactnessPayload :
      AncientKappaSolutionCompactnessPayload
        hamiltonCompactnessPayload)
    (ancientKappaSolutionLimitExtractionPayload :
      AncientKappaSolutionLimitExtractionPayload
        hamiltonCompactnessPayload)
    (kappaSolutionPointedRescalingPayload :
      KappaSolutionPointedRescalingPayload
        ancientKappaSolutionLimitExtractionPayload)
    (kappaSolutionCurvatureNormalizationPayload :
      KappaSolutionCurvatureNormalizationPayload
        kappaSolutionPointedRescalingPayload)
    (kappaSolutionStructurePayload :
      KappaSolutionStructureTheoryPayload
        kappaSolutionCurvatureNormalizationPayload)
    (kappaSolutionNonnegativeCurvatureOperatorPayload :
      KappaSolutionNonnegativeCurvatureOperatorPayload
        kappaSolutionStructurePayload)
    (kappaSolutionAsymptoticSolitonPayload :
      KappaSolutionAsymptoticSolitonPayload
        kappaSolutionNonnegativeCurvatureOperatorPayload)
    (canonicalNeighborhoodScaleControlPayload :
      CanonicalNeighborhoodScaleControlPayload
        ancientKappaSolutionCompactnessPayload)
    (canonicalNeighborhoodStabilityPayload :
      CanonicalNeighborhoodStabilityPayload
        canonicalNeighborhoodScaleControlPayload)
    (canonicalNeighborhoodPersistenceAcrossScalesPayload :
      CanonicalNeighborhoodPersistenceAcrossScalesPayload
        canonicalNeighborhoodStabilityPayload)
    (canonicalNeighborhoodNeckCapDichotomyPayload :
      CanonicalNeighborhoodNeckCapDichotomyPayload
        canonicalNeighborhoodPersistenceAcrossScalesPayload)
    (canonicalNeighborhoodClassificationPayload :
      CanonicalNeighborhoodClassificationPayload
        canonicalNeighborhoodNeckCapDichotomyPayload)
    (canonicalNeighborhoodTheoremPayload :
      CanonicalNeighborhoodTheoremPayload
        canonicalNeighborhoodClassificationPayload)
    (singularityModelClassificationPayload :
      SingularityModelClassificationPayload
        kappaSolutionAsymptoticSolitonPayload
        canonicalNeighborhoodTheoremPayload)
    (hCoverage :
      Function.Surjective
        (SingularityModelClassificationPayloadSource.of_payload
          singularityModelClassificationPayload).singularityModelToPointedRescalingIndex)
    (noLocalCollapsingPayload :
      PerelmanNoLocalCollapsingPayload
        noLocalCollapsingContradictionSetupPayload) :
    ∃ _constructionStatement :
      RicciFlowWithSurgeryConstructionStatement flow,
    ∃ _constructionSubobligations :
      RicciFlowWithSurgeryConstructionSubobligationsPayload flow,
    ∃ _withSurgery : HasRicciFlowWithSurgery n M,
    ∃ _noLocalCollapsing : HasPerelmanNoLocalCollapsing flow,
    ∃ _reducedVolume : HasPerelmanReducedVolumeMonotonicity flow,
    ∃ _canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow,
    ∃ _singularityModelClassification :
      HasSingularityModelClassification flow,
      HasSingularityModelBlowupClassification flow := by
  rcases surgery_construction_payload_of_construction_package
      constructionPackage with
    ⟨constructionStatement, constructionSubobligations, withSurgery⟩
  exact
    ⟨constructionStatement, constructionSubobligations, withSurgery,
      perelman_no_local_collapsing_of_payload noLocalCollapsingPayload,
      perelman_reduced_volume_monotonicity_of_payload
        reducedVolumeMonotonicityPayload,
      canonical_neighborhood_theorem_of_payload
        canonicalNeighborhoodTheoremPayload,
      singularity_model_classification_of_payload
        singularityModelClassificationPayload,
      perelman_singularity_model_blowup_classification_of_payload_source_and_coverage
        (SingularityModelClassificationPayloadSource.of_payload
          singularityModelClassificationPayload)
        hCoverage⟩

/-- Theorem contract for `surgery_perelman_finite_extinction_control_certificate_of_payloads`. -/
theorem surgery_perelman_finite_extinction_control_certificate_of_payloads_eq :
    @Poincare.surgery_perelman_finite_extinction_control_certificate_of_payloads =
      @Poincare.surgery_perelman_finite_extinction_control_certificate_of_payloads :=
  rfl

end Poincare
