/-
Proof-progress slice for the three-dimensional stationary zero Ricci-flow
analytic boundary.

This file specializes the existing stationary/zero-flow analytic route to the
project's `ThreeManifoldModelWithCorners` target family. It now supplies the
stationary zero metric-derivative route, the standard zero Ricci route, and the
stationary zero Ricci-flow equation evidence; analytic sub-obligations remain
explicit inputs.
-/

import Poincare.Surgery
import Poincare.ProofProgress.AnalyticProductionPackageLeviCivita

universe u

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
The project three-manifold model has the standard smooth Riemannian metric
available from mathlib's inner-product-vector-space API.

This is the positive part of the package-layer investigation: for the concrete
model `M = ThreeManifoldModel`, mathlib supplies the stationary metric input via
`riemannianMetricVectorSpace`.
-/
noncomputable def three_manifold_model_standard_riemannian_metric :
    ContMDiffRiemannianMetric ThreeManifoldModelWithCorners ω
      ThreeManifoldModel
      (fun x : ThreeManifoldModel =>
        TangentSpace ThreeManifoldModelWithCorners x) :=
  riemannianMetricVectorSpace ThreeManifoldModel

/-- The standard vector-space Riemannian metric gives a concrete metric witness. -/
theorem three_manifold_model_standard_riemannian_metric_nonempty :
    Nonempty
      (ContMDiffRiemannianMetric ThreeManifoldModelWithCorners ω
        ThreeManifoldModel
        (fun x : ThreeManifoldModel =>
          TangentSpace ThreeManifoldModelWithCorners x)) :=
  ⟨three_manifold_model_standard_riemannian_metric⟩

/--
The project standard metric is definitionally mathlib's vector-space
Riemannian metric on the Euclidean three-manifold model.
-/
@[simp] theorem three_manifold_model_standard_riemannian_metric_eq_vectorSpaceMetric :
    three_manifold_model_standard_riemannian_metric =
      riemannianMetricVectorSpace ThreeManifoldModel :=
  rfl

/--
Scoped standard-metric flatness payload for the Euclidean three-manifold model.

This records the concrete standard metric identity used by the generic
zero-curvature export below.
-/
structure ThreeManifoldModelStandardScopedZeroRiemannCurvatureData : Prop where
  metric_eq_vectorSpaceMetric :
    three_manifold_model_standard_riemannian_metric =
      riemannianMetricVectorSpace ThreeManifoldModel

/--
The standard-model-only bridge is scoped to the concrete standard vector-space
metric. Its export to the generic zero Riemann-curvature predicate is proved
separately below from the standard Euclidean three-space data source.
-/
structure ThreeManifoldModelStandardZeroRiemannCurvatureBridge : Prop where
  scopedZeroRiemannCurvature :
    ThreeManifoldModelStandardScopedZeroRiemannCurvatureData

/-- The scoped standard flatness data is constructible for the vector-space metric. -/
theorem three_manifold_model_standard_scoped_zero_riemann_curvature_data_current_api :
    ThreeManifoldModelStandardScopedZeroRiemannCurvatureData where
  metric_eq_vectorSpaceMetric := rfl

/-- The scoped standard-model bridge is closed without changing the generic API. -/
theorem three_manifold_model_standard_zero_riemann_curvature_bridge_current_api :
    ThreeManifoldModelStandardZeroRiemannCurvatureBridge where
  scopedZeroRiemannCurvature :=
    three_manifold_model_standard_scoped_zero_riemann_curvature_data_current_api

/-- The standard model carries the narrow Euclidean three-space flatness data. -/
theorem three_manifold_model_standard_zero_riemann_curvature_metric_flatness_data_current_api :
    StandardEuclideanThreeZeroRiemannCurvatureMetricData
      three_manifold_model_standard_riemannian_metric :=
  standardEuclideanThreeZeroRiemannCurvatureMetricData_vectorSpace

/-- The standard metric now exports to the generic zero Riemann-curvature predicate. -/
theorem three_manifold_model_standard_zero_riemann_curvature_metric_current_api :
    HasZeroRiemannCurvatureMetric
      three_manifold_model_standard_riemannian_metric :=
  hasZeroRiemannCurvatureMetric_of_standardEuclideanThreeZeroRiemannCurvatureMetricData
    three_manifold_model_standard_riemannian_metric
    three_manifold_model_standard_zero_riemann_curvature_metric_flatness_data_current_api

/-- The standard metric now has generic zero Riemann-curvature metric data. -/
theorem three_manifold_model_standard_zero_riemann_curvature_metric_data_current_api :
    ZeroRiemannCurvatureMetricData
      three_manifold_model_standard_riemannian_metric :=
  zeroRiemannCurvatureMetricData_of_zeroRiemannCurvature
    three_manifold_model_standard_riemannian_metric
    three_manifold_model_standard_zero_riemann_curvature_metric_current_api

/-- The closed scoped bridge exports to generic zero Riemann-curvature metric data. -/
theorem three_manifold_model_standard_zero_riemann_curvature_metric_data_of_bridge_current_api
    (_bridge : ThreeManifoldModelStandardZeroRiemannCurvatureBridge) :
    ZeroRiemannCurvatureMetricData
      three_manifold_model_standard_riemannian_metric :=
  three_manifold_model_standard_zero_riemann_curvature_metric_data_current_api

/--
The closed scoped bridge exports to zero Riemann-curvature metric data exactly
because the standard metric data is now available.
-/
theorem three_manifold_model_standard_zero_riemann_curvature_bridge_export_iff_current_api :
    (ThreeManifoldModelStandardZeroRiemannCurvatureBridge →
        ZeroRiemannCurvatureMetricData
          three_manifold_model_standard_riemannian_metric) ↔
      ZeroRiemannCurvatureMetricData
        three_manifold_model_standard_riemannian_metric := by
  constructor
  · intro exportData
    exact exportData three_manifold_model_standard_zero_riemann_curvature_bridge_current_api
  · intro data _bridge
    exact data

/--
Generic zero Riemann-curvature metric data for the standard metric is exactly a
generic zero Riemann-curvature witness for the same metric.
-/
theorem three_manifold_model_standard_zero_riemann_curvature_metric_data_iff_current_api :
    ZeroRiemannCurvatureMetricData
        three_manifold_model_standard_riemannian_metric ↔
      HasZeroRiemannCurvatureMetric
        three_manifold_model_standard_riemannian_metric := by
  constructor
  · intro data
    exact data.zeroRiemannCurvature
  · intro zeroRiemannCurvature
    exact
      zeroRiemannCurvatureMetricData_of_zeroRiemannCurvature
        three_manifold_model_standard_riemannian_metric
        zeroRiemannCurvature

/--
Generic zero Riemann-curvature data is still the input needed to derive
Ricci-flatness of the standard metric.
-/
theorem three_manifold_model_standard_zero_ricci_curvature_metric_of_zeroRiemannCurvatureMetricData_current_api
    (data :
      ZeroRiemannCurvatureMetricData
        three_manifold_model_standard_riemannian_metric) :
    HasZeroRicciCurvatureMetric
      three_manifold_model_standard_riemannian_metric :=
  hasZeroRicciCurvatureMetric_of_zeroRiemannCurvatureMetricData
    three_manifold_model_standard_riemannian_metric
    data

/-- The standard metric is Ricci-flat via its zero Riemann-curvature data. -/
theorem three_manifold_model_standard_zero_ricci_curvature_metric_current_api :
    HasZeroRicciCurvatureMetric
      three_manifold_model_standard_riemannian_metric :=
  three_manifold_model_standard_zero_ricci_curvature_metric_of_zeroRiemannCurvatureMetricData_current_api
    three_manifold_model_standard_zero_riemann_curvature_metric_data_current_api

/--
With generic zero Riemann-curvature data, the stationary standard metric has the
zero Ricci tensor candidate.
-/
theorem three_manifold_model_standard_stationary_zero_ricci_identification_of_zeroRiemannCurvatureMetricData_current_api
    (data :
      ZeroRiemannCurvatureMetricData
        three_manifold_model_standard_riemannian_metric) :
    IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric
          three_manifold_model_standard_riemannian_metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric
            three_manifold_model_standard_riemannian_metric)) :=
  stationary_zero_ricci_identification_of_zeroRicciMetric
    three_manifold_model_standard_riemannian_metric
    (three_manifold_model_standard_zero_ricci_curvature_metric_of_zeroRiemannCurvatureMetricData_current_api
      data)

/--
The stationary standard metric has the zero Ricci tensor candidate via the
closed zero Riemann-curvature export.
-/
theorem three_manifold_model_standard_stationary_zero_ricci_identification_current_api :
    IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric
          three_manifold_model_standard_riemannian_metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric
            three_manifold_model_standard_riemannian_metric)) :=
  three_manifold_model_standard_stationary_zero_ricci_identification_of_zeroRiemannCurvatureMetricData_current_api
    three_manifold_model_standard_zero_riemann_curvature_metric_data_current_api

/--
The concrete vector-space model has a stationary time-dependent metric family.

This reaches the metric part of the target package shape, but not the Ricci,
metric-derivative, equation-interface, or analytic-subobligation interfaces.
-/
theorem three_manifold_model_stationary_metric_family_nonempty :
    Nonempty
      (Σ n : ℕ∞ω,
        TimeDependentRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel) :=
  ⟨⟨ω,
    stationary_time_dependent_riemannian_metric
      three_manifold_model_standard_riemannian_metric⟩⟩

/--
Any three-manifold analytic-foundation package now exposes the final explicit
curvature evolution field.
-/
theorem three_manifold_analytic_foundation_package_curvature_evolution_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package :
      RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M) :
    HasCurvatureEvolutionEquations
      (ricci_flow_data_of_analytic_foundation_package package) :=
  curvature_evolution_of_analytic_foundation_package package

/--
Any sigma-packaged three-manifold analytic foundation exposes a flow with the
final explicit curvature evolution field.
-/
theorem three_manifold_sigma_analytic_foundation_package_curvature_evolution_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package :
      Σ n : ℕ∞ω,
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M) :
    ∃ n : ℕ∞ω,
      ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
        HasCurvatureEvolutionEquations flow := by
  rcases package with ⟨n, package⟩
  exact
    ⟨n, ricci_flow_data_of_analytic_foundation_package package,
      curvature_evolution_of_analytic_foundation_package package⟩

/--
The stationary zero metric-derivative interface is now backed by the concrete
stationary/zero payload from `Poincare.RicciFlow`.
-/
theorem stationary_zero_metric_derivative_identification_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)) :
    IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)) :=
  stationary_zero_metric_derivative_identification metric

/--
The stationary zero Ricci-identification interface is constructible from a
scoped Ricci-flat metric payload.
-/
theorem stationary_zero_ricci_identification_of_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (data : StationaryZeroRicciTensorIdentificationData metric) :
    IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)) :=
  stationary_zero_ricci_identification_of_data metric data

/--
A concrete Ricci-flat metric witness is the exact missing input for the
stationary zero Ricci tensor identification.
-/
theorem stationary_zero_ricci_identification_of_zeroRicciMetric_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (zeroRicciMetric : HasZeroRicciCurvatureMetric metric) :
    IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)) :=
  stationary_zero_ricci_identification_of_zeroRicciMetric
    metric zeroRicciMetric

/--
Zero Riemann-curvature metric data supplies the Ricci-flat metric witness needed
by the stationary zero Ricci route.
-/
theorem stationary_zero_ricci_metric_witness_of_zeroRiemannCurvatureMetricData_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (data : ZeroRiemannCurvatureMetricData metric) :
    HasZeroRicciCurvatureMetric metric :=
  hasZeroRicciCurvatureMetric_of_zeroRiemannCurvatureMetricData
    metric data

/--
Zero Riemann-curvature metric data supplies the stationary zero Ricci tensor
identification consumed by the equation-verification route.
-/
theorem stationary_zero_ricci_identification_of_zeroRiemannCurvatureMetricData_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (data : ZeroRiemannCurvatureMetricData metric) :
    IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)) :=
  stationary_zero_ricci_identification_of_zeroRicciMetric_current_api
    metric
    (stationary_zero_ricci_metric_witness_of_zeroRiemannCurvatureMetricData_current_api
      metric data)

/--
Any generic zero Riemann-curvature witness exposes the current concrete
standard-Euclidean flatness data source.
-/
theorem stationary_zero_riemann_curvature_metric_standardEuclideanThreeFlatMetric_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (zeroRiemannCurvature : HasZeroRiemannCurvatureMetric metric) :
    StandardEuclideanThreeZeroRiemannCurvatureMetricData metric :=
  zeroRiemannCurvature.standardEuclideanThreeFlatMetric

/--
Any generic zero Riemann-curvature metric data exposes the current concrete
standard-Euclidean flatness data source.
-/
theorem stationary_zero_riemann_curvature_metric_data_standardEuclideanThreeFlatMetric_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (data : ZeroRiemannCurvatureMetricData metric) :
    StandardEuclideanThreeZeroRiemannCurvatureMetricData metric :=
  stationary_zero_riemann_curvature_metric_standardEuclideanThreeFlatMetric_current_api
    metric data.zeroRiemannCurvature

/--
The stationary zero-derivative/zero-Ricci verification now supplies the
Ricci-flow equation interface.
-/
theorem stationary_zero_satisfies_ricci_flow_equation_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))) :
    SatisfiesRicciFlowEquation
      (stationary_time_dependent_riemannian_metric metric)
      (zero_ricci_curvature_data identifiesRicci) :=
  satisfies_ricci_flow_equation_of_equation_verification
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/--
The standard stationary metric carries concrete Ricci-flow equation evidence.
-/
theorem three_manifold_model_standard_stationary_zero_satisfies_ricci_flow_equation_current_api :
    SatisfiesRicciFlowEquation
      (stationary_time_dependent_riemannian_metric
        three_manifold_model_standard_riemannian_metric)
      (zero_ricci_curvature_data
        three_manifold_model_standard_stationary_zero_ricci_identification_current_api) :=
  stationary_zero_satisfies_ricci_flow_equation_current_api
    three_manifold_model_standard_riemannian_metric
    (stationary_zero_metric_derivative_identification_current_api
      three_manifold_model_standard_riemannian_metric)
    three_manifold_model_standard_stationary_zero_ricci_identification_current_api

/--
Stationary zero Ricci-flow data can now be built without an external equation
evidence hypothesis.
-/
noncomputable def stationary_zero_ricci_flow_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))) :
    RicciFlowData ThreeManifoldModelWithCorners n M :=
  zero_ricci_flow_data
    (stationary_time_dependent_riemannian_metric metric)
    identifiesRicci
    (stationary_zero_satisfies_ricci_flow_equation_current_api
      metric identifiesDerivative identifiesRicci)

/-- The standard stationary zero Ricci-flow data is now constructible. -/
noncomputable def three_manifold_model_standard_stationary_zero_ricci_flow_data_current_api :
    RicciFlowData ThreeManifoldModelWithCorners ω ThreeManifoldModel :=
  stationary_zero_ricci_flow_data_current_api
    three_manifold_model_standard_riemannian_metric
    (stationary_zero_metric_derivative_identification_current_api
      three_manifold_model_standard_riemannian_metric)
    three_manifold_model_standard_stationary_zero_ricci_identification_current_api

/--
The commutator right-hand side used by a concrete Riemann-curvature
construction for the derived stationary zero Ricci flow.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t
      (fun y : M => connectionAtTime t Z y (Y y)) x (X x) -
    connectionAtTime t
      (fun y : M => connectionAtTime t Z y (X y)) x (Y x) -
    connectionAtTime t Z x
      (VectorField.mlieBracket ThreeManifoldModelWithCorners X Y x)

/--
The first connection term in the curvature-construction commutator RHS for the
derived stationary zero Ricci flow.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t
    (fun y : M => connectionAtTime t Z y (Y y)) x (X x)

/--
The second connection term in the curvature-construction commutator RHS for
the derived stationary zero Ricci flow.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t
    (fun y : M => connectionAtTime t Z y (X y)) x (Y x)

/--
The Lie-bracket connection term in the curvature-construction commutator RHS
for the derived stationary zero Ricci flow.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t Z x
    (VectorField.mlieBracket ThreeManifoldModelWithCorners X Y x)

/--
The inner connection field `∇_Y Z` appearing in the first connection term of
the curvature-construction commutator RHS.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ)
    (Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    (y : M) → TangentSpace ThreeManifoldModelWithCorners y :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  fun y : M => connectionAtTime t Z y (Y y)

/--
The inner connection field `∇_X Z` appearing in the second connection term of
the curvature-construction commutator RHS.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ)
    (X Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    (y : M) → TangentSpace ThreeManifoldModelWithCorners y :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  fun y : M => connectionAtTime t Z y (X y)

/--
The selected time-indexed tangent connection field for the stationary-zero
curvature construction.
-/
noncomputable def stationary_zero_riemann_curvature_construction_connection_at_time_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    TimeDependentTangentConnectionField
      (metric_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime

/--
The selected pointwise connection term `∇_A B` for the stationary-zero
curvature construction.
-/
noncomputable def stationary_zero_riemann_curvature_construction_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (A B : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t B x (A x)

/--
The pointwise inner connection term `∇_Y Z` that underlies the field-level
zero equation in the torsion-normal representative frontier.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t Z x (Y x)

/--
The pointwise inner connection term `∇_X Z` that underlies the field-level
zero equation in the torsion-normal representative frontier.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t Z x (X x)

/--
The mixed connection term `∇_X Y` at the base point used to derive bracket
vanishing from the torsion-free identity.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t Y x (X x)

/--
The mixed connection term `∇_Y X` at the base point used to derive bracket
vanishing from the torsion-free identity.
-/
noncomputable def stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (t : ℝ) {x : M}
    (X Y : (y : M) → TangentSpace ThreeManifoldModelWithCorners y) :
    TangentSpace ThreeManifoldModelWithCorners x :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime t X x (Y x)

/--
A tangent vector field is smooth at the base point when its bundled tangent
section is manifold-differentiable there.
-/
abbrev StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y)
    (x : M) : Prop :=
  MDifferentiableAt
    ThreeManifoldModelWithCorners
    ThreeManifoldModelWithCorners.tangent
    (fun y : M =>
      (Xext y : TangentBundle ThreeManifoldModelWithCorners M)) x

/--
Chosen raw tangent-vector-field representative for a tangent vector at a base
point.

This is only the representative choice; the theorem that its value at the
base point is the prescribed tangent vector is stored separately.
-/
structure StationaryZeroTangentVectorFieldRawExtensionCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {x : M}
    (_X : TangentSpace ThreeManifoldModelWithCorners x) where
  Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y

/--
Raw representative-choice data for pointwise tangent vectors.
-/
structure StationaryZeroTangentVectorFieldRawExtensionDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  tangent_vector_field_raw_extension :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroTangentVectorFieldRawExtensionCurrentApi (M := M) X

/--
Basepoint value data for the selected raw representatives.
-/
structure StationaryZeroTangentVectorFieldValueAtPointDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (rawExtensionAtPoint :
      StationaryZeroTangentVectorFieldRawExtensionDataCurrentApi (M := M)) where
  tangent_vector_field_value_at_point :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      (rawExtensionAtPoint.tangent_vector_field_raw_extension X).Xext x = X

/--
Chosen tangent-vector-field representative with the prescribed value at a base
point.

This isolates the value-extension part of the previous smooth tangent-field
extension frontier from the separate smoothness-at-point requirement.
-/
structure StationaryZeroTangentVectorFieldValueExtensionCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {x : M}
    (X : TangentSpace ThreeManifoldModelWithCorners x) where
  Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y
  Xext_eq : Xext x = X

/--
Pointwise value-extension data for tangent vectors.
-/
structure StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  rawExtensionAtPoint :
    StationaryZeroTangentVectorFieldRawExtensionDataCurrentApi (M := M)
  valueAtPoint :
    StationaryZeroTangentVectorFieldValueAtPointDataCurrentApi
      rawExtensionAtPoint

/--
Selected raw representatives plus their basepoint value theorem recover the
previous value-extension object.
-/
def stationary_zero_tangent_vector_field_value_extension_of_raw_extension_and_value_at_point_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (rawExtensionAtPoint :
      StationaryZeroTangentVectorFieldRawExtensionDataCurrentApi (M := M))
    (valueAtPoint :
      StationaryZeroTangentVectorFieldValueAtPointDataCurrentApi
        rawExtensionAtPoint) :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroTangentVectorFieldValueExtensionCurrentApi (M := M) X := by
  intro x X
  exact
    { Xext := (rawExtensionAtPoint.tangent_vector_field_raw_extension X).Xext
      Xext_eq := valueAtPoint.tangent_vector_field_value_at_point X }

/--
The narrowed value-extension payload still exposes the previous selected
representative-with-value object.
-/
def stationary_zero_tangent_vector_field_value_extension_of_value_extension_data_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (valueExtensionAtPoint :
      StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi (M := M)) :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroTangentVectorFieldValueExtensionCurrentApi (M := M) X :=
  stationary_zero_tangent_vector_field_value_extension_of_raw_extension_and_value_at_point_current_api
    valueExtensionAtPoint.rawExtensionAtPoint
    valueExtensionAtPoint.valueAtPoint

/--
Smoothness data for the selected pointwise value representatives.
-/
structure StationaryZeroTangentVectorFieldExtensionSmoothnessDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (valueExtensionAtPoint :
      StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi (M := M)) where
  tangent_vector_field_extension_smoothAt :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
        (valueExtensionAtPoint.rawExtensionAtPoint.tangent_vector_field_raw_extension X).Xext x

/--
Pointwise smooth tangent-vector-field extension data for the stationary-zero
curvature route.

This now stores a selected value representative and the remaining theorem that
the selected representative is smooth at the base point.
-/
structure StationaryZeroTangentVectorFieldExtensionDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  valueExtensionAtPoint :
    StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi (M := M)
  smoothnessAtPoint :
    StationaryZeroTangentVectorFieldExtensionSmoothnessDataCurrentApi
      valueExtensionAtPoint

/--
Selected value-extension data plus smoothness data recover the previous
existential smooth tangent-vector-field extension witness.
-/
theorem stationary_zero_tangent_vector_field_extension_of_value_extension_and_smoothness_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (valueExtensionAtPoint :
      StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi (M := M))
    (smoothnessAtPoint :
      StationaryZeroTangentVectorFieldExtensionSmoothnessDataCurrentApi
        valueExtensionAtPoint) :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
        Xext x = X ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x := by
  intro x X
  let selected :=
    stationary_zero_tangent_vector_field_value_extension_of_value_extension_data_current_api
      valueExtensionAtPoint X
  exact
    ⟨selected.Xext, selected.Xext_eq,
      smoothnessAtPoint.tangent_vector_field_extension_smoothAt X⟩

/--
The narrowed tangent-vector-field extension payload still exposes its previous
existential extension witness.
-/
theorem stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (tangentVectorFieldExtensionAtTime :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M)) :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
        Xext x = X ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x :=
  stationary_zero_tangent_vector_field_extension_of_value_extension_and_smoothness_current_api
    tangentVectorFieldExtensionAtTime.valueExtensionAtPoint
    tangentVectorFieldExtensionAtTime.smoothnessAtPoint

/--
Classical choice turns an existential smooth extension witness into selected
raw representative data.
-/
noncomputable def stationary_zero_tangent_vector_field_raw_extension_data_of_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroTangentVectorFieldRawExtensionDataCurrentApi (M := M) where
  tangent_vector_field_raw_extension := by
    intro x X
    let witness := extensionExists X
    exact
      { Xext := Classical.choose witness
      }

/--
Classical choice preserves the value-at-point proof for the selected raw
representative.
-/
noncomputable def stationary_zero_tangent_vector_field_value_at_point_data_of_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroTangentVectorFieldValueAtPointDataCurrentApi
      (stationary_zero_tangent_vector_field_raw_extension_data_of_extension_exists_current_api
        extensionExists) where
  tangent_vector_field_value_at_point := by
    intro x X
    let witness := extensionExists X
    exact (Classical.choose_spec witness).1

/--
An existential smooth extension source supplies the narrowed value-extension
payload.
-/
noncomputable def stationary_zero_tangent_vector_field_value_extension_data_of_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroTangentVectorFieldValueExtensionDataCurrentApi (M := M) where
  rawExtensionAtPoint :=
    stationary_zero_tangent_vector_field_raw_extension_data_of_extension_exists_current_api
      extensionExists
  valueAtPoint :=
    stationary_zero_tangent_vector_field_value_at_point_data_of_extension_exists_current_api
      extensionExists

/--
Classical choice preserves the smoothness proof for the selected value
representative.
-/
noncomputable def stationary_zero_tangent_vector_field_extension_smoothness_data_of_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroTangentVectorFieldExtensionSmoothnessDataCurrentApi
      (stationary_zero_tangent_vector_field_value_extension_data_of_extension_exists_current_api
        extensionExists) where
  tangent_vector_field_extension_smoothAt := by
    intro x X
    let witness := extensionExists X
    exact (Classical.choose_spec witness).2

/--
An existential smooth extension source supplies the narrowed tangent-vector
field extension payload.
-/
noncomputable def stationary_zero_tangent_vector_field_extension_data_of_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M) where
  valueExtensionAtPoint :=
    stationary_zero_tangent_vector_field_value_extension_data_of_extension_exists_current_api
      extensionExists
  smoothnessAtPoint :=
    stationary_zero_tangent_vector_field_extension_smoothness_data_of_extension_exists_current_api
      extensionExists

/--
Connection-field time-independence data for the stationary-zero curvature
construction commutator.

This is the connection-level stationarity obligation below selected
connection-term time-independence: the chosen time-dependent tangent connection
field for the stationary flow is equal to its initial slice.
-/
structure StationaryZeroRiemannCurvatureConstructionConnectionAtTimeTimeIndependenceDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  connection_at_time_time_independent :
    ∀ t : ℝ,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime t =
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime 0

/--
The selected connection field for the stationary-zero construction is
time-independent under the current uniqueness API.
-/
theorem stationary_zero_riemann_curvature_construction_connection_at_time_time_independent_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    ∀ t : ℝ,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime t =
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime 0 := by
  intro t
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  let constantInitialConnectionAtTime :
      TimeDependentTangentConnectionField
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)) :=
    fun _ => connectionAtTime 0
  have hconstant :
      constantInitialConnectionAtTime = connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.eq_connectionAtTime
      constantInitialConnectionAtTime
  have ht : constantInitialConnectionAtTime t = connectionAtTime t :=
    congrFun hconstant t
  simpa [stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
    metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
    connectionAtTime, constantInitialConnectionAtTime] using ht.symm

/--
The connection-field time-independence payload is constructible from the
current uniqueness API.
-/
def stationary_zero_riemann_curvature_construction_connection_at_time_time_independence_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    StationaryZeroRiemannCurvatureConstructionConnectionAtTimeTimeIndependenceDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime :=
  { connection_at_time_time_independent :=
      stationary_zero_riemann_curvature_construction_connection_at_time_time_independent_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime }

/--
Selected connection-term time-independence data for the stationary-zero
curvature construction commutator.

This payload is now closed by the connection-field uniqueness API; it remains as
the public route marker for selected pointwise term time-independence.
-/
structure StationaryZeroRiemannCurvatureConstructionSelectedConnectionTermTimeIndependenceDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where

/--
Connection-field time-independence supplies selected connection-term
time-independence by applying the equal time-slice connections to `B` in
direction `A`.
-/
theorem stationary_zero_riemann_curvature_construction_selected_connection_term_time_independent_of_connection_at_time_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (connectionAtTimeTimeIndependenceAtTime :
      StationaryZeroRiemannCurvatureConstructionConnectionAtTimeTimeIndependenceDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ (A B : (y : M) → TangentSpace ThreeManifoldModelWithCorners y)
      (t : ℝ) (y : M),
      stationary_zero_riemann_curvature_construction_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := y) A B =
      stationary_zero_riemann_curvature_construction_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 (x := y) A B := by
  intro A B t y
  simpa [stationary_zero_riemann_curvature_construction_connection_term_current_api,
    stationary_zero_riemann_curvature_construction_connection_at_time_current_api] using
    congrArg (fun connectionAtTime => connectionAtTime B y (A y))
      (connectionAtTimeTimeIndependenceAtTime.connection_at_time_time_independent t)

/--
The narrowed selected connection-term time-independence payload still exposes
the previous selected-term equality.
-/
theorem stationary_zero_riemann_curvature_construction_selected_connection_term_time_independent_of_selected_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (_selectedConnectionTermTimeIndependenceAtTime :
      StationaryZeroRiemannCurvatureConstructionSelectedConnectionTermTimeIndependenceDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ (A B : (y : M) → TangentSpace ThreeManifoldModelWithCorners y)
      (t : ℝ) (y : M),
      stationary_zero_riemann_curvature_construction_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := y) A B =
      stationary_zero_riemann_curvature_construction_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 (x := y) A B :=
  stationary_zero_riemann_curvature_construction_selected_connection_term_time_independent_of_connection_at_time_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_connection_at_time_time_independence_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)

/--
Chosen smooth representatives for an ordered tangent-vector pair at a base
point.

This strips the commuting-pair normal-frame frontier down to the extension
part: the remaining connection and bracket identities are recorded separately
for these selected representatives.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {x : M}
    (X Y : TangentSpace ThreeManifoldModelWithCorners x) where
  Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y
  Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y
  Xext_eq : Xext x = X
  Yext_eq : Yext x = Y
  Xext_smoothAt : StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x
  Yext_smoothAt : StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x

/--
Initial-time representative-choice data for ordered tangent-vector pairs.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  initial_time_commuting_pair_representatives :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y

/--
The existing single-vector extension payload supplies selected representatives
for an ordered pair by applying it separately to `X` and `Y`.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (tangentVectorFieldExtensionAtTime :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
      (M := M) where
  initial_time_commuting_pair_representatives := by
    intro x X Y
    let Xdata :=
      stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
        tangentVectorFieldExtensionAtTime X
    let Ydata :=
      stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
        tangentVectorFieldExtensionAtTime Y
    exact
      { Xext := Classical.choose Xdata
        Yext := Classical.choose Ydata
        Xext_eq := (Classical.choose_spec Xdata).1
        Yext_eq := (Classical.choose_spec Ydata).1
        Xext_smoothAt := (Classical.choose_spec Xdata).2
        Yext_smoothAt := (Classical.choose_spec Ydata).2 }

/--
An existential smooth tangent-vector-field extension source supplies selected
ordered-pair representatives by first selecting the single-vector extension
data and then applying it to each member of the pair.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
      (M := M) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
    (stationary_zero_tangent_vector_field_extension_data_of_extension_exists_current_api
      extensionExists)

/--
For the representatives selected from an existential smooth extension source,
the first selected vector field still has the prescribed value at the base
point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_eq_of_tangent_vector_field_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      extensionExists).initial_time_commuting_pair_representatives X Y).Xext x = X :=
  ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
    extensionExists).initial_time_commuting_pair_representatives X Y).Xext_eq

/--
For the representatives selected from an existential smooth extension source,
the second selected vector field still has the prescribed value at the base
point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_eq_of_tangent_vector_field_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      extensionExists).initial_time_commuting_pair_representatives X Y).Yext x = Y :=
  ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
    extensionExists).initial_time_commuting_pair_representatives X Y).Yext_eq

/--
For the representatives selected from an existential smooth extension source,
the first selected vector field carries the expected smoothness evidence at
the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_smoothAt_of_tangent_vector_field_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
      ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        extensionExists).initial_time_commuting_pair_representatives X Y).Xext x :=
  ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
    extensionExists).initial_time_commuting_pair_representatives X Y).Xext_smoothAt

/--
For the representatives selected from an existential smooth extension source,
the second selected vector field carries the expected smoothness evidence at
the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_smoothAt_of_tangent_vector_field_extension_exists_current_api
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
      ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        extensionExists).initial_time_commuting_pair_representatives X Y).Yext x :=
  ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
    extensionExists).initial_time_commuting_pair_representatives X Y).Yext_smoothAt

/--
The remaining local normal-coordinate condition for a chosen commuting-pair
representative: the selected initial connection has zero `∇_X Y` term and the
base-point Lie bracket vanishes.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  stationary_zero_riemann_curvature_construction_connection_at_time_current_api
    metric identifiesDerivative identifiesRicci
    curvatureConstructionAtTime 0 pair.Yext x (pair.Xext x) = 0 ∧
  VectorField.mlieBracket ThreeManifoldModelWithCorners pair.Xext pair.Yext x = 0

/--
The initial connection-zero part of the commuting-pair normal-coordinate
condition.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  stationary_zero_riemann_curvature_construction_connection_at_time_current_api
    metric identifiesDerivative identifiesRicci
    curvatureConstructionAtTime 0 pair.Yext x (pair.Xext x) = 0

/--
The forward mixed connection term `∇_X Y` for the selected initial-time
commuting-pair representatives, stated directly in the commutator notation
used by the curvature construction.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
    metric identifiesDerivative identifiesRicci
    curvatureConstructionAtTime 0 (x := x) pair.Xext pair.Yext = 0

/--
The actual initial-time connection coefficient `∇_X Y` for the selected
commuting-pair representatives, unfolded to the connection field supplied by
the curvature-construction data.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime 0 pair.Yext x (pair.Xext x) = 0

/--
The base-vector form of the selected initial-time connection coefficient:
`∇_X Y = 0` at the base point, with the first argument already replaced by the
target tangent vector selected by the representative's value proof.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  connectionAtTime 0 pair.Yext x X = 0

/--
The selected representative's value theorem rewrites the actual forward
connection-coefficient expression to the base-vector coefficient expression.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) =
      connectionAtTime 0 pair.Yext x X := by
  simp [pair.Xext_eq]

/--
Zero of the base-vector coefficient transports back to zero of the selected
forward coefficient expression.  This is the pointwise zero transport supplied
by the selected representative's value theorem.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (baseVectorConnectionCoefficientZeroAtTime :
      let metricCompatibleConnectionAtTime :=
        curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
      let torsionFreeConnectionAtTime :=
        metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
      let connectionAtTime :=
        torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
      connectionAtTime 0 pair.Yext x X = 0) :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) = 0 :=
  (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair).trans
    baseVectorConnectionCoefficientZeroAtTime

/--
Zero of the selected forward connection-coefficient expression transports to
zero of the base-vector coefficient expression.  This is the reverse direction
of the selected representative's value-based coefficient rewrite.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_forward_connection_coefficient_expression_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (forwardConnectionCoefficientZeroAtTime :
      let metricCompatibleConnectionAtTime :=
        curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
      let torsionFreeConnectionAtTime :=
        metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
      let connectionAtTime :=
        torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
      connectionAtTime 0 pair.Yext x (pair.Xext x) = 0) :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = 0 :=
  (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair).symm.trans
    forwardConnectionCoefficientZeroAtTime

/--
For the representatives selected from an existential smooth extension source,
the forward connection coefficient can be evaluated using the requested base
vector `X` instead of the selected representative value `Xext x`.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_of_tangent_vector_field_extension_exists_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    let pair :=
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        extensionExists).initial_time_commuting_pair_representatives X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) =
      connectionAtTime 0 pair.Yext x X := by
  simpa using
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        extensionExists).initial_time_commuting_pair_representatives X Y)

/--
For representatives selected from an existential smooth extension source,
zero of the base-vector coefficient expression gives zero of the selected
forward coefficient expression.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_of_tangent_vector_field_extension_exists_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x)
    (baseVectorConnectionCoefficientZeroAtTime :
      let pair :=
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
          extensionExists).initial_time_commuting_pair_representatives X Y
      let metricCompatibleConnectionAtTime :=
        curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
      let torsionFreeConnectionAtTime :=
        metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
      let connectionAtTime :=
        torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
      connectionAtTime 0 pair.Yext x X = 0) :
    let pair :=
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        extensionExists).initial_time_commuting_pair_representatives X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      extensionExists).initial_time_commuting_pair_representatives X Y)
    baseVectorConnectionCoefficientZeroAtTime

/--
Normal-coordinate Christoffel-symbol data for the selected base-vector
coefficient `∇_X Y` at the initial time.

This separates the coefficient calculation from the actual local
normal-coordinate theorem: identify the selected connection coefficient with a
Christoffel symbol at the base point, then prove that symbol vanishes.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) where
  christoffelSymbolAtBase : TangentSpace ThreeManifoldModelWithCorners x
  connection_coefficient_eq_christoffel :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = christoffelSymbolAtBase
  christoffelSymbolAtBase_eq_zero : christoffelSymbolAtBase = 0

/--
Christoffel-formula data for the selected initial-time coefficient.  The
formula separates the selected connection coefficient from the metric
first-derivative combination that vanishes in normal coordinates.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) where
  christoffelSymbolAtBase : TangentSpace ThreeManifoldModelWithCorners x
  metricFirstDerivativeCombinationAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  connection_coefficient_eq_christoffel :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = christoffelSymbolAtBase
  christoffel_eq_metric_first_derivative_combination :
    christoffelSymbolAtBase = metricFirstDerivativeCombinationAtBase

/--
The first half of the selected Christoffel formula: identify the actual
initial-time connection coefficient with the selected Christoffel symbol in the
normal-coordinate chart.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) where
  christoffelSymbolAtBase : TangentSpace ThreeManifoldModelWithCorners x
  connection_coefficient_eq_christoffel :
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = christoffelSymbolAtBase

/--
Coefficient identification plus vanishing of the selected Christoffel symbol
recovers the pointwise normal-coordinate Christoffel-symbol vanishing payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_coefficient_identification_and_symbol_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (christoffelSymbolAtBase_eq_zero :
      coefficientIdentificationAtTime.christoffelSymbolAtBase = 0) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair where
  christoffelSymbolAtBase :=
    coefficientIdentificationAtTime.christoffelSymbolAtBase
  connection_coefficient_eq_christoffel :=
    coefficientIdentificationAtTime.connection_coefficient_eq_christoffel
  christoffelSymbolAtBase_eq_zero :=
    christoffelSymbolAtBase_eq_zero

/--
The second half of the selected Christoffel formula: express the selected
Christoffel symbol as the metric-first-derivative combination.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  metricFirstDerivativeCombinationAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  christoffel_eq_metric_first_derivative_combination :
    coefficientIdentificationAtTime.christoffelSymbolAtBase =
      metricFirstDerivativeCombinationAtBase

/--
The selected connection-coefficient identification and Christoffel metric formula
recover the previous Christoffel-formula payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_coefficient_identification_and_metric_derivative_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (metricDerivativeFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaCurrentApi
        coefficientIdentificationAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair where
  christoffelSymbolAtBase := coefficientIdentificationAtTime.christoffelSymbolAtBase
  metricFirstDerivativeCombinationAtBase :=
    metricDerivativeFormulaAtTime.metricFirstDerivativeCombinationAtBase
  connection_coefficient_eq_christoffel :=
    coefficientIdentificationAtTime.connection_coefficient_eq_christoffel
  christoffel_eq_metric_first_derivative_combination :=
    metricDerivativeFormulaAtTime.christoffel_eq_metric_first_derivative_combination

/--
Normal-coordinate metric-first-derivative vanishing for the formula source of
the selected Christoffel symbol.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  metric_first_derivative_combination_eq_zero :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase = 0

/--
The first normal-coordinate metric-derivative contribution is identified as a
summand of the metric-first-derivative combination in the selected Christoffel
formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermContributionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  firstMetricDerivativeTermAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  firstMetricDerivativeRemainderAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  metric_first_derivative_combination_eq_first_plus_remainder :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      firstMetricDerivativeTermAtBase + firstMetricDerivativeRemainderAtBase

/--
A concrete decomposition of the selected metric-first-derivative combination
into the first, second, and inverse-correction normal-coordinate terms.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  firstMetricDerivativeTermAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  secondMetricDerivativeTermAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  inverseMetricDerivativeCorrectionAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  metric_first_derivative_combination_eq_selected_terms :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      firstMetricDerivativeTermAtBase + secondMetricDerivativeTermAtBase -
        inverseMetricDerivativeCorrectionAtBase

/--
The three selected normal-coordinate terms in the metric-first-derivative
combination, separated from the proof that they give the formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  firstMetricDerivativeTermAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  secondMetricDerivativeTermAtBase :
    TangentSpace ThreeManifoldModelWithCorners x
  inverseMetricDerivativeCorrectionAtBase :
    TangentSpace ThreeManifoldModelWithCorners x

/--
The exact source-combination identity needed after the selected source fields
have been fixed.  This isolates the raw Christoffel metric-derivative
combination equality without carrying the broader decomposition route.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) where
  metric_first_derivative_combination_eq_source_combination :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
        selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
          selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The older selected-term decomposition determines the selected source fields, so
the downstream source is no longer arbitrary when it is built through this
constructor.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
      christoffelFormulaAtTime where
  firstMetricDerivativeTermAtBase :=
    selectedTermDecompositionAtTime.firstMetricDerivativeTermAtBase
  secondMetricDerivativeTermAtBase :=
    selectedTermDecompositionAtTime.secondMetricDerivativeTermAtBase
  inverseMetricDerivativeCorrectionAtBase :=
    selectedTermDecompositionAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The selected-term decomposition carries exactly the source-combination identity
for the source fields constructed from that decomposition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_combination_identity_of_selected_term_decomposition_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
        selectedTermDecompositionAtTime) where
  metric_first_derivative_combination_eq_source_combination := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api]
      using
        selectedTermDecompositionAtTime.metric_first_derivative_combination_eq_selected_terms

/--
The intermediate metric-first-derivative combination selected by the coordinate
formula before expanding it into the three source terms.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) where
  selectedMetricFirstDerivativeCombinationAtBase :
    TangentSpace ThreeManifoldModelWithCorners x

/--
Identification of the selected coordinate combination with the Christoffel
formula's metric-first-derivative combination.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    {selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime}
    (selectedTermCombinationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationCurrentApi
        selectedTermSourceAtTime) where
  metric_first_derivative_combination_eq_selected_combination :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      selectedTermCombinationAtTime.selectedMetricFirstDerivativeCombinationAtBase

/--
Expansion of the selected coordinate combination into the concrete selected
first, second, and inverse-correction source terms.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationExpansionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    {selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime}
    (selectedTermCombinationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationCurrentApi
        selectedTermSourceAtTime) where
  selected_combination_eq_selected_source_terms :
    selectedTermCombinationAtTime.selectedMetricFirstDerivativeCombinationAtBase =
      selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
        selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
          selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The canonical selected combination is the explicit first-plus-second-minus-
inverse source expression.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationCurrentApi
      selectedTermSourceAtTime where
  selectedMetricFirstDerivativeCombinationAtBase :=
    selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
      selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
        selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The canonical selected combination expands to the selected source terms by
definition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_expansion_of_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationExpansionCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
        selectedTermSourceAtTime) where
  selected_combination_eq_selected_source_terms := rfl

/--
For the canonical source-built selected combination, the selected-combination
identification is exactly the raw identity between the Christoffel
metric-derivative combination and the three selected source terms.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_identification_of_source_combination_identity_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (metricFirstDerivativeCombinationEqSourceCombinationAtTime :
      christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
        selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
          selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
            selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
        selectedTermSourceAtTime) where
  metric_first_derivative_combination_eq_selected_combination := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api]
      using metricFirstDerivativeCombinationEqSourceCombinationAtTime

/--
The exact source-combination identity payload recovers the canonical
selected-combination identification.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_identification_of_source_combination_identity_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (sourceCombinationIdentityAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
        selectedTermSourceAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_identification_of_source_combination_identity_current_api
    selectedTermSourceAtTime
    sourceCombinationIdentityAtTime.metric_first_derivative_combination_eq_source_combination

/--
The concrete formula asserting that the selected source terms decompose the
metric-first-derivative combination.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
{n : ℕ∞ω}
{M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
[IsManifold ThreeManifoldModelWithCorners 1 M]
[IsManifold ThreeManifoldModelWithCorners 2 M]
{metric :
  ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
    ThreeManifoldModel
    (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
{identifiesDerivative :
  IsMetricTimeDerivativeOf
    (stationary_time_dependent_riemannian_metric metric)
    (zero_metric_time_derivative_field
      (stationary_time_dependent_riemannian_metric metric))}
{identifiesRicci :
  IsRicciTensorOf
    (stationary_time_dependent_riemannian_metric metric)
    (zero_ricci_tensor_field
      (stationary_time_dependent_riemannian_metric metric))}
{curvatureConstructionAtTime :
  RiemannCurvatureTensorConstructionData
    (metric_of_ricci_flow_data
      (stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci))}
{x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
{pair :
  StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
    (M := M) X Y}
{christoffelFormulaAtTime :
  StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
(selectedTermSourceAtTime :
  StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
    christoffelFormulaAtTime) where
metric_first_derivative_combination_eq_selected_source_terms :
  christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
    selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
      selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
        selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The exact source-combination identity is the selected-term formula for the
already chosen selected source fields.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_source_combination_identity_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (sourceCombinationIdentityAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_selected_source_terms :=
    sourceCombinationIdentityAtTime.metric_first_derivative_combination_eq_source_combination

/--
The selected-term decomposition supplies the selected-term formula for the
source fields built from that same decomposition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_selected_term_decomposition_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
        selectedTermDecompositionAtTime) where
  metric_first_derivative_combination_eq_selected_source_terms := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api]
      using
        selectedTermDecompositionAtTime.metric_first_derivative_combination_eq_selected_terms

/--
The earlier selected-term formula payload is the exact source-combination
identity for the already chosen selected source fields.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_combination_identity_of_selected_term_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_source_combination :=
    selectedTermFormulaAtTime.metric_first_derivative_combination_eq_selected_source_terms

/--
The selected coordinate combination, its identification with the Christoffel
metric-first-derivative combination, and its expansion into source terms recover
the selected-term formula payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_combination_identification_and_expansion_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermCombinationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationCurrentApi
        selectedTermSourceAtTime)
    (selectedTermCombinationIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
        selectedTermCombinationAtTime)
    (selectedTermCombinationExpansionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationExpansionCurrentApi
        selectedTermCombinationAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_selected_source_terms := by
    rw [selectedTermCombinationIdentificationAtTime.metric_first_derivative_combination_eq_selected_combination]
    exact selectedTermCombinationExpansionAtTime.selected_combination_eq_selected_source_terms

/--
For the canonical selected source expression, the selected-term formula only
requires identifying the Christoffel metric-derivative combination with that
canonical expression.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_source_combination_identification_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermCombinationIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
          selectedTermSourceAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
      selectedTermSourceAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_combination_identification_and_expansion_current_api
    selectedTermSourceAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
      selectedTermSourceAtTime)
    selectedTermCombinationIdentificationAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_expansion_of_source_current_api
      selectedTermSourceAtTime)

/--
  Selected source terms plus their concrete formula recover the selected-term
  decomposition payload.
  -/
  def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_source_and_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
      christoffelFormulaAtTime where
  firstMetricDerivativeTermAtBase :=
    selectedTermSourceAtTime.firstMetricDerivativeTermAtBase
  secondMetricDerivativeTermAtBase :=
    selectedTermSourceAtTime.secondMetricDerivativeTermAtBase
  inverseMetricDerivativeCorrectionAtBase :=
    selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase
  metric_first_derivative_combination_eq_selected_terms :=
      selectedTermFormulaAtTime.metric_first_derivative_combination_eq_selected_source_terms

/--
Algebraic selected source terms obtained directly from the Christoffel
metric-first-derivative combination.  This is not a normal-coordinate vanishing
theorem; it fixes a concrete upstream source so the selected-term decomposition
is no longer an arbitrary three-field payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
      christoffelFormulaAtTime where
  firstMetricDerivativeTermAtBase :=
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase
  secondMetricDerivativeTermAtBase := 0
  inverseMetricDerivativeCorrectionAtBase := 0

/--
The algebraic selected source carries its source-combination identity by
definition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_combination_identity_of_algebraic_selected_term_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api
        christoffelFormulaAtTime) where
  metric_first_derivative_combination_eq_source_combination := by
    simp [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api]

/--
The algebraic selected source supplies the selected-term formula without an
additional formula payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_algebraic_selected_term_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api
        christoffelFormulaAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_source_combination_identity_data_current_api
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api
      christoffelFormulaAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_combination_identity_of_algebraic_selected_term_source_current_api
      christoffelFormulaAtTime)

/--
The Christoffel formula data alone supplies an algebraic selected-term
decomposition of its metric-first-derivative combination.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_algebraic_selected_term_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
      christoffelFormulaAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_source_and_formula_current_api
    christoffelFormulaAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api
      christoffelFormulaAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_algebraic_selected_term_source_current_api
      christoffelFormulaAtTime)

  /--
  The selected-term decomposition recovers the first contribution with the
  remainder identified as the selected second term minus the inverse correction.
  -/
  noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_contribution_of_selected_term_decomposition_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermContributionCurrentApi
      christoffelFormulaAtTime where
    firstMetricDerivativeTermAtBase :=
      selectedTermDecompositionAtTime.firstMetricDerivativeTermAtBase
    firstMetricDerivativeRemainderAtBase :=
      selectedTermDecompositionAtTime.secondMetricDerivativeTermAtBase -
        selectedTermDecompositionAtTime.inverseMetricDerivativeCorrectionAtBase
    metric_first_derivative_combination_eq_first_plus_remainder := by
      rw [selectedTermDecompositionAtTime.metric_first_derivative_combination_eq_selected_terms]
      simp [sub_eq_add_neg, add_assoc]

/--
Selection of the first normal-coordinate metric-derivative term that appears in
the selected Christoffel formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermSelectionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  firstMetricDerivativeTermAtBase : TangentSpace ThreeManifoldModelWithCorners x

/--
A first metric-derivative contribution recovers the first component selection.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_selection_of_contribution_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (firstContributionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermContributionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime where
  firstMetricDerivativeTermAtBase :=
    firstContributionAtTime.firstMetricDerivativeTermAtBase

/--
Selection of the second normal-coordinate metric-derivative term that appears in
the selected Christoffel formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermSelectionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
    secondMetricDerivativeTermAtBase : TangentSpace ThreeManifoldModelWithCorners x

  /--
  The selected-term decomposition recovers the second component selection.
  -/
  def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_selection_of_selected_term_decomposition_current_api
      {n : ℕ∞ω}
      {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
      [IsManifold ThreeManifoldModelWithCorners 1 M]
      [IsManifold ThreeManifoldModelWithCorners 2 M]
      {metric :
        ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel
          (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
      {identifiesDerivative :
        IsMetricTimeDerivativeOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_metric_time_derivative_field
            (stationary_time_dependent_riemannian_metric metric))}
      {identifiesRicci :
        IsRicciTensorOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric))}
      {curvatureConstructionAtTime :
        RiemannCurvatureTensorConstructionData
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))}
      {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
      {pair :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
          (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
      (selectedTermDecompositionAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
          christoffelFormulaAtTime) :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime where
    secondMetricDerivativeTermAtBase :=
      selectedTermDecompositionAtTime.secondMetricDerivativeTermAtBase

  /--
  Selection of the inverse-metric correction term that appears in the selected
  Christoffel formula.
  -/
  structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionSelectionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
    inverseMetricDerivativeCorrectionAtBase :
      TangentSpace ThreeManifoldModelWithCorners x

  /--
  The selected-term decomposition recovers the inverse-correction component
  selection.
  -/
  def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_selection_of_selected_term_decomposition_current_api
      {n : ℕ∞ω}
      {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
      [IsManifold ThreeManifoldModelWithCorners 1 M]
      [IsManifold ThreeManifoldModelWithCorners 2 M]
      {metric :
        ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel
          (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
      {identifiesDerivative :
        IsMetricTimeDerivativeOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_metric_time_derivative_field
            (stationary_time_dependent_riemannian_metric metric))}
      {identifiesRicci :
        IsRicciTensorOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric))}
      {curvatureConstructionAtTime :
        RiemannCurvatureTensorConstructionData
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))}
      {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
      {pair :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
          (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
      (selectedTermDecompositionAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
          christoffelFormulaAtTime) :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionSelectionCurrentApi
        christoffelFormulaAtTime where
    inverseMetricDerivativeCorrectionAtBase :=
      selectedTermDecompositionAtTime.inverseMetricDerivativeCorrectionAtBase

  /--
  Selection of the three normal-coordinate metric-derivative terms that appear in
  the selected Christoffel formula.
  -/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  firstMetricDerivativeTermSelectionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime
  secondMetricDerivativeTermSelectionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime
  inverseMetricDerivativeCorrectionSelectionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionSelectionCurrentApi
      christoffelFormulaAtTime

/--
The three individual metric-derivative term selections recover the combined
term-selection payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (firstSelectionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime)
    (secondSelectionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime)
    (inverseCorrectionSelectionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionSelectionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime where
    firstMetricDerivativeTermSelectionAtTime := firstSelectionAtTime
    secondMetricDerivativeTermSelectionAtTime := secondSelectionAtTime
    inverseMetricDerivativeCorrectionSelectionAtTime :=
      inverseCorrectionSelectionAtTime

  /--
  The selected-term decomposition recovers the combined component-selection
  payload.
  -/
  noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api
      {n : ℕ∞ω}
      {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
      [IsManifold ThreeManifoldModelWithCorners 1 M]
      [IsManifold ThreeManifoldModelWithCorners 2 M]
      {metric :
        ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel
          (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
      {identifiesDerivative :
        IsMetricTimeDerivativeOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_metric_time_derivative_field
            (stationary_time_dependent_riemannian_metric metric))}
      {identifiesRicci :
        IsRicciTensorOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric))}
      {curvatureConstructionAtTime :
        RiemannCurvatureTensorConstructionData
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))}
      {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
      {pair :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
          (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
      (selectedTermDecompositionAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
          christoffelFormulaAtTime) :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api
      christoffelFormulaAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_selection_of_contribution_current_api
        christoffelFormulaAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_contribution_of_selected_term_decomposition_current_api
          christoffelFormulaAtTime selectedTermDecompositionAtTime))
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_selection_of_selected_term_decomposition_current_api
        christoffelFormulaAtTime selectedTermDecompositionAtTime)
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_selection_of_selected_term_decomposition_current_api
        christoffelFormulaAtTime selectedTermDecompositionAtTime)

  /--
  Formula expanding the selected metric-first-derivative combination into the
  three selected normal-coordinate derivative terms.
  -/
  structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (termSelectionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime) where
  metric_first_derivative_combination_eq_terms :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      termSelectionAtTime.firstMetricDerivativeTermSelectionAtTime.firstMetricDerivativeTermAtBase +
        termSelectionAtTime.secondMetricDerivativeTermSelectionAtTime.secondMetricDerivativeTermAtBase -
          termSelectionAtTime.inverseMetricDerivativeCorrectionSelectionAtTime.inverseMetricDerivativeCorrectionAtBase

/--
The selected source terms determine the corresponding component-selection
payload for the metric-first-derivative expansion formula.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime where
  firstMetricDerivativeTermSelectionAtTime := {
    firstMetricDerivativeTermAtBase :=
      selectedTermSourceAtTime.firstMetricDerivativeTermAtBase }
  secondMetricDerivativeTermSelectionAtTime := {
    secondMetricDerivativeTermAtBase :=
      selectedTermSourceAtTime.secondMetricDerivativeTermAtBase }
  inverseMetricDerivativeCorrectionSelectionAtTime := {
    inverseMetricDerivativeCorrectionAtBase :=
      selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase }

/--
Source-specific formula for the selected metric-first-derivative expansion.
This is the remaining equality after the source-built term selection has fixed
the three component fields.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime) where
  metric_first_derivative_combination_eq_source_terms :
    christoffelFormulaAtTime.metricFirstDerivativeCombinationAtBase =
      selectedTermSourceAtTime.firstMetricDerivativeTermAtBase +
        selectedTermSourceAtTime.secondMetricDerivativeTermAtBase -
          selectedTermSourceAtTime.inverseMetricDerivativeCorrectionAtBase

/--
For the canonical selected source combination, the source-term expansion formula
only requires identifying the Christoffel metric-derivative combination with
that canonical source combination.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_source_combination_identification_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermCombinationIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
          selectedTermSourceAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_source_terms := by
    rw [selectedTermCombinationIdentificationAtTime.metric_first_derivative_combination_eq_selected_combination]
    exact
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_expansion_of_source_current_api
        selectedTermSourceAtTime).selected_combination_eq_selected_source_terms

/--
The source-combination identity payload directly supplies the source-term
expansion formula.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_source_combination_identity_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (sourceCombinationIdentityAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceCombinationIdentityCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_source_terms :=
    sourceCombinationIdentityAtTime.metric_first_derivative_combination_eq_source_combination

/--
The earlier selected-term formula payload directly supplies the source-term
expansion formula.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_selected_term_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
      selectedTermSourceAtTime where
  metric_first_derivative_combination_eq_source_terms :=
    selectedTermFormulaAtTime.metric_first_derivative_combination_eq_selected_source_terms

/--
The selected-term decomposition supplies the source-term expansion formula for
the source fields built from that decomposition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_selected_term_decomposition_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
        selectedTermDecompositionAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_selected_term_formula_current_api
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
      selectedTermDecompositionAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_selected_term_decomposition_source_current_api
      selectedTermDecompositionAtTime)

/--
The source-specific expansion equality recovers the generic term-expansion
formula for the source-built term selection.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_source_term_expansion_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (sourceTermExpansionFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSourceTermExpansionFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
        selectedTermSourceAtTime) where
  metric_first_derivative_combination_eq_terms := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api]
      using
        sourceTermExpansionFormulaAtTime.metric_first_derivative_combination_eq_source_terms

/--
The selected-term formula feeds directly into the source-built term-expansion
formula.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
        selectedTermSourceAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_source_term_expansion_formula_current_api
    selectedTermSourceAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_source_term_expansion_formula_of_selected_term_formula_current_api
      selectedTermSourceAtTime selectedTermFormulaAtTime)

/--
The selected-term decomposition feeds the source-built term-expansion formula
through the source fields it determines.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_decomposition_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
          selectedTermDecompositionAtTime)) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_formula_current_api
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
      selectedTermDecompositionAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_selected_term_decomposition_source_current_api
      selectedTermDecompositionAtTime)

/--
The metric-first-derivative expansion formula for the source-built term
selection identifies the Christoffel combination with the canonical selected
source combination.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_identification_of_source_term_expansion_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (termExpansionFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
          selectedTermSourceAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermCombinationIdentificationCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api
        selectedTermSourceAtTime) where
  metric_first_derivative_combination_eq_selected_combination := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_combination_of_source_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api]
      using termExpansionFormulaAtTime.metric_first_derivative_combination_eq_terms

/--
Expansion of the selected metric-first-derivative combination into the three
normal-coordinate derivative terms that appear in the Christoffel formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  termSelectionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
      christoffelFormulaAtTime
  termExpansionFormulaAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
      termSelectionAtTime

/--
The selected three metric-derivative terms plus their expansion formula recover
the previous term-expansion payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selection_and_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (termSelectionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermSelectionCurrentApi
        christoffelFormulaAtTime)
    (termExpansionFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
        termSelectionAtTime) :
  StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
    christoffelFormulaAtTime where
    termSelectionAtTime := termSelectionAtTime
    termExpansionFormulaAtTime := termExpansionFormulaAtTime

/--
The selected-term formula feeds directly into the source-built term-expansion
payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermSourceAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermSourceCurrentApi
        christoffelFormulaAtTime)
    (selectedTermFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermFormulaCurrentApi
        selectedTermSourceAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
      christoffelFormulaAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selection_and_formula_current_api
    christoffelFormulaAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_source_current_api
      selectedTermSourceAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_formula_current_api
      selectedTermSourceAtTime selectedTermFormulaAtTime)

/--
The selected-term decomposition feeds directly into the source-built
term-expansion payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_source_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (selectedTermDecompositionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
      christoffelFormulaAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_formula_current_api
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_source_of_selected_term_decomposition_current_api
      selectedTermDecompositionAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_formula_of_selected_term_decomposition_source_current_api
      selectedTermDecompositionAtTime)

  /--
  The selected-term decomposition supplies the expansion formula for the combined
  selection rebuilt from those terms.
  -/
  def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_decomposition_current_api
      {n : ℕ∞ω}
      {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
      [IsManifold ThreeManifoldModelWithCorners 1 M]
      [IsManifold ThreeManifoldModelWithCorners 2 M]
      {metric :
        ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel
          (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
      {identifiesDerivative :
        IsMetricTimeDerivativeOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_metric_time_derivative_field
            (stationary_time_dependent_riemannian_metric metric))}
      {identifiesRicci :
        IsRicciTensorOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric))}
      {curvatureConstructionAtTime :
        RiemannCurvatureTensorConstructionData
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))}
      {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
      {pair :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
          (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
      (selectedTermDecompositionAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
          christoffelFormulaAtTime) :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionFormulaCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api
          christoffelFormulaAtTime selectedTermDecompositionAtTime) where
    metric_first_derivative_combination_eq_terms := by
      simpa [
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api,
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api,
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_selection_of_contribution_current_api,
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_contribution_of_selected_term_decomposition_current_api,
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_selection_of_selected_term_decomposition_current_api,
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_selection_of_selected_term_decomposition_current_api]
        using
          selectedTermDecompositionAtTime.metric_first_derivative_combination_eq_selected_terms

  /--
  The selected-term decomposition recovers the current metric-first-derivative
  term-expansion payload.
  -/
  noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_current_api
      {n : ℕ∞ω}
      {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
      [IsManifold ThreeManifoldModelWithCorners 1 M]
      [IsManifold ThreeManifoldModelWithCorners 2 M]
      {metric :
        ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
          ThreeManifoldModel
          (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
      {identifiesDerivative :
        IsMetricTimeDerivativeOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_metric_time_derivative_field
            (stationary_time_dependent_riemannian_metric metric))}
      {identifiesRicci :
        IsRicciTensorOf
          (stationary_time_dependent_riemannian_metric metric)
          (zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric))}
      {curvatureConstructionAtTime :
        RiemannCurvatureTensorConstructionData
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))}
      {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
      {pair :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
          (M := M) X Y}
      (christoffelFormulaAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
      (selectedTermDecompositionAtTime :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeSelectedTermDecompositionCurrentApi
          christoffelFormulaAtTime) :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
        christoffelFormulaAtTime where
    termSelectionAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api
        christoffelFormulaAtTime selectedTermDecompositionAtTime
    termExpansionFormulaAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_formula_of_selected_term_decomposition_current_api
        christoffelFormulaAtTime selectedTermDecompositionAtTime

  /--
  The first selected normal-coordinate metric-derivative term vanishes at the base
  point.
  -/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (termExpansionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
        christoffelFormulaAtTime) where
  first_metric_derivative_term_eq_zero :
    termExpansionAtTime.termSelectionAtTime.firstMetricDerivativeTermSelectionAtTime.firstMetricDerivativeTermAtBase = 0

/--
The second selected normal-coordinate metric-derivative term vanishes at the base
point.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (termExpansionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
        christoffelFormulaAtTime) where
  second_metric_derivative_term_eq_zero :
    termExpansionAtTime.termSelectionAtTime.secondMetricDerivativeTermSelectionAtTime.secondMetricDerivativeTermAtBase = 0

/--
The inverse-metric correction term in the selected Christoffel formula vanishes
at the base point.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (termExpansionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
        christoffelFormulaAtTime) where
  inverse_metric_derivative_correction_eq_zero :
    termExpansionAtTime.termSelectionAtTime.inverseMetricDerivativeCorrectionSelectionAtTime.inverseMetricDerivativeCorrectionAtBase = 0

/--
Termwise normal-coordinate vanishing for the metric-first-derivative combination
appearing in the selected Christoffel formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) where
  termExpansionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
      christoffelFormulaAtTime
  firstMetricDerivativeTermVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermVanishingCurrentApi
      termExpansionAtTime
  secondMetricDerivativeTermVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermVanishingCurrentApi
      termExpansionAtTime
  inverseMetricDerivativeCorrectionVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionVanishingCurrentApi
      termExpansionAtTime

/--
The algebraic selected-term decomposition determines the corresponding
metric-first-derivative term expansion.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
      christoffelFormulaAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_current_api
    christoffelFormulaAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_algebraic_selected_term_source_current_api
      christoffelFormulaAtTime)

/--
For the algebraic expansion, the first selected term is exactly the
Christoffel metric-first-derivative combination, so its vanishing is supplied by
the existing metric-first-derivative vanishing payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_vanishing_of_metric_first_derivative_vanishing_algebraic_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    {christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair}
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermVanishingCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api
        christoffelFormulaAtTime) where
  first_metric_derivative_term_eq_zero := by
    simpa [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_selection_of_contribution_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_contribution_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_algebraic_selected_term_source_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_source_and_formula_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api]
      using
        metricFirstDerivativeVanishingAtTime.metric_first_derivative_combination_eq_zero

/--
For the algebraic expansion, the second selected term vanishes by definition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_vanishing_of_algebraic_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermVanishingCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api
        christoffelFormulaAtTime) where
  second_metric_derivative_term_eq_zero := by
    simp [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_selection_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_algebraic_selected_term_source_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_source_and_formula_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api]

/--
For the algebraic expansion, the inverse-correction term vanishes by definition.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_vanishing_of_algebraic_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionVanishingCurrentApi
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api
        christoffelFormulaAtTime) where
  inverse_metric_derivative_correction_eq_zero := by
    simp [
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_expansion_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_selection_of_component_selections_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_selection_of_selected_term_decomposition_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_algebraic_selected_term_source_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_selected_term_decomposition_of_source_and_formula_current_api,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_selected_term_source_current_api]

/--
For the algebraic expansion, metric-first-derivative combination vanishing is
equivalent to termwise vanishing: the first term is the combination and the
other two terms are definitionally zero.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_vanishing_of_metric_first_derivative_vanishing_algebraic_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingCurrentApi
      christoffelFormulaAtTime where
  termExpansionAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_algebraic_term_expansion_current_api
      christoffelFormulaAtTime
  firstMetricDerivativeTermVanishingAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_first_metric_derivative_term_vanishing_of_metric_first_derivative_vanishing_algebraic_current_api
      metricFirstDerivativeVanishingAtTime
  secondMetricDerivativeTermVanishingAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_second_metric_derivative_term_vanishing_of_algebraic_current_api
      christoffelFormulaAtTime
  inverseMetricDerivativeCorrectionVanishingAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_inverse_metric_derivative_correction_vanishing_of_algebraic_current_api
      christoffelFormulaAtTime

/--
The metric-first-derivative term expansion plus vanishing of its three selected
components recovers the previous termwise vanishing payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_vanishing_of_expansion_and_component_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (termExpansionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermExpansionCurrentApi
        christoffelFormulaAtTime)
    (firstTermVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateFirstMetricDerivativeTermVanishingCurrentApi
        termExpansionAtTime)
    (secondTermVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateSecondMetricDerivativeTermVanishingCurrentApi
        termExpansionAtTime)
    (inverseCorrectionVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateInverseMetricDerivativeCorrectionVanishingCurrentApi
        termExpansionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingCurrentApi
      christoffelFormulaAtTime where
  termExpansionAtTime := termExpansionAtTime
  firstMetricDerivativeTermVanishingAtTime := firstTermVanishingAtTime
  secondMetricDerivativeTermVanishingAtTime := secondTermVanishingAtTime
  inverseMetricDerivativeCorrectionVanishingAtTime := inverseCorrectionVanishingAtTime

/--
Termwise normal-coordinate metric derivative vanishing recovers vanishing of the
selected metric-first-derivative combination.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_term_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    {metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x)}
    {identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric))}
    {identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))}
    {curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))}
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (metricFirstDerivativeTermVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
      christoffelFormulaAtTime where
  metric_first_derivative_combination_eq_zero := by
    rw [metricFirstDerivativeTermVanishingAtTime.termExpansionAtTime.termExpansionFormulaAtTime.metric_first_derivative_combination_eq_terms]
    rw [metricFirstDerivativeTermVanishingAtTime.firstMetricDerivativeTermVanishingAtTime.first_metric_derivative_term_eq_zero]
    rw [metricFirstDerivativeTermVanishingAtTime.secondMetricDerivativeTermVanishingAtTime.second_metric_derivative_term_eq_zero]
    rw [metricFirstDerivativeTermVanishingAtTime.inverseMetricDerivativeCorrectionVanishingAtTime.inverse_metric_derivative_correction_eq_zero]
    simp

/--
The Christoffel formula plus pointwise normal-coordinate Christoffel-symbol
vanishing recovers vanishing of the selected metric-first-derivative
combination.  This is the reverse direction of the formula-to-symbol bridge and
moves the remaining metric-derivative obligation to the upstream
normal-coordinate Christoffel vanishing fact.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_christoffel_formula_and_christoffel_symbol_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (christoffelSymbolVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
      christoffelFormulaAtTime where
  metric_first_derivative_combination_eq_zero := by
    have connection_eq_zero :
        let metricCompatibleConnectionAtTime :=
          curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
        let torsionFreeConnectionAtTime :=
          metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
        let connectionAtTime :=
          torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
        connectionAtTime 0 pair.Yext x X = 0 := by
      exact
        christoffelSymbolVanishingAtTime.connection_coefficient_eq_christoffel.trans
          christoffelSymbolVanishingAtTime.christoffelSymbolAtBase_eq_zero
    have christoffel_eq_zero :
        christoffelFormulaAtTime.christoffelSymbolAtBase = 0 := by
      exact
        christoffelFormulaAtTime.connection_coefficient_eq_christoffel.symm.trans
          connection_eq_zero
    exact
      christoffelFormulaAtTime.christoffel_eq_metric_first_derivative_combination.symm.trans
        christoffel_eq_zero

/--
The Christoffel formula plus normal-coordinate metric-first-derivative
vanishing recovers the selected Christoffel-symbol vanishing payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_christoffel_formula_and_metric_first_derivative_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
        christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair where
  christoffelSymbolAtBase := christoffelFormulaAtTime.christoffelSymbolAtBase
  connection_coefficient_eq_christoffel :=
    christoffelFormulaAtTime.connection_coefficient_eq_christoffel
  christoffelSymbolAtBase_eq_zero := by
    rw [christoffelFormulaAtTime.christoffel_eq_metric_first_derivative_combination]
    exact metricFirstDerivativeVanishingAtTime.metric_first_derivative_combination_eq_zero

/--
Normal-coordinate Christoffel-symbol data gives the base-vector connection
coefficient vanishing.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_normal_coordinate_christoffel_symbol_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y)
    (christoffelSymbolVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair := by
  rw [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi]
  rw [christoffelSymbolVanishingAtTime.connection_coefficient_eq_christoffel]
  exact christoffelSymbolVanishingAtTime.christoffelSymbolAtBase_eq_zero

/--
The base-point Lie-bracket-zero part of the commuting-pair normal-coordinate
condition.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  VectorField.mlieBracket ThreeManifoldModelWithCorners pair.Xext pair.Yext x = 0

/--
The reverse mixed connection-zero part used to recover the commuting-pair
bracket-zero identity from torsion-freeness.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) : Prop :=
  stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
    metric identifiesDerivative identifiesRicci
    curvatureConstructionAtTime 0 (x := x) pair.Xext pair.Yext = 0

/--
Connection-coefficient identification data for the selected initial-time
commuting-pair representatives.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
The current coefficient-identification API only requires a symbol together with
an equality to the selected connection coefficient.  Taking that symbol to be
the selected connection coefficient itself supplies the identification field;
the genuinely geometric content remains in the metric-derivative formula.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_of_connection_coefficient_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    (pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair where
  christoffelSymbolAtBase :=
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X
  connection_coefficient_eq_christoffel := rfl

/--
Selected pair representatives supply coefficient-identification data by taking
each selected Christoffel symbol to be its represented connection coefficient.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification := by
    intro x X Y
    exact
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_of_connection_coefficient_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
Normal-coordinate vanishing of the selected Christoffel symbols, after the
coefficient-identification family has fixed which symbol represents each
initial-time connection coefficient.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_zero :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      (coefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
        X Y).christoffelSymbolAtBase = 0

/--
The selected representative's value equation turns the actual forward
connection coefficient `∇_(Xext x) Yext` into the base-vector coefficient
`∇_X Yext`.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_connection_coefficient_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (forwardConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair := by
  simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi,
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
    pair.Xext_eq] using forwardConnectionCoefficientZeroAtTime

/--
Direct forward connection-coefficient vanishing for the selected initial-time
representatives.  This keeps the remaining local connection obligation before
the base-vector replacement, at the coefficient actually supplied by the
chosen smooth representative.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initial_time_commuting_pair_forward_connection_coefficients_zero :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
Forward connection-coefficient normal representatives for ordered tangent pairs.

This is the upstream local normal-coordinate source for the direct
coefficient-zero payload: instead of asking arbitrary selected smooth
extensions to satisfy `∇_(Xext x) Yext = 0`, it asks for smooth representatives
chosen with that initial connection coefficient already zero.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initial_time_commuting_pair_forward_connection_coefficient_normal_representatives :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0

/--
The normal-representative source canonically selects the ordered pair
representatives used by the direct coefficient-zero payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
      (M := M) where
  initial_time_commuting_pair_representatives := by
    intro x X Y
    let Xwitness :=
      forwardConnectionCoefficientNormalRepresentativeAtTime.initial_time_commuting_pair_forward_connection_coefficient_normal_representatives
        X Y
    let Xext := Classical.choose Xwitness
    let Ywitness := Classical.choose_spec Xwitness
    let Yext := Classical.choose Ywitness
    let h := Classical.choose_spec Ywitness
    exact
      { Xext := Xext
        Yext := Yext
        Xext_eq := h.1
        Yext_eq := h.2.1
        Xext_smoothAt := h.2.2.1
        Yext_smoothAt := h.2.2.2.1 }

/--
Forward connection-coefficient normal representatives supply direct
coefficient-zero data for the representatives chosen from the same source.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) where
  initial_time_commuting_pair_forward_connection_coefficients_zero := by
    intro x X Y
    let normal :=
      forwardConnectionCoefficientNormalRepresentativeAtTime.initial_time_commuting_pair_forward_connection_coefficient_normal_representatives
        X Y
    let h :=
      Classical.choose_spec
        (Classical.choose_spec normal)
    have hconnection := h.2.2.2.2
    change
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        { Xext := Classical.choose normal
          Yext := Classical.choose (Classical.choose_spec normal)
          Xext_eq := h.1
          Yext_eq := h.2.1
          Xext_smoothAt := h.2.2.1
          Yext_smoothAt := h.2.2.2.1 }
    simpa [
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
    ] using hconnection

/--
Selected smooth pair representatives plus direct forward connection-coefficient
zero data recover the forward coefficient normal-representative source.  This
keeps the remaining source below the existential normal-representative payload:
choose the representatives, then prove the single selected coefficient
`∇_(Xext x) Yext` vanishes.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_forward_connection_coefficient_direct_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime where
  initial_time_commuting_pair_forward_connection_coefficient_normal_representatives := by
    intro x X Y
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    have hconnection :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
      forwardConnectionCoefficientDirectZeroAtTime.initial_time_commuting_pair_forward_connection_coefficients_zero
        X Y
    exact
      ⟨pair.Xext, pair.Yext, pair.Xext_eq, pair.Yext_eq,
        pair.Xext_smoothAt, pair.Yext_smoothAt, by
          simpa [
            StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
            pair
          ] using hconnection⟩

/--
Direct base-vector connection-coefficient vanishing for the selected
initial-time representatives.  This is the local connection fact which, once
coefficient identification has selected a Christoffel symbol for the
coefficient, implies the selected Christoffel symbol is zero.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
Direct forward connection-coefficient zero data supplies the base-vector direct
zero family by replacing `Xext x` with the selected base vector `X`.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_direct_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero := by
    intro x X Y
    exact
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_connection_coefficient_zero_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (forwardConnectionCoefficientDirectZeroAtTime.initial_time_commuting_pair_forward_connection_coefficients_zero
          X Y)

/--
Raw base-vector connection-coefficient zero data recovers the direct selected
coefficient-zero payload by replacing the base vector with the chosen
representative's value at the base point.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_base_vector_connection_coefficient_direct_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initial_time_commuting_pair_forward_connection_coefficients_zero := by
    intro x X Y
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    have hbase :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
      forwardBaseVectorConnectionCoefficientDirectZeroAtTime.initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero
        X Y
    simpa [
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi,
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
      pair, pair.Xext_eq
    ] using hbase

/--
Selected smooth pair representatives plus raw base-vector coefficient-zero data
recover the forward coefficient normal-representative source.  This keeps the
remaining coefficient theorem at the base-vector connection term before the
`Xext x = X` substitution.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_forward_base_vector_connection_coefficient_direct_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_forward_connection_coefficient_direct_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_base_vector_connection_coefficient_direct_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      forwardBaseVectorConnectionCoefficientDirectZeroAtTime)

/--
An existential smooth tangent-vector-field extension source supplies the
representatives needed by the base-vector coefficient route.  The remaining
normal-representative input is therefore only the base-vector coefficient-zero
data for those selected representatives.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_tangent_vector_field_extension_exists_and_forward_base_vector_connection_coefficient_direct_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (extensionExists :
      ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
        ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Xext x = X ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
    (forwardBaseVectorConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
          extensionExists)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_forward_base_vector_connection_coefficient_direct_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      extensionExists)
    forwardBaseVectorConnectionCoefficientDirectZeroAtTime

/--
Base-vector connection-coefficient vanishing proves vanishing of the selected
Christoffel symbol fixed by coefficient identification.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_zero_of_coefficient_identification_and_base_vector_connection_coefficient_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {X Y : TangentSpace ThreeManifoldModelWithCorners x}
    {pair :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeCurrentApi
        (M := M) X Y}
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair)
    (baseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair) :
    coefficientIdentificationAtTime.christoffelSymbolAtBase = 0 := by
  exact
    coefficientIdentificationAtTime.connection_coefficient_eq_christoffel.symm.trans
      baseVectorConnectionCoefficientZeroAtTime

/--
Direct base-vector connection-coefficient vanishing data supplies the selected
Christoffel-symbol zero family once coefficient identification fixes the
symbol representing each connection coefficient.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_zero_data_of_base_vector_connection_coefficient_direct_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (baseVectorConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime coefficientIdentificationAtTime where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_zero := by
    intro x X Y
    exact
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_zero_of_coefficient_identification_and_base_vector_connection_coefficient_zero_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (coefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
          X Y)
        (baseVectorConnectionCoefficientDirectZeroAtTime.initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero
          X Y)

/--
Metric-derivative formula data for the selected Christoffel symbols.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaCurrentApi
        (coefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
          X Y)

/--
Christoffel-formula data for the selected initial-time commuting-pair
representatives is narrowed to coefficient identification plus the
metric-derivative formula.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
  initialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      initialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationAtTime

/--
Once coefficient identification is supplied by the selected connection
coefficient itself, the full Christoffel-formula data is reduced to the
metric-derivative formula for that chosen coefficient identification.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_metric_derivative_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (metricDerivativeFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          initialTimeCommutingPairRepresentativeAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
  initialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaAtTime :=
    metricDerivativeFormulaAtTime

/--
The selected Christoffel-formula data already contains the coefficient
identification used by the connection-zero route.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_christoffel_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime :=
  christoffelFormulaAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationAtTime

/--
The narrowed Christoffel-formula data still exposes the previous per-pair
Christoffel-formula payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_coefficient_identification_and_metric_derivative_formula_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y)
      (christoffelFormulaAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
        X Y)
      (christoffelFormulaAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula
        X Y)

/--
Termwise metric-first-derivative vanishing data for the selected Christoffel
formulae.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) where
  initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_terms_vanish :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          initialTimeCommutingPairRepresentativeAtTime
          christoffelFormulaAtTime X Y)

/--
Normal-coordinate metric-first-derivative vanishing data for the selected
Christoffel formulae.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) where
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime

/--
Pointwise normal-coordinate Christoffel-symbol vanishing for every selected
initial-time commuting pair.  Together with the Christoffel-formula data, this
is the upstream normal-coordinate fact needed to recover metric-first-derivative
vanishing.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolPointwiseVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_vanish :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
Coefficient-identification data plus the selected symbol-zero family recovers
the pointwise Christoffel-symbol vanishing data required by the current route.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_pointwise_vanishing_data_of_coefficient_identification_and_symbol_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (christoffelSymbolZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime coefficientIdentificationAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolPointwiseVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_vanish := by
    intro x X Y
    exact
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_coefficient_identification_and_symbol_zero_current_api
        (coefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
          X Y)
        (christoffelSymbolZeroAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_zero
          X Y)

/--
Formula data plus pointwise normal-coordinate Christoffel-symbol vanishing
recovers the current metric-first-derivative vanishing data.  The termwise
payload is filled through the accepted algebraic term-expansion route, so the
only remaining mathematical input is the upstream Christoffel-symbol vanishing
family.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_data_of_christoffel_formula_and_christoffel_symbol_pointwise_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (christoffelSymbolPointwiseVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolPointwiseVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime where
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingAtTime := {
    initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_terms_vanish := by
      intro x X Y
      exact
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_vanishing_of_metric_first_derivative_vanishing_algebraic_current_api
          (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            initialTimeCommutingPairRepresentativeAtTime
            christoffelFormulaAtTime X Y)
          (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_christoffel_formula_and_christoffel_symbol_vanishing_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
              X Y)
            (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
              metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
              initialTimeCommutingPairRepresentativeAtTime
              christoffelFormulaAtTime X Y)
            (christoffelSymbolPointwiseVanishingAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbols_vanish
              X Y))
  }

/--
The narrowed metric-first-derivative data still exposes the previous per-pair
metric-first-derivative vanishing payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_forward_normal_coordinate_metric_first_derivative_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingCurrentApi
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          initialTimeCommutingPairRepresentativeAtTime
          christoffelFormulaAtTime X Y) := by
  intro x X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_term_vanishing_current_api
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        christoffelFormulaAtTime X Y)
      (metricFirstDerivativeVanishingAtTime.initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingAtTime.initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_terms_vanish
        X Y)

/--
Normal-coordinate Christoffel-symbol vanishing data is narrowed to the
Christoffel formula and the metric-first-derivative vanishing source.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime

/--
Christoffel-formula data plus metric-first-derivative vanishing are exactly
the normal-coordinate Christoffel-symbol vanishing data used by the
base-vector coefficient route.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime :=
    christoffelFormulaAtTime
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingAtTime :=
    metricFirstDerivativeVanishingAtTime

/--
The narrowed Christoffel-symbol data still exposes the previous pointwise
symbol-vanishing payload.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_forward_normal_coordinate_christoffel_symbol_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelSymbolVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_christoffel_formula_and_metric_first_derivative_vanishing_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y)
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        christoffelSymbolVanishingAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime
        X Y)
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_forward_normal_coordinate_metric_first_derivative_vanishing_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        christoffelSymbolVanishingAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime
        christoffelSymbolVanishingAtTime.initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingAtTime
        X Y)

/--
Direct base-vector connection-coefficient zero data, together with the
coefficient-identification and Christoffel-formula payloads, supplies the full
normal-coordinate Christoffel-symbol vanishing data used by the older
base-vector coefficient-zero route.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_data_of_coefficient_identification_formula_and_base_vector_connection_coefficient_direct_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (baseVectorConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaAtTime :=
    christoffelFormulaAtTime
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_data_of_christoffel_formula_and_christoffel_symbol_pointwise_vanishing_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      christoffelFormulaAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_pointwise_vanishing_data_of_coefficient_identification_and_symbol_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        coefficientIdentificationAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_zero_data_of_base_vector_connection_coefficient_direct_zero_data_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          initialTimeCommutingPairRepresentativeAtTime
          coefficientIdentificationAtTime
          baseVectorConnectionCoefficientDirectZeroAtTime))

/--
Forward base-vector connection-coefficient zero data is narrowed to the
normal-coordinate Christoffel-symbol source.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime

/--
Normal-coordinate Christoffel-symbol vanishing data supplies the base-vector
connection-coefficient zero data consumed by the selected coefficient route.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_forward_normal_coordinate_christoffel_symbol_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelSymbolVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingAtTime :=
    christoffelSymbolVanishingAtTime

/--
Christoffel-formula data and metric-first-derivative vanishing therefore
supply the base-vector connection-coefficient zero data directly.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_forward_normal_coordinate_christoffel_symbol_vanishing_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      christoffelFormulaAtTime metricFirstDerivativeVanishingAtTime)

/--
The narrowed base-vector coefficient payload still exposes the previous
base-vector coefficient-zero proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_normal_coordinate_christoffel_symbol_vanishing_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_of_forward_normal_coordinate_christoffel_symbol_vanishing_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        forwardBaseVectorConnectionCoefficientZeroAtTime.initialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingAtTime
        X Y)

/--
The base-vector coefficient payload recovers the previous coefficient form by
using the selected representative's value equation.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hbase :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      forwardBaseVectorConnectionCoefficientZeroAtTime X Y
  simpa [
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi,
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
    pair
  ] using
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair hbase

/--
Forward connection-coefficient zero data is narrowed to the base-vector
coefficient source.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime

/--
The narrowed coefficient payload still exposes the previous coefficient-zero
proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_of_forward_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    forwardConnectionCoefficientZeroAtTime.initialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroAtTime

/--
The base-vector coefficient-zero source also recovers the direct selected
coefficient-zero payload by applying the selected representative's value
equation.  This lets the raw direct coefficient-zero frontier reuse the
existing normal-coordinate/base-vector coefficient route.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initial_time_commuting_pair_forward_connection_coefficients_zero := by
    intro x X Y
    exact
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime
        forwardBaseVectorConnectionCoefficientZeroAtTime X Y

/--
Forward connection-coefficient zero data exposes the same direct selected
coefficient-zero payload; its stored source is already the base-vector
coefficient-zero data.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    forwardConnectionCoefficientZeroAtTime.initialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroAtTime

/--
The explicit connection-coefficient payload recovers the forward mixed
connection-term proposition used by the commutator notation.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_of_forward_connection_coefficient_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hcoeff :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_of_forward_connection_coefficient_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime forwardConnectionCoefficientZeroAtTime
      X Y
  simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi,
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi,
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroCurrentApi,
    stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api,
    pair] using hcoeff

/--
Forward mixed connection-term zero data is narrowed to the actual selected
initial-time connection coefficient.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardConnectionCoefficientZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime

/--
Direct selected connection-coefficient zero data supplies the stored
forward-term-zero payload once the normal-coordinate coefficient-identification
and Christoffel-formula data are available.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_connection_coefficient_direct_zero_and_normal_coordinate_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardConnectionCoefficientZeroAtTime := {
    initialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroAtTime := {
      initialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_vanishing_data_of_coefficient_identification_formula_and_base_vector_connection_coefficient_direct_zero_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          initialTimeCommutingPairRepresentativeAtTime
          coefficientIdentificationAtTime
          christoffelFormulaAtTime
          (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_direct_zero_data_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            initialTimeCommutingPairRepresentativeAtTime
            forwardConnectionCoefficientDirectZeroAtTime) } }

/--
Direct selected connection-coefficient zero data and the selected Christoffel
formula data fill the stored forward-term-zero payload; the coefficient
identification is read from the formula data itself.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_connection_coefficient_direct_zero_and_christoffel_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_connection_coefficient_direct_zero_and_normal_coordinate_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_christoffel_formula_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      christoffelFormulaAtTime)
    christoffelFormulaAtTime
    forwardConnectionCoefficientDirectZeroAtTime

/--
The narrowed forward-term payload still exposes the previous commutator-form
forward connection-term proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_of_forward_connection_term_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionTermZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_of_forward_connection_coefficient_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    forwardConnectionTermZeroAtTime.initialTimeCommutingPairForwardConnectionCoefficientZeroAtTime

/--
The explicit forward mixed connection-term payload recovers the older
connection-zero proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_forward_connection_term_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardConnectionTermZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hterm :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_of_forward_connection_term_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime forwardConnectionTermZeroAtTime
      X Y
  simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi,
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroCurrentApi,
    stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
    stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api,
    pair] using hterm

/--
Connection-zero data is narrowed to the explicit forward mixed connection-term
source used by the commutator construction.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairForwardConnectionTermZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime

/--
Base-vector coefficient-zero data already supplies the stored forward
coefficient-zero payload.  This keeps the selected coefficient route below the
connection-zero interface, with the only remaining source being the
base-vector normal-coordinate coefficient calculation.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroAtTime :=
    forwardBaseVectorConnectionCoefficientZeroAtTime

/--
Base-vector coefficient-zero data fills the forward mixed connection-term
payload by first transporting through the selected representative value
equation.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionTermZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardConnectionCoefficientZeroAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      forwardBaseVectorConnectionCoefficientZeroAtTime

/--
Base-vector coefficient-zero data fills the connection-zero data record
directly.  This removes the need to consume a broader commuting-pair
connection-zero package when the normal-coordinate coefficient calculation is
already available.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardConnectionTermZeroAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      forwardBaseVectorConnectionCoefficientZeroAtTime

/--
Christoffel-formula data plus metric-first-derivative vanishing supplies the
connection-zero data through the base-vector coefficient calculation.  The new
remaining analytic source is the specific Christoffel/metric-derivative
normal-coordinate fact, not the broader connection-zero package.
-/
def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (metricFirstDerivativeVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime christoffelFormulaAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      christoffelFormulaAtTime metricFirstDerivativeVanishingAtTime)

/--
Direct selected connection-coefficient zero data, with the matching
normal-coordinate coefficient-identification and Christoffel-formula payloads,
fills the connection-zero data record by constructing its forward-term source.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_direct_zero_and_normal_coordinate_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardConnectionTermZeroAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_connection_coefficient_direct_zero_and_normal_coordinate_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      coefficientIdentificationAtTime
      christoffelFormulaAtTime
      forwardConnectionCoefficientDirectZeroAtTime

/--
Direct selected connection-coefficient zero data and selected Christoffel
formula data fill the connection-zero record; the coefficient-identification
field is recovered from the formula data.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_direct_zero_and_christoffel_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (forwardConnectionCoefficientDirectZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientDirectZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime where
  initialTimeCommutingPairForwardConnectionTermZeroAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_term_zero_data_of_forward_connection_coefficient_direct_zero_and_christoffel_formula_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      christoffelFormulaAtTime
      forwardConnectionCoefficientDirectZeroAtTime

/--
Forward connection-coefficient normal representatives drive the connection-zero
payload for the representatives selected from the same source, once the
normal-coordinate coefficient-identification and Christoffel-formula data are
available for those selected representatives.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_and_normal_coordinate_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (coefficientIdentificationAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelCoefficientIdentificationDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime))
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_direct_zero_and_normal_coordinate_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    coefficientIdentificationAtTime
    christoffelFormulaAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
Forward coefficient normal representatives drive the selected connection-zero
data from a single selected Christoffel-formula payload.  The matching
coefficient-identification payload is taken from that formula data.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_and_christoffel_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (christoffelFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_direct_zero_and_christoffel_formula_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    christoffelFormulaAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
Forward coefficient normal representatives drive the selected connection-zero
data from only the metric-derivative formula for the coefficient identification
chosen by the selected connection coefficient.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_and_metric_derivative_formula_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (metricDerivativeFormulaAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime)
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            forwardConnectionCoefficientNormalRepresentativeAtTime))) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_and_christoffel_formula_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    forwardConnectionCoefficientNormalRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_metric_derivative_formula_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime)
      metricDerivativeFormulaAtTime)

/--
Forward coefficient normal representatives supply the metric-derivative formula
for the coefficient-identification source that takes each Christoffel symbol to
be the selected connection coefficient itself.  The selected metric-derivative
combination is `0`, and the formula equality is exactly the direct
base-vector coefficient vanishing supplied by the normal representatives.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelMetricDerivativeFormulaDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime)
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime)) where
  initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula := by
    intro x X Y
    let representativeAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime
    let coefficientIdentificationAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification_data_of_connection_coefficient_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        representativeAtTime
    let directZeroAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime
    let baseVectorDirectZeroAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_direct_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        representativeAtTime directZeroAtTime
    exact
      { metricFirstDerivativeCombinationAtBase := 0
        christoffel_eq_metric_first_derivative_combination := by
          exact
            stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_symbol_zero_of_coefficient_identification_and_base_vector_connection_coefficient_zero_current_api
              metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
              (coefficientIdentificationAtTime.initial_time_commuting_pair_forward_normal_coordinate_christoffel_coefficient_identification
                X Y)
              (baseVectorDirectZeroAtTime.initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero
                X Y) }

/--
Forward coefficient normal representatives therefore supply the selected
Christoffel-formula data for the representatives chosen from the same source.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelFormulaDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_metric_derivative_formula_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
For the Christoffel formula selected from forward coefficient normal
representatives, the metric-first-derivative combination vanishes.  The formula
source has its selected Christoffel symbol represented by the same connection
coefficient whose base-vector value is supplied as zero by the normal
representative payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime)
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) where
  initialTimeCommutingPairForwardNormalCoordinateMetricFirstDerivativeTermVanishingAtTime := {
    initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_terms_vanish := by
      intro x X Y
      let representativeAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime
      let christoffelFormulaDataAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime
      let christoffelFormulaAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_of_forward_normal_coordinate_christoffel_formula_data_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          representativeAtTime christoffelFormulaDataAtTime X Y
      let directZeroAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime
      let baseVectorDirectZeroAtTime :=
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_direct_zero_data_of_forward_connection_coefficient_direct_zero_data_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          representativeAtTime directZeroAtTime
      let christoffelSymbolVanishingAtTime :
          StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardNormalCoordinateChristoffelSymbolVanishingCurrentApi
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            (representativeAtTime.initial_time_commuting_pair_representatives X Y) :=
        { christoffelSymbolAtBase := christoffelFormulaAtTime.christoffelSymbolAtBase
          connection_coefficient_eq_christoffel :=
            christoffelFormulaAtTime.connection_coefficient_eq_christoffel
          christoffelSymbolAtBase_eq_zero := by
            exact
              christoffelFormulaAtTime.connection_coefficient_eq_christoffel.symm.trans
                (baseVectorDirectZeroAtTime.initial_time_commuting_pair_forward_base_vector_connection_coefficients_zero
                  X Y) }
      exact
        stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_term_vanishing_of_metric_first_derivative_vanishing_algebraic_current_api
          christoffelFormulaAtTime
          (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_of_christoffel_formula_and_christoffel_symbol_vanishing_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            (representativeAtTime.initial_time_commuting_pair_representatives X Y)
            christoffelFormulaAtTime christoffelSymbolVanishingAtTime)
  }

/--
Forward coefficient normal representatives directly supply the narrower
base-vector coefficient-zero data for the representatives selected from the
same source.  The proof goes through the already constructed selected
Christoffel-formula data and its metric-first-derivative vanishing data.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_christoffel_formula_and_metric_first_derivative_vanishing_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_metric_first_derivative_vanishing_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
The same normal-representative source exposes the pointwise base-vector
coefficient-zero proposition for every selected ordered pair.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime).initial_time_commuting_pair_representatives
            X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_of_forward_base_vector_connection_coefficient_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
The forward coefficient normal-representative source now drives the selected
connection-zero data without an external metric-derivative formula payload.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        forwardConnectionCoefficientNormalRepresentativeAtTime) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_connection_coefficient_normal_representatives_and_metric_derivative_formula_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    forwardConnectionCoefficientNormalRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_normal_coordinate_christoffel_metric_derivative_formula_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
The narrowed connection-zero data still exposes the previous forward
connection-zero proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_forward_connection_term_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    connectionZeroAtTime.initialTimeCommutingPairForwardConnectionTermZeroAtTime

/--
The lower base-vector coefficient-zero source exposes the same selected
connection-zero proposition as the broader connection-zero package.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_forward_base_vector_connection_coefficient_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (forwardBaseVectorConnectionCoefficientZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardBaseVectorConnectionCoefficientZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_data_of_forward_base_vector_connection_coefficient_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      forwardBaseVectorConnectionCoefficientZeroAtTime)

/--
Forward coefficient normal representatives expose the pointwise
connection-zero proposition for the representatives selected from the same
source, via the narrower base-vector coefficient-zero data route.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_forward_connection_coefficient_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (forwardConnectionCoefficientNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          forwardConnectionCoefficientNormalRepresentativeAtTime).initial_time_commuting_pair_representatives
            X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_forward_base_vector_connection_coefficient_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_zero_data_of_forward_connection_coefficient_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      forwardConnectionCoefficientNormalRepresentativeAtTime)

/--
Connection-zero data for the chosen commuting-pair representatives also
supplies the base-vector form of the same initial forward coefficient.  The
only extra step is the representative value rewrite from `Xext x` back to `X`.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_connection_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = 0 := by
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hconnection :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_forward_connection_coefficient_expression_zero_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair
      (by
        simpa [
          StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi,
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
          pair
        ] using hconnection)

/--
Chosen ordered-pair representatives plus their connection-zero data supply the
forward coefficient normal-representative source.  This connects the newer
existential source to the existing commuting-pair ladder without requiring the
bracket-zero half of that ladder.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_connection_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime where
  initial_time_commuting_pair_forward_connection_coefficient_normal_representatives := by
    intro x X Y
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    have hconnection :
        StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime X Y
    exact
      ⟨pair.Xext, pair.Yext, pair.Xext_eq, pair.Yext_eq,
        pair.Xext_smoothAt, pair.Yext_smoothAt, by
          simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi,
            pair] using hconnection⟩

/--
Reverse mixed connection-zero data for the selected initial-time commuting-pair
representatives.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initial_time_commuting_pair_reverse_connection_zero :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y)

/--
Lie-bracket-zero data is narrowed to the reverse mixed connection-zero source;
the bracket equation is recovered below from torsion-freeness and the forward
connection-zero payload.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (_connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) where
  initialTimeCommutingPairReverseConnectionZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime

/--
Forward and reverse mixed connection-zero equations force the selected pair's
Lie bracket to vanish by torsion-freeness of the constructed connection.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_connection_zero_and_reverse_connection_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (reverseConnectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroCurrentApi
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  have htorsion : (connectionAtTime 0).torsion = 0 :=
    torsionFreeConnectionAtTime.torsion_eq_zero 0
  have hbracket :
      connectionAtTime 0 pair.Yext x (pair.Xext x) -
          connectionAtTime 0 pair.Xext x (pair.Yext x) =
        VectorField.mlieBracket ThreeManifoldModelWithCorners pair.Xext pair.Yext x :=
    ((connectionAtTime 0).torsion_eq_zero_iff.mp htorsion)
      pair.Xext_smoothAt pair.Yext_smoothAt
  have hXY :
      connectionAtTime 0 pair.Yext x (pair.Xext x) = 0 := by
    simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
      pair, metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
      connectionAtTime] using
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime X Y
  have hYX :
      connectionAtTime 0 pair.Xext x (pair.Yext x) = 0 := by
    simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairReverseConnectionZeroCurrentApi,
      stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api,
      pair, metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
      connectionAtTime] using
      reverseConnectionZeroAtTime.initial_time_commuting_pair_reverse_connection_zero X Y
  rw [hXY, hYX] at hbracket
  simpa [StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroCurrentApi] using
    hbracket.symm

/--
The narrowed bracket-zero payload still exposes the previous raw bracket-zero
condition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_bracket_zero_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (bracketZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroCurrentApi
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_connection_zero_and_reverse_connection_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    connectionZeroAtTime
    bracketZeroAtTime.initialTimeCommutingPairReverseConnectionZeroAtTime

/--
Condition data for the selected initial-time commuting-pair representatives.

This is the narrowed frontier below the former broad commuting-pair normal
representative field: once the representatives are selected, the missing
analytic theorem is split into the initial connection-zero and bracket-zero
normal-coordinate identities for those representatives.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M)) where
  initialTimeCommutingPairConnectionZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
  initialTimeCommutingPairBracketZeroAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      initialTimeCommutingPairConnectionZeroAtTime

/--
The split connection-zero and bracket-zero payloads recover the previous
commuting-pair condition proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_connection_zero_and_bracket_zero_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (connectionZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime)
    (bracketZeroAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) := by
  intro x X Y
  exact
    ⟨stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime X Y,
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_bracket_zero_data_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime connectionZeroAtTime
        bracketZeroAtTime X Y⟩

/--
The narrowed commuting-pair condition payload still exposes its previous
combined condition proposition.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_condition_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (initialTimeCommutingPairConditionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
          X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_connection_zero_and_bracket_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairRepresentativeAtTime
    initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairConnectionZeroAtTime
    initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairBracketZeroAtTime

/--
Initial-time commuting-pair normal representative data for the stationary-zero
curvature construction commutator.

This now stores the split local normal-frame sources: chosen smooth
representatives for the ordered pair, and the remaining theorem that those
chosen representatives have zero initial connection term and bracket at the
base point.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  commutingPairTangentVectorFieldExtensionAtTime :
    StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M)
  initialTimeCommutingPairConditionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
        commutingPairTangentVectorFieldExtensionAtTime)

/--
The normal-representative payload exposes the pointwise connection-zero
proposition for the representatives selected from its tangent-vector-field
extension source.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_commuting_pair_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConnectionZeroCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
          initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime).initial_time_commuting_pair_representatives
            X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_connection_zero_of_connection_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairConnectionZeroAtTime

/--
The normal-representative payload also exposes the pointwise bracket-zero
proposition for the representatives selected from its tangent-vector-field
extension source.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_commuting_pair_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairBracketZeroCurrentApi
        ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
          initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime).initial_time_commuting_pair_representatives
            X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_bracket_zero_of_bracket_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairConnectionZeroAtTime
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairBracketZeroAtTime

/--
The normal-representative payload exposes the full initial-time commuting-pair
condition for the representatives selected from its tangent-vector-field
extension source.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_commuting_pair_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
          initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime).initial_time_commuting_pair_representatives
            X Y) :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_condition_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime

/--
The existing commuting-pair normal-representative payload supplies the newer
forward coefficient normal-representative source by forgetting the bracket-zero
component and retaining the selected connection-zero representatives.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_commuting_pair_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairForwardConnectionCoefficientNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_normal_representatives_of_pair_representatives_and_connection_zero_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairConnectionZeroAtTime

/--
The initial-time commuting-pair normal-representative package supplies the
base-vector form of the forward coefficient zero.  This is the concrete
connection-term projection below the forward-coefficient interface.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_commuting_pair_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    let initialTimeCommutingPairRepresentativeAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
        initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x X = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_connection_zero_data_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime.initialTimeCommutingPairConnectionZeroAtTime
    X Y

/--
The same commuting-pair normal-representative package therefore gives zero of
the selected forward coefficient expression, by first passing through the
base-vector coefficient expression.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_commuting_pair_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    let initialTimeCommutingPairRepresentativeAtTime :=
      stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
        initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime
    let pair :=
      initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
        X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) = 0 := by
  let initialTimeCommutingPairRepresentativeAtTime :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hbase :
      let metricCompatibleConnectionAtTime :=
        curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
      let torsionFreeConnectionAtTime :=
        metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
      let connectionAtTime :=
        torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
      connectionAtTime 0 pair.Yext x X = 0 :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_base_vector_connection_coefficient_expression_zero_of_commuting_pair_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairNormalRepresentativeAtTime X Y
  exact
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime pair hbase

/--
Selected pair representatives plus their initial connection/bracket condition
recover the previous commuting-pair normal representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_pair_representatives_and_conditions_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairRepresentativeDataCurrentApi
        (M := M))
    (initialTimeCommutingPairConditionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeCommutingPairRepresentativeAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 := by
  intro x X Y
  let pair :=
    initialTimeCommutingPairRepresentativeAtTime.initial_time_commuting_pair_representatives
      X Y
  have hcondition :=
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_conditions_of_condition_data_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairRepresentativeAtTime
      initialTimeCommutingPairConditionAtTime X Y
  rcases hcondition with ⟨hconnection, hbracket⟩
  exact
    ⟨pair.Xext, pair.Yext, pair.Xext_eq, pair.Yext_eq,
      pair.Xext_smoothAt, pair.Yext_smoothAt, hconnection, hbracket⟩

/--
The single-vector extension payload plus the selected-pair condition recovers
the previous commuting-pair normal representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_tangent_vector_field_extension_and_conditions_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (tangentVectorFieldExtensionAtTime :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M))
    (initialTimeCommutingPairConditionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairConditionDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
          tangentVectorFieldExtensionAtTime)) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_pair_representatives_and_conditions_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_current_api
      tangentVectorFieldExtensionAtTime)
    initialTimeCommutingPairConditionAtTime

/--
The narrowed commuting-pair payload still exposes its previous existential
representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_commuting_pair_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_tangent_vector_field_extension_and_conditions_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeCommutingPairNormalRepresentativeAtTime.commutingPairTangentVectorFieldExtensionAtTime
    initialTimeCommutingPairNormalRepresentativeAtTime.initialTimeCommutingPairConditionAtTime

/--
Chosen smooth representative for the third tangent vector after the ordered
`X,Y` pair has been fixed.

The choice is intentionally separate from the parallelism equations so the
frontier distinguishes extension existence from the connection-term vanishing
needed for the stationary-zero curvature construction.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeCurrentApi
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {x : M}
    (Z : TangentSpace ThreeManifoldModelWithCorners x) where
  Zext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y
  Zext_eq : Zext x = Z
  Zext_smoothAt : StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x

/--
Representative-choice data for the third tangent vector, conditional on the
already chosen commuting `X,Y` pair and its hypotheses.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initial_time_parallel_third_representatives :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x)
      (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      Xext x = X →
      Yext x = Y →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x →
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 Yext x (Xext x) = 0 →
      VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 →
        StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeCurrentApi
          (M := M) Z

/--
The existing single-vector extension payload supplies the selected third
representative, independently of the already chosen commuting pair.
-/
noncomputable def stationary_zero_riemann_curvature_construction_initial_time_parallel_third_representative_data_of_tangent_vector_field_extension_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (tangentVectorFieldExtensionAtTime :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M)) :
    StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime where
  initial_time_parallel_third_representatives := by
    intro x _X _Y Z _Xext _Yext _hX _hY _hXsmooth _hYsmooth _hXY _hbracket
    let Zdata :=
      stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
        tangentVectorFieldExtensionAtTime Z
    exact
      { Zext := Classical.choose Zdata
        Zext_eq := (Classical.choose_spec Zdata).1
        Zext_smoothAt := (Classical.choose_spec Zdata).2 }

/--
The remaining parallel-third condition for a selected third representative:
it must be parallel, for the initial connection, along both selected fields.
-/
def StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    {x : M} {Z : TangentSpace ThreeManifoldModelWithCorners x}
    (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y)
    (third :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeCurrentApi
        (M := M) Z) : Prop :=
  (∀ y : M,
    stationary_zero_riemann_curvature_construction_connection_at_time_current_api
      metric identifiesDerivative identifiesRicci
      curvatureConstructionAtTime 0 third.Zext y (Yext y) = 0) ∧
  (∀ y : M,
    stationary_zero_riemann_curvature_construction_connection_at_time_current_api
      metric identifiesDerivative identifiesRicci
      curvatureConstructionAtTime 0 third.Zext y (Xext y) = 0)

/--
Condition data for selected parallel-third representatives.

This is the narrowed frontier below the former broad parallel-third normal
representative field: after the third representative has been chosen, the
remaining analytic theorem is precisely its two initial parallelism equations.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeParallelThirdRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) where
  initial_time_parallel_third_conditions :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x)
      (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y)
      (hX : Xext x = X)
      (hY : Yext x = Y)
      (hXsmooth :
        StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x)
      (hYsmooth :
        StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x)
      (hXY :
        stationary_zero_riemann_curvature_construction_connection_at_time_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime 0 Yext x (Xext x) = 0)
      (hbracket :
        VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0),
        StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionCurrentApi
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          Xext Yext
          (initialTimeParallelThirdRepresentativeAtTime.initial_time_parallel_third_representatives
            X Y Z Xext Yext hX hY hXsmooth hYsmooth hXY hbracket)

/--
Initial-time parallel-third normal representative data for the stationary-zero
curvature construction commutator.

This now stores the split local normal-frame sources for the third vector: a
selected smooth representative, and the theorem that this selected
representative is parallel along the chosen `X,Y` fields for the initial
connection.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  parallelThirdTangentVectorFieldExtensionAtTime :
    StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M)
  initialTimeParallelThirdConditionAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      (stationary_zero_riemann_curvature_construction_initial_time_parallel_third_representative_data_of_tangent_vector_field_extension_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        parallelThirdTangentVectorFieldExtensionAtTime)

/--
Selected third representatives plus their two initial parallelism conditions
recover the previous parallel-third normal representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_third_representatives_and_conditions_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeParallelThirdRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (initialTimeParallelThirdConditionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        initialTimeParallelThirdRepresentativeAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x)
      (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      Xext x = X →
      Yext x = Y →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x →
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 Yext x (Xext x) = 0 →
      VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 →
        ∃ Zext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Zext x = Z ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Xext y) = 0) := by
  intro x X Y Z Xext Yext hX hY hXsmooth hYsmooth hXY hbracket
  let third :=
    initialTimeParallelThirdRepresentativeAtTime.initial_time_parallel_third_representatives
      X Y Z Xext Yext hX hY hXsmooth hYsmooth hXY hbracket
  have hcondition :=
    initialTimeParallelThirdConditionAtTime.initial_time_parallel_third_conditions
      X Y Z Xext Yext hX hY hXsmooth hYsmooth hXY hbracket
  rcases hcondition with ⟨hYZ0, hXZ0⟩
  exact ⟨third.Zext, third.Zext_eq, third.Zext_smoothAt, hYZ0, hXZ0⟩

/--
The single-vector extension payload plus the selected-third parallelism
condition recovers the previous parallel-third normal representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_tangent_vector_field_extension_and_conditions_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (tangentVectorFieldExtensionAtTime :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M))
    (initialTimeParallelThirdConditionAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdConditionDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        (stationary_zero_riemann_curvature_construction_initial_time_parallel_third_representative_data_of_tangent_vector_field_extension_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          tangentVectorFieldExtensionAtTime)) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x)
      (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      Xext x = X →
      Yext x = Y →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x →
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 Yext x (Xext x) = 0 →
      VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 →
        ∃ Zext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Zext x = Z ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Xext y) = 0) :=
  stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_third_representatives_and_conditions_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_riemann_curvature_construction_initial_time_parallel_third_representative_data_of_tangent_vector_field_extension_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      tangentVectorFieldExtensionAtTime)
    initialTimeParallelThirdConditionAtTime

/--
The narrowed parallel-third payload still exposes its previous existential
representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_parallel_third_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeParallelThirdNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x)
      (Xext Yext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      Xext x = X →
      Yext x = Y →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x →
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime 0 Yext x (Xext x) = 0 →
      VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 →
        ∃ Zext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
          Zext x = Z ∧
            StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
            (∀ y : M,
              stationary_zero_riemann_curvature_construction_connection_at_time_current_api
                metric identifiesDerivative identifiesRicci
                curvatureConstructionAtTime 0 Zext y (Xext y) = 0) :=
  stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_tangent_vector_field_extension_and_conditions_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeParallelThirdNormalRepresentativeAtTime.parallelThirdTangentVectorFieldExtensionAtTime
    initialTimeParallelThirdNormalRepresentativeAtTime.initialTimeParallelThirdConditionAtTime

/--
Initial-time connection-field bracket-normal representative data for the
stationary-zero curvature construction commutator.

This payload now stores the split local normal-frame sources: a commuting
normal pair for `X,Y`, and a compatible parallel `Z` representative for that
chosen pair.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeBracketNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialTimeCommutingPairNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
  initialTimeParallelThirdNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Commuting-pair normal representatives and compatible parallel-third
representatives recover the previous bracket-normal triple witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_bracket_normal_representatives_of_pair_and_parallel_third_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeCommutingPairNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeCommutingPairNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (initialTimeParallelThirdNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeParallelThirdNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Xext y) = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_normal_representatives_of_commuting_pair_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeCommutingPairNormalRepresentativeAtTime
      X Y with
    ⟨Xext, Yext, hX, hY, hXdiff, hYdiff, hXY, hbracket⟩
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_parallel_third_normal_representatives_of_parallel_third_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeParallelThirdNormalRepresentativeAtTime
      X Y Z Xext Yext hX hY hXdiff hYdiff hXY hbracket with
    ⟨Zext, hZ, hZdiff, hYZ0, hXZ0⟩
  exact
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hXZ0, hXY, hbracket⟩

/--
The narrowed bracket-normal payload still exposes its previous triple witness
through the split pair/parallel-third sources.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_bracket_normal_representatives_of_bracket_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeBracketNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Xext y) = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_bracket_normal_representatives_of_pair_and_parallel_third_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime.initialTimeCommutingPairNormalRepresentativeAtTime
    initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime.initialTimeParallelThirdNormalRepresentativeAtTime

/--
Initial-time connection-field zero normal representative data for the
stationary-zero curvature construction commutator.

This payload now stores the sharper bracket-normal source.  The removed mixed
connection zero is recovered from torsion-freeness of the selected initial
connection.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeZeroNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeBracketNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Bracket-normal representatives recover full initial-time connection-field zero
normal representatives using torsion-freeness at the initial time.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_zero_normal_representatives_of_bracket_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeBracketNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Xext y) = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Xext x (Yext x) = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_bracket_normal_representatives_of_bracket_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hXZ0, hXY, hbracket0⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hXZ0, hXY, ?_⟩
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  have htorsion : (connectionAtTime 0).torsion = 0 :=
    torsionFreeConnectionAtTime.torsion_eq_zero 0
  have hbracket :
      connectionAtTime 0 Yext x (Xext x) -
          connectionAtTime 0 Xext x (Yext x) =
        VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x :=
    ((connectionAtTime 0).torsion_eq_zero_iff.mp htorsion) hXdiff hYdiff
  have hXY' : connectionAtTime 0 Yext x (Xext x) = 0 := by
    simpa [stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
      metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
      connectionAtTime] using hXY
  have hYX' : connectionAtTime 0 Xext x (Yext x) = 0 := by
    rw [hXY', hbracket0] at hbracket
    simpa using hbracket
  simpa [stationary_zero_riemann_curvature_construction_connection_at_time_current_api,
    metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
    connectionAtTime] using hYX'

/--
The narrowed zero-normal payload still exposes its previous initial-time
connection-field representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_zero_normal_representatives_of_connection_at_time_zero_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeZeroNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Yext y) = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_at_time_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 Zext y (Xext y) = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Yext x (Xext x) = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_at_time_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 Xext x (Yext x) = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_zero_normal_representatives_of_bracket_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime.initialTimeConnectionAtTimeBracketNormalRepresentativeAtTime

/--
Initial-time connection-term zero normal representative data for the
stationary-zero curvature construction commutator.

This payload now stores the sharper connection-field source, from which the
selected connection-term wrapper identities are recovered definitionally.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermZeroNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeZeroNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Initial-time connection-field zero normal representatives supply the selected
connection-term zero normal representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_term_zero_normal_representatives_of_connection_at_time_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionAtTimeZeroNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_connection_at_time_zero_normal_representatives_of_connection_at_time_zero_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hXZ0, hXY, hYX⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      ?_, ?_, ?_, ?_⟩
  · intro y
    simpa [stationary_zero_riemann_curvature_construction_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api] using hYZ0 y
  · intro y
    simpa [stationary_zero_riemann_curvature_construction_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api] using hXZ0 y
  · simpa [stationary_zero_riemann_curvature_construction_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api] using hXY
  · simpa [stationary_zero_riemann_curvature_construction_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_at_time_current_api] using hYX

/--
The narrowed selected connection-term zero-normal payload still exposes the
previous representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_term_zero_normal_representatives_of_initial_time_connection_term_zero_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionTermZeroNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermZeroNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext = 0) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_connection_term_zero_normal_representatives_of_connection_at_time_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeConnectionTermZeroNormalRepresentativeAtTime.initialTimeConnectionAtTimeZeroNormalRepresentativeAtTime

/--
Initial-time connection-term normal representative data for the
stationary-zero curvature construction commutator.

This payload now stores the two deeper sources separately: initial-time zero
normal representatives, and time-independence of the selected connection term.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialTimeConnectionTermZeroNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermZeroNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Initial-time zero normal representatives and selected connection-term
time-independence recover the previous initial-time connection-term
representative witness.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_term_normal_representatives_of_zero_normal_and_time_independence_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionTermZeroNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermZeroNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    (selectedConnectionTermTimeIndependenceAtTime :
      StationaryZeroRiemannCurvatureConstructionSelectedConnectionTermTimeIndependenceDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext =
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext =
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_connection_term_zero_normal_representatives_of_initial_time_connection_term_zero_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeConnectionTermZeroNormalRepresentativeAtTime X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hXZ0, hXY, hYX⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, ?_, hXZ0, ?_, hXY, hYX⟩
  · intro t y
    exact
      stationary_zero_riemann_curvature_construction_selected_connection_term_time_independent_of_selected_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        selectedConnectionTermTimeIndependenceAtTime
        Yext Zext t y
  · intro t y
    exact
      stationary_zero_riemann_curvature_construction_selected_connection_term_time_independent_of_selected_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        selectedConnectionTermTimeIndependenceAtTime
        Xext Zext t y

/--
The narrowed initial-time connection-term payload still exposes its previous
representative witness through the split zero-normal and stationary-connection
sources.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_connection_term_normal_representatives_of_initial_time_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionTermNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext =
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Yext Zext) ∧
          (∀ y : M,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext =
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime 0 (x := y) Xext Zext) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_connection_term_normal_representatives_of_zero_normal_and_time_independence_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialTimeConnectionTermNormalRepresentativeAtTime.initialTimeConnectionTermZeroNormalRepresentativeAtTime
    {}

/--
Initial directional covariant-derivative normal representative data for the
stationary-zero curvature construction commutator.

This is the next frontier below directional covariant-derivative normal
representatives.  It now stores the sharper initial-time connection-term
source, from which all-time inner vanishing is recovered using the explicit
time-independence identities.
-/
structure StationaryZeroRiemannCurvatureConstructionInitialDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialTimeConnectionTermNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Initial-time connection-term normal representatives recover the previous
initial directional witness by propagating the inner `∇_Y Z` and `∇_X Z`
identities from `t = 0` to all times.
-/
theorem stationary_zero_riemann_curvature_construction_initial_directional_covariant_derivative_normal_representatives_of_initial_time_connection_term_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialTimeConnectionTermNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialTimeConnectionTermNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_time_connection_term_normal_representatives_of_initial_time_connection_term_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialTimeConnectionTermNormalRepresentativeAtTime X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ0, hYZtime, hXZ0, hXZtime, hXY, hYX⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      ?_, ?_, hXY, hYX⟩
  · intro t y
    rw [hYZtime t y]
    exact hYZ0 y
  · intro t y
    rw [hXZtime t y]
    exact hXZ0 y

/--
The narrowed initial directional payload still exposes its previous witness
through the initial-time connection-term source.
-/
theorem stationary_zero_riemann_curvature_construction_initial_directional_covariant_derivative_normal_representatives_of_initial_directional_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialDirectionalCovariantDerivativeNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Xext Yext = 0 ∧
          stationary_zero_riemann_curvature_construction_connection_term_current_api
            metric identifiesDerivative identifiesRicci
            curvatureConstructionAtTime 0 (x := x) Yext Xext = 0 :=
  stationary_zero_riemann_curvature_construction_initial_directional_covariant_derivative_normal_representatives_of_initial_time_connection_term_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    initialDirectionalCovariantDerivativeNormalRepresentativeAtTime.initialTimeConnectionTermNormalRepresentativeAtTime

/--
Directional covariant-derivative normal representative data for the
stationary-zero curvature construction commutator.

This payload now stores the stricter initial directional source.  The old
existential-time mixed terms are recovered by choosing the initial time slice.
-/
structure StationaryZeroRiemannCurvatureConstructionDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  initialDirectionalCovariantDerivativeNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionInitialDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Initial directional covariant-derivative normal representatives supply the
previous directional witness by choosing `t = 0` for the mixed terms.
-/
theorem stationary_zero_riemann_curvature_construction_directional_covariant_derivative_normal_representatives_of_initial_directional_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (initialDirectionalCovariantDerivativeNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionInitialDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Yext Xext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_initial_directional_covariant_derivative_normal_representatives_of_initial_directional_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      initialDirectionalCovariantDerivativeNormalRepresentativeAtTime X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ, hXZ, hXY, hYX⟩
  exact
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ, hXZ, ⟨0, hXY, hYX⟩⟩

/--
The narrowed directional payload still exposes its previous representative
witness through the initial directional source.
-/
theorem stationary_zero_riemann_curvature_construction_directional_covariant_derivative_normal_representatives_of_directional_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (directionalCovariantDerivativeNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Yext Xext = 0 :=
  stationary_zero_riemann_curvature_construction_directional_covariant_derivative_normal_representatives_of_initial_directional_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    directionalCovariantDerivativeNormalRepresentativeAtTime.initialDirectionalCovariantDerivativeNormalRepresentativeAtTime

/--
Covariant-derivative normal representative data for the stationary-zero
curvature construction commutator.

This payload now stores the stricter directional covariant-derivative normal
source.  The old pointwise representative witness is recovered by specializing
the selected connection term to the exact ordered pairs used by the route.
-/
structure StationaryZeroRiemannCurvatureConstructionCovariantDerivativeNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  directionalCovariantDerivativeNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Pointwise connection-normal representative data for the stationary-zero
curvature construction commutator.

This payload now stores the stricter covariant-derivative normal source.  The
old pointwise representative witness is recovered by specializing the generic
selected-connection term to the ordered pairs appearing in the commutator
route.
-/
structure StationaryZeroRiemannCurvatureConstructionPointwiseConnectionNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  covariantDerivativeNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionCovariantDerivativeNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Covariant-derivative normal representatives supply the previous pointwise
connection-normal witness by specializing the generic connection term.
-/
theorem stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_covariant_derivative_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (covariantDerivativeNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionCovariantDerivativeNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 := by
  intro x X Y Z
  let directionalCovariantDerivativeNormalRepresentativeAtTime :=
    covariantDerivativeNormalRepresentativeAtTime.directionalCovariantDerivativeNormalRepresentativeAtTime
  rcases
    stationary_zero_riemann_curvature_construction_directional_covariant_derivative_normal_representatives_of_directional_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      directionalCovariantDerivativeNormalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ, hXZ, hMixed⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      ?_, ?_, ?_⟩
  · intro t y
    simpa [
      stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_term_current_api
    ] using hYZ t y
  · intro t y
    simpa [
      stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api,
      stationary_zero_riemann_curvature_construction_connection_term_current_api
    ] using hXZ t y
  · rcases hMixed with ⟨t0, hXY, hYX⟩
    refine ⟨t0, ?_, ?_⟩
    · simpa [
        stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api,
        stationary_zero_riemann_curvature_construction_connection_term_current_api
      ] using hXY
    · simpa [
        stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api,
        stationary_zero_riemann_curvature_construction_connection_term_current_api
      ] using hYX

/--
Directional covariant-derivative normal representatives supply the previous
pointwise connection-normal witness through the covariant-derivative wrapper.
-/
theorem stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_directional_covariant_derivative_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (directionalCovariantDerivativeNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionDirectionalCovariantDerivativeNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 :=
  stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_covariant_derivative_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    { directionalCovariantDerivativeNormalRepresentativeAtTime :=
        directionalCovariantDerivativeNormalRepresentativeAtTime }

/--
The narrowed pointwise connection-normal payload still exposes its previous
representative witness through the stricter covariant-derivative normal source.
-/
theorem stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_pointwise_connection_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (pointwiseConnectionNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionPointwiseConnectionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Yext Zext = 0) ∧
          (∀ (t : ℝ) (y : M),
            stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := y) Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 :=
  stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_covariant_derivative_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    pointwiseConnectionNormalRepresentativeAtTime.covariantDerivativeNormalRepresentativeAtTime

/--
Torsion-normal representative data for the stationary-zero curvature
construction commutator.

This payload now stores the stricter pointwise connection-normal source.  The
old torsion-normal representative witness is recovered by function
extensionality on the inner connection fields.
-/
structure StationaryZeroRiemannCurvatureConstructionTorsionNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  pointwiseConnectionNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionPointwiseConnectionNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Pointwise connection-normal representatives supply the previous torsion-normal
representative witness by converting pointwise inner-connection vanishing into
field-level zero equations.
-/
theorem stationary_zero_riemann_curvature_construction_torsion_normal_representatives_of_pointwise_connection_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (pointwiseConnectionNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionPointwiseConnectionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_pointwise_connection_normal_representatives_of_pointwise_connection_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      pointwiseConnectionNormalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYZ, hXZ, hMixed⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      ?_, ?_, hMixed⟩
  · intro t
    funext y
    simpa [
      stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api,
      stationary_zero_riemann_curvature_construction_commutator_YZ_pointwise_inner_connection_term_current_api
    ] using hYZ t y
  · intro t
    funext y
    simpa [
      stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api,
      stationary_zero_riemann_curvature_construction_commutator_XZ_pointwise_inner_connection_term_current_api
    ] using hXZ t y

/--
The narrowed torsion-normal payload still exposes its previous representative
witness through the stricter pointwise connection-normal source.
-/
theorem stationary_zero_riemann_curvature_construction_torsion_normal_representatives_of_torsion_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (torsionNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionTorsionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Xext Zext = 0) ∧
          ∃ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 ∧
            stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext = 0 :=
  stationary_zero_riemann_curvature_construction_torsion_normal_representatives_of_pointwise_connection_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    torsionNormalRepresentativeAtTime.pointwiseConnectionNormalRepresentativeAtTime

/--
Parallel-normal representative data for the stationary-zero curvature
construction commutator.

This payload now stores the stricter torsion-normal source.  The old
parallel-normal representative witness is recovered by the torsion-free
identity for the constructed connection.
-/
structure StationaryZeroRiemannCurvatureConstructionParallelNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  torsionNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionTorsionNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Torsion-normal representatives supply the previous parallel-normal
representative witness.  The bracket component follows from the stored
mixed-connection zero equations and the torsion-free identity for the
constructed connection.
-/
theorem stationary_zero_riemann_curvature_construction_parallel_normal_representatives_of_torsion_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (torsionNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionTorsionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Xext Zext = 0) ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_torsion_normal_representatives_of_torsion_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      torsionNormalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYinner, hXinner, hMixed⟩
  rcases hMixed with ⟨t0, hXY, hYX⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYinner, hXinner, ?_⟩
  let metricCompatibleConnectionAtTime :=
    curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
  let torsionFreeConnectionAtTime :=
    metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
  let connectionAtTime :=
    torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
  have htorsion : (connectionAtTime t0).torsion = 0 :=
    torsionFreeConnectionAtTime.torsion_eq_zero t0
  have hbracket :
      connectionAtTime t0 Yext x (Xext x) -
          connectionAtTime t0 Xext x (Yext x) =
        VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x :=
    ((connectionAtTime t0).torsion_eq_zero_iff.mp htorsion) hXdiff hYdiff
  have hXY' : connectionAtTime t0 Yext x (Xext x) = 0 := by
    simpa [stationary_zero_riemann_curvature_construction_commutator_XY_mixed_connection_term_current_api,
      metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
      connectionAtTime] using hXY
  have hYX' : connectionAtTime t0 Xext x (Yext x) = 0 := by
    simpa [stationary_zero_riemann_curvature_construction_commutator_YX_mixed_connection_term_current_api,
      metricCompatibleConnectionAtTime, torsionFreeConnectionAtTime,
      connectionAtTime] using hYX
  rw [hXY', hYX'] at hbracket
  simpa using hbracket.symm

/--
The narrowed parallel-normal payload still exposes its previous representative
witness through the stricter torsion-normal source.
-/
theorem stationary_zero_riemann_curvature_construction_parallel_normal_representatives_of_parallel_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (parallelNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionParallelNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t Xext Zext = 0) ∧
          VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x = 0 :=
  stationary_zero_riemann_curvature_construction_parallel_normal_representatives_of_torsion_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    parallelNormalRepresentativeAtTime.torsionNormalRepresentativeAtTime

/--
Normal-representative data for the stationary-zero curvature construction
commutator.

This is the concrete local differential-geometric obligation below the
commutator frontier: for each tangent-vector triple, choose smooth vector-field
representatives at the point such that the three connection terms in the
curvature-construction commutator vanish.  It is narrower than asking those
terms to vanish for every smooth representative.
-/
structure StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  parallelNormalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionParallelNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
Parallel-normal representatives supply the previous normal-representative
connection-term vanishing witness.
-/
theorem stationary_zero_riemann_curvature_construction_normal_representatives_connection_terms_eq_zero_of_parallel_normal_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (parallelNormalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionParallelNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0) ∧
          ∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_parallel_normal_representatives_of_parallel_normal_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      parallelNormalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hYinner, hXinner, hBracket⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      ?_, ?_, ?_⟩
  · intro t
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    change
      connectionAtTime t
        (stationary_zero_riemann_curvature_construction_commutator_Y_inner_connection_field_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t Yext Zext)
        x (Xext x) = 0
    rw [hYinner t]
    simp
  · intro t
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    change
      connectionAtTime t
        (stationary_zero_riemann_curvature_construction_commutator_X_inner_connection_field_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t Xext Zext)
        x (Yext x) = 0
    rw [hXinner t]
    simp
  · intro t
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    change
      connectionAtTime t Zext x
        (VectorField.mlieBracket ThreeManifoldModelWithCorners Xext Yext x) = 0
    rw [hBracket]
    simp

/--
The normal-representative payload still exposes its connection-term vanishing
witness through the stricter parallel-normal source.
-/
theorem stationary_zero_riemann_curvature_construction_normal_representatives_connection_terms_eq_zero_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0) ∧
          (∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0) ∧
          ∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0 :=
  stationary_zero_riemann_curvature_construction_normal_representatives_connection_terms_eq_zero_of_parallel_normal_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    normalRepresentativeAtTime.parallelNormalRepresentativeAtTime

/--
Normal representatives supply the existential smooth tangent-vector-field
extension witness by applying the normal-representative payload to `(X, 0, 0)`.
-/
theorem stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ Xext : (y : M) → TangentSpace ThreeManifoldModelWithCorners y,
        Xext x = X ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x := by
  intro x X
  rcases
    stationary_zero_riemann_curvature_construction_normal_representatives_connection_terms_eq_zero_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime
      X 0 0 with
    ⟨Xext, _Yext, _Zext, hX, _hY, _hZ, hXdiff, _hYdiff, _hZdiff,
      _hFirst, _hSecond, _hBracket⟩
  exact ⟨Xext, hX, hXdiff⟩

/--
Normal representatives supply the narrowed standalone smooth
tangent-vector-field extension data.
-/
noncomputable def stationary_zero_tangent_vector_field_extension_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M) :=
  stationary_zero_tangent_vector_field_extension_data_of_extension_exists_current_api
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime)

/--
The raw tangent-vector-field representative selected from normal
representatives has the prescribed value at its base point.
-/
theorem stationary_zero_tangent_vector_field_raw_extension_value_at_point_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x) :
    ((stationary_zero_tangent_vector_field_extension_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime).valueExtensionAtPoint.rawExtensionAtPoint.tangent_vector_field_raw_extension
        X).Xext x = X :=
  (stationary_zero_tangent_vector_field_extension_of_normal_representatives_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    normalRepresentativeAtTime).valueExtensionAtPoint.valueAtPoint.tangent_vector_field_value_at_point X

/--
The raw tangent-vector-field representative selected from normal
representatives carries the smoothness evidence at its base point.
-/
theorem stationary_zero_tangent_vector_field_raw_extension_smoothAt_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X : TangentSpace ThreeManifoldModelWithCorners x) :
    StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
      ((stationary_zero_tangent_vector_field_extension_of_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        normalRepresentativeAtTime).valueExtensionAtPoint.rawExtensionAtPoint.tangent_vector_field_raw_extension
          X).Xext x :=
  (stationary_zero_tangent_vector_field_extension_of_normal_representatives_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    normalRepresentativeAtTime).smoothnessAtPoint.tangent_vector_field_extension_smoothAt X

/--
The commuting-pair representative selected from normal representatives has
first vector-field value `X` at the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_eq_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y).Xext x = X :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_eq_of_tangent_vector_field_extension_exists_current_api
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y

/--
The commuting-pair representative selected from normal representatives has
second vector-field value `Y` at the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_eq_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
      (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
        normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y).Yext x = Y :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_eq_of_tangent_vector_field_extension_exists_current_api
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y

/--
The first commuting-pair vector field selected from normal representatives is
smooth at the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_smoothAt_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
      ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y).Xext x :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Xext_smoothAt_of_tangent_vector_field_extension_exists_current_api
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y

/--
The second commuting-pair vector field selected from normal representatives is
smooth at the base point.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_smoothAt_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi
      ((stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y).Yext x :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_Yext_smoothAt_of_tangent_vector_field_extension_exists_current_api
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y

/--
For commuting-pair representatives selected from normal representatives, the
forward connection coefficient can be evaluated using the requested base vector
`X` instead of the selected representative value `Xext x`.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x) :
    let pair :=
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) =
      connectionAtTime 0 pair.Yext x X :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_eq_base_vector_expression_of_tangent_vector_field_extension_exists_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y

/--
For commuting-pair representatives selected from normal representatives, zero
of the base-vector coefficient expression gives zero of the selected forward
coefficient expression.
-/
theorem stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime)
    {x : M} (X Y : TangentSpace ThreeManifoldModelWithCorners x)
    (baseVectorConnectionCoefficientZeroAtTime :
      let pair :=
        (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
          (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
            metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
            normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y
      let metricCompatibleConnectionAtTime :=
        curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
      let torsionFreeConnectionAtTime :=
        metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
      let connectionAtTime :=
        torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
      connectionAtTime 0 pair.Yext x X = 0) :
    let pair :=
      (stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_representative_data_of_tangent_vector_field_extension_exists_current_api
        (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          normalRepresentativeAtTime)).initial_time_commuting_pair_representatives X Y
    let metricCompatibleConnectionAtTime :=
      curvatureConstructionAtTime.connectionTheoryAtTime.metricCompatibleConnectionAtTime
    let torsionFreeConnectionAtTime :=
      metricCompatibleConnectionAtTime.torsionFreeConnectionAtTime
    let connectionAtTime :=
      torsionFreeConnectionAtTime.uniqueConnectionAtTime.connectionAtTime
    connectionAtTime 0 pair.Yext x (pair.Xext x) = 0 :=
  stationary_zero_riemann_curvature_construction_initial_time_commuting_pair_forward_connection_coefficient_expression_zero_of_base_vector_expression_zero_of_tangent_vector_field_extension_exists_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    (stationary_zero_tangent_vector_field_extension_exists_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime) X Y
    baseVectorConnectionCoefficientZeroAtTime

/--
Normal representatives supply the combined commutator-extension witness used to
apply the stored curvature-construction commutator formula.
-/
theorem stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          ∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_normal_representatives_connection_terms_eq_zero_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      hFirst, hSecond, hBracket⟩
  refine
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff, ?_⟩
  intro t
  have hFirstAt := hFirst t
  have hSecondAt := hSecond t
  have hBracketAt := hBracket t
  change
    stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) Xext Yext Zext -
      stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) Xext Yext Zext -
      stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0
  rw [hFirstAt, hSecondAt, hBracketAt]
  simp

/--
Connection-term vanishing data for the stationary-zero curvature construction
commutator.

This is the next frontier below commutator RHS vanishing: after smooth
representatives are supplied, each of the three connection terms appearing in
the construction commutator must vanish.
-/
structure StationaryZeroRiemannCurvatureConstructionConnectionTermVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  first_connection_term_eq_zero :
    ∀ {x : M}
      (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi X x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Y x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Z x →
      ∀ t : ℝ,
        stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) X Y Z = 0
  second_connection_term_eq_zero :
    ∀ {x : M}
      (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi X x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Y x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Z x →
      ∀ t : ℝ,
        stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) X Y Z = 0
  bracket_connection_term_eq_zero :
    ∀ {x : M}
      (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi X x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Y x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Z x →
      ∀ t : ℝ,
        stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) X Y Z = 0

/--
Vanishing of the three connection terms supplies vanishing of the full
curvature-construction commutator RHS.
-/
theorem stationary_zero_riemann_curvature_construction_commutator_rhs_eq_zero_of_connection_terms_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (connectionTermVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionConnectionTermVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M}
      (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi X x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Y x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Z x →
      ∀ t : ℝ,
        stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) X Y Z = 0 := by
  intro x X Y Z hX hY hZ t
  have hFirst :=
    connectionTermVanishingAtTime.first_connection_term_eq_zero
      X Y Z hX hY hZ t
  have hSecond :=
    connectionTermVanishingAtTime.second_connection_term_eq_zero
      X Y Z hX hY hZ t
  have hBracket :=
    connectionTermVanishingAtTime.bracket_connection_term_eq_zero
      X Y Z hX hY hZ t
  change
    stationary_zero_riemann_curvature_construction_commutator_first_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) X Y Z -
      stationary_zero_riemann_curvature_construction_commutator_second_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) X Y Z -
      stationary_zero_riemann_curvature_construction_commutator_bracket_connection_term_current_api
        metric identifiesDerivative identifiesRicci
        curvatureConstructionAtTime t (x := x) X Y Z = 0
  rw [hFirst, hSecond, hBracket]
  simp

/--
Commutator right-hand-side vanishing data for the stationary-zero curvature
route.

This now stores the stricter connection-term vanishing payload; the full
commutator RHS zero identity is recovered by subtracting the three zero terms.
-/
structure StationaryZeroRiemannCurvatureConstructionCommutatorRhsVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  connectionTermVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionConnectionTermVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
The commutator RHS vanishing payload still exposes the full RHS zero identity
from its narrower connection-term vanishing data.
-/
theorem stationary_zero_riemann_curvature_construction_commutator_rhs_eq_zero_of_rhs_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (commutatorRhsVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionCommutatorRhsVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M}
      (X Y Z : (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi X x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Y x →
      StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Z x →
      ∀ t : ℝ,
        stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) X Y Z = 0 :=
  stationary_zero_riemann_curvature_construction_commutator_rhs_eq_zero_of_connection_terms_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    commutatorRhsVanishingAtTime.connectionTermVanishingAtTime

/--
Smooth tangent-vector-field extension data and commutator RHS vanishing supply
the combined extension-plus-zero witness previously stored as the commutator
frontier.
-/
theorem stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_extension_and_rhs_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (vectorFieldExtensionAtPoint :
      StationaryZeroTangentVectorFieldExtensionDataCurrentApi (M := M))
    (commutatorRhsVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionCommutatorRhsVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          ∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0 := by
  intro x X Y Z
  rcases
    stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
      vectorFieldExtensionAtPoint X with
    ⟨Xext, hX, hXdiff⟩
  rcases
    stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
      vectorFieldExtensionAtPoint Y with
    ⟨Yext, hY, hYdiff⟩
  rcases
    stationary_zero_tangent_vector_field_extension_of_tangent_vector_field_extension_data_current_api
      vectorFieldExtensionAtPoint Z with
    ⟨Zext, hZ, hZdiff⟩
  exact
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff,
      fun t =>
        stationary_zero_riemann_curvature_construction_commutator_rhs_eq_zero_of_rhs_vanishing_current_api
          metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
          commutatorRhsVanishingAtTime
          Xext Yext Zext hXdiff hYdiff hZdiff t⟩

/--
Construction-commutator vanishing data for the stationary-zero curvature
route.

This now stores the local normal-representative payload.  The standalone
tangent-vector extension data and commutator RHS zero identity are both derived
from that chosen-representative source.
-/
structure StationaryZeroRiemannCurvatureConstructionCommutatorVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  normalRepresentativeAtTime :
    StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
The factored commutator vanishing payload still exposes the combined
extension-plus-zero witness used to apply the stored construction commutator
formula.
-/
theorem stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_commutator_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvatureCommutatorVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionCommutatorVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      ∃ (Xext Yext Zext :
          (y : M) → TangentSpace ThreeManifoldModelWithCorners y),
        Xext x = X ∧
          Yext x = Y ∧
          Zext x = Z ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Xext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Yext x ∧
          StationaryZeroSmoothTangentVectorFieldAtPointCurrentApi Zext x ∧
          ∀ t : ℝ,
            stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
              metric identifiesDerivative identifiesRicci
              curvatureConstructionAtTime t (x := x) Xext Yext Zext = 0 :=
  stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_normal_representatives_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    curvatureCommutatorVanishingAtTime.normalRepresentativeAtTime

/--
Commutator-extension vanishing supplies pointwise vanishing for the concrete
Riemann-curvature construction.
-/
theorem stationary_zero_riemann_curvature_construction_apply_eq_zero_of_commutator_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvatureCommutatorVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionCommutatorVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      curvatureConstructionAtTime.curvatureAtTime t x X Y Z = 0 := by
  intro t x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_commutator_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      curvatureCommutatorVanishingAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff, hcomm⟩
  rw [← hX, ← hY, ← hZ]
  calc
    curvatureConstructionAtTime.curvatureAtTime
        t x (Xext x) (Yext x) (Zext x) =
        stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) Xext Yext Zext := by
      simpa [stationary_zero_riemann_curvature_construction_commutator_rhs_current_api]
        using
          curvatureConstructionAtTime.curvature_eq_commutator
            t (X := Xext) (Y := Yext) (Z := Zext) (x := x)
            hXdiff hYdiff hZdiff
    _ = 0 := hcomm t

/--
Normal-representative data directly supplies pointwise vanishing for the
concrete Riemann-curvature construction, without routing through the
commutator wrapper payload.
-/
theorem stationary_zero_riemann_curvature_construction_apply_eq_zero_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      curvatureConstructionAtTime.curvatureAtTime t x X Y Z = 0 := by
  intro t x X Y Z
  rcases
    stationary_zero_riemann_curvature_construction_commutator_extension_eq_zero_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime
      X Y Z with
    ⟨Xext, Yext, Zext, hX, hY, hZ, hXdiff, hYdiff, hZdiff, hcomm⟩
  rw [← hX, ← hY, ← hZ]
  calc
    curvatureConstructionAtTime.curvatureAtTime
        t x (Xext x) (Yext x) (Zext x) =
        stationary_zero_riemann_curvature_construction_commutator_rhs_current_api
          metric identifiesDerivative identifiesRicci
          curvatureConstructionAtTime t (x := x) Xext Yext Zext := by
      simpa [stationary_zero_riemann_curvature_construction_commutator_rhs_current_api]
        using
          curvatureConstructionAtTime.curvature_eq_commutator
            t (X := Xext) (Y := Yext) (Z := Zext) (x := x)
            hXdiff hYdiff hZdiff
    _ = 0 := hcomm t

/--
Normal-representative data directly supplies the field-level zero identity for
the concrete Riemann-curvature construction.
-/
theorem stationary_zero_riemann_curvature_construction_field_eq_zero_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    curvatureConstructionAtTime.curvatureAtTime =
      (fun _t _x => 0 :
        TimeDependentRiemannCurvatureTensorField
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))) := by
  funext t x
  ext X Y Z
  exact
    stationary_zero_riemann_curvature_construction_apply_eq_zero_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      normalRepresentativeAtTime t X Y Z

/--
Pointwise stationary-zero Riemann-curvature vanishing for the concrete
curvature field stored by a Riemann-curvature construction.

This is the next frontier below field-level vanishing: it asks for the
constructed curvature endomorphism to evaluate to zero at each time, point, and
tangent-vector triple.
-/
structure StationaryZeroRiemannCurvatureConstructionPointwiseVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  curvatureCommutatorVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionCommutatorVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
The pointwise vanishing payload still exposes the pointwise zero identity by
applying the construction commutator formula to its narrower commutator data.
-/
theorem stationary_zero_riemann_curvature_construction_apply_eq_zero_of_pointwise_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvaturePointwiseVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionPointwiseVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      curvatureConstructionAtTime.curvatureAtTime t x X Y Z = 0 :=
  stationary_zero_riemann_curvature_construction_apply_eq_zero_of_commutator_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    curvaturePointwiseVanishingAtTime.curvatureCommutatorVanishingAtTime

/--
Pointwise stationary-zero Riemann-curvature vanishing supplies the field-level
zero identity for the concrete curvature field stored by the construction.
-/
theorem stationary_zero_riemann_curvature_construction_field_eq_zero_of_pointwise_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvaturePointwiseVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionPointwiseVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    curvatureConstructionAtTime.curvatureAtTime =
      (fun _t _x => 0 :
        TimeDependentRiemannCurvatureTensorField
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))) := by
  funext t x
  ext X Y Z
  exact
    stationary_zero_riemann_curvature_construction_apply_eq_zero_of_pointwise_current_api
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
      curvaturePointwiseVanishingAtTime t X Y Z

/--
Curvature-construction-level stationary-zero Riemann-curvature vanishing data.

This is the current deepest analytic field identity: the actual
`curvatureAtTime` stored by a concrete Riemann-curvature construction must be
the zero time-dependent Riemann tensor field.
-/
structure StationaryZeroRiemannCurvatureConstructionFieldVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  curvaturePointwiseVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionPointwiseVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci curvatureConstructionAtTime

/--
The construction-level vanishing payload still exposes the field-level
curvature identity by extensionality from its pointwise vanishing data.
-/
theorem stationary_zero_riemann_curvature_construction_field_eq_zero_of_construction_field_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (curvatureConstructionAtTime :
      RiemannCurvatureTensorConstructionData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvatureConstructionFieldVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionFieldVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci curvatureConstructionAtTime) :
    curvatureConstructionAtTime.curvatureAtTime =
      (fun _t _x => 0 :
        TimeDependentRiemannCurvatureTensorField
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci))) :=
  stationary_zero_riemann_curvature_construction_field_eq_zero_of_pointwise_current_api
    metric identifiesDerivative identifiesRicci curvatureConstructionAtTime
    curvatureConstructionFieldVanishingAtTime.curvaturePointwiseVanishingAtTime

/--
Field-level stationary-zero Riemann-curvature vanishing data.

This is the point where the analytic route now waits for the actual constructed
Riemann tensor to be identified with the zero tensor field.  It is narrower
than the previous raw pointwise equality: all pointwise vanishing consequences
are derived from this single tensor-field identity below.
-/
structure StationaryZeroRiemannCurvatureTensorFieldVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) where
  curvatureAtTime_eq_zero :
    secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime =
      (fun _t _x => 0 :
        TimeDependentRiemannCurvatureTensorField
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)))

/--
A field-level zero Riemann-curvature identity supplies the pointwise vanishing
formula used by the Ricci contraction constructor.
-/
theorem stationary_zero_riemann_curvature_eq_zero_of_tensor_field_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvatureTensorVanishingAtTime :
      StationaryZeroRiemannCurvatureTensorFieldVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci secondBianchiAtTime) :
    let curvatureAtTime :=
      secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
    ∀ (t : ℝ) {x : M} (X Y Z : TangentSpace ThreeManifoldModelWithCorners x),
      curvatureAtTime t x X Y Z = 0 := by
  dsimp
  intro t x X Y Z
  rw [curvatureTensorVanishingAtTime.curvatureAtTime_eq_zero]
  rfl

/--
Curvature-construction-level zero data supplies the second-Bianchi-nested
tensor-field vanishing payload.
-/
theorem stationary_zero_riemann_curvature_tensor_field_vanishing_of_construction_field_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (curvatureConstructionFieldVanishingAtTime :
      StationaryZeroRiemannCurvatureConstructionFieldVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci
        secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureTensorFieldVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci secondBianchiAtTime where
  curvatureAtTime_eq_zero :=
    stationary_zero_riemann_curvature_construction_field_eq_zero_of_construction_field_vanishing_current_api
      metric identifiesDerivative identifiesRicci
      secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime
      curvatureConstructionFieldVanishingAtTime

/--
Normal-representative data for the second-Bianchi-nested construction directly
supplies the tensor-field vanishing payload.
-/
theorem stationary_zero_riemann_curvature_tensor_field_vanishing_of_normal_representatives_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (secondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci)))
    (normalRepresentativeAtTime :
      StationaryZeroRiemannCurvatureConstructionNormalRepresentativeDataCurrentApi
        metric identifiesDerivative identifiesRicci
        secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime) :
    StationaryZeroRiemannCurvatureTensorFieldVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci secondBianchiAtTime where
  curvatureAtTime_eq_zero :=
    stationary_zero_riemann_curvature_construction_field_eq_zero_of_normal_representatives_current_api
      metric identifiesDerivative identifiesRicci
      secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime
      normalRepresentativeAtTime

/--
Stationary-zero Riemann-curvature vanishing data for the constructed curvature
tensor.

This is the next honest payload below Ricci tensor contraction formula data:
it records the Riemann-curvature data through second Bianchi together with a
curvature-construction-level zero identity for the constructed tangent-valued
Riemann tensor. The Ricci trace functional and curvature endomorphism are then
reconstructed as zero data below.
-/
structure StationaryZeroRiemannCurvatureVanishingDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))) where
  secondBianchiAtTime :
    RiemannCurvatureSecondBianchiData
      (metric_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci))
  curvatureConstructionFieldVanishingAtTime :
    StationaryZeroRiemannCurvatureConstructionFieldVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci
      secondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime

/--
The stationary-zero Riemann-curvature vanishing payload still supplies the
second-Bianchi-nested tensor-field vanishing payload by projection from its
curvature-construction-level identity.
-/
theorem stationary_zero_riemann_curvature_tensor_field_vanishing_of_riemann_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (riemannCurvatureVanishingAtTime :
      StationaryZeroRiemannCurvatureVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    StationaryZeroRiemannCurvatureTensorFieldVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci
      riemannCurvatureVanishingAtTime.secondBianchiAtTime :=
  stationary_zero_riemann_curvature_tensor_field_vanishing_of_construction_field_vanishing_current_api
    metric identifiesDerivative identifiesRicci
    riemannCurvatureVanishingAtTime.secondBianchiAtTime
    riemannCurvatureVanishingAtTime.curvatureConstructionFieldVanishingAtTime

/--
Concrete analytic production data still needed for the stationary zero flow.

This is narrower than `AnalyticFoundationSubobligationsPayload`: the
Levi-Civita, curvature, basic metric regularity, metric derivative,
initial-compatibility, DeTurck gauge, short-time, continuation, and regularity
fields are produced by the existing analytic production bridge from these
concrete data objects, while the stationary zero Ricci-flow equation and
evolution identity candidates are derived internally from the stationary zero
route and the Riemann-vanishing payload. The Ricci tensor contraction formula,
scalar-contraction formula, and scalar-curvature theory are reconstructed using
zero trace data for the stationary zero curvature data. The DeTurck
equation-to-pullback chain is stored only once, in
`pullbackIdentityAtTime`; the intermediate vector-field, equation,
linearization, parabolic, fixed-point, short-time, regularity, and ODE data are
read from that chain.
-/
structure StationaryZeroAnalyticFoundationProductionDataCurrentApi
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric))) where
  riemannCurvatureVanishingAtTime :
    StationaryZeroRiemannCurvatureVanishingDataCurrentApi
      metric identifiesDerivative identifiesRicci
  pullbackIdentityAtTime :
    DeTurckPullbackEquationIdentityData
      (stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci)
  uniquenessByInitialMetric :
    ∀ comparisonFlow : RicciFlowData ThreeManifoldModelWithCorners n M,
      (metric_of_ricci_flow_data comparisonFlow).metricAtTime 0 =
          (metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)).metricAtTime 0 →
        metric_of_ricci_flow_data comparisonFlow =
          metric_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)

/--
Stationary-zero Riemann-curvature vanishing data supplies the Ricci tensor
contraction-formula payload by using the zero curvature endomorphism and zero
trace functional.
-/
noncomputable def stationary_zero_ricci_contraction_formula_data_of_riemann_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (riemannCurvatureVanishingAtTime :
      StationaryZeroRiemannCurvatureVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    RicciTensorContractionFormulaData
      (curvature_data_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) where
  secondBianchiAtTime := riemannCurvatureVanishingAtTime.secondBianchiAtTime
  traceAtTime := fun _ _ _ => 0
  curvatureEndomorphismAtTime := fun _ _ _ _ => 0
  curvature_endomorphism_eq_riemann := fun t {x} X Y Z => by
    symm
    exact
      stationary_zero_riemann_curvature_eq_zero_of_tensor_field_vanishing_current_api
        metric identifiesDerivative identifiesRicci
        riemannCurvatureVanishingAtTime.secondBianchiAtTime
        (stationary_zero_riemann_curvature_tensor_field_vanishing_of_riemann_vanishing_current_api
          metric identifiesDerivative identifiesRicci riemannCurvatureVanishingAtTime) t Z X Y
  ricci_eq_trace_curvature_endomorphism := by
    intro t x X Y
    rfl

/--
Ricci contraction-formula data supplies the stationary-zero scalar-contraction
formula payload by pairing it with the zero scalar trace functional.
-/
noncomputable def stationary_zero_scalar_contraction_formula_data_of_ricci_contraction_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData
        (curvature_data_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    ScalarCurvatureContractionFormulaData
      (curvature_data_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) where
  ricciContractionFormulaAtTime := ricciContractionFormulaAtTime
  traceAtTime := fun _ _ _ => 0
  scalar_eq_trace_ricci := by
    intro t x
    rfl

/--
Stationary-zero Riemann-curvature vanishing data supplies the scalar-contraction
formula through the derived Ricci contraction formula.
-/
noncomputable def stationary_zero_scalar_contraction_formula_data_of_riemann_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (riemannCurvatureVanishingAtTime :
      StationaryZeroRiemannCurvatureVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ScalarCurvatureContractionFormulaData
      (curvature_data_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  stationary_zero_scalar_contraction_formula_data_of_ricci_contraction_formula_current_api
    metric identifiesDerivative identifiesRicci
    (stationary_zero_ricci_contraction_formula_data_of_riemann_vanishing_current_api
      metric identifiesDerivative identifiesRicci riemannCurvatureVanishingAtTime)

/--
Ricci contraction-formula data supplies the stationary-zero scalar-curvature
theory payload through the reconstructed scalar-contraction formula and local
canonical contraction constructors.
-/
noncomputable def stationary_zero_scalar_curvature_theory_data_of_ricci_contraction_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData
        (curvature_data_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    ScalarCurvatureTheoryData
      (curvature_data_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  scalarCurvatureTheoryData_of_ricciContractionTheoryData
    (ricciContractionTheoryData_of_scalarContractionFormulaData
      (stationary_zero_scalar_contraction_formula_data_of_ricci_contraction_formula_current_api
        metric identifiesDerivative identifiesRicci ricciContractionFormulaAtTime))

/--
Stationary-zero Riemann-curvature vanishing data supplies the scalar-curvature
theory payload through the derived Ricci and scalar contraction formulas.
-/
noncomputable def stationary_zero_scalar_curvature_theory_data_of_riemann_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (riemannCurvatureVanishingAtTime :
      StationaryZeroRiemannCurvatureVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ScalarCurvatureTheoryData
      (curvature_data_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  stationary_zero_scalar_curvature_theory_data_of_ricci_contraction_formula_current_api
    metric identifiesDerivative identifiesRicci
    (stationary_zero_ricci_contraction_formula_data_of_riemann_vanishing_current_api
      metric identifiesDerivative identifiesRicci riemannCurvatureVanishingAtTime)

/--
The Ricci contraction formula already contains the Riemann second-Bianchi data.
-/
noncomputable def stationary_zero_riemann_second_bianchi_data_of_ricci_contraction_formula_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (ricciContractionFormulaAtTime :
      RicciTensorContractionFormulaData
        (curvature_data_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci))) :
    RiemannCurvatureSecondBianchiData
      (metric_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  ricciContractionFormulaAtTime.secondBianchiAtTime

/--
Stationary-zero Riemann-curvature vanishing data exposes the underlying
Riemann second-Bianchi data needed by the downstream curvature-evolution
constructor.
-/
noncomputable def stationary_zero_riemann_second_bianchi_data_of_riemann_vanishing_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (riemannCurvatureVanishingAtTime :
      StationaryZeroRiemannCurvatureVanishingDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    RiemannCurvatureSecondBianchiData
      (metric_of_ricci_flow_data
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :=
  riemannCurvatureVanishingAtTime.secondBianchiAtTime

/--
Concrete stationary-zero production data supplies the full analytic
sub-obligation payload for the derived stationary zero Ricci flow.
-/
theorem stationary_zero_analytic_foundation_subobligations_payload_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    AnalyticFoundationSubobligationsPayload
      (stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci) := by
  let flow :=
    stationary_zero_ricci_flow_data_current_api
      metric identifiesDerivative identifiesRicci
  let odeAtTime := data.pullbackIdentityAtTime.odeAtTime
  let regularityAtTime := odeAtTime.regularityAtTime
  let shortTimeAtTime := regularityAtTime.shortTimeAtTime
  let fixedPointAtTime := shortTimeAtTime.fixedPointAtTime
  let linearTheoryAtTime := fixedPointAtTime.linearTheoryAtTime
  let strictParabolicAtTime := linearTheoryAtTime.strictParabolicAtTime
  let linearizationAtTime := strictParabolicAtTime.linearizationAtTime
  let ricciDeTurckEquationAtTime := linearizationAtTime.equationAtTime
  let zeroTwoTensorAtTime :
      ℝ → TangentCovariantTwoTensor ThreeManifoldModelWithCorners M :=
    fun _ => zero_tangent_covariant_two_tensor ThreeManifoldModelWithCorners M
  let zeroScalarAtTime : ℝ → M → ℝ := fun _ _ => 0
  let scalarCurvatureTheoryAtTime :
      ScalarCurvatureTheoryData
        (curvature_data_of_ricci_flow_data flow) :=
    stationary_zero_scalar_curvature_theory_data_of_riemann_vanishing_current_api
      metric identifiesDerivative identifiesRicci data.riemannCurvatureVanishingAtTime
  let riemannSecondBianchiAtTime :
      RiemannCurvatureSecondBianchiData
        (metric_of_ricci_flow_data flow) :=
    stationary_zero_riemann_second_bianchi_data_of_riemann_vanishing_current_api
      metric identifiesDerivative identifiesRicci data.riemannCurvatureVanishingAtTime
  let riemannCurvatureAtTime :
      TimeDependentRiemannCurvatureTensorField
        (metric_of_ricci_flow_data flow) :=
    riemannSecondBianchiAtTime.firstBianchiAtTime.curvatureSymmetryAtTime.curvatureConstructionAtTime.curvatureAtTime
  have production :=
    analyticProductionPackage_firstFortySeven_of_scalarCurvatureTheoryData_and_ricciFlowEquationVerification
      (flow := flow)
      scalarCurvatureTheoryAtTime
      (zero_ricci_flow_equation_verification identifiesDerivative identifiesRicci)
      odeAtTime.vectorFieldAtTime
      ricciDeTurckEquationAtTime
      linearizationAtTime
      strictParabolicAtTime
      linearTheoryAtTime
      fixedPointAtTime
      shortTimeAtTime
      regularityAtTime
      odeAtTime
      data.pullbackIdentityAtTime
      data.uniquenessByInitialMetric
      zeroTwoTensorAtTime
      zeroTwoTensorAtTime
      (by intro t; rfl)
      zeroScalarAtTime
      zeroScalarAtTime
      (by intro t; rfl)
      zeroScalarAtTime
      (by intro t x; exact le_rfl)
      zeroScalarAtTime
      zeroScalarAtTime
      (by intro t x; exact le_rfl)
      riemannSecondBianchiAtTime
      riemannCurvatureAtTime
      riemannCurvatureAtTime
      (by intro t; rfl)
  rw [analyticFoundationSubobligationsPayload_eq]
  tauto

/--
Concrete stationary-zero production data builds the analytic foundation package
for the derived stationary zero Ricci flow.
-/
noncomputable def stationary_zero_analytic_foundation_package_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M :=
  stationary_zero_ricci_flow_analytic_foundation_package
    metric identifiesRicci
    (stationary_zero_satisfies_ricci_flow_equation_current_api
      metric identifiesDerivative identifiesRicci)
    (stationary_zero_analytic_foundation_subobligations_payload_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data)

/--
The production-data package stores exactly the stationary zero Ricci-flow data
derived from the metric, zero derivative, and zero Ricci witnesses.
-/
@[simp] theorem stationary_zero_analytic_foundation_package_of_production_data_current_api_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ricci_flow_data_of_analytic_foundation_package
        (stationary_zero_analytic_foundation_package_of_production_data_current_api
          metric identifiesDerivative identifiesRicci data) =
      stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci :=
  stationary_zero_ricci_flow_analytic_foundation_package_eq
    metric identifiesRicci
    (stationary_zero_satisfies_ricci_flow_equation_current_api
      metric identifiesDerivative identifiesRicci)
    (stationary_zero_analytic_foundation_subobligations_payload_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data)

/--
The package built from stationary-zero production data supplies the analytic
foundation statement with equation boundary for the derived flow.
-/
theorem stationary_zero_analytic_foundation_with_equation_boundary_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    AnalyticFoundationWithEquationBoundaryStatement
      (stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci) :=
  analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
    metric identifiesDerivative identifiesRicci
    (stationary_zero_satisfies_ricci_flow_equation_current_api
      metric identifiesDerivative identifiesRicci)
    (stationary_zero_analytic_foundation_subobligations_payload_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data)

/--
The stationary-zero production package exposes the curvature-evolution field of
the analytic foundation package for the derived flow.
-/
theorem stationary_zero_analytic_foundation_curvature_evolution_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    HasCurvatureEvolutionEquations
      (stationary_zero_ricci_flow_data_current_api
        metric identifiesDerivative identifiesRicci) := by
  let package :=
    stationary_zero_analytic_foundation_package_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data
  have hflow :
      package.flow =
        stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci := by
    exact
      stationary_zero_analytic_foundation_package_of_production_data_current_api_eq
        metric identifiesDerivative identifiesRicci data
  have result :
      HasCurvatureEvolutionEquations
        (ricci_flow_data_of_analytic_foundation_package package) :=
    curvature_evolution_of_analytic_foundation_package package
  change HasCurvatureEvolutionEquations package.flow at result
  rw [hflow] at result
  exact result

/--
The analytic sub-obligation payload now exposes the final explicit curvature
evolution field.
-/
theorem analytic_foundation_subobligations_payload_curvature_evolution_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    AnalyticFoundationSubobligationsPayload flow →
      HasCurvatureEvolutionEquations flow := by
  intro h
  let package :=
    analytic_foundation_package_of_subobligations_payload flow h
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq flow h
  have result :
      HasCurvatureEvolutionEquations
        (ricci_flow_data_of_analytic_foundation_package package) :=
    curvature_evolution_of_analytic_foundation_package package
  change HasCurvatureEvolutionEquations package.flow at result
  rw [hflow] at result
  exact result

/--
For the actual three-manifold model, the stationary zero analytic-boundary route
now derives its Ricci-flow equation evidence internally from the supplied zero
metric-derivative and zero Ricci identifications.

The analytic sub-obligation payload remains an explicit hypothesis, but it is
attached to the derived stationary zero Ricci-flow data package rather than to a
caller-supplied equation witness.
-/
theorem three_manifold_stationary_zero_analytic_foundation_surface_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci)) :
    ∃ package :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ricci_flow_data_of_analytic_foundation_package package =
        stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci ∧
      AnalyticFoundationWithEquationBoundaryStatement
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) ∧
      (∀ t,
        metric_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t = metric) ∧
      (∀ t x (v w : TangentSpace ThreeManifoldModelWithCorners x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w = 0 ∧
        ricci_tensor_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x v w = 0 ∧
        scalar_curvature_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x = 0 ∧
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)) t x v w = 0 ∧
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data
              (stationary_zero_ricci_flow_data_current_api
                metric identifiesDerivative identifiesRicci)) t x v w) := by
  let derivedEquation :=
    stationary_zero_satisfies_ricci_flow_equation_current_api
      metric identifiesDerivative identifiesRicci
  refine
    ⟨stationary_zero_ricci_flow_analytic_foundation_package
      metric identifiesRicci derivedEquation subobligations, ?_, ?_, ?_, ?_⟩
  · exact
      stationary_zero_ricci_flow_analytic_foundation_package_eq
        metric identifiesRicci derivedEquation subobligations
  · exact
      analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
        metric identifiesDerivative identifiesRicci derivedEquation
        subobligations
  · intro t
    exact
      metric_at_time_of_stationary_zero_ricci_flow_data_eq
        metric identifiesRicci derivedEquation t
  · intro t x v w
    exact
      ⟨metric_time_derivative_at_time_apply_of_stationary_zero_ricci_flow_equation_boundary_package
          metric identifiesDerivative identifiesRicci derivedEquation t x v w,
        ricci_tensor_at_time_apply_of_stationary_zero_ricci_flow_data
          metric identifiesRicci derivedEquation t x v w,
        scalar_curvature_at_time_of_stationary_zero_ricci_flow_data_eq
          metric identifiesRicci derivedEquation t x,
        ricci_flow_rhs_tensor_apply_of_stationary_zero_ricci_flow_data
          metric identifiesRicci derivedEquation t x v w,
        equation_at_time_apply_of_equation_boundary_package_projection
          (stationary_zero_ricci_flow_equation_boundary_package
            metric identifiesDerivative identifiesRicci derivedEquation)
          t x v w⟩

/--
Concrete stationary-zero production data builds the analytic boundary package
without requiring the caller to provide the broad sub-obligation conjunction.
-/
theorem three_manifold_stationary_zero_analytic_foundation_surface_payload_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ∃ package :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ricci_flow_data_of_analytic_foundation_package package =
        stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci ∧
      AnalyticFoundationWithEquationBoundaryStatement
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) ∧
      (∀ t,
        metric_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t = metric) ∧
      (∀ t x (v w : TangentSpace ThreeManifoldModelWithCorners x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w = 0 ∧
        ricci_tensor_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x v w = 0 ∧
        scalar_curvature_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x = 0 ∧
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)) t x v w = 0 ∧
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data
              (stationary_zero_ricci_flow_data_current_api
                metric identifiesDerivative identifiesRicci)) t x v w) :=
  three_manifold_stationary_zero_analytic_foundation_surface_payload
    metric identifiesDerivative identifiesRicci
    (stationary_zero_analytic_foundation_subobligations_payload_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data)

/--
Compact production-data analytic payload: the same stationary-zero production
data constructs the analytic foundation package, identifies its stored flow
with the derived stationary-zero Ricci flow, supplies the equation-boundary
statement, and exposes curvature evolution for that derived flow.
-/
theorem stationary_zero_analytic_foundation_package_boundary_and_curvature_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ∃ package :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ricci_flow_data_of_analytic_foundation_package package =
        stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci ∧
      AnalyticFoundationWithEquationBoundaryStatement
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) ∧
      HasCurvatureEvolutionEquations
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) := by
  exact
    ⟨ stationary_zero_analytic_foundation_package_of_production_data_current_api
        metric identifiesDerivative identifiesRicci data
    , stationary_zero_analytic_foundation_package_of_production_data_current_api_eq
        metric identifiesDerivative identifiesRicci data
    , stationary_zero_analytic_foundation_with_equation_boundary_of_production_data_current_api
        metric identifiesDerivative identifiesRicci data
    , stationary_zero_analytic_foundation_curvature_evolution_of_production_data_current_api
        metric identifiesDerivative identifiesRicci data
    ⟩

/--
Concrete stationary-zero production data supplies the full analytic surface
payload, including the stored package, equation boundary, pointwise stationary
zero equations, and curvature-evolution evidence for the same derived flow.
-/
theorem three_manifold_stationary_zero_analytic_foundation_surface_and_curvature_payload_of_production_data_current_api
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    [IsManifold ThreeManifoldModelWithCorners 2 M]
    (metric :
      ContMDiffRiemannianMetric ThreeManifoldModelWithCorners n
        ThreeManifoldModel
        (fun x : M => TangentSpace ThreeManifoldModelWithCorners x))
    (identifiesDerivative :
      IsMetricTimeDerivativeOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_metric_time_derivative_field
          (stationary_time_dependent_riemannian_metric metric)))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (data :
      StationaryZeroAnalyticFoundationProductionDataCurrentApi
        metric identifiesDerivative identifiesRicci) :
    ∃ package :
        RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M,
      ricci_flow_data_of_analytic_foundation_package package =
        stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci ∧
      AnalyticFoundationWithEquationBoundaryStatement
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) ∧
      (∀ t,
        metric_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t = metric) ∧
      (∀ t x (v w : TangentSpace ThreeManifoldModelWithCorners x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w = 0 ∧
        ricci_tensor_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x v w = 0 ∧
        scalar_curvature_at_time_of_ricci_flow_data
          (stationary_zero_ricci_flow_data_current_api
            metric identifiesDerivative identifiesRicci) t x = 0 ∧
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (stationary_zero_ricci_flow_data_current_api
              metric identifiesDerivative identifiesRicci)) t x v w = 0 ∧
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            (metric_derivative_data_of_equation_boundary_package
              (stationary_zero_ricci_flow_equation_boundary_package
                metric identifiesDerivative identifiesRicci
                (stationary_zero_satisfies_ricci_flow_equation_current_api
                  metric identifiesDerivative identifiesRicci))))
            t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data
              (stationary_zero_ricci_flow_data_current_api
                metric identifiesDerivative identifiesRicci)) t x v w) ∧
      HasCurvatureEvolutionEquations
        (stationary_zero_ricci_flow_data_current_api
          metric identifiesDerivative identifiesRicci) := by
  rcases
    three_manifold_stationary_zero_analytic_foundation_surface_payload_of_production_data_current_api
      metric identifiesDerivative identifiesRicci data with
    ⟨package, hflow, equationBoundary, metricAtTime, pointwiseBoundary⟩
  exact
    ⟨ package
    , hflow
    , equationBoundary
    , metricAtTime
    , pointwiseBoundary
    , stationary_zero_analytic_foundation_curvature_evolution_of_production_data_current_api
        metric identifiesDerivative identifiesRicci data
    ⟩

end Poincare
