/-
Proof-progress slice for replacing the constructorless Levi-Civita existence
interface with concrete mathlib connection data.

The production interface now stores time-indexed bundled tangent covariant
derivatives.  Mathlib currently exposes smooth Riemannian metric slices and
bundled covariant derivatives, but this revision does not expose a theorem
constructing the Levi-Civita connection of a `ContMDiffRiemannianMetric`.
This module keeps the bridge from every existing `RicciFlowData` metric slice
into mathlib's Riemannian-bundle API and records the exact remaining input.
-/

import Poincare.AnalyticFoundation
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

universe u v w

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
Compatibility alias for the now-refactored production
`HasLeviCivitaConnectionExistence` shape.
-/
def ProposedHasLeviCivitaConnectionExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : Prop :=
  HasLeviCivitaConnectionExistence g

/-- The refactored production shape is exactly nonemptiness of the connection field. -/
theorem proposedHasLeviCivitaConnectionExistence_iff
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    ProposedHasLeviCivitaConnectionExistence g ↔
      Nonempty (TimeDependentTangentConnectionField g) :=
  hasLeviCivitaConnectionExistence_iff_connectionField_nonempty g

/--
Supplying one bundled tangent covariant derivative for every time proves the
production non-vacuous Levi-Civita-existence shape.
-/
theorem proposedHasLeviCivitaConnectionExistence_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (connectionAtTime : TimeDependentTangentConnectionField g) :
    ProposedHasLeviCivitaConnectionExistence g :=
  hasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/--
For a Ricci-flow datum, the exact missing connection field is one bundled
mathlib tangent covariant derivative for each time.
-/
theorem connectionField_for_flow_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow) =
      (ℝ → TangentCovariantDerivative I M) :=
  rfl

/--
Every existing Ricci-flow metric slice is already a smooth mathlib Riemannian
metric on the tangent bundle.
-/
theorem flow_metric_slice_contMDiffRiemannianMetric_nonempty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    Nonempty
      (ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x)) :=
  ⟨metric_at_time_of_ricci_flow_data flow t⟩

/--
The existing metric slice can be registered as a `RiemannianBundle`, and mathlib
then supplies the smooth Riemannian-bundle instance.

This is the positive bridge available today: the first analytic blocker is not
missing a metric slice; it is missing the covariant-derivative/Levi-Civita
constructor from such a slice.
-/
theorem flow_metric_slice_induces_contMDiff_riemannian_bundle
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I n E
      (fun x : M => TangentSpace I x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
  infer_instance

/--
If the missing mathlib/local constructor is supplied as a connection field for a
flow metric, the first analytic sub-obligation has the production non-vacuous
witness.
-/
theorem proposed_first_analytic_subobligation_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow)) :
    ProposedHasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) :=
  proposedHasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/--
The same concrete connection field directly constructs the production analytic
package's first field.
-/
theorem first_analytic_package_field_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow)) :
    HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data flow) :=
  hasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/--
For a Ricci-flow datum, a concrete time-dependent tangent connection field
simultaneously exposes the smooth metric slices, the refactored
Levi-Civita-existence proposition, and the first analytic package field.
-/
theorem flow_metric_slices_proposed_and_first_analytic_field_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow)) :
    (∀ _t : ℝ,
      Nonempty
        (ContMDiffRiemannianMetric I n E
          (fun x : M => TangentSpace I x))) ∧
      ProposedHasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) :=
  ⟨ flow_metric_slice_contMDiffRiemannianMetric_nonempty flow
  , proposed_first_analytic_subobligation_of_connectionField
      connectionAtTime
  , first_analytic_package_field_of_connectionField connectionAtTime
  ⟩

/--
A nonempty connection-field input for a Ricci-flow datum can be consumed as one
selected time-dependent tangent connection field, together with its definitional
shape, every smooth metric slice, every induced smooth Riemannian-bundle slice,
and the first analytic package field.
-/
theorem flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_nonemptyConnectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionField :
      Nonempty (TimeDependentTangentConnectionField
        (metric_of_ricci_flow_data flow))) :
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
      TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow) =
        (ℝ → TangentCovariantDerivative I M) ∧
      (∀ _t : ℝ,
        Nonempty
          (ContMDiffRiemannianMetric I n E
            (fun x : M => TangentSpace I x))) ∧
      (∀ t : ℝ,
        letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
          ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
        IsContMDiffRiemannianBundle I n E
          (fun x : M => TangentSpace I x)) ∧
      ProposedHasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) := by
  rcases connectionField with ⟨connectionAtTime⟩
  exact
    ⟨ connectionAtTime
    , connectionField_for_flow_eq flow
    , flow_metric_slice_contMDiffRiemannianMetric_nonempty flow
    , flow_metric_slice_induces_contMDiff_riemannian_bundle flow
    , proposed_first_analytic_subobligation_of_connectionField
        connectionAtTime
    , first_analytic_package_field_of_connectionField connectionAtTime
    ⟩

/--
The production Levi-Civita-existence field is strong enough to recover a
selected mathlib time-dependent tangent connection field, together with the
metric-slice and Riemannian-bundle evidence used by downstream analytic
consumers.
-/
theorem flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_leviCivitaExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (leviCivitaExistence :
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow)) :
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
      TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow) =
        (ℝ → TangentCovariantDerivative I M) ∧
      (∀ _t : ℝ,
        Nonempty
          (ContMDiffRiemannianMetric I n E
            (fun x : M => TangentSpace I x))) ∧
      (∀ t : ℝ,
        letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
          ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
        IsContMDiffRiemannianBundle I n E
          (fun x : M => TangentSpace I x)) ∧
      ProposedHasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) :=
  flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_nonemptyConnectionField
    ((hasLeviCivitaConnectionExistence_iff_connectionField_nonempty
      (metric_of_ricci_flow_data flow)).1 leviCivitaExistence)

/--
Any analytic sub-obligation payload contains enough Levi-Civita data to expose
the selected mathlib connection field and the metric/Riemannian-bundle slices
needed by the concrete connection interface.
-/
theorem flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_subobligations
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
      TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow) =
        (ℝ → TangentCovariantDerivative I M) ∧
      (∀ _t : ℝ,
        Nonempty
          (ContMDiffRiemannianMetric I n E
            (fun x : M => TangentSpace I x))) ∧
      (∀ t : ℝ,
        letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
          ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
        IsContMDiffRiemannianBundle I n E
          (fun x : M => TangentSpace I x)) ∧
      ProposedHasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) :=
  flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_leviCivitaExistence
    subobligations.1

/--
The analytic sub-obligation payload can be retained while projecting the
concrete Levi-Civita connection-field interface from it.  This endpoint is for
downstream analytic consumers that need the full theorem-shaped analytic
payload and the selected mathlib connection/smooth metric-slice evidence in
one proof object.
-/
theorem analyticFoundationSubobligationsPayload_and_flow_metric_slices_riemannianBundle_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    AnalyticFoundationSubobligationsPayload flow ∧
      ∃ _connectionAtTime :
        TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
        TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow) =
          (ℝ → TangentCovariantDerivative I M) ∧
        (∀ _t : ℝ,
          Nonempty
            (ContMDiffRiemannianMetric I n E
              (fun x : M => TangentSpace I x))) ∧
        (∀ t : ℝ,
          letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨(metric_at_time_of_ricci_flow_data flow t).toRiemannianMetric⟩
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        ProposedHasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) :=
  ⟨ subobligations
  , flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_subobligations
      subobligations
  ⟩

/--
At a fixed time, an analytic sub-obligation payload retains the concrete metric
slice, the induced smooth Riemannian-bundle evidence for that slice, and the
selected time-dependent tangent connection field that closes the first analytic
package field.
-/
theorem analyticFoundationSubobligationsPayload_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (t : ℝ) :
    AnalyticFoundationSubobligationsPayload flow ∧
      ∃ metricSlice :
        ContMDiffRiemannianMetric I n E
          (fun x : M => TangentSpace I x),
        metricSlice = metric_at_time_of_ricci_flow_data flow t ∧
        (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨metricSlice.toRiemannianMetric⟩;
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        ∃ _connectionAtTime :
          TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow),
          TimeDependentTangentConnectionField
              (metric_of_ricci_flow_data flow) =
            (ℝ → TangentCovariantDerivative I M) ∧
          ProposedHasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow) ∧
          HasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow) := by
  rcases
    flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_subobligations
      subobligations with
    ⟨connectionAtTime, hConnectionField, _metricSlices, _bundleSlices,
      hProposed, hFirstField⟩
  let metricSlice :
      ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x) :=
    metric_at_time_of_ricci_flow_data flow t
  have hBundle :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨metricSlice.toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I n E
        (fun x : M => TangentSpace I x) := by
    simpa [metricSlice] using
      flow_metric_slice_induces_contMDiff_riemannian_bundle flow t
  exact
    ⟨ subobligations
    , metricSlice
    , rfl
    , hBundle
    , connectionAtTime
    , hConnectionField
    , hProposed
    , hFirstField
    ⟩

/--
A completed analytic-foundation package retains the fixed-time metric slice,
the induced smooth Riemannian-bundle evidence, the selected time-dependent
tangent connection field, and the first Levi-Civita package field for its
projected Ricci-flow datum.  This is the package-level version of the local
sub-obligation projection above.
-/
theorem analyticFoundationPackage_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (t : ℝ) :
    let flow := ricci_flow_data_of_analytic_foundation_package package
    AnalyticFoundationSubobligationsPayload flow ∧
      ∃ metricSlice :
        ContMDiffRiemannianMetric I n E
          (fun x : M => TangentSpace I x),
        metricSlice = metric_at_time_of_ricci_flow_data flow t ∧
        (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨metricSlice.toRiemannianMetric⟩;
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        ∃ _connectionAtTime :
          TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow),
          TimeDependentTangentConnectionField
              (metric_of_ricci_flow_data flow) =
            (ℝ → TangentCovariantDerivative I M) ∧
          ProposedHasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow) ∧
          HasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow) :=
  analyticFoundationSubobligationsPayload_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
    (analytic_foundation_subobligations_of_analytic_foundation_package
      package) t

/--
Named-flow package endpoint for fixed-time analytic consumers.  It opens a
completed analytic-foundation package into the selected Ricci-flow datum, the
package sub-obligation payload, the fixed metric slice, the induced smooth
Riemannian-bundle evidence, and the selected connection field that closes the
first Levi-Civita package field.
-/
theorem analyticFoundationPackage_namedFlow_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (t : ℝ) :
    ∃ flow : RicciFlowData I n M,
    ∃ subobligations :
      AnalyticFoundationSubobligationsPayload
        (ricci_flow_data_of_analytic_foundation_package package),
    ∃ metricSlice :
      ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x),
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package)),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        subobligations =
            analytic_foundation_subobligations_of_analytic_foundation_package
              package ∧
        metricSlice =
          metric_at_time_of_ricci_flow_data
            (ricci_flow_data_of_analytic_foundation_package package) t ∧
        (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨metricSlice.toRiemannianMetric⟩;
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_analytic_foundation_package package)) =
          (ℝ → TangentCovariantDerivative I M) ∧
        ProposedHasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_analytic_foundation_package package)) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_analytic_foundation_package package)) := by
  let subobligations :=
    analytic_foundation_subobligations_of_analytic_foundation_package
      package
  rcases
    analyticFoundationSubobligationsPayload_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
      subobligations t with
    ⟨ _subobligations
    , metricSlice
    , hMetricSlice
    , hBundle
    , connectionAtTime
    , hConnectionField
    , hProposed
    , hFirstField
    ⟩
  exact
    ⟨ ricci_flow_data_of_analytic_foundation_package package
    , subobligations
    , metricSlice
    , connectionAtTime
    , rfl
    , rfl
    , hMetricSlice
    , hBundle
    , hConnectionField
    , hProposed
    , hFirstField
    ⟩

/--
All-time named-flow package endpoint for analytic consumers.  A completed
analytic-foundation package supplies, at every time parameter, the selected
Ricci-flow datum, the package sub-obligation payload, the metric slice, the
smooth Riemannian-bundle evidence induced by that slice, and the connection
field closing the first Levi-Civita analytic package field.
-/
theorem analyticFoundationPackage_namedFlow_allTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∀ t : ℝ,
      ∃ flow : RicciFlowData I n M,
      ∃ subobligations :
        AnalyticFoundationSubobligationsPayload
          (ricci_flow_data_of_analytic_foundation_package package),
      ∃ metricSlice :
        ContMDiffRiemannianMetric I n E
          (fun x : M => TangentSpace I x),
      ∃ _connectionAtTime :
        TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_analytic_foundation_package package)),
        flow = ricci_flow_data_of_analytic_foundation_package package ∧
          subobligations =
              analytic_foundation_subobligations_of_analytic_foundation_package
                package ∧
          metricSlice =
            metric_at_time_of_ricci_flow_data
              (ricci_flow_data_of_analytic_foundation_package package) t ∧
          (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
              ⟨metricSlice.toRiemannianMetric⟩;
            IsContMDiffRiemannianBundle I n E
              (fun x : M => TangentSpace I x)) ∧
          TimeDependentTangentConnectionField
              (metric_of_ricci_flow_data
                (ricci_flow_data_of_analytic_foundation_package package)) =
            (ℝ → TangentCovariantDerivative I M) ∧
          ProposedHasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_analytic_foundation_package package)) ∧
          HasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data
              (ricci_flow_data_of_analytic_foundation_package package)) := by
  intro t
  exact
    analyticFoundationPackage_namedFlow_fixedTime_metricSlice_riemannianBundle_connectionField_and_first_analytic_field
      package t

/--
Package endpoint with shared analytic data across all time slices.  It names
the projected Ricci-flow datum, the analytic sub-obligation payload, and one
selected time-dependent tangent connection field once, then exposes every
metric slice and its induced smooth Riemannian-bundle evidence from that same
package data.  This avoids downstream finite-extinction consumers having to
reopen a fresh existential package separately at each time.
-/
theorem analyticFoundationPackage_namedFlow_sharedConnection_allTime_metricSlice_riemannianBundle_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ flow : RicciFlowData I n M,
    ∃ _subobligations : AnalyticFoundationSubobligationsPayload flow,
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow) =
          (ℝ → TangentCovariantDerivative I M) ∧
        ProposedHasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        (∀ t : ℝ,
          ∃ metricSlice :
            ContMDiffRiemannianMetric I n E
              (fun x : M => TangentSpace I x),
            metricSlice = metric_at_time_of_ricci_flow_data flow t ∧
              Nonempty
                (ContMDiffRiemannianMetric I n E
                  (fun x : M => TangentSpace I x)) ∧
              (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
                  ⟨metricSlice.toRiemannianMetric⟩;
                IsContMDiffRiemannianBundle I n E
                  (fun x : M => TangentSpace I x))) := by
  let flow := ricci_flow_data_of_analytic_foundation_package package
  let subobligations :=
    analytic_foundation_subobligations_of_analytic_foundation_package
      package
  rcases
    flow_metric_slices_riemannianBundle_connectionField_and_first_analytic_field_of_subobligations
      subobligations with
    ⟨connectionAtTime, hConnectionField, hMetricSlices, hBundleSlices,
      hProposed, hFirstField⟩
  refine
    ⟨ flow
    , subobligations
    , connectionAtTime
    , rfl
    , hConnectionField
    , hProposed
    , hFirstField
    , ?_
    ⟩
  intro t
  let metricSlice :
      ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x) :=
    metric_at_time_of_ricci_flow_data flow t
  have hBundle :
      letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨metricSlice.toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I n E
        (fun x : M => TangentSpace I x) := by
    simpa [metricSlice] using hBundleSlices t
  exact
    ⟨ metricSlice
    , rfl
    , hMetricSlices t
    , hBundle
    ⟩

/--
Fixed-time consumer form of the shared-connection analytic package endpoint.
It keeps one selected metric slice at `t₀` together with its smooth
Riemannian-bundle evidence, while retaining the same named flow, sub-obligation
payload, shared connection field, first analytic field, and all-time metric
slice family.
-/
theorem analyticFoundationPackage_namedFlow_sharedConnection_fixedTime_and_allTime_metricSlice_riemannianBundle_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) (t₀ : ℝ) :
    ∃ flow : RicciFlowData I n M,
    ∃ _subobligations : AnalyticFoundationSubobligationsPayload flow,
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
    ∃ selectedMetricSlice :
      ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        selectedMetricSlice = metric_at_time_of_ricci_flow_data flow t₀ ∧
        (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨selectedMetricSlice.toRiemannianMetric⟩;
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow) =
          (ℝ → TangentCovariantDerivative I M) ∧
        ProposedHasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        (∀ t : ℝ,
          ∃ metricSlice :
            ContMDiffRiemannianMetric I n E
              (fun x : M => TangentSpace I x),
            metricSlice = metric_at_time_of_ricci_flow_data flow t ∧
              Nonempty
                (ContMDiffRiemannianMetric I n E
                  (fun x : M => TangentSpace I x)) ∧
              (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
                  ⟨metricSlice.toRiemannianMetric⟩;
                IsContMDiffRiemannianBundle I n E
                  (fun x : M => TangentSpace I x))) := by
  rcases
    analyticFoundationPackage_namedFlow_sharedConnection_allTime_metricSlice_riemannianBundle_and_first_analytic_field
      package with
    ⟨ flow
    , subobligations
    , connectionAtTime
    , hFlow
    , hConnectionField
    , hProposed
    , hFirstField
    , allMetricSlices
    ⟩
  rcases allMetricSlices t₀ with
    ⟨ selectedMetricSlice
    , hSelectedMetricSlice
    , _hSelectedNonempty
    , hSelectedBundle
    ⟩
  exact
    ⟨ flow
    , subobligations
    , connectionAtTime
    , selectedMetricSlice
    , hFlow
    , hSelectedMetricSlice
    , hSelectedBundle
    , hConnectionField
    , hProposed
    , hFirstField
    , allMetricSlices
    ⟩

/--
Fixed-time package endpoint retaining the nonempty connection-field proposition.
The selected shared connection is kept as an explicit witness, so consumers can
use either the concrete time-dependent tangent connection or the production
nonemptiness shape, while also retaining the selected metric slice and the
all-time Riemannian-bundle family from the same analytic package.
-/
theorem analyticFoundationPackage_namedFlow_sharedConnection_fixedTime_nonemptyConnection_and_allTime_metricSlice_riemannianBundle_and_first_analytic_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) (t₀ : ℝ) :
    ∃ flow : RicciFlowData I n M,
    ∃ _subobligations : AnalyticFoundationSubobligationsPayload flow,
    ∃ _connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow),
    ∃ selectedMetricSlice :
      ContMDiffRiemannianMetric I n E
        (fun x : M => TangentSpace I x),
      flow = ricci_flow_data_of_analytic_foundation_package package ∧
        Nonempty
          (TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow)) ∧
        (ProposedHasLeviCivitaConnectionExistence
            (metric_of_ricci_flow_data flow) ↔
          Nonempty
            (TimeDependentTangentConnectionField
              (metric_of_ricci_flow_data flow))) ∧
        selectedMetricSlice = metric_at_time_of_ricci_flow_data flow t₀ ∧
        Nonempty
          (ContMDiffRiemannianMetric I n E
            (fun x : M => TangentSpace I x)) ∧
        (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
            ⟨selectedMetricSlice.toRiemannianMetric⟩;
          IsContMDiffRiemannianBundle I n E
            (fun x : M => TangentSpace I x)) ∧
        TimeDependentTangentConnectionField
            (metric_of_ricci_flow_data flow) =
          (ℝ → TangentCovariantDerivative I M) ∧
        ProposedHasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        HasLeviCivitaConnectionExistence
          (metric_of_ricci_flow_data flow) ∧
        (∀ t : ℝ,
          ∃ metricSlice :
            ContMDiffRiemannianMetric I n E
              (fun x : M => TangentSpace I x),
            metricSlice = metric_at_time_of_ricci_flow_data flow t ∧
              Nonempty
                (ContMDiffRiemannianMetric I n E
                  (fun x : M => TangentSpace I x)) ∧
              (letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
                  ⟨metricSlice.toRiemannianMetric⟩;
                IsContMDiffRiemannianBundle I n E
                  (fun x : M => TangentSpace I x))) := by
  rcases
    analyticFoundationPackage_namedFlow_sharedConnection_fixedTime_and_allTime_metricSlice_riemannianBundle_and_first_analytic_field
      package t₀ with
    ⟨ flow
    , subobligations
    , connectionAtTime
    , selectedMetricSlice
    , hFlow
    , hSelectedMetricSlice
    , hSelectedBundle
    , hConnectionField
    , hProposed
    , hFirstField
    , allMetricSlices
    ⟩
  exact
    ⟨ flow
    , subobligations
    , connectionAtTime
    , selectedMetricSlice
    , hFlow
    , ⟨connectionAtTime⟩
    , proposedHasLeviCivitaConnectionExistence_iff
        (metric_of_ricci_flow_data flow)
    , hSelectedMetricSlice
    , ⟨selectedMetricSlice⟩
    , hSelectedBundle
    , hConnectionField
    , hProposed
    , hFirstField
    , allMetricSlices
    ⟩

end Poincare
