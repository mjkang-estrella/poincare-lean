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

end Poincare
