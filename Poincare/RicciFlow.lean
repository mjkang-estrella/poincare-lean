/-
Minimal Ricci-flow API surface.

Mathlib currently has Riemannian metric and manifold infrastructure, but not the
Ricci curvature / Ricci flow equation stack needed for Perelman's proof. The
definitions here make the missing curvature and equation layers explicit
interfaces.
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic
import Poincare.RicciFlowInterface

universe u v

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
A smooth time-dependent Riemannian metric on a manifold.

`metricAtTime t` uses mathlib's `ContMDiffRiemannianMetric`; regularity is kept
as a parameter so later work can choose the amount of smoothness needed.
-/
structure TimeDependentRiemannianMetric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The Riemannian metric at time `t`. -/
  metricAtTime :
    ℝ → ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)

/-- A time-independent metric family obtained from one Riemannian metric. -/
noncomputable def stationary_time_dependent_riemannian_metric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)) :
    TimeDependentRiemannianMetric I n M where
  metricAtTime := fun _t => metric

/-- The stationary metric family stores the supplied metric at every time. -/
@[simp] theorem stationary_time_dependent_riemannian_metric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)) :
    stationary_time_dependent_riemannian_metric metric =
      ({ metricAtTime := fun _t => metric } :
        TimeDependentRiemannianMetric I n M) :=
  rfl

/-- A covariant two-tensor field on the tangent bundle. -/
abbrev TangentCovariantTwoTensor
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] : Type _ :=
  (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

/--
The tangent covariant two-tensor alias is definitionally the dependent family
of continuous bilinear forms on tangent spaces.
-/
theorem tangentCovariantTwoTensor_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    TangentCovariantTwoTensor I M =
      ((x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  rfl

/--
The zero covariant two-tensor field on the tangent bundle.

This is only a tensor candidate; it does not assert that any metric has zero
Ricci curvature.
-/
noncomputable def zero_tangent_covariant_two_tensor
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    TangentCovariantTwoTensor I M :=
  fun _x => 0

/-- The zero tensor candidate is the pointwise zero bilinear form. -/
@[simp] theorem zero_tangent_covariant_two_tensor_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    zero_tangent_covariant_two_tensor I M =
      (fun _x => 0 : TangentCovariantTwoTensor I M) :=
  rfl

/-- At each point, the zero tensor candidate is the zero bilinear form. -/
@[simp] theorem zero_tangent_covariant_two_tensor_apply
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (x : M) :
    zero_tangent_covariant_two_tensor I M x = 0 :=
  rfl

/-- The pointwise zero-tensor simp proof is the definitional equality proof. -/
@[simp] theorem zero_tangent_covariant_two_tensor_apply_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (x : M) :
    zero_tangent_covariant_two_tensor_apply (I := I) (M := M) x = rfl := by
  apply Subsingleton.elim

/--
Candidate Ricci tensor field for a time-dependent metric.

The field is separate from the identification theorem below because mathlib does
not yet provide the curvature construction that should determine it.
-/
structure RicciTensorField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) where
  /-- The candidate Ricci tensor at each time. -/
  tensorAtTime : ℝ → TangentCovariantTwoTensor I M

/-- The zero candidate Ricci tensor field for a time-dependent metric. -/
noncomputable def zero_ricci_tensor_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : RicciTensorField g where
  tensorAtTime := fun _t => zero_tangent_covariant_two_tensor I M

/-- The zero candidate Ricci tensor field is timewise the zero tensor. -/
@[simp] theorem zero_ricci_tensor_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    zero_ricci_tensor_field g =
      ({ tensorAtTime := fun _t => zero_tangent_covariant_two_tensor I M } :
        RicciTensorField g) :=
  rfl

/--
Candidate scalar curvature field for a time-dependent metric.

It is recorded separately from the Ricci tensor because the formal contraction
from the Ricci tensor to scalar curvature is part of the missing curvature
formalization.
-/
structure ScalarCurvatureField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) where
  /-- The candidate scalar curvature at each time and point. -/
  scalarAtTime : ℝ → M → ℝ

/-- The zero candidate scalar-curvature field for a time-dependent metric. -/
noncomputable def zero_scalar_curvature_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) : ScalarCurvatureField g where
  scalarAtTime := fun _t _x => 0

/-- The zero candidate scalar-curvature field is pointwise zero. -/
@[simp] theorem zero_scalar_curvature_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    zero_scalar_curvature_field g =
      ({ scalarAtTime := fun _t _x => 0 } : ScalarCurvatureField g) :=
  rfl

/--
Candidate time derivative of a time-dependent metric.

The derivative is a covariant two-tensor at each time.  The separate
identification predicate below records the still-missing theorem that a
candidate really is the derivative of the metric family.
-/
structure MetricTimeDerivativeField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) where
  /-- Candidate metric derivative at each time. -/
  derivativeAtTime : ℝ → TangentCovariantTwoTensor I M

/-- The zero candidate time derivative for a time-dependent metric. -/
noncomputable def zero_metric_time_derivative_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    MetricTimeDerivativeField g where
  derivativeAtTime := fun _t => zero_tangent_covariant_two_tensor I M

/-- The zero candidate metric derivative is timewise the zero tensor. -/
@[simp] theorem zero_metric_time_derivative_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) :
    zero_metric_time_derivative_field g =
      ({ derivativeAtTime := fun _t => zero_tangent_covariant_two_tensor I M } :
        MetricTimeDerivativeField g) :=
  rfl

/--
Interface asserting that a candidate tensor is the Ricci tensor of a metric.

This predicate has no constructors in this file; it is the curvature-theory
boundary that future work must replace with a real definition and theorem.
-/
inductive IsRicciTensorOf
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (_ricci : RicciTensorField g) : Prop

/--
Interface asserting that a candidate tensor field is the time derivative of a
metric family.

This predicate has no constructors in this file; it is the metric
differentiation boundary that future analytic formalization must supply.
-/
inductive IsMetricTimeDerivativeOf
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (_derivative : MetricTimeDerivativeField g) : Prop

/-- Metric time-derivative data attached to a time-dependent metric. -/
structure MetricTimeDerivativeData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) where
  /-- Candidate metric time derivative. -/
  derivative : MetricTimeDerivativeField g
  /-- Evidence that the candidate derivative is the derivative of `g`. -/
  identifiesDerivative : IsMetricTimeDerivativeOf g derivative

/-- Ricci curvature data attached to a time-dependent metric. -/
structure RicciCurvatureData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) where
  /-- Candidate Ricci tensor field. -/
  ricci : RicciTensorField g
  /-- Candidate scalar curvature field. -/
  scalar : ScalarCurvatureField g
  /-- Evidence that the candidate tensor is the Ricci tensor of `g`. -/
  identifiesRicci : IsRicciTensorOf g ricci

/--
Interface for the Ricci flow equation.

This predicate has no constructors in this file. Future curvature formalization
should replace uses of this interface with a definition in terms of the
derivative of the metric and the Ricci tensor.
-/
inductive SatisfiesRicciFlowEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (_curvature : RicciCurvatureData g) : Prop

/--
Ricci-flow data is a time-dependent Riemannian metric together with a proof that
it satisfies the current equation interface.
-/
structure RicciFlowData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- The metric family. -/
  metric : TimeDependentRiemannianMetric I n M
  /-- Ricci tensor data for the metric family. -/
  curvature : RicciCurvatureData metric
  /-- Equation evidence for the current interface. -/
  equation : SatisfiesRicciFlowEquation metric curvature

/-- Project the metric family from Ricci-flow data. -/
def metric_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    TimeDependentRiemannianMetric I n M :=
  flow.metric

/-- The named metric projection is definitionally the structure field. -/
@[simp] theorem metric_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    metric_of_ricci_flow_data flow = flow.metric :=
  rfl

/-- Project the curvature data from Ricci-flow data. -/
def curvature_data_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    RicciCurvatureData (metric_of_ricci_flow_data flow) :=
  flow.curvature

/-- The named curvature projection is definitionally the structure field. -/
@[simp] theorem curvature_data_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    curvature_data_of_ricci_flow_data flow = flow.curvature :=
  rfl

/-- Evaluate a time-dependent Riemannian metric at a time. -/
def metric_at_time_of_time_dependent_metric
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (t : ℝ) :
    ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x) :=
  g.metricAtTime t

/-- The named time-slice projection is definitionally the metric field at time. -/
@[simp] theorem metric_at_time_of_time_dependent_metric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (t : ℝ) :
    metric_at_time_of_time_dependent_metric g t = g.metricAtTime t :=
  rfl

/-- Evaluating a stationary metric family returns the supplied metric. -/
@[simp] theorem metric_at_time_of_stationary_time_dependent_riemannian_metric_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (t : ℝ) :
    metric_at_time_of_time_dependent_metric
      (stationary_time_dependent_riemannian_metric metric) t =
        metric :=
  rfl

/-- Evaluate the metric family of Ricci-flow data at a time. -/
def metric_at_time_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x) :=
  metric_at_time_of_time_dependent_metric (metric_of_ricci_flow_data flow) t

/-- The named flow metric time slice is definitionally the metric field at time. -/
@[simp] theorem metric_at_time_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    metric_at_time_of_ricci_flow_data flow t = flow.metric.metricAtTime t :=
  rfl

/-- Project the candidate derivative from metric time-derivative data. -/
def metric_time_derivative_field_of_metric_derivative_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeData g) : MetricTimeDerivativeField g :=
  derivative.derivative

/-- The named metric-derivative projection is definitionally the structure field. -/
@[simp] theorem metric_time_derivative_field_of_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeData g) :
    metric_time_derivative_field_of_metric_derivative_data derivative =
      derivative.derivative :=
  rfl

/-- Metric time-derivative data carries derivative-identification evidence. -/
theorem metric_time_derivative_identification_of_metric_derivative_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeData g) :
    IsMetricTimeDerivativeOf g
      (metric_time_derivative_field_of_metric_derivative_data derivative) :=
  derivative.identifiesDerivative

/-- The named metric-derivative identification theorem is stored evidence. -/
@[simp] theorem metric_time_derivative_identification_of_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeData g) :
    metric_time_derivative_identification_of_metric_derivative_data derivative =
      derivative.identifiesDerivative :=
  rfl

/-- Evaluate a candidate metric time-derivative field at a time. -/
def metric_time_derivative_at_time_of_metric_derivative_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeField g) (t : ℝ) :
    TangentCovariantTwoTensor I M :=
  derivative.derivativeAtTime t

/-- The named metric-derivative time slice is the derivative field at time. -/
@[simp] theorem metric_time_derivative_at_time_of_metric_derivative_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeField g) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field derivative t =
      derivative.derivativeAtTime t :=
  rfl

/-- The named metric-derivative time slice applied at a point and two tangent vectors. -/
@[simp] theorem metric_time_derivative_at_time_apply
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeField g)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field derivative t x v w =
      derivative.derivativeAtTime t x v w :=
  rfl

/-- The pointwise metric-derivative time-slice proof is definitional. -/
@[simp] theorem metric_time_derivative_at_time_apply_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (derivative : MetricTimeDerivativeField g)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_apply derivative t x v w = rfl := by
  apply Subsingleton.elim

/-- Evaluating the zero metric derivative at any time returns the zero tensor. -/
@[simp] theorem metric_time_derivative_at_time_of_zero_metric_time_derivative_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (zero_metric_time_derivative_field g) t =
        zero_tangent_covariant_two_tensor I M :=
  rfl

/-- Project the candidate Ricci tensor from Ricci-curvature data. -/
def ricci_tensor_field_of_curvature_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    RicciTensorField g :=
  curvature.ricci

/-- The named Ricci-tensor projection is definitionally the curvature field. -/
@[simp] theorem ricci_tensor_field_of_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    ricci_tensor_field_of_curvature_data curvature = curvature.ricci :=
  rfl

/-- Project the candidate scalar curvature from Ricci-curvature data. -/
def scalar_curvature_field_of_curvature_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    ScalarCurvatureField g :=
  curvature.scalar

/-- The named scalar-curvature projection is definitionally the curvature field. -/
@[simp] theorem scalar_curvature_field_of_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    scalar_curvature_field_of_curvature_data curvature = curvature.scalar :=
  rfl

/-- Evaluate a candidate Ricci tensor field at a time. -/
def ricci_tensor_at_time_of_ricci_tensor_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (ricci : RicciTensorField g) (t : ℝ) :
    TangentCovariantTwoTensor I M :=
  ricci.tensorAtTime t

/-- The named Ricci-tensor time slice is definitionally the tensor field at time. -/
@[simp] theorem ricci_tensor_at_time_of_ricci_tensor_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (ricci : RicciTensorField g) (t : ℝ) :
    ricci_tensor_at_time_of_ricci_tensor_field ricci t = ricci.tensorAtTime t :=
  rfl

/-- Evaluating the zero candidate Ricci tensor at any time returns the zero tensor. -/
@[simp] theorem ricci_tensor_at_time_of_zero_ricci_tensor_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (t : ℝ) :
    ricci_tensor_at_time_of_ricci_tensor_field (zero_ricci_tensor_field g) t =
      zero_tangent_covariant_two_tensor I M :=
  rfl

/-- The right-hand side `-2 Ricci` of the Ricci-flow equation. -/
noncomputable def ricci_flow_rhs_tensor
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) (t : ℝ) :
    TangentCovariantTwoTensor I M :=
  fun x => (-2 : ℝ) •
    ricci_tensor_at_time_of_ricci_tensor_field
      (ricci_tensor_field_of_curvature_data curvature) t x

/-- The named Ricci-flow right-hand side is pointwise `-2 • Ricci`. -/
@[simp] theorem ricci_flow_rhs_tensor_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) (t : ℝ) :
    ricci_flow_rhs_tensor curvature t =
      (fun x => (-2 : ℝ) • curvature.ricci.tensorAtTime t x :
        TangentCovariantTwoTensor I M) :=
  rfl

/-- At a point, the Ricci-flow right-hand side is `-2 • Ricci`. -/
@[simp] theorem ricci_flow_rhs_tensor_apply
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) (t : ℝ) (x : M) :
    ricci_flow_rhs_tensor curvature t x =
      (-2 : ℝ) • curvature.ricci.tensorAtTime t x :=
  rfl

/-- The pointwise Ricci-flow right-hand-side simp proof is definitional. -/
@[simp] theorem ricci_flow_rhs_tensor_apply_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) (t : ℝ) (x : M) :
    ricci_flow_rhs_tensor_apply curvature t x = rfl := by
  apply Subsingleton.elim

/-- Evaluate a candidate scalar curvature field at a time and point. -/
def scalar_curvature_at_time_of_scalar_curvature_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (scalar : ScalarCurvatureField g) (t : ℝ) (x : M) : ℝ :=
  scalar.scalarAtTime t x

/-- The named scalar-curvature time slice is definitionally the scalar field. -/
@[simp] theorem scalar_curvature_at_time_of_scalar_curvature_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (scalar : ScalarCurvatureField g) (t : ℝ) (x : M) :
    scalar_curvature_at_time_of_scalar_curvature_field scalar t x =
      scalar.scalarAtTime t x :=
  rfl

/-- Evaluating the zero candidate scalar curvature at any time and point gives zero. -/
@[simp] theorem scalar_curvature_at_time_of_zero_scalar_curvature_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M) (t : ℝ) (x : M) :
    scalar_curvature_at_time_of_scalar_curvature_field
      (zero_scalar_curvature_field g) t x = 0 :=
  rfl

/-- Evaluate the Ricci tensor field of Ricci-flow data at a time. -/
def ricci_tensor_at_time_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    TangentCovariantTwoTensor I M :=
  ricci_tensor_at_time_of_ricci_tensor_field
    (ricci_tensor_field_of_curvature_data
      (curvature_data_of_ricci_flow_data flow)) t

/-- The named flow Ricci-tensor time slice is definitionally the curvature tensor field. -/
@[simp] theorem ricci_tensor_at_time_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) :
    ricci_tensor_at_time_of_ricci_flow_data flow t =
      flow.curvature.ricci.tensorAtTime t :=
  rfl

/-- Evaluate the scalar curvature field of Ricci-flow data at a time and point. -/
def scalar_curvature_at_time_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) (x : M) : ℝ :=
  scalar_curvature_at_time_of_scalar_curvature_field
    (scalar_curvature_field_of_curvature_data
      (curvature_data_of_ricci_flow_data flow)) t x

/-- The named flow scalar-curvature value is definitionally the curvature scalar field. -/
@[simp] theorem scalar_curvature_at_time_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) (t : ℝ) (x : M) :
    scalar_curvature_at_time_of_ricci_flow_data flow t x =
      flow.curvature.scalar.scalarAtTime t x :=
  rfl

/-- Curvature data carries evidence that its candidate tensor is Ricci. -/
theorem ricci_identification_of_curvature_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    IsRicciTensorOf g (ricci_tensor_field_of_curvature_data curvature) :=
  curvature.identifiesRicci

/-- The named curvature Ricci-identification theorem is the stored evidence. -/
theorem ricci_identification_of_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) :
    ricci_identification_of_curvature_data curvature = curvature.identifiesRicci :=
  rfl

/-- Ricci-flow data carries Ricci-identification evidence for its curvature. -/
theorem ricci_identification_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    IsRicciTensorOf
      (metric_of_ricci_flow_data flow)
      (ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data flow)) :=
  (curvature_data_of_ricci_flow_data flow).identifiesRicci

/-- The named flow Ricci-identification theorem is the stored evidence. -/
theorem ricci_identification_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    ricci_identification_of_ricci_flow_data flow =
      flow.curvature.identifiesRicci :=
  rfl

/-- Any `RicciFlowData` carries evidence for the Ricci-flow equation interface. -/
theorem RicciFlowData.satisfies_equation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    SatisfiesRicciFlowEquation flow.metric flow.curvature :=
  flow.equation

/-- The dot-notation equation theorem is the stored equation evidence. -/
theorem RicciFlowData.satisfies_equation_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    flow.satisfies_equation = flow.equation :=
  rfl

/-- Ricci-flow data carries evidence for the equation using the named projections. -/
theorem equation_evidence_of_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow) :=
  flow.equation

/-- The named flow equation-evidence theorem is the stored equation evidence. -/
theorem equation_evidence_of_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    equation_evidence_of_ricci_flow_data flow = flow.equation :=
  rfl

/--
Concrete verification data for the equation `∂ₜ g = -2 Ricci`.

This structure does not construct `SatisfiesRicciFlowEquation`; it records the
explicit analytic equality that a future bridge theorem must connect to that
interface.
-/
structure RicciFlowEquationVerification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (curvature : RicciCurvatureData g) where
  /-- The candidate metric derivative, with identification evidence. -/
  metricDerivative : MetricTimeDerivativeData g
  /-- Pointwise-in-time equality with the `-2 Ricci` right-hand side. -/
  equationAtTime : ∀ t,
    metric_time_derivative_at_time_of_metric_derivative_field
      metricDerivative.derivative t = ricci_flow_rhs_tensor curvature t

/-- Project metric-derivative data from a Ricci-flow equation verification. -/
def metric_derivative_data_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) :
    MetricTimeDerivativeData g :=
  verification.metricDerivative

/-- The equation-verification metric-derivative projection is stored data. -/
@[simp] theorem metric_derivative_data_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) :
    metric_derivative_data_of_ricci_flow_equation_verification verification =
      verification.metricDerivative :=
  rfl

/-- A Ricci-flow equation verification supplies the explicit equality at time `t`. -/
theorem equation_at_time_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      verification.metricDerivative.derivative t = ricci_flow_rhs_tensor curvature t :=
  verification.equationAtTime t

/-- The named equation-at-time theorem is stored equation evidence. -/
@[simp] theorem equation_at_time_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) (t : ℝ) :
    equation_at_time_of_ricci_flow_equation_verification verification t =
      verification.equationAtTime t :=
  rfl

/-- A Ricci-flow equation verification carries metric-derivative identification evidence. -/
theorem metric_time_derivative_identification_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) :
    IsMetricTimeDerivativeOf g
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_ricci_flow_equation_verification verification)) :=
  verification.metricDerivative.identifiesDerivative

/-- The equation-verification derivative-identification theorem is stored evidence. -/
@[simp] theorem metric_time_derivative_identification_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) :
    metric_time_derivative_identification_of_ricci_flow_equation_verification
      verification = verification.metricDerivative.identifiesDerivative :=
  rfl

/--
The equation equality also holds when the candidate derivative is reached
through the named equation-verification projection.
-/
theorem equation_at_time_of_ricci_flow_equation_verification_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_ricci_flow_equation_verification verification)) t =
        ricci_flow_rhs_tensor curvature t :=
  verification.equationAtTime t

/-- The projection-routed equation theorem is stored equation evidence. -/
@[simp] theorem equation_at_time_of_ricci_flow_equation_verification_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature) (t : ℝ) :
    equation_at_time_of_ricci_flow_equation_verification_projection
      verification t = verification.equationAtTime t :=
  rfl

/--
The projection-routed equation also holds pointwise at a point and pair of
tangent vectors.
-/
theorem equation_at_time_apply_of_ricci_flow_equation_verification_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_ricci_flow_equation_verification verification)) t x v w =
        ricci_flow_rhs_tensor curvature t x v w :=
  congrArg (fun tensor => tensor x v w)
    (equation_at_time_of_ricci_flow_equation_verification_projection
      verification t)

/-- The pointwise projection-routed equation proof is tensor equality application. -/
@[simp] theorem equation_at_time_apply_of_ricci_flow_equation_verification_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    {curvature : RicciCurvatureData g}
    (verification : RicciFlowEquationVerification curvature)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_ricci_flow_equation_verification_projection
      verification t x v w =
      congrArg (fun tensor => tensor x v w)
        (equation_at_time_of_ricci_flow_equation_verification_projection
          verification t) := by
  apply Subsingleton.elim

/--
If the candidate Ricci tensor is the zero tensor field, the explicit
right-hand side `-2 Ricci` is pointwise zero.

The Ricci-identification evidence is an input; this theorem does not construct
Ricci curvature for any metric.
-/
@[simp] theorem ricci_flow_rhs_tensor_of_zero_ricci_tensor_field_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) :
    ricci_flow_rhs_tensor
      ({ ricci := zero_ricci_tensor_field g
         scalar := zero_scalar_curvature_field g
         identifiesRicci := identifiesRicci } : RicciCurvatureData g) t =
      zero_tangent_covariant_two_tensor I M := by
  change
    (fun x : M =>
      (-2 : ℝ) •
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) =
      (fun x : M =>
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
  funext x
  ext v w
  change (-2 : ℝ) * (0 : ℝ) = 0
  norm_num

/--
Curvature data assembled from the zero Ricci and scalar-curvature candidates.

The Ricci-identification evidence is still an input; this definition packages a
candidate once future curvature theory proves that the candidate is really the
Ricci tensor.
-/
noncomputable def zero_ricci_curvature_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    RicciCurvatureData g where
  ricci := zero_ricci_tensor_field g
  scalar := zero_scalar_curvature_field g
  identifiesRicci := identifiesRicci

/-- The zero curvature-data package is the explicit zero Ricci/scalar payload. -/
@[simp] theorem zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    zero_ricci_curvature_data identifiesRicci =
      ({ ricci := zero_ricci_tensor_field g
         scalar := zero_scalar_curvature_field g
         identifiesRicci := identifiesRicci } : RicciCurvatureData g) :=
  rfl

/-- The Ricci projection of zero curvature data is the zero Ricci candidate. -/
@[simp] theorem ricci_tensor_field_of_zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    ricci_tensor_field_of_curvature_data
      (zero_ricci_curvature_data identifiesRicci) =
        zero_ricci_tensor_field g :=
  rfl

/-- The scalar projection of zero curvature data is the zero scalar candidate. -/
@[simp] theorem scalar_curvature_field_of_zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    scalar_curvature_field_of_curvature_data
      (zero_ricci_curvature_data identifiesRicci) =
        zero_scalar_curvature_field g :=
  rfl

/-- The Ricci-identification projection of zero curvature data is the supplied evidence. -/
@[simp] theorem ricci_identification_of_zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    ricci_identification_of_curvature_data
      (zero_ricci_curvature_data identifiesRicci) =
        identifiesRicci :=
  rfl

/-- The right-hand side attached to zero curvature data is pointwise zero. -/
@[simp] theorem ricci_flow_rhs_tensor_of_zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) :
    ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t =
      zero_tangent_covariant_two_tensor I M := by
  exact
    ricci_flow_rhs_tensor_of_zero_ricci_tensor_field_eq
      (g := g) identifiesRicci t

/-- Pointwise, the zero-curvature Ricci-flow right-hand side is the scalar zero. -/
@[simp] theorem ricci_flow_rhs_tensor_apply_of_zero_ricci_curvature_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t x v w = 0 := by
  change (-2 : ℝ) * (0 : ℝ) = 0
  norm_num

/-- The pointwise zero-curvature RHS proof is the scalar zero calculation. -/
@[simp] theorem ricci_flow_rhs_tensor_apply_of_zero_ricci_curvature_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    ricci_flow_rhs_tensor_apply_of_zero_ricci_curvature_data
      identifiesRicci t x v w =
      (by
        change (-2 : ℝ) * (0 : ℝ) = 0
        norm_num) := by
  apply Subsingleton.elim

/--
Metric-derivative data assembled from the zero derivative candidate.

The derivative-identification evidence is still an input; this is the explicit
package that a future metric-differentiation theorem must inhabit in the flat
or stationary case.
-/
noncomputable def zero_metric_derivative_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g)) :
    MetricTimeDerivativeData g where
  derivative := zero_metric_time_derivative_field g
  identifiesDerivative := identifiesDerivative

/-- The zero metric-derivative package is the explicit zero derivative payload. -/
@[simp] theorem zero_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g)) :
    zero_metric_derivative_data identifiesDerivative =
      ({ derivative := zero_metric_time_derivative_field g
         identifiesDerivative := identifiesDerivative } :
        MetricTimeDerivativeData g) :=
  rfl

/-- The derivative projection of zero derivative data is the zero derivative candidate. -/
@[simp] theorem metric_time_derivative_field_of_zero_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g)) :
    metric_time_derivative_field_of_metric_derivative_data
      (zero_metric_derivative_data identifiesDerivative) =
        zero_metric_time_derivative_field g :=
  rfl

/--
Evaluating the derivative field inside zero derivative data returns the zero
two-tensor at every time.
-/
@[simp] theorem metric_time_derivative_at_time_of_zero_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (zero_metric_derivative_data identifiesDerivative)) t =
        zero_tangent_covariant_two_tensor I M :=
  rfl

/--
Pointwise, the zero metric-derivative data evaluates to the scalar zero at
every time, point, and pair of tangent vectors.
-/
@[simp] theorem metric_time_derivative_at_time_apply_of_zero_metric_derivative_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (zero_metric_derivative_data identifiesDerivative)) t x v w = 0 :=
  rfl

/-- The pointwise zero metric-derivative-data proof is definitional. -/
@[simp] theorem metric_time_derivative_at_time_apply_of_zero_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_apply_of_zero_metric_derivative_data
      identifiesDerivative t x v w = rfl := by
  apply Subsingleton.elim

/-- The derivative-identification projection is the supplied evidence. -/
@[simp] theorem metric_time_derivative_identification_of_zero_metric_derivative_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g)) :
    metric_time_derivative_identification_of_metric_derivative_data
      (zero_metric_derivative_data identifiesDerivative) =
        identifiesDerivative :=
  rfl

/--
Concrete equation verification for the zero-derivative/zero-Ricci candidate.

Both identification proofs remain explicit inputs. The result proves only the
pointwise analytic equality `0 = -2 * 0`, not the abstract Ricci-flow equation
interface.
-/
noncomputable def zero_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    RicciFlowEquationVerification
      (zero_ricci_curvature_data identifiesRicci) where
  metricDerivative := zero_metric_derivative_data identifiesDerivative
  equationAtTime := by
    intro t
    change zero_tangent_covariant_two_tensor I M =
      ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t
    exact (ricci_flow_rhs_tensor_of_zero_ricci_tensor_field_eq
      (g := g) identifiesRicci t).symm

/-- The zero equation verification is the explicit zero derivative equation payload. -/
@[simp] theorem zero_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci =
      ({ metricDerivative := zero_metric_derivative_data identifiesDerivative
         equationAtTime := by
            intro t
            change zero_tangent_covariant_two_tensor I M =
              ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t
            exact (ricci_flow_rhs_tensor_of_zero_ricci_tensor_field_eq
              (g := g) identifiesRicci t).symm } :
        RicciFlowEquationVerification
          (zero_ricci_curvature_data identifiesRicci)) :=
  rfl

/-- The metric-derivative projection of zero equation verification is the zero package. -/
@[simp] theorem metric_derivative_data_of_zero_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    metric_derivative_data_of_ricci_flow_equation_verification
      (zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci) =
        zero_metric_derivative_data identifiesDerivative :=
  rfl

/--
The zero equation verification carries exactly the supplied zero-derivative
identification evidence.
-/
@[simp] theorem metric_time_derivative_identification_of_zero_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    metric_time_derivative_identification_of_ricci_flow_equation_verification
      (zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci) =
        identifiesDerivative :=
  rfl

/-- The zero equation verification proves the expected pointwise equation. -/
theorem equation_at_time_of_zero_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_ricci_flow_equation_verification
          (zero_ricci_flow_equation_verification
            identifiesDerivative identifiesRicci))) t =
        ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t :=
  equation_at_time_of_ricci_flow_equation_verification_projection
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci) t

/-- The named zero equation theorem is the stored equation proof. -/
@[simp] theorem equation_at_time_of_zero_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) :
    equation_at_time_of_zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci t =
      (zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci).equationAtTime t :=
  rfl

/--
The zero equation verification proves the Ricci-flow equation pointwise at a
point and pair of tangent vectors.
-/
theorem equation_at_time_apply_of_zero_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_ricci_flow_equation_verification
          (zero_ricci_flow_equation_verification
            identifiesDerivative identifiesRicci))) t x v w =
        ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t x v w :=
  equation_at_time_apply_of_ricci_flow_equation_verification_projection
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci) t x v w

/-- The pointwise zero equation theorem is the projection-routed proof. -/
@[simp] theorem equation_at_time_apply_of_zero_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci t x v w =
      equation_at_time_apply_of_ricci_flow_equation_verification_projection
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) t x v w :=
  rfl

/--
Ricci-flow data with zero Ricci/scalar candidates.

The abstract equation-interface evidence is still an explicit input; this does
not manufacture `SatisfiesRicciFlowEquation`.
-/
noncomputable def zero_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowData I n M where
  metric := g
  curvature := zero_ricci_curvature_data identifiesRicci
  equation := equationEvidence

/-- The zero Ricci-flow data package stores the supplied metric and evidence. -/
@[simp] theorem zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    zero_ricci_flow_data g identifiesRicci equationEvidence =
      ({ metric := g
         curvature := zero_ricci_curvature_data identifiesRicci
         equation := equationEvidence } : RicciFlowData I n M) :=
  rfl

/-- The metric projection of zero Ricci-flow data is the supplied metric. -/
@[simp] theorem metric_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    metric_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) = g :=
  rfl

/-- The curvature projection of zero Ricci-flow data is the zero curvature package. -/
@[simp] theorem curvature_data_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    curvature_data_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) =
        zero_ricci_curvature_data identifiesRicci :=
  rfl

/-- The right-hand side projected from zero Ricci-flow data is the zero tensor. -/
@[simp] theorem ricci_flow_rhs_tensor_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    ricci_flow_rhs_tensor
      (curvature_data_of_ricci_flow_data
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) t =
        zero_tangent_covariant_two_tensor I M := by
  change ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t =
    zero_tangent_covariant_two_tensor I M
  exact
    ricci_flow_rhs_tensor_of_zero_ricci_curvature_data_eq
      (g := g) identifiesRicci t

/-- Pointwise, the RHS projected from zero Ricci-flow data is scalar zero. -/
@[simp] theorem ricci_flow_rhs_tensor_apply_of_zero_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    ricci_flow_rhs_tensor
      (curvature_data_of_ricci_flow_data
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) t x v w = 0 := by
  change ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t x v w = 0
  exact
    ricci_flow_rhs_tensor_apply_of_zero_ricci_curvature_data
      (g := g) identifiesRicci t x v w

/-- The pointwise zero Ricci-flow-data RHS proof is the zero-curvature-data proof. -/
@[simp] theorem ricci_flow_rhs_tensor_apply_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    ricci_flow_rhs_tensor_apply_of_zero_ricci_flow_data
      g identifiesRicci equationEvidence t x v w =
      (by
        change ricci_flow_rhs_tensor (zero_ricci_curvature_data identifiesRicci) t x v w = 0
        exact
          ricci_flow_rhs_tensor_apply_of_zero_ricci_curvature_data
            (g := g) identifiesRicci t x v w) := by
  apply Subsingleton.elim

/-- The equation projection of zero Ricci-flow data is the supplied equation evidence. -/
@[simp] theorem equation_evidence_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    equation_evidence_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) =
        equationEvidence :=
  rfl

/-- The metric time-slice of zero Ricci-flow data is the supplied metric family. -/
@[simp] theorem metric_at_time_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (g : TimeDependentRiemannianMetric I n M)
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    metric_at_time_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) t =
        g.metricAtTime t :=
  rfl

/-- The Ricci tensor time-slice of zero Ricci-flow data is the zero tensor. -/
@[simp] theorem ricci_tensor_at_time_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    ricci_tensor_at_time_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) t =
        zero_tangent_covariant_two_tensor I M :=
  rfl

/-- The scalar-curvature time-slice of zero Ricci-flow data is zero. -/
@[simp] theorem scalar_curvature_at_time_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) (x : M) :
    scalar_curvature_at_time_of_ricci_flow_data
      (zero_ricci_flow_data g identifiesRicci equationEvidence) t x = 0 :=
  rfl

/--
The metric time-slice of stationary zero Ricci-flow data is the original
Riemannian metric.
-/
@[simp] theorem metric_at_time_of_stationary_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
    (identifiesRicci :
      IsRicciTensorOf
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_tensor_field
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (t : ℝ) :
    metric_at_time_of_ricci_flow_data
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) t =
        metric :=
  rfl

/--
Zero metric derivative and zero Ricci candidates satisfy the explicit
Ricci-flow equation verification once their still-missing analytic
identification evidence is supplied.

This is only an equation-verification consistency result. It deliberately does
not construct the abstract `SatisfiesRicciFlowEquation` interface.
-/
theorem zero_derivative_zero_ricci_equation_verification_exists
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    ∃ curvature : RicciCurvatureData g,
      curvature.ricci = zero_ricci_tensor_field g ∧
      curvature.scalar = zero_scalar_curvature_field g ∧
      ∃ verification : RicciFlowEquationVerification curvature,
        verification.metricDerivative.derivative = zero_metric_time_derivative_field g ∧
        ∀ t,
          metric_time_derivative_at_time_of_metric_derivative_field
            verification.metricDerivative.derivative t =
            ricci_flow_rhs_tensor curvature t := by
  let curvature : RicciCurvatureData g :=
    zero_ricci_curvature_data identifiesRicci
  let verification : RicciFlowEquationVerification curvature :=
    zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci
  exact ⟨curvature, rfl, rfl, verification, rfl, verification.equationAtTime⟩

/--
The zero-derivative/zero-Ricci consistency theorem is exactly the explicit
curvature, derivative-data, and equation-verification payload construction.
-/
theorem zero_derivative_zero_ricci_equation_verification_exists_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g)) :
    zero_derivative_zero_ricci_equation_verification_exists
      identifiesDerivative identifiesRicci =
      (by
        let curvature : RicciCurvatureData g :=
          zero_ricci_curvature_data identifiesRicci
        let verification : RicciFlowEquationVerification curvature :=
          zero_ricci_flow_equation_verification
            identifiesDerivative identifiesRicci
        exact
          ⟨curvature, rfl, rfl, verification, rfl,
            verification.equationAtTime⟩) := by
  apply Subsingleton.elim

/--
The stationary metric-family specialization of the zero derivative / zero Ricci
equation-verification payload.
-/
theorem stationary_zero_derivative_zero_ricci_equation_verification_exists
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
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
    ∃ curvature :
        RicciCurvatureData
          (stationary_time_dependent_riemannian_metric metric),
      curvature.ricci =
          zero_ricci_tensor_field
            (stationary_time_dependent_riemannian_metric metric) ∧
      curvature.scalar =
          zero_scalar_curvature_field
            (stationary_time_dependent_riemannian_metric metric) ∧
      ∃ verification : RicciFlowEquationVerification curvature,
        verification.metricDerivative.derivative =
            zero_metric_time_derivative_field
              (stationary_time_dependent_riemannian_metric metric) ∧
        ∀ t,
          metric_time_derivative_at_time_of_metric_derivative_field
            verification.metricDerivative.derivative t =
            ricci_flow_rhs_tensor curvature t :=
  zero_derivative_zero_ricci_equation_verification_exists
    identifiesDerivative identifiesRicci

/--
The stationary specialization delegates to the generic zero-candidate
verification route.
-/
theorem stationary_zero_derivative_zero_ricci_equation_verification_exists_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (metric :
      ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x))
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
    stationary_zero_derivative_zero_ricci_equation_verification_exists
      metric identifiesDerivative identifiesRicci =
      zero_derivative_zero_ricci_equation_verification_exists
        identifiesDerivative identifiesRicci := by
  apply Subsingleton.elim

end Poincare
