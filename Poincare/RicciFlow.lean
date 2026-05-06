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

end Poincare
