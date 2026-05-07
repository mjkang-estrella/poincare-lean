/-
Typed interfaces for the analytic Ricci-flow foundation.

This module narrows the `ricciFlowAnalyticFoundation` milestone into the
curvature and PDE layers that have to exist before the surgery package can be a
real theorem. The predicates have no constructors here; they are proof
obligations for future formalization, not assumptions manufactured locally.
-/

import Poincare.RicciFlow

universe u v

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/-- Interface for the Levi-Civita connection theory of a time-dependent metric. -/
inductive HasLeviCivitaConnectionTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for existence of a Levi-Civita connection for each metric time slice. -/
inductive HasLeviCivitaConnectionExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for uniqueness of the Levi-Civita connection. -/
inductive HasLeviCivitaConnectionUniqueness
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the torsion-free property of the Levi-Civita connection. -/
inductive HasLeviCivitaTorsionFreeProperty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for metric compatibility of the Levi-Civita connection. -/
inductive HasLeviCivitaMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the Riemann-curvature tensor theory of a time-dependent metric. -/
inductive HasRiemannCurvatureTensorTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for constructing the Riemann curvature tensor from the connection. -/
inductive HasRiemannCurvatureTensorConstruction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the standard symmetries of the Riemann curvature tensor. -/
inductive HasRiemannCurvatureTensorSymmetries
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the first Bianchi identity. -/
inductive HasFirstBianchiIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the second Bianchi identity. -/
inductive HasSecondBianchiIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for deriving the Ricci tensor by contracting curvature. -/
inductive HasRicciContractionTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (_curvature : RicciCurvatureData g) : Prop

/-- Interface for the contraction formula defining the Ricci tensor. -/
inductive HasRicciTensorContractionFormula
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (_curvature : RicciCurvatureData g) : Prop

/-- Interface for the contraction formula defining scalar curvature. -/
inductive HasScalarCurvatureContractionFormula
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (_curvature : RicciCurvatureData g) : Prop

/-- Interface for regularity of the time-dependent metric family. -/
inductive HasTimeDependentMetricRegularity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for the time derivative of the metric family. -/
inductive HasMetricTimeDerivativeTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_g : TimeDependentRiemannianMetric I n M) : Prop

/-- Interface for scalar curvature derived from Ricci-curvature data. -/
inductive HasScalarCurvatureTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (_curvature : RicciCurvatureData g) : Prop

/-- Interface for deriving the Ricci-flow equation from metric derivative and Ricci data. -/
inductive HasRicciFlowEquationDerivation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/--
Boundary package for the explicit Ricci-flow equation `∂ₜ g = -2 Ricci`.

The package separates the concrete pointwise equation verification from the
abstract `SatisfiesRicciFlowEquation` interface carried by existing flow data.
-/
structure RicciFlowEquationBoundaryPackage
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) where
  /-- Explicit pointwise verification of `∂ₜ g = -2 Ricci`. -/
  verification :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)
  /-- The existing equation-interface evidence for the same flow. -/
  equationEvidence :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)

/-- Project explicit equation verification from an equation-boundary package. -/
def ricci_flow_equation_verification_of_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow) :=
  package.verification

/-- The boundary-package equation-verification projection is stored data. -/
@[simp] theorem ricci_flow_equation_verification_of_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    ricci_flow_equation_verification_of_boundary_package package =
      package.verification :=
  rfl

/-- Project metric-derivative data from an equation-boundary package. -/
def metric_derivative_data_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    MetricTimeDerivativeData (metric_of_ricci_flow_data flow) :=
  metric_derivative_data_of_ricci_flow_equation_verification
    package.verification

/-- The boundary-package metric-derivative projection delegates to verification. -/
@[simp] theorem metric_derivative_data_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    metric_derivative_data_of_equation_boundary_package package =
      metric_derivative_data_of_ricci_flow_equation_verification
        package.verification :=
  rfl

/-- An equation-boundary package supplies the explicit equation at time `t`. -/
theorem equation_at_time_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      package.verification.metricDerivative.derivative t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t :=
  equation_at_time_of_ricci_flow_equation_verification
    package.verification t

/-- The named boundary-package equation theorem is stored verification evidence. -/
@[simp] theorem equation_at_time_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    equation_at_time_of_equation_boundary_package package t =
      package.verification.equationAtTime t :=
  rfl

/-- An equation-boundary package carries metric-derivative identification evidence. -/
theorem metric_time_derivative_identification_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    IsMetricTimeDerivativeOf
      (metric_of_ricci_flow_data flow)
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) :=
  metric_time_derivative_identification_of_ricci_flow_equation_verification
    package.verification

/-- The boundary-package derivative-identification theorem is stored verification evidence. -/
@[simp] theorem metric_time_derivative_identification_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    metric_time_derivative_identification_of_equation_boundary_package
      package = package.verification.metricDerivative.identifiesDerivative :=
  rfl

/--
The boundary-package equation equality also holds through the named
metric-derivative projection.
-/
theorem equation_at_time_of_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) t =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t :=
  equation_at_time_of_ricci_flow_equation_verification_projection
    package.verification t

/-- The boundary-package projection-routed equation theorem is stored evidence. -/
@[simp] theorem equation_at_time_of_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) (t : ℝ) :
    equation_at_time_of_equation_boundary_package_projection package t =
      package.verification.equationAtTime t :=
  rfl

/--
The boundary-package projection-routed equation also holds pointwise at a point
and pair of tangent vectors.
-/
theorem equation_at_time_apply_of_equation_boundary_package_projection
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_equation_boundary_package package)) t x v w =
        ricci_flow_rhs_tensor (curvature_data_of_ricci_flow_data flow) t x v w :=
  congrArg (fun tensor => tensor x v w)
    (equation_at_time_of_equation_boundary_package_projection package t)

/-- The pointwise boundary-package equation proof is tensor equality application. -/
@[simp] theorem equation_at_time_apply_of_equation_boundary_package_projection_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    equation_at_time_apply_of_equation_boundary_package_projection
      package t x v w =
      congrArg (fun tensor => tensor x v w)
        (equation_at_time_of_equation_boundary_package_projection package t) := by
  apply Subsingleton.elim

/-- Project equation-interface evidence from an equation-boundary package. -/
theorem equation_evidence_of_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow) :=
  package.equationEvidence

/-- The boundary-package equation-interface theorem is stored evidence. -/
@[simp] theorem equation_evidence_of_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (package : RicciFlowEquationBoundaryPackage flow) :
    equation_evidence_of_equation_boundary_package package =
      package.equationEvidence :=
  rfl

/-- Statement that the explicit Ricci-flow equation boundary is available. -/
def RicciFlowEquationBoundaryStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  Nonempty (RicciFlowEquationBoundaryPackage flow)

/-- The equation-boundary statement is nonemptiness of the boundary package. -/
theorem ricciFlowEquationBoundaryStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    RicciFlowEquationBoundaryStatement flow =
      Nonempty (RicciFlowEquationBoundaryPackage flow) :=
  rfl

/--
Assemble the equation-boundary package from explicit pointwise
`∂ₜ g = -2 Ricci` verification for the same flow.

The abstract equation-interface evidence still comes from the checked
`RicciFlowData`; the explicit verification is not used to manufacture it.
-/
def equation_boundary_package_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    RicciFlowEquationBoundaryPackage flow where
  verification := verification
  equationEvidence := equation_evidence_of_ricci_flow_data flow

/-- The verification-to-boundary-package constructor stores the supplied fields. -/
@[simp] theorem equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_boundary_package_of_ricci_flow_equation_verification
      flow verification =
        ({ verification := verification
           equationEvidence := equation_evidence_of_ricci_flow_data flow } :
          RicciFlowEquationBoundaryPackage flow) :=
  rfl

/-- The constructed boundary package projects back to the supplied verification. -/
@[simp] theorem ricci_flow_equation_verification_of_equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ricci_flow_equation_verification_of_boundary_package
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification) =
        verification :=
  rfl

/-- The constructed boundary package carries the flow's stored equation evidence. -/
@[simp] theorem equation_evidence_of_equation_boundary_package_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    equation_evidence_of_equation_boundary_package
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification) =
        equation_evidence_of_ricci_flow_data flow :=
  rfl

/-- A supplied explicit Ricci-flow equation verification exposes the boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    RicciFlowEquationBoundaryStatement flow :=
  ⟨equation_boundary_package_of_ricci_flow_equation_verification
    flow verification⟩

/-- The verification-to-boundary statement route is nonemptiness of the package route. -/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
      flow verification =
        ⟨equation_boundary_package_of_ricci_flow_equation_verification
          flow verification⟩ := by
  apply Subsingleton.elim

/--
Equation-boundary package for zero Ricci-flow data.

The metric-derivative identification, Ricci identification, and abstract
equation-interface evidence are all supplied inputs; this only routes the
explicit zero equation verification through the analytic boundary package.
-/
noncomputable def zero_ricci_flow_equation_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryPackage
      (zero_ricci_flow_data g identifiesRicci equationEvidence) :=
  equation_boundary_package_of_ricci_flow_equation_verification
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    (zero_ricci_flow_equation_verification
      identifiesDerivative identifiesRicci)

/-- The zero equation-boundary package is assembled from the zero verification. -/
@[simp] theorem zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    zero_ricci_flow_equation_boundary_package
      identifiesDerivative identifiesRicci equationEvidence =
      equation_boundary_package_of_ricci_flow_equation_verification
        (zero_ricci_flow_data g identifiesRicci equationEvidence)
        (zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci) :=
  rfl

/-- Equation-boundary package for stationary zero Ricci-flow data. -/
noncomputable def stationary_zero_ricci_flow_equation_boundary_package
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryPackage
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) :=
  zero_ricci_flow_equation_boundary_package
    identifiesDerivative identifiesRicci equationEvidence

/-- The stationary zero equation-boundary package delegates to the zero package. -/
@[simp] theorem stationary_zero_ricci_flow_equation_boundary_package_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    stationary_zero_ricci_flow_equation_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence =
      zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence :=
  rfl

/-- The zero boundary package projects to the explicit zero equation verification. -/
@[simp] theorem ricci_flow_equation_verification_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ricci_flow_equation_verification_of_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
        zero_ricci_flow_equation_verification
          identifiesDerivative identifiesRicci :=
  rfl

/-- The stationary zero boundary package projects to the zero equation verification. -/
@[simp] theorem ricci_flow_equation_verification_of_stationary_zero_ricci_flow_equation_boundary_package_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ricci_flow_equation_verification_of_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      zero_ricci_flow_equation_verification
        identifiesDerivative identifiesRicci :=
  rfl

/-- The zero boundary package keeps the supplied abstract equation evidence. -/
@[simp] theorem equation_evidence_of_zero_ricci_flow_equation_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    equation_evidence_of_equation_boundary_package
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence) =
        equationEvidence :=
  rfl

/-- The stationary zero boundary package keeps the supplied equation evidence. -/
@[simp] theorem equation_evidence_of_stationary_zero_ricci_flow_equation_boundary_package_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    equation_evidence_of_equation_boundary_package
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence) =
      equationEvidence :=
  rfl

/-- Zero Ricci-flow data with explicit zero verification exposes the boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) :=
  ⟨zero_ricci_flow_equation_boundary_package
    identifiesDerivative identifiesRicci equationEvidence⟩

/-- The zero boundary-statement route is nonemptiness of the zero boundary package. -/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci)) :
    ricciFlowEquationBoundaryStatement_of_zero_ricci_flow_data
      identifiesDerivative identifiesRicci equationEvidence =
      ⟨zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence⟩ := by
  apply Subsingleton.elim

/-- Stationary zero Ricci-flow data exposes the equation-boundary statement. -/
theorem ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    RicciFlowEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) :=
  ⟨stationary_zero_ricci_flow_equation_boundary_package
    metric identifiesDerivative identifiesRicci equationEvidence⟩

/--
The stationary zero boundary-statement route is nonemptiness of the stationary
zero boundary package.
-/
@[simp] theorem ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci)) :
    ricciFlowEquationBoundaryStatement_of_stationary_zero_ricci_flow_data
      metric identifiesDerivative identifiesRicci equationEvidence =
      ⟨stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence⟩ := by
  apply Subsingleton.elim

/-- Interface for compatibility of the flow with the prescribed initial metric. -/
inductive HasInitialMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the DeTurck gauge-fixing input used to make the PDE parabolic. -/
inductive HasDeTurckGaugeFixing
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for compatibility of the background metric in DeTurck gauge. -/
inductive HasDeTurckBackgroundMetricCompatibility
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for constructing the DeTurck vector field. -/
inductive HasDeTurckVectorFieldConstruction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for deriving the Ricci-DeTurck equation from the Ricci-flow equation. -/
inductive HasDeTurckEquationDerivation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the linearization of the Ricci-DeTurck operator. -/
inductive HasRicciDeTurckLinearization
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for strict parabolicity of the Ricci-DeTurck system. -/
inductive HasStrictlyParabolicDeTurckSystem
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for linear parabolic theory used by Ricci-DeTurck flow. -/
inductive HasParabolicLinearTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the contraction/fixed-point argument for Ricci-DeTurck flow. -/
inductive HasParabolicFixedPointArgument
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for short-time existence of the Ricci-DeTurck flow. -/
inductive HasDeTurckShortTimeExistence
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for bootstrapping short-time Ricci-DeTurck solutions to smoothness. -/
inductive HasShortTimeRegularityBootstrap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for solving the DeTurck diffeomorphism ODE. -/
inductive HasDeTurckDiffeomorphismODE
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface identifying the pulled-back DeTurck equation with Ricci flow. -/
inductive HasDeTurckPullbackEquationIdentity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for pulling a Ricci-DeTurck solution back to a Ricci-flow solution. -/
inductive HasDeTurckPullbackToRicciFlow
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the short-time existence theorem for Ricci flow. -/
inductive HasShortTimeRicciFlowSolution
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the maximal-time interval of a Ricci-flow solution. -/
inductive HasRicciFlowMaximalTimeInterval
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the continuation criterion needed before surgery starts. -/
inductive HasRicciFlowContinuationCriterion
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the curvature blow-up alternative in the continuation criterion. -/
inductive HasCurvatureBlowUpContinuationCriterion
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for extending bounded-curvature solutions past a finite time. -/
inductive HasMaximalSolutionExtension
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the parabolic Schauder estimates used by Ricci-flow regularity. -/
inductive HasParabolicSchauderEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for parabolic regularity estimates for the Ricci-flow PDE. -/
inductive HasRicciFlowParabolicRegularity
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for Shi-type derivative estimates along Ricci flow. -/
inductive HasShiDerivativeEstimates
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for bootstrapping curvature derivative bounds from Shi estimates. -/
inductive HasCurvatureDerivativeBootstrap
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for Hamilton's tensor maximum principle in the Ricci-flow setting. -/
inductive HasHamiltonMaximumPrinciple
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for uniqueness of the Ricci-flow solution. -/
inductive HasRicciFlowUniquenessTheory
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the metric evolution equation along Ricci flow. -/
inductive HasMetricEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the Ricci tensor evolution equation along Ricci flow. -/
inductive HasRicciTensorEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the scalar curvature evolution equation along Ricci flow. -/
inductive HasScalarCurvatureEvolutionEquation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for the curvature-norm evolution inequality used in estimates. -/
inductive HasCurvatureNormEvolutionInequality
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/-- Interface for curvature evolution equations along Ricci flow. -/
inductive HasCurvatureEvolutionEquations
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_flow : RicciFlowData I n M) : Prop

/--
Analytic foundation package for Ricci flow before surgery.

The package records a Ricci-flow solution plus the connection, curvature,
Ricci-contraction, short-time existence, and continuation-theorem inputs that a
real formalization would have to prove.
-/
structure RicciFlowAnalyticFoundationPackage
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] where
  /-- Ricci-flow data supplied by the analytic foundation. -/
  flow : RicciFlowData I n M
  /-- Existence of the Levi-Civita connection for the metric family. -/
  leviCivitaExistence :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow)
  /-- Uniqueness of the Levi-Civita connection. -/
  leviCivitaUniqueness :
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow)
  /-- Torsion-free property of the Levi-Civita connection. -/
  leviCivitaTorsionFree :
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow)
  /-- Metric compatibility of the Levi-Civita connection. -/
  leviCivitaMetricCompatibility :
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow)
  /-- Levi-Civita connection theory for the metric family. -/
  leviCivita :
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow)
  /-- Construction of the Riemann curvature tensor. -/
  riemannCurvatureConstruction :
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow)
  /-- Standard Riemann curvature tensor symmetries. -/
  riemannCurvatureSymmetries :
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow)
  /-- First Bianchi identity for the Riemann tensor. -/
  firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow)
  /-- Second Bianchi identity for the Riemann tensor. -/
  secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow)
  /-- Riemann-curvature tensor theory for the metric family. -/
  riemannCurvature :
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow)
  /-- Ricci tensor contraction formula. -/
  ricciContractionFormula :
    HasRicciTensorContractionFormula (curvature_data_of_ricci_flow_data flow)
  /-- Scalar-curvature contraction formula. -/
  scalarCurvatureContraction :
    HasScalarCurvatureContractionFormula (curvature_data_of_ricci_flow_data flow)
  /-- Ricci tensor obtained from curvature contraction. -/
  ricciContraction :
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow)
  /-- Regularity of the time-dependent metric family. -/
  metricRegularity :
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow)
  /-- Time-derivative theory for the metric family. -/
  metricTimeDerivative :
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow)
  /-- Scalar-curvature theory attached to the curvature data. -/
  scalarCurvature :
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow)
  /-- Derivation of the Ricci-flow equation from the analytic objects. -/
  equationDerivation : HasRicciFlowEquationDerivation flow
  /-- Compatibility of the flow with the initial metric. -/
  initialMetricCompatibility : HasInitialMetricCompatibility flow
  /-- DeTurck gauge-fixing input for the Ricci-flow PDE. -/
  deturckGauge : HasDeTurckGaugeFixing flow
  /-- Compatibility of the background metric used by DeTurck gauge. -/
  deturckBackgroundMetric :
    HasDeTurckBackgroundMetricCompatibility flow
  /-- Construction of the DeTurck vector field. -/
  deturckVectorField : HasDeTurckVectorFieldConstruction flow
  /-- Derivation of the Ricci-DeTurck equation. -/
  deturckEquation : HasDeTurckEquationDerivation flow
  /-- Linearization of the Ricci-DeTurck operator. -/
  deturckLinearization : HasRicciDeTurckLinearization flow
  /-- Strict parabolicity of the DeTurck-gauged equation. -/
  strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow
  /-- Linear parabolic theory for the DeTurck system. -/
  parabolicLinearTheory : HasParabolicLinearTheory flow
  /-- Fixed-point argument for the nonlinear DeTurck system. -/
  parabolicFixedPoint : HasParabolicFixedPointArgument flow
  /-- Short-time existence for Ricci-DeTurck flow. -/
  deturckShortTime : HasDeTurckShortTimeExistence flow
  /-- Regularity bootstrap for the short-time DeTurck solution. -/
  shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow
  /-- ODE for DeTurck diffeomorphisms. -/
  deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow
  /-- Identification of the pulled-back DeTurck equation with Ricci flow. -/
  deturckPullbackEquationIdentity :
    HasDeTurckPullbackEquationIdentity flow
  /-- Pullback from DeTurck flow to Ricci flow. -/
  deturckPullback : HasDeTurckPullbackToRicciFlow flow
  /-- Short-time existence of the Ricci-flow solution. -/
  shortTimeExistence : HasShortTimeRicciFlowSolution flow
  /-- Maximal time interval for the Ricci-flow solution. -/
  maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow
  /-- Continuation criterion for the Ricci-flow solution. -/
  continuationCriterion : HasRicciFlowContinuationCriterion flow
  /-- Curvature blow-up alternative in the continuation theorem. -/
  curvatureBlowUpCriterion : HasCurvatureBlowUpContinuationCriterion flow
  /-- Extension theorem for bounded-curvature maximal solutions. -/
  maximalSolutionExtension : HasMaximalSolutionExtension flow
  /-- Parabolic Schauder estimates for the gauged/ungauged PDE. -/
  parabolicSchauder : HasParabolicSchauderEstimates flow
  /-- Parabolic regularity estimates for the Ricci-flow PDE. -/
  parabolicRegularity : HasRicciFlowParabolicRegularity flow
  /-- Shi-type derivative estimates along the flow. -/
  shiDerivativeEstimates : HasShiDerivativeEstimates flow
  /-- Curvature derivative bootstrap from Shi estimates. -/
  curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow
  /-- Hamilton maximum-principle input for tensor estimates. -/
  maximumPrinciple : HasHamiltonMaximumPrinciple flow
  /-- Uniqueness theory for the Ricci-flow solution. -/
  uniquenessTheory : HasRicciFlowUniquenessTheory flow
  /-- Metric evolution equation along Ricci flow. -/
  metricEvolution : HasMetricEvolutionEquation flow
  /-- Ricci tensor evolution equation along Ricci flow. -/
  ricciTensorEvolution : HasRicciTensorEvolutionEquation flow
  /-- Scalar curvature evolution equation along Ricci flow. -/
  scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow
  /-- Curvature-norm evolution inequality along Ricci flow. -/
  curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow
  /-- Curvature evolution equations along the flow. -/
  curvatureEvolution : HasCurvatureEvolutionEquations flow

/--
The fixed-flow analytic derivation statement: the Ricci-flow data is accompanied
by the connection, curvature, DeTurck, short-time, continuation, regularity, and
evolution evidence that accounts for its Ricci-identification and equation
interfaces.
-/
def AnalyticFoundationDerivationStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  ∃ _leviCivitaExistence :
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaUniqueness :
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaTorsionFree :
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow),
  ∃ _leviCivitaMetricCompatibility :
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow),
  ∃ _leviCivita :
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvatureConstruction :
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvatureSymmetries :
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow),
  ∃ _firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow),
  ∃ _secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow),
  ∃ _riemannCurvature :
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow),
  ∃ _ricciContractionFormula :
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data flow),
  ∃ _scalarCurvatureContraction :
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data flow),
  ∃ _ricciContraction :
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow),
  ∃ _metricRegularity :
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow),
  ∃ _metricTimeDerivative :
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow),
  ∃ _scalarCurvature :
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow),
  ∃ _equationDerivation : HasRicciFlowEquationDerivation flow,
  ∃ _initialMetricCompatibility : HasInitialMetricCompatibility flow,
  ∃ _deturckGauge : HasDeTurckGaugeFixing flow,
  ∃ _deturckBackgroundMetric :
    HasDeTurckBackgroundMetricCompatibility flow,
  ∃ _deturckVectorField : HasDeTurckVectorFieldConstruction flow,
  ∃ _deturckEquation : HasDeTurckEquationDerivation flow,
  ∃ _deturckLinearization : HasRicciDeTurckLinearization flow,
  ∃ _strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow,
  ∃ _parabolicLinearTheory : HasParabolicLinearTheory flow,
  ∃ _parabolicFixedPoint : HasParabolicFixedPointArgument flow,
  ∃ _deturckShortTime : HasDeTurckShortTimeExistence flow,
  ∃ _shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow,
  ∃ _deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow,
  ∃ _deturckPullbackEquationIdentity :
    HasDeTurckPullbackEquationIdentity flow,
  ∃ _deturckPullback : HasDeTurckPullbackToRicciFlow flow,
  ∃ _shortTimeExistence : HasShortTimeRicciFlowSolution flow,
  ∃ _maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow,
  ∃ _continuationCriterion : HasRicciFlowContinuationCriterion flow,
  ∃ _curvatureBlowUpCriterion :
    HasCurvatureBlowUpContinuationCriterion flow,
  ∃ _maximalSolutionExtension : HasMaximalSolutionExtension flow,
  ∃ _parabolicSchauder : HasParabolicSchauderEstimates flow,
  ∃ _parabolicRegularity : HasRicciFlowParabolicRegularity flow,
  ∃ _shiDerivativeEstimates : HasShiDerivativeEstimates flow,
  ∃ _curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow,
  ∃ _maximumPrinciple : HasHamiltonMaximumPrinciple flow,
  ∃ _uniquenessTheory : HasRicciFlowUniquenessTheory flow,
  ∃ _metricEvolution : HasMetricEvolutionEquation flow,
  ∃ _ricciTensorEvolution : HasRicciTensorEvolutionEquation flow,
  ∃ _scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow,
  ∃ _curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow,
  ∃ _curvatureEvolution : HasCurvatureEvolutionEquations flow,
  ∃ _ricciIdentification :
    IsRicciTensorOf
      (metric_of_ricci_flow_data flow)
      (ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data flow)),
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data flow)
      (curvature_data_of_ricci_flow_data flow)

/--
The fixed-flow analytic derivation statement is exactly the listed connection,
curvature, DeTurck, short-time, continuation, regularity, evolution,
Ricci-identification, and Ricci-flow equation witness stack.
-/
theorem analyticFoundationDerivationStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationDerivationStatement flow =
      (∃ _leviCivitaExistence :
        HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaUniqueness :
        HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaTorsionFree :
        HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow),
      ∃ _leviCivitaMetricCompatibility :
        HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow),
      ∃ _leviCivita :
        HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvatureConstruction :
        HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvatureSymmetries :
        HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow),
      ∃ _firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow),
      ∃ _secondBianchi :
        HasSecondBianchiIdentity (metric_of_ricci_flow_data flow),
      ∃ _riemannCurvature :
        HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow),
      ∃ _ricciContractionFormula :
        HasRicciTensorContractionFormula
          (curvature_data_of_ricci_flow_data flow),
      ∃ _scalarCurvatureContraction :
        HasScalarCurvatureContractionFormula
          (curvature_data_of_ricci_flow_data flow),
      ∃ _ricciContraction :
        HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow),
      ∃ _metricRegularity :
        HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow),
      ∃ _metricTimeDerivative :
        HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow),
      ∃ _scalarCurvature :
        HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow),
      ∃ _equationDerivation : HasRicciFlowEquationDerivation flow,
      ∃ _initialMetricCompatibility : HasInitialMetricCompatibility flow,
      ∃ _deturckGauge : HasDeTurckGaugeFixing flow,
      ∃ _deturckBackgroundMetric :
        HasDeTurckBackgroundMetricCompatibility flow,
      ∃ _deturckVectorField : HasDeTurckVectorFieldConstruction flow,
      ∃ _deturckEquation : HasDeTurckEquationDerivation flow,
      ∃ _deturckLinearization : HasRicciDeTurckLinearization flow,
      ∃ _strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow,
      ∃ _parabolicLinearTheory : HasParabolicLinearTheory flow,
      ∃ _parabolicFixedPoint : HasParabolicFixedPointArgument flow,
      ∃ _deturckShortTime : HasDeTurckShortTimeExistence flow,
      ∃ _shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow,
      ∃ _deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow,
      ∃ _deturckPullbackEquationIdentity :
        HasDeTurckPullbackEquationIdentity flow,
      ∃ _deturckPullback : HasDeTurckPullbackToRicciFlow flow,
      ∃ _shortTimeExistence : HasShortTimeRicciFlowSolution flow,
      ∃ _maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow,
      ∃ _continuationCriterion : HasRicciFlowContinuationCriterion flow,
      ∃ _curvatureBlowUpCriterion :
        HasCurvatureBlowUpContinuationCriterion flow,
      ∃ _maximalSolutionExtension : HasMaximalSolutionExtension flow,
      ∃ _parabolicSchauder : HasParabolicSchauderEstimates flow,
      ∃ _parabolicRegularity : HasRicciFlowParabolicRegularity flow,
      ∃ _shiDerivativeEstimates : HasShiDerivativeEstimates flow,
      ∃ _curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow,
      ∃ _maximumPrinciple : HasHamiltonMaximumPrinciple flow,
      ∃ _uniquenessTheory : HasRicciFlowUniquenessTheory flow,
      ∃ _metricEvolution : HasMetricEvolutionEquation flow,
      ∃ _ricciTensorEvolution : HasRicciTensorEvolutionEquation flow,
      ∃ _scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow,
      ∃ _curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow,
      ∃ _curvatureEvolution : HasCurvatureEvolutionEquations flow,
      ∃ _ricciIdentification :
        IsRicciTensorOf
          (metric_of_ricci_flow_data flow)
          (ricci_tensor_field_of_curvature_data
            (curvature_data_of_ricci_flow_data flow)),
        SatisfiesRicciFlowEquation
          (metric_of_ricci_flow_data flow)
          (curvature_data_of_ricci_flow_data flow)) :=
  rfl

/--
The theorem-shaped analytic foundation statement supplied by a completed
analytic package.
-/
def RicciFlowAnalyticFoundationStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    Prop :=
  ∃ flow : RicciFlowData I n M, AnalyticFoundationDerivationStatement flow

/--
The theorem-shaped analytic-foundation interface is exactly existence of
Ricci-flow data equipped with the fixed-flow analytic derivation statement.
-/
theorem ricciFlowAnalyticFoundationStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    RicciFlowAnalyticFoundationStatement I n M =
      (∃ flow : RicciFlowData I n M,
        AnalyticFoundationDerivationStatement flow) :=
  rfl

/--
Analytic foundation strengthened with the explicit Ricci-flow equation boundary.

This is a theorem-shaped target for future wiring: it requires both the existing
analytic derivation stack and a boundary package witnessing the pointwise
equation `∂ₜ g = -2 Ricci`.
-/
def AnalyticFoundationWithEquationBoundaryStatement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  AnalyticFoundationDerivationStatement flow ∧
    RicciFlowEquationBoundaryStatement flow

/-- The strengthened analytic-boundary statement is a conjunction of its parts. -/
theorem analyticFoundationWithEquationBoundaryStatement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationWithEquationBoundaryStatement flow =
      (AnalyticFoundationDerivationStatement flow ∧
        RicciFlowEquationBoundaryStatement flow) :=
  rfl

/-- Assemble the strengthened analytic-boundary statement from its components. -/
theorem analytic_foundation_with_equation_boundary_of_derivation_and_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (boundary : RicciFlowEquationBoundaryStatement flow) :
    AnalyticFoundationWithEquationBoundaryStatement flow :=
  ⟨derivation, boundary⟩

/-- The strengthened analytic-boundary assembler is the conjunction constructor. -/
@[simp] theorem analytic_foundation_with_equation_boundary_of_derivation_and_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (boundary : RicciFlowEquationBoundaryStatement flow) :
    analytic_foundation_with_equation_boundary_of_derivation_and_boundary
      derivation boundary =
        ⟨derivation, boundary⟩ :=
  rfl

/--
Assemble the strengthened analytic-boundary statement from the analytic
derivation stack and explicit pointwise Ricci-flow equation verification.
-/
theorem analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationWithEquationBoundaryStatement flow :=
  analytic_foundation_with_equation_boundary_of_derivation_and_boundary
    derivation
    (ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
      flow verification)

/--
The derivation-plus-verification route delegates to the boundary-statement
constructor built from the supplied explicit equation verification.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (derivation : AnalyticFoundationDerivationStatement flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_with_equation_boundary_of_derivation_and_ricci_flow_equation_verification
      derivation verification =
      analytic_foundation_with_equation_boundary_of_derivation_and_boundary
        derivation
        (ricciFlowEquationBoundaryStatement_of_ricci_flow_equation_verification
          flow verification) := by
  apply Subsingleton.elim

/-- Project the analytic derivation stack from the strengthened statement. -/
theorem analytic_foundation_derivation_of_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    AnalyticFoundationDerivationStatement flow :=
  statement.1

/-- The analytic-derivation projection is the first component. -/
@[simp] theorem analytic_foundation_derivation_of_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    analytic_foundation_derivation_of_with_equation_boundary statement =
      statement.1 :=
  rfl

/-- Project the equation boundary from the strengthened statement. -/
theorem equation_boundary_of_analytic_foundation_with_equation_boundary
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    RicciFlowEquationBoundaryStatement flow :=
  statement.2

/-- The equation-boundary projection is the second component. -/
@[simp] theorem equation_boundary_of_analytic_foundation_with_equation_boundary_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (statement : AnalyticFoundationWithEquationBoundaryStatement flow) :
    equation_boundary_of_analytic_foundation_with_equation_boundary statement =
      statement.2 :=
  rfl

/--
Assemble the fixed-flow analytic derivation statement from the named analytic
foundation components.
-/
theorem analytic_foundation_derivation_statement_of_components
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (leviCivitaExistence :
      HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow))
    (leviCivitaUniqueness :
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow))
    (leviCivitaTorsionFree :
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow))
    (leviCivitaMetricCompatibility :
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow))
    (leviCivita :
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow))
    (riemannCurvatureConstruction :
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow))
    (riemannCurvatureSymmetries :
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow))
    (firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow))
    (secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow))
    (riemannCurvature :
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow))
    (ricciContractionFormula :
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (scalarCurvatureContraction :
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (ricciContraction :
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow))
    (metricRegularity :
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow))
    (metricTimeDerivative :
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow))
    (scalarCurvature :
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow))
    (equationDerivation : HasRicciFlowEquationDerivation flow)
    (initialMetricCompatibility : HasInitialMetricCompatibility flow)
    (deturckGauge : HasDeTurckGaugeFixing flow)
    (deturckBackgroundMetric :
      HasDeTurckBackgroundMetricCompatibility flow)
    (deturckVectorField : HasDeTurckVectorFieldConstruction flow)
    (deturckEquation : HasDeTurckEquationDerivation flow)
    (deturckLinearization : HasRicciDeTurckLinearization flow)
    (strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow)
    (parabolicLinearTheory : HasParabolicLinearTheory flow)
    (parabolicFixedPoint : HasParabolicFixedPointArgument flow)
    (deturckShortTime : HasDeTurckShortTimeExistence flow)
    (shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow)
    (deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow)
    (deturckPullbackEquationIdentity :
      HasDeTurckPullbackEquationIdentity flow)
    (deturckPullback : HasDeTurckPullbackToRicciFlow flow)
    (shortTimeExistence : HasShortTimeRicciFlowSolution flow)
    (maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow)
    (continuationCriterion : HasRicciFlowContinuationCriterion flow)
    (curvatureBlowUpCriterion :
      HasCurvatureBlowUpContinuationCriterion flow)
    (maximalSolutionExtension : HasMaximalSolutionExtension flow)
    (parabolicSchauder : HasParabolicSchauderEstimates flow)
    (parabolicRegularity : HasRicciFlowParabolicRegularity flow)
    (shiDerivativeEstimates : HasShiDerivativeEstimates flow)
    (curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow)
    (maximumPrinciple : HasHamiltonMaximumPrinciple flow)
    (uniquenessTheory : HasRicciFlowUniquenessTheory flow)
    (metricEvolution : HasMetricEvolutionEquation flow)
    (ricciTensorEvolution : HasRicciTensorEvolutionEquation flow)
    (scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow)
    (curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow)
    (curvatureEvolution : HasCurvatureEvolutionEquations flow)
    (ricciIdentification :
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationDerivationStatement flow :=
  ⟨leviCivitaExistence, leviCivitaUniqueness,
    leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
    riemannCurvatureConstruction, riemannCurvatureSymmetries, firstBianchi,
    secondBianchi, riemannCurvature, ricciContractionFormula,
    scalarCurvatureContraction, ricciContraction, metricRegularity,
    metricTimeDerivative, scalarCurvature, equationDerivation,
    initialMetricCompatibility, deturckGauge, deturckBackgroundMetric,
    deturckVectorField, deturckEquation, deturckLinearization,
    strictParabolicDeturck, parabolicLinearTheory, parabolicFixedPoint,
    deturckShortTime, shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
    deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
    maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
    maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
    shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
    uniquenessTheory, metricEvolution, ricciTensorEvolution,
    scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution,
    ricciIdentification, equationEvidence⟩

/--
The fixed-flow analytic-foundation component assembler is exactly the tuple of
connection, curvature, DeTurck, continuation, regularity, evolution,
Ricci-identification, and equation witnesses.
-/
theorem analytic_foundation_derivation_statement_of_components_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (leviCivitaExistence :
      HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow))
    (leviCivitaUniqueness :
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow))
    (leviCivitaTorsionFree :
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow))
    (leviCivitaMetricCompatibility :
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow))
    (leviCivita :
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow))
    (riemannCurvatureConstruction :
      HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow))
    (riemannCurvatureSymmetries :
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow))
    (firstBianchi : HasFirstBianchiIdentity (metric_of_ricci_flow_data flow))
    (secondBianchi : HasSecondBianchiIdentity (metric_of_ricci_flow_data flow))
    (riemannCurvature :
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow))
    (ricciContractionFormula :
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (scalarCurvatureContraction :
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow))
    (ricciContraction :
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow))
    (metricRegularity :
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow))
    (metricTimeDerivative :
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow))
    (scalarCurvature :
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow))
    (equationDerivation : HasRicciFlowEquationDerivation flow)
    (initialMetricCompatibility : HasInitialMetricCompatibility flow)
    (deturckGauge : HasDeTurckGaugeFixing flow)
    (deturckBackgroundMetric :
      HasDeTurckBackgroundMetricCompatibility flow)
    (deturckVectorField : HasDeTurckVectorFieldConstruction flow)
    (deturckEquation : HasDeTurckEquationDerivation flow)
    (deturckLinearization : HasRicciDeTurckLinearization flow)
    (strictParabolicDeturck : HasStrictlyParabolicDeTurckSystem flow)
    (parabolicLinearTheory : HasParabolicLinearTheory flow)
    (parabolicFixedPoint : HasParabolicFixedPointArgument flow)
    (deturckShortTime : HasDeTurckShortTimeExistence flow)
    (shortTimeRegularityBootstrap : HasShortTimeRegularityBootstrap flow)
    (deturckDiffeomorphismODE : HasDeTurckDiffeomorphismODE flow)
    (deturckPullbackEquationIdentity :
      HasDeTurckPullbackEquationIdentity flow)
    (deturckPullback : HasDeTurckPullbackToRicciFlow flow)
    (shortTimeExistence : HasShortTimeRicciFlowSolution flow)
    (maximalTimeInterval : HasRicciFlowMaximalTimeInterval flow)
    (continuationCriterion : HasRicciFlowContinuationCriterion flow)
    (curvatureBlowUpCriterion :
      HasCurvatureBlowUpContinuationCriterion flow)
    (maximalSolutionExtension : HasMaximalSolutionExtension flow)
    (parabolicSchauder : HasParabolicSchauderEstimates flow)
    (parabolicRegularity : HasRicciFlowParabolicRegularity flow)
    (shiDerivativeEstimates : HasShiDerivativeEstimates flow)
    (curvatureDerivativeBootstrap : HasCurvatureDerivativeBootstrap flow)
    (maximumPrinciple : HasHamiltonMaximumPrinciple flow)
    (uniquenessTheory : HasRicciFlowUniquenessTheory flow)
    (metricEvolution : HasMetricEvolutionEquation flow)
    (ricciTensorEvolution : HasRicciTensorEvolutionEquation flow)
    (scalarCurvatureEvolution : HasScalarCurvatureEvolutionEquation flow)
    (curvatureNormEvolution : HasCurvatureNormEvolutionInequality flow)
    (curvatureEvolution : HasCurvatureEvolutionEquations flow)
    (ricciIdentification :
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_derivation_statement_of_components flow
        leviCivitaExistence leviCivitaUniqueness leviCivitaTorsionFree
        leviCivitaMetricCompatibility leviCivita
        riemannCurvatureConstruction riemannCurvatureSymmetries firstBianchi
        secondBianchi riemannCurvature ricciContractionFormula
        scalarCurvatureContraction ricciContraction metricRegularity
        metricTimeDerivative scalarCurvature equationDerivation
        initialMetricCompatibility deturckGauge deturckBackgroundMetric
        deturckVectorField deturckEquation deturckLinearization
        strictParabolicDeturck parabolicLinearTheory parabolicFixedPoint
        deturckShortTime shortTimeRegularityBootstrap deturckDiffeomorphismODE
        deturckPullbackEquationIdentity deturckPullback shortTimeExistence
        maximalTimeInterval continuationCriterion curvatureBlowUpCriterion
        maximalSolutionExtension parabolicSchauder parabolicRegularity
        shiDerivativeEstimates curvatureDerivativeBootstrap maximumPrinciple
        uniquenessTheory metricEvolution ricciTensorEvolution
        scalarCurvatureEvolution curvatureNormEvolution curvatureEvolution
        ricciIdentification equationEvidence =
      (by
        exact ⟨leviCivitaExistence, leviCivitaUniqueness,
          leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
          riemannCurvatureConstruction, riemannCurvatureSymmetries,
          firstBianchi, secondBianchi, riemannCurvature,
          ricciContractionFormula, scalarCurvatureContraction,
          ricciContraction, metricRegularity, metricTimeDerivative,
          scalarCurvature, equationDerivation, initialMetricCompatibility,
          deturckGauge, deturckBackgroundMetric, deturckVectorField,
          deturckEquation, deturckLinearization, strictParabolicDeturck,
          parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
          shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
          deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
          maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
          maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
          shiDerivativeEstimates, curvatureDerivativeBootstrap,
          maximumPrinciple, uniquenessTheory, metricEvolution,
          ricciTensorEvolution, scalarCurvatureEvolution,
          curvatureNormEvolution, curvatureEvolution, ricciIdentification,
          equationEvidence⟩) := by
  apply Subsingleton.elim

/--
Semantic alias for the named analytic sub-obligation payload exposed by a
theorem-shaped fixed-flow analytic derivation statement.
-/
abbrev AnalyticFoundationSubobligationsPayload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
    HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
    HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorConstruction (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
    HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
    HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
    HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data flow) ∧
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data flow) ∧
    HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
    HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
    HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
    HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
    HasRicciFlowEquationDerivation flow ∧
    HasInitialMetricCompatibility flow ∧
    HasDeTurckGaugeFixing flow ∧
    HasDeTurckBackgroundMetricCompatibility flow ∧
    HasDeTurckVectorFieldConstruction flow ∧
    HasDeTurckEquationDerivation flow ∧
    HasRicciDeTurckLinearization flow ∧
    HasStrictlyParabolicDeTurckSystem flow ∧
    HasParabolicLinearTheory flow ∧
    HasParabolicFixedPointArgument flow ∧
    HasDeTurckShortTimeExistence flow ∧
    HasShortTimeRegularityBootstrap flow ∧
    HasDeTurckDiffeomorphismODE flow ∧
    HasDeTurckPullbackEquationIdentity flow ∧
    HasDeTurckPullbackToRicciFlow flow ∧
    HasShortTimeRicciFlowSolution flow ∧
    HasRicciFlowMaximalTimeInterval flow ∧
    HasRicciFlowContinuationCriterion flow ∧
    HasCurvatureBlowUpContinuationCriterion flow ∧
    HasMaximalSolutionExtension flow ∧
    HasParabolicSchauderEstimates flow ∧
    HasRicciFlowParabolicRegularity flow ∧
    HasShiDerivativeEstimates flow ∧
    HasCurvatureDerivativeBootstrap flow ∧
    HasHamiltonMaximumPrinciple flow ∧
    HasRicciFlowUniquenessTheory flow ∧
    HasMetricEvolutionEquation flow ∧
    HasRicciTensorEvolutionEquation flow ∧
    HasScalarCurvatureEvolutionEquation flow ∧
    HasCurvatureNormEvolutionInequality flow ∧
    HasCurvatureEvolutionEquations flow

/--
The analytic sub-obligation payload alias is definitionally the full
Levi-Civita, curvature, DeTurck, continuation, regularity, uniqueness, and
evolution-equation witness stack for the fixed Ricci-flow data.
-/
theorem analyticFoundationSubobligationsPayload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationSubobligationsPayload flow =
      (HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionUniqueness (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaTorsionFreeProperty (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaMetricCompatibility (metric_of_ricci_flow_data flow) ∧
      HasLeviCivitaConnectionTheory (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorConstruction
        (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorSymmetries (metric_of_ricci_flow_data flow) ∧
      HasFirstBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasSecondBianchiIdentity (metric_of_ricci_flow_data flow) ∧
      HasRiemannCurvatureTensorTheory (metric_of_ricci_flow_data flow) ∧
      HasRicciTensorContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasScalarCurvatureContractionFormula
        (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciContractionTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasTimeDependentMetricRegularity (metric_of_ricci_flow_data flow) ∧
      HasMetricTimeDerivativeTheory (metric_of_ricci_flow_data flow) ∧
      HasScalarCurvatureTheory (curvature_data_of_ricci_flow_data flow) ∧
      HasRicciFlowEquationDerivation flow ∧
      HasInitialMetricCompatibility flow ∧
      HasDeTurckGaugeFixing flow ∧
      HasDeTurckBackgroundMetricCompatibility flow ∧
      HasDeTurckVectorFieldConstruction flow ∧
      HasDeTurckEquationDerivation flow ∧
      HasRicciDeTurckLinearization flow ∧
      HasStrictlyParabolicDeTurckSystem flow ∧
      HasParabolicLinearTheory flow ∧
      HasParabolicFixedPointArgument flow ∧
      HasDeTurckShortTimeExistence flow ∧
      HasShortTimeRegularityBootstrap flow ∧
      HasDeTurckDiffeomorphismODE flow ∧
      HasDeTurckPullbackEquationIdentity flow ∧
      HasDeTurckPullbackToRicciFlow flow ∧
      HasShortTimeRicciFlowSolution flow ∧
      HasRicciFlowMaximalTimeInterval flow ∧
      HasRicciFlowContinuationCriterion flow ∧
      HasCurvatureBlowUpContinuationCriterion flow ∧
      HasMaximalSolutionExtension flow ∧
      HasParabolicSchauderEstimates flow ∧
      HasRicciFlowParabolicRegularity flow ∧
      HasShiDerivativeEstimates flow ∧
      HasCurvatureDerivativeBootstrap flow ∧
      HasHamiltonMaximumPrinciple flow ∧
      HasRicciFlowUniquenessTheory flow ∧
      HasMetricEvolutionEquation flow ∧
      HasRicciTensorEvolutionEquation flow ∧
      HasScalarCurvatureEvolutionEquation flow ∧
      HasCurvatureNormEvolutionInequality flow ∧
      HasCurvatureEvolutionEquations flow) :=
  rfl

/--
Build an analytic-foundation package from fixed Ricci-flow data and the named
analytic sub-obligation payload for that same flow.

This is the reusable payload-to-package direction: the flow already stores its
Ricci-identification and equation evidence, while the payload supplies the
Levi-Civita, curvature, DeTurck, continuation, regularity, uniqueness, and
evolution-equation obligations.
-/
noncomputable def analytic_foundation_package_of_subobligations_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    RicciFlowAnalyticFoundationPackage I n M := by
  rcases subobligations with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution⟩
  exact
    { flow := flow
      leviCivitaExistence := leviCivitaExistence
      leviCivitaUniqueness := leviCivitaUniqueness
      leviCivitaTorsionFree := leviCivitaTorsionFree
      leviCivitaMetricCompatibility := leviCivitaMetricCompatibility
      leviCivita := leviCivita
      riemannCurvatureConstruction := riemannCurvatureConstruction
      riemannCurvatureSymmetries := riemannCurvatureSymmetries
      firstBianchi := firstBianchi
      secondBianchi := secondBianchi
      riemannCurvature := riemannCurvature
      ricciContractionFormula := ricciContractionFormula
      scalarCurvatureContraction := scalarCurvatureContraction
      ricciContraction := ricciContraction
      metricRegularity := metricRegularity
      metricTimeDerivative := metricTimeDerivative
      scalarCurvature := scalarCurvature
      equationDerivation := equationDerivation
      initialMetricCompatibility := initialMetricCompatibility
      deturckGauge := deturckGauge
      deturckBackgroundMetric := deturckBackgroundMetric
      deturckVectorField := deturckVectorField
      deturckEquation := deturckEquation
      deturckLinearization := deturckLinearization
      strictParabolicDeturck := strictParabolicDeturck
      parabolicLinearTheory := parabolicLinearTheory
      parabolicFixedPoint := parabolicFixedPoint
      deturckShortTime := deturckShortTime
      shortTimeRegularityBootstrap := shortTimeRegularityBootstrap
      deturckDiffeomorphismODE := deturckDiffeomorphismODE
      deturckPullbackEquationIdentity := deturckPullbackEquationIdentity
      deturckPullback := deturckPullback
      shortTimeExistence := shortTimeExistence
      maximalTimeInterval := maximalTimeInterval
      continuationCriterion := continuationCriterion
      curvatureBlowUpCriterion := curvatureBlowUpCriterion
      maximalSolutionExtension := maximalSolutionExtension
      parabolicSchauder := parabolicSchauder
      parabolicRegularity := parabolicRegularity
      shiDerivativeEstimates := shiDerivativeEstimates
      curvatureDerivativeBootstrap := curvatureDerivativeBootstrap
      maximumPrinciple := maximumPrinciple
      uniquenessTheory := uniquenessTheory
      metricEvolution := metricEvolution
      ricciTensorEvolution := ricciTensorEvolution
      scalarCurvatureEvolution := scalarCurvatureEvolution
      curvatureNormEvolution := curvatureNormEvolution
      curvatureEvolution := curvatureEvolution }

/-- The generic analytic package constructor stores the supplied flow data. -/
@[simp] theorem analytic_foundation_package_of_subobligations_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    (analytic_foundation_package_of_subobligations_payload
      flow subobligations).flow = flow := by
  rcases subobligations with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution⟩
  rfl

/--
The fixed-flow analytic derivation statement exposes the named analytic
connection, curvature, DeTurck, continuation, regularity, and evolution
sub-obligations.
-/
theorem analytic_foundation_subobligations_of_derivation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (statement : AnalyticFoundationDerivationStatement flow) :
    AnalyticFoundationSubobligationsPayload flow := by
  rcases statement with
    ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
      leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
      riemannCurvatureSymmetries, firstBianchi, secondBianchi,
      riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
      ricciContraction, metricRegularity, metricTimeDerivative,
      scalarCurvature, equationDerivation, initialMetricCompatibility,
      deturckGauge, deturckBackgroundMetric, deturckVectorField,
      deturckEquation, deturckLinearization, strictParabolicDeturck,
      parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
      shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
      deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
      maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
      maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
      shiDerivativeEstimates, curvatureDerivativeBootstrap, maximumPrinciple,
      uniquenessTheory, metricEvolution, ricciTensorEvolution,
      scalarCurvatureEvolution, curvatureNormEvolution, curvatureEvolution,
      _ricciIdentification, _equationEvidence⟩
  exact ⟨leviCivitaExistence, leviCivitaUniqueness, leviCivitaTorsionFree,
    leviCivitaMetricCompatibility, leviCivita, riemannCurvatureConstruction,
    riemannCurvatureSymmetries, firstBianchi, secondBianchi,
    riemannCurvature, ricciContractionFormula, scalarCurvatureContraction,
    ricciContraction, metricRegularity, metricTimeDerivative, scalarCurvature,
    equationDerivation, initialMetricCompatibility, deturckGauge,
    deturckBackgroundMetric, deturckVectorField, deturckEquation,
    deturckLinearization, strictParabolicDeturck, parabolicLinearTheory,
    parabolicFixedPoint, deturckShortTime, shortTimeRegularityBootstrap,
    deturckDiffeomorphismODE, deturckPullbackEquationIdentity,
    deturckPullback, shortTimeExistence, maximalTimeInterval,
    continuationCriterion, curvatureBlowUpCriterion, maximalSolutionExtension,
    parabolicSchauder, parabolicRegularity, shiDerivativeEstimates,
    curvatureDerivativeBootstrap, maximumPrinciple, uniquenessTheory,
    metricEvolution, ricciTensorEvolution, scalarCurvatureEvolution,
    curvatureNormEvolution, curvatureEvolution⟩

/--
The analytic derivation statement bridge exposes exactly the connection,
curvature, DeTurck, continuation, regularity, and evolution sub-obligations
stored before the Ricci-identification and equation evidence.
-/
theorem analytic_foundation_subobligations_of_derivation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (statement : AnalyticFoundationDerivationStatement flow) :
    analytic_foundation_subobligations_of_derivation_statement flow statement =
      (by
        rcases statement with
          ⟨leviCivitaExistence, leviCivitaUniqueness,
            leviCivitaTorsionFree, leviCivitaMetricCompatibility,
            leviCivita, riemannCurvatureConstruction,
            riemannCurvatureSymmetries, firstBianchi, secondBianchi,
            riemannCurvature, ricciContractionFormula,
            scalarCurvatureContraction, ricciContraction, metricRegularity,
            metricTimeDerivative, scalarCurvature, equationDerivation,
            initialMetricCompatibility, deturckGauge, deturckBackgroundMetric,
            deturckVectorField, deturckEquation, deturckLinearization,
            strictParabolicDeturck, parabolicLinearTheory,
            parabolicFixedPoint, deturckShortTime,
            shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
            deturckPullbackEquationIdentity, deturckPullback,
            shortTimeExistence, maximalTimeInterval, continuationCriterion,
            curvatureBlowUpCriterion, maximalSolutionExtension,
            parabolicSchauder, parabolicRegularity, shiDerivativeEstimates,
            curvatureDerivativeBootstrap, maximumPrinciple, uniquenessTheory,
            metricEvolution, ricciTensorEvolution, scalarCurvatureEvolution,
            curvatureNormEvolution, curvatureEvolution, _ricciIdentification,
            _equationEvidence⟩
        exact ⟨leviCivitaExistence, leviCivitaUniqueness,
          leviCivitaTorsionFree, leviCivitaMetricCompatibility, leviCivita,
          riemannCurvatureConstruction, riemannCurvatureSymmetries,
          firstBianchi, secondBianchi, riemannCurvature,
          ricciContractionFormula, scalarCurvatureContraction,
          ricciContraction, metricRegularity, metricTimeDerivative,
          scalarCurvature, equationDerivation, initialMetricCompatibility,
          deturckGauge, deturckBackgroundMetric, deturckVectorField,
          deturckEquation, deturckLinearization, strictParabolicDeturck,
          parabolicLinearTheory, parabolicFixedPoint, deturckShortTime,
          shortTimeRegularityBootstrap, deturckDiffeomorphismODE,
          deturckPullbackEquationIdentity, deturckPullback, shortTimeExistence,
          maximalTimeInterval, continuationCriterion, curvatureBlowUpCriterion,
          maximalSolutionExtension, parabolicSchauder, parabolicRegularity,
          shiDerivativeEstimates, curvatureDerivativeBootstrap,
          maximumPrinciple, uniquenessTheory, metricEvolution,
          ricciTensorEvolution, scalarCurvatureEvolution,
          curvatureNormEvolution, curvatureEvolution⟩) := by
  apply Subsingleton.elim

/-- Project Ricci-flow data from an analytic-foundation package. -/
def ricci_flow_data_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    RicciFlowData I n M :=
  package.flow

/-- The named analytic-foundation flow projection is definitionally the package field. -/
@[simp] theorem ricci_flow_data_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_flow_data_of_analytic_foundation_package package = package.flow :=
  rfl

/-- Project Levi-Civita connection existence from an analytic-foundation package. -/
theorem levi_civita_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionExistence
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaExistence

/-- Project Levi-Civita connection uniqueness from an analytic-foundation package. -/
theorem levi_civita_uniqueness_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionUniqueness
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaUniqueness

/-- Project the torsion-free Levi-Civita property from an analytic-foundation package. -/
theorem levi_civita_torsion_free_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaTorsionFreeProperty
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaTorsionFree

/-- Project Levi-Civita metric compatibility from an analytic-foundation package. -/
theorem levi_civita_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaMetricCompatibility
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivitaMetricCompatibility

/-- Project the Levi-Civita theory input from an analytic-foundation package. -/
theorem levi_civita_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasLeviCivitaConnectionTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.leviCivita

/-- Project Riemann curvature tensor construction from an analytic-foundation package. -/
theorem riemann_curvature_construction_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorConstruction
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvatureConstruction

/-- Project Riemann curvature tensor symmetries from an analytic-foundation package. -/
theorem riemann_curvature_symmetries_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorSymmetries
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvatureSymmetries

/-- Project the first Bianchi identity from an analytic-foundation package. -/
theorem first_bianchi_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasFirstBianchiIdentity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.firstBianchi

/-- Project the second Bianchi identity from an analytic-foundation package. -/
theorem second_bianchi_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasSecondBianchiIdentity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.secondBianchi

/-- Project the Riemann-curvature theory input from an analytic-foundation package. -/
theorem riemann_curvature_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRiemannCurvatureTensorTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.riemannCurvature

/-- Project the Ricci tensor contraction formula from an analytic-foundation package. -/
theorem ricci_contraction_formula_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciTensorContractionFormula
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.ricciContractionFormula

/-- Project the scalar-curvature contraction formula from an analytic-foundation package. -/
theorem scalar_curvature_contraction_formula_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureContractionFormula
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.scalarCurvatureContraction

/-- Project the Ricci-contraction theory input from an analytic-foundation package. -/
theorem ricci_contraction_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciContractionTheory
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.ricciContraction

/-- Project metric-regularity theory from an analytic-foundation package. -/
theorem metric_regularity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasTimeDependentMetricRegularity
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.metricRegularity

/-- Project metric-time-derivative theory from an analytic-foundation package. -/
theorem metric_time_derivative_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMetricTimeDerivativeTheory
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.metricTimeDerivative

/-- Project scalar-curvature theory from an analytic-foundation package. -/
theorem scalar_curvature_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureTheory
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  package.scalarCurvature

/-- Project Ricci-flow equation derivation from an analytic-foundation package. -/
theorem equation_derivation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowEquationDerivation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.equationDerivation

/--
The analytic-foundation Ricci-flow equation derivation projection is exactly
the stored package field.
-/
@[simp] theorem equation_derivation_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    equation_derivation_of_analytic_foundation_package package =
      package.equationDerivation :=
  rfl

/-- Project initial-metric compatibility from an analytic-foundation package. -/
theorem initial_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasInitialMetricCompatibility
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.initialMetricCompatibility

/-- Project DeTurck gauge fixing from an analytic-foundation package. -/
theorem deturck_gauge_fixing_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckGaugeFixing
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckGauge

/-- Project DeTurck background-metric compatibility from an analytic-foundation package. -/
theorem deturck_background_metric_compatibility_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckBackgroundMetricCompatibility
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckBackgroundMetric

/-- Project DeTurck vector-field construction from an analytic-foundation package. -/
theorem deturck_vector_field_construction_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckVectorFieldConstruction
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckVectorField

/-- Project the Ricci-DeTurck equation derivation from an analytic-foundation package. -/
theorem deturck_equation_derivation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckEquationDerivation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckEquation

/--
The analytic-foundation Ricci-DeTurck equation derivation projection is exactly
the stored package field.
-/
@[simp] theorem deturck_equation_derivation_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_equation_derivation_of_analytic_foundation_package package =
      package.deturckEquation :=
  rfl

/-- Project Ricci-DeTurck operator linearization from an analytic-foundation package. -/
theorem ricci_deturck_linearization_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciDeTurckLinearization
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckLinearization

/-- Project strict parabolicity of the Ricci-DeTurck system. -/
theorem strictly_parabolic_deturck_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasStrictlyParabolicDeTurckSystem
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.strictParabolicDeturck

/-- Project linear parabolic theory from an analytic-foundation package. -/
theorem parabolic_linear_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicLinearTheory
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicLinearTheory

/-- Project the parabolic fixed-point argument from an analytic-foundation package. -/
theorem parabolic_fixed_point_argument_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicFixedPointArgument
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicFixedPoint

/-- Project short-time existence for the Ricci-DeTurck flow. -/
theorem deturck_short_time_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckShortTimeExistence
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckShortTime

/-- Project short-time regularity bootstrap from an analytic-foundation package. -/
theorem short_time_regularity_bootstrap_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShortTimeRegularityBootstrap
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shortTimeRegularityBootstrap

/-- Project the DeTurck diffeomorphism ODE from an analytic-foundation package. -/
theorem deturck_diffeomorphism_ode_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckDiffeomorphismODE
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckDiffeomorphismODE

/-- Project the DeTurck pullback equation identity from an analytic-foundation package. -/
theorem deturck_pullback_equation_identity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckPullbackEquationIdentity
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckPullbackEquationIdentity

/-- Project the pullback from Ricci-DeTurck flow to Ricci flow. -/
theorem deturck_pullback_to_ricci_flow_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasDeTurckPullbackToRicciFlow
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.deturckPullback

/-- Project short-time existence from an analytic-foundation package. -/
theorem short_time_existence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShortTimeRicciFlowSolution
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shortTimeExistence

/-- Project the maximal-time interval from an analytic-foundation package. -/
theorem maximal_time_interval_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowMaximalTimeInterval
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximalTimeInterval

/-- Project the continuation criterion from an analytic-foundation package. -/
theorem continuation_criterion_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowContinuationCriterion
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.continuationCriterion

/-- Project the curvature blow-up continuation criterion. -/
theorem curvature_blowup_criterion_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureBlowUpContinuationCriterion
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureBlowUpCriterion

/-- Project maximal-solution extension from an analytic-foundation package. -/
theorem maximal_solution_extension_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMaximalSolutionExtension
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximalSolutionExtension

/-- Project parabolic Schauder estimates from an analytic-foundation package. -/
theorem parabolic_schauder_estimates_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasParabolicSchauderEstimates
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicSchauder

/-- Project parabolic regularity from an analytic-foundation package. -/
theorem parabolic_regularity_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowParabolicRegularity
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.parabolicRegularity

/-- Project Shi-type derivative estimates from an analytic-foundation package. -/
theorem shi_derivative_estimates_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasShiDerivativeEstimates
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.shiDerivativeEstimates

/-- Project curvature derivative bootstrap from an analytic-foundation package. -/
theorem curvature_derivative_bootstrap_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureDerivativeBootstrap
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureDerivativeBootstrap

/-- Project Hamilton's maximum principle from an analytic-foundation package. -/
theorem hamilton_maximum_principle_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasHamiltonMaximumPrinciple
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.maximumPrinciple

/-- Project Ricci-flow uniqueness theory from an analytic-foundation package. -/
theorem uniqueness_theory_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciFlowUniquenessTheory
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.uniquenessTheory

/-- Project the metric evolution equation from an analytic-foundation package. -/
theorem metric_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasMetricEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.metricEvolution

/-- Project the Ricci tensor evolution equation from an analytic-foundation package. -/
theorem ricci_tensor_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasRicciTensorEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.ricciTensorEvolution

/-- Project the scalar curvature evolution equation from an analytic-foundation package. -/
theorem scalar_curvature_evolution_equation_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasScalarCurvatureEvolutionEquation
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.scalarCurvatureEvolution

/-- Project the curvature-norm evolution inequality from an analytic-foundation package. -/
theorem curvature_norm_evolution_inequality_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureNormEvolutionInequality
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureNormEvolution

/-- Project curvature evolution equations from an analytic-foundation package. -/
theorem curvature_evolution_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureEvolutionEquations
      (ricci_flow_data_of_analytic_foundation_package package) :=
  package.curvatureEvolution

/- Direct analytic-foundation package projections are stored package fields. -/
section AnalyticFoundationPackageProjectionContracts

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

@[simp] theorem levi_civita_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_existence_of_analytic_foundation_package package =
      package.leviCivitaExistence :=
  rfl

@[simp] theorem levi_civita_uniqueness_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_uniqueness_of_analytic_foundation_package package =
      package.leviCivitaUniqueness :=
  rfl

@[simp] theorem levi_civita_torsion_free_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_torsion_free_of_analytic_foundation_package package =
      package.leviCivitaTorsionFree :=
  rfl

@[simp] theorem levi_civita_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_metric_compatibility_of_analytic_foundation_package package =
      package.leviCivitaMetricCompatibility :=
  rfl

@[simp] theorem levi_civita_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    levi_civita_theory_of_analytic_foundation_package package =
      package.leviCivita :=
  rfl

@[simp] theorem riemann_curvature_construction_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_construction_of_analytic_foundation_package package =
      package.riemannCurvatureConstruction :=
  rfl

@[simp] theorem riemann_curvature_symmetries_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_symmetries_of_analytic_foundation_package package =
      package.riemannCurvatureSymmetries :=
  rfl

@[simp] theorem first_bianchi_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    first_bianchi_identity_of_analytic_foundation_package package =
      package.firstBianchi :=
  rfl

@[simp] theorem second_bianchi_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    second_bianchi_identity_of_analytic_foundation_package package =
      package.secondBianchi :=
  rfl

@[simp] theorem riemann_curvature_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    riemann_curvature_theory_of_analytic_foundation_package package =
      package.riemannCurvature :=
  rfl

@[simp] theorem ricci_contraction_formula_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_contraction_formula_of_analytic_foundation_package package =
      package.ricciContractionFormula :=
  rfl

@[simp] theorem scalar_curvature_contraction_formula_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_contraction_formula_of_analytic_foundation_package
      package =
      package.scalarCurvatureContraction :=
  rfl

@[simp] theorem ricci_contraction_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_contraction_theory_of_analytic_foundation_package package =
      package.ricciContraction :=
  rfl

@[simp] theorem metric_regularity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_regularity_of_analytic_foundation_package package =
      package.metricRegularity :=
  rfl

@[simp] theorem metric_time_derivative_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_time_derivative_of_analytic_foundation_package package =
      package.metricTimeDerivative :=
  rfl

@[simp] theorem scalar_curvature_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_theory_of_analytic_foundation_package package =
      package.scalarCurvature :=
  rfl

@[simp] theorem initial_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    initial_metric_compatibility_of_analytic_foundation_package package =
      package.initialMetricCompatibility :=
  rfl

@[simp] theorem deturck_gauge_fixing_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_gauge_fixing_of_analytic_foundation_package package =
      package.deturckGauge :=
  rfl

@[simp] theorem deturck_background_metric_compatibility_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_background_metric_compatibility_of_analytic_foundation_package
      package =
      package.deturckBackgroundMetric :=
  rfl

@[simp] theorem deturck_vector_field_construction_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_vector_field_construction_of_analytic_foundation_package package =
      package.deturckVectorField :=
  rfl

@[simp] theorem ricci_deturck_linearization_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_deturck_linearization_of_analytic_foundation_package package =
      package.deturckLinearization :=
  rfl

@[simp] theorem strictly_parabolic_deturck_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    strictly_parabolic_deturck_of_analytic_foundation_package package =
      package.strictParabolicDeturck :=
  rfl

@[simp] theorem parabolic_linear_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_linear_theory_of_analytic_foundation_package package =
      package.parabolicLinearTheory :=
  rfl

@[simp] theorem parabolic_fixed_point_argument_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_fixed_point_argument_of_analytic_foundation_package package =
      package.parabolicFixedPoint :=
  rfl

@[simp] theorem deturck_short_time_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_short_time_existence_of_analytic_foundation_package package =
      package.deturckShortTime :=
  rfl

@[simp] theorem short_time_regularity_bootstrap_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    short_time_regularity_bootstrap_of_analytic_foundation_package package =
      package.shortTimeRegularityBootstrap :=
  rfl

@[simp] theorem deturck_diffeomorphism_ode_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_diffeomorphism_ode_of_analytic_foundation_package package =
      package.deturckDiffeomorphismODE :=
  rfl

@[simp] theorem deturck_pullback_equation_identity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_pullback_equation_identity_of_analytic_foundation_package package =
      package.deturckPullbackEquationIdentity :=
  rfl

@[simp] theorem deturck_pullback_to_ricci_flow_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    deturck_pullback_to_ricci_flow_of_analytic_foundation_package package =
      package.deturckPullback :=
  rfl

@[simp] theorem short_time_existence_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    short_time_existence_of_analytic_foundation_package package =
      package.shortTimeExistence :=
  rfl

@[simp] theorem maximal_time_interval_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    maximal_time_interval_of_analytic_foundation_package package =
      package.maximalTimeInterval :=
  rfl

@[simp] theorem continuation_criterion_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    continuation_criterion_of_analytic_foundation_package package =
      package.continuationCriterion :=
  rfl

@[simp] theorem curvature_blowup_criterion_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_blowup_criterion_of_analytic_foundation_package package =
      package.curvatureBlowUpCriterion :=
  rfl

@[simp] theorem maximal_solution_extension_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    maximal_solution_extension_of_analytic_foundation_package package =
      package.maximalSolutionExtension :=
  rfl

@[simp] theorem parabolic_schauder_estimates_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_schauder_estimates_of_analytic_foundation_package package =
      package.parabolicSchauder :=
  rfl

@[simp] theorem parabolic_regularity_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    parabolic_regularity_of_analytic_foundation_package package =
      package.parabolicRegularity :=
  rfl

@[simp] theorem shi_derivative_estimates_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    shi_derivative_estimates_of_analytic_foundation_package package =
      package.shiDerivativeEstimates :=
  rfl

@[simp] theorem curvature_derivative_bootstrap_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_derivative_bootstrap_of_analytic_foundation_package package =
      package.curvatureDerivativeBootstrap :=
  rfl

@[simp] theorem hamilton_maximum_principle_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    hamilton_maximum_principle_of_analytic_foundation_package package =
      package.maximumPrinciple :=
  rfl

@[simp] theorem uniqueness_theory_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    uniqueness_theory_of_analytic_foundation_package package =
      package.uniquenessTheory :=
  rfl

@[simp] theorem metric_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    metric_evolution_equation_of_analytic_foundation_package package =
      package.metricEvolution :=
  rfl

@[simp] theorem ricci_tensor_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_tensor_evolution_equation_of_analytic_foundation_package package =
      package.ricciTensorEvolution :=
  rfl

@[simp] theorem scalar_curvature_evolution_equation_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    scalar_curvature_evolution_equation_of_analytic_foundation_package package =
      package.scalarCurvatureEvolution :=
  rfl

@[simp] theorem curvature_norm_evolution_inequality_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_norm_evolution_inequality_of_analytic_foundation_package
      package =
      package.curvatureNormEvolution :=
  rfl

@[simp] theorem curvature_evolution_of_analytic_foundation_package_eq
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    curvature_evolution_of_analytic_foundation_package package =
      package.curvatureEvolution :=
  rfl

end AnalyticFoundationPackageProjectionContracts

/-- Project Ricci-identification evidence from an analytic-foundation package. -/
theorem ricci_identification_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    IsRicciTensorOf
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package))
      (ricci_tensor_field_of_curvature_data
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :=
  ricci_identification_of_ricci_flow_data
    (ricci_flow_data_of_analytic_foundation_package package)

/--
The analytic-foundation Ricci-identification projection delegates to the stored
flow data.
-/
theorem ricci_identification_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ricci_identification_of_analytic_foundation_package package =
      ricci_identification_of_ricci_flow_data package.flow :=
  rfl

/-- Project Ricci-flow equation evidence from an analytic-foundation package. -/
theorem equation_evidence_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package))
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_analytic_foundation_package package)) :=
  equation_evidence_of_ricci_flow_data
    (ricci_flow_data_of_analytic_foundation_package package)

/-- The analytic-foundation equation projection delegates to the stored flow data. -/
theorem equation_evidence_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    equation_evidence_of_analytic_foundation_package package =
      equation_evidence_of_ricci_flow_data package.flow :=
  rfl

/--
A completed analytic-foundation package assembles the fixed-flow analytic
derivation statement for its projected Ricci-flow data.
-/
theorem analytic_foundation_derivation_statement_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    AnalyticFoundationDerivationStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_derivation_statement_of_components
    (ricci_flow_data_of_analytic_foundation_package package)
    (levi_civita_existence_of_analytic_foundation_package package)
    (levi_civita_uniqueness_of_analytic_foundation_package package)
    (levi_civita_torsion_free_of_analytic_foundation_package package)
    (levi_civita_metric_compatibility_of_analytic_foundation_package package)
    (levi_civita_theory_of_analytic_foundation_package package)
    (riemann_curvature_construction_of_analytic_foundation_package package)
    (riemann_curvature_symmetries_of_analytic_foundation_package package)
    (first_bianchi_identity_of_analytic_foundation_package package)
    (second_bianchi_identity_of_analytic_foundation_package package)
    (riemann_curvature_theory_of_analytic_foundation_package package)
    (ricci_contraction_formula_of_analytic_foundation_package package)
    (scalar_curvature_contraction_formula_of_analytic_foundation_package package)
    (ricci_contraction_theory_of_analytic_foundation_package package)
    (metric_regularity_of_analytic_foundation_package package)
    (metric_time_derivative_of_analytic_foundation_package package)
    (scalar_curvature_theory_of_analytic_foundation_package package)
    (equation_derivation_of_analytic_foundation_package package)
    (initial_metric_compatibility_of_analytic_foundation_package package)
    (deturck_gauge_fixing_of_analytic_foundation_package package)
    (deturck_background_metric_compatibility_of_analytic_foundation_package
      package)
    (deturck_vector_field_construction_of_analytic_foundation_package package)
    (deturck_equation_derivation_of_analytic_foundation_package package)
    (ricci_deturck_linearization_of_analytic_foundation_package package)
    (strictly_parabolic_deturck_of_analytic_foundation_package package)
    (parabolic_linear_theory_of_analytic_foundation_package package)
    (parabolic_fixed_point_argument_of_analytic_foundation_package package)
    (deturck_short_time_existence_of_analytic_foundation_package package)
    (short_time_regularity_bootstrap_of_analytic_foundation_package package)
    (deturck_diffeomorphism_ode_of_analytic_foundation_package package)
    (deturck_pullback_equation_identity_of_analytic_foundation_package package)
    (deturck_pullback_to_ricci_flow_of_analytic_foundation_package package)
    (short_time_existence_of_analytic_foundation_package package)
    (maximal_time_interval_of_analytic_foundation_package package)
    (continuation_criterion_of_analytic_foundation_package package)
    (curvature_blowup_criterion_of_analytic_foundation_package package)
    (maximal_solution_extension_of_analytic_foundation_package package)
    (parabolic_schauder_estimates_of_analytic_foundation_package package)
    (parabolic_regularity_of_analytic_foundation_package package)
    (shi_derivative_estimates_of_analytic_foundation_package package)
    (curvature_derivative_bootstrap_of_analytic_foundation_package package)
    (hamilton_maximum_principle_of_analytic_foundation_package package)
    (uniqueness_theory_of_analytic_foundation_package package)
    (metric_evolution_equation_of_analytic_foundation_package package)
    (ricci_tensor_evolution_equation_of_analytic_foundation_package package)
    (scalar_curvature_evolution_equation_of_analytic_foundation_package package)
    (curvature_norm_evolution_inequality_of_analytic_foundation_package package)
    (curvature_evolution_of_analytic_foundation_package package)
    (ricci_identification_of_analytic_foundation_package package)
    (equation_evidence_of_analytic_foundation_package package)

/--
The analytic-foundation package derivation statement is exactly the fixed-flow
component assembler applied to the package projections.
-/
theorem analytic_foundation_derivation_statement_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package =
      analytic_foundation_derivation_statement_of_components
        (ricci_flow_data_of_analytic_foundation_package package)
        (levi_civita_existence_of_analytic_foundation_package package)
        (levi_civita_uniqueness_of_analytic_foundation_package package)
        (levi_civita_torsion_free_of_analytic_foundation_package package)
        (levi_civita_metric_compatibility_of_analytic_foundation_package
          package)
        (levi_civita_theory_of_analytic_foundation_package package)
        (riemann_curvature_construction_of_analytic_foundation_package package)
        (riemann_curvature_symmetries_of_analytic_foundation_package package)
        (first_bianchi_identity_of_analytic_foundation_package package)
        (second_bianchi_identity_of_analytic_foundation_package package)
        (riemann_curvature_theory_of_analytic_foundation_package package)
        (ricci_contraction_formula_of_analytic_foundation_package package)
        (scalar_curvature_contraction_formula_of_analytic_foundation_package
          package)
        (ricci_contraction_theory_of_analytic_foundation_package package)
        (metric_regularity_of_analytic_foundation_package package)
        (metric_time_derivative_of_analytic_foundation_package package)
        (scalar_curvature_theory_of_analytic_foundation_package package)
        (equation_derivation_of_analytic_foundation_package package)
        (initial_metric_compatibility_of_analytic_foundation_package package)
        (deturck_gauge_fixing_of_analytic_foundation_package package)
        (deturck_background_metric_compatibility_of_analytic_foundation_package
          package)
        (deturck_vector_field_construction_of_analytic_foundation_package
          package)
        (deturck_equation_derivation_of_analytic_foundation_package package)
        (ricci_deturck_linearization_of_analytic_foundation_package package)
        (strictly_parabolic_deturck_of_analytic_foundation_package package)
        (parabolic_linear_theory_of_analytic_foundation_package package)
        (parabolic_fixed_point_argument_of_analytic_foundation_package package)
        (deturck_short_time_existence_of_analytic_foundation_package package)
        (short_time_regularity_bootstrap_of_analytic_foundation_package
          package)
        (deturck_diffeomorphism_ode_of_analytic_foundation_package package)
        (deturck_pullback_equation_identity_of_analytic_foundation_package
          package)
        (deturck_pullback_to_ricci_flow_of_analytic_foundation_package package)
        (short_time_existence_of_analytic_foundation_package package)
        (maximal_time_interval_of_analytic_foundation_package package)
        (continuation_criterion_of_analytic_foundation_package package)
        (curvature_blowup_criterion_of_analytic_foundation_package package)
        (maximal_solution_extension_of_analytic_foundation_package package)
        (parabolic_schauder_estimates_of_analytic_foundation_package package)
        (parabolic_regularity_of_analytic_foundation_package package)
        (shi_derivative_estimates_of_analytic_foundation_package package)
        (curvature_derivative_bootstrap_of_analytic_foundation_package package)
        (hamilton_maximum_principle_of_analytic_foundation_package package)
        (uniqueness_theory_of_analytic_foundation_package package)
        (metric_evolution_equation_of_analytic_foundation_package package)
        (ricci_tensor_evolution_equation_of_analytic_foundation_package
          package)
        (scalar_curvature_evolution_equation_of_analytic_foundation_package
          package)
        (curvature_norm_evolution_inequality_of_analytic_foundation_package
          package)
        (curvature_evolution_of_analytic_foundation_package package)
        (ricci_identification_of_analytic_foundation_package package)
        (equation_evidence_of_analytic_foundation_package package) :=
  rfl

/--
Fixed Ricci-flow data and the named analytic sub-obligation payload for that
flow reconstruct the fixed-flow analytic derivation statement.
-/
theorem analytic_foundation_derivation_statement_of_subobligations_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    AnalyticFoundationDerivationStatement flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload flow subobligations
  have hflow :
      ricci_flow_data_of_analytic_foundation_package package = flow := by
    change package.flow = flow
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      AnalyticFoundationDerivationStatement
        (ricci_flow_data_of_analytic_foundation_package package) :=
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package
  rw [← hflow]
  exact result

/--
The payload-to-derivation route rebuilds the generic analytic package from the
payload and delegates to the package-level derivation assembler.
-/
@[simp] theorem analytic_foundation_derivation_statement_of_subobligations_payload_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    analytic_foundation_derivation_statement_of_subobligations_payload
      flow subobligations =
      (by
        let package :=
          analytic_foundation_package_of_subobligations_payload
            flow subobligations
        have hflow :
            ricci_flow_data_of_analytic_foundation_package package = flow := by
          change package.flow = flow
          exact analytic_foundation_package_of_subobligations_payload_eq
            flow subobligations
        have result :
            AnalyticFoundationDerivationStatement
              (ricci_flow_data_of_analytic_foundation_package package) :=
          analytic_foundation_derivation_statement_of_analytic_foundation_package
            package
        rw [← hflow]
        exact result) := by
  apply Subsingleton.elim

/--
An analytic-foundation package plus an explicit equation-boundary package
supplies the strengthened analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (boundary : RicciFlowEquationBoundaryPackage
      (ricci_flow_data_of_analytic_foundation_package package)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  ⟨analytic_foundation_derivation_statement_of_analytic_foundation_package
      package,
    ⟨boundary⟩⟩

/--
The package-plus-boundary strengthened statement is the pair of the assembled
derivation statement and the provided boundary package.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (boundary : RicciFlowEquationBoundaryPackage
      (ricci_flow_data_of_analytic_foundation_package package)) :
    analytic_foundation_with_equation_boundary_of_package package boundary =
      ⟨analytic_foundation_derivation_statement_of_analytic_foundation_package
          package,
        ⟨boundary⟩⟩ :=
  rfl

/--
Fixed Ricci-flow data, the named analytic sub-obligation payload for that flow,
and an already assembled equation-boundary package supply the strengthened
analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (boundary : RicciFlowEquationBoundaryPackage flow) :
    AnalyticFoundationWithEquationBoundaryStatement flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload flow subobligations
  have hflow : package.flow = flow :=
    analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have hboundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_analytic_foundation_package package) := by
    change RicciFlowEquationBoundaryPackage package.flow
    rw [hflow]
    exact boundary
  have result :
      AnalyticFoundationWithEquationBoundaryStatement
        (ricci_flow_data_of_analytic_foundation_package package) :=
    analytic_foundation_with_equation_boundary_of_package package hboundary
  simpa [ricci_flow_data_of_analytic_foundation_package, hflow] using result

/--
The fixed-flow payload-plus-boundary route delegates through the generic
payload-to-package bridge and the package-plus-boundary assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (boundary : RicciFlowEquationBoundaryPackage flow) :
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      flow subobligations boundary =
      (by
        let package :=
          analytic_foundation_package_of_subobligations_payload
            flow subobligations
        have hflow : package.flow = flow :=
          analytic_foundation_package_of_subobligations_payload_eq
            flow subobligations
        have hboundary :
            RicciFlowEquationBoundaryPackage
              (ricci_flow_data_of_analytic_foundation_package package) := by
          change RicciFlowEquationBoundaryPackage package.flow
          rw [hflow]
          exact boundary
        have result :
            AnalyticFoundationWithEquationBoundaryStatement
              (ricci_flow_data_of_analytic_foundation_package package) :=
          analytic_foundation_with_equation_boundary_of_package
            package hboundary
        simpa [ricci_flow_data_of_analytic_foundation_package, hflow] using
          result) := by
  apply Subsingleton.elim

/--
An analytic-foundation package plus explicit pointwise equation verification
supplies the strengthened analytic-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_with_equation_boundary_of_package
    package
    (equation_boundary_package_of_ricci_flow_equation_verification
      (ricci_flow_data_of_analytic_foundation_package package)
      verification)

/--
The package-plus-verification route delegates to the package-plus-boundary route
using the boundary package constructed from the supplied verification.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))) :
    analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
      package verification =
      analytic_foundation_with_equation_boundary_of_package
        package
        (equation_boundary_package_of_ricci_flow_equation_verification
          (ricci_flow_data_of_analytic_foundation_package package)
          verification) := by
  apply Subsingleton.elim

/--
Fixed Ricci-flow data, the named analytic sub-obligation payload for that flow,
and an explicit pointwise equation verification supply the strengthened
analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    AnalyticFoundationWithEquationBoundaryStatement flow := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      flow subobligations
      (equation_boundary_package_of_ricci_flow_equation_verification
        flow verification)

/--
The flow-level payload-plus-verification route delegates through the generic
payload-to-package bridge and the package-plus-verification assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M)
    (subobligations : AnalyticFoundationSubobligationsPayload flow)
    (verification :
      RicciFlowEquationVerification (curvature_data_of_ricci_flow_data flow)) :
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_ricci_flow_equation_verification
      flow subobligations verification =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            flow subobligations
            (equation_boundary_package_of_ricci_flow_equation_verification
              flow verification)) := by
  apply Subsingleton.elim

/--
Analytic package for zero Ricci-flow data from the existing analytic
sub-obligation payload.

All PDE, regularity, curvature-contraction, and evolution inputs remain in the
payload; this constructor only records that the payload is attached to the
zero Ricci-flow data package.
-/
noncomputable def zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  analytic_foundation_package_of_subobligations_payload
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    subobligations

/-- The zero analytic package stores the zero Ricci-flow data. -/
@[simp] theorem zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    ricci_flow_data_of_analytic_foundation_package
      (zero_ricci_flow_analytic_foundation_package
        identifiesRicci equationEvidence subobligations) =
        zero_ricci_flow_data g identifiesRicci equationEvidence := by
  change (zero_ricci_flow_analytic_foundation_package
    identifiesRicci equationEvidence subobligations).flow =
      zero_ricci_flow_data g identifiesRicci equationEvidence
  exact analytic_foundation_package_of_subobligations_payload_eq
    (zero_ricci_flow_data g identifiesRicci equationEvidence)
    subobligations

/-- Analytic-foundation package for stationary zero Ricci-flow data. -/
noncomputable def stationary_zero_ricci_flow_analytic_foundation_package
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
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    RicciFlowAnalyticFoundationPackage I n M :=
  zero_ricci_flow_analytic_foundation_package
    identifiesRicci equationEvidence subobligations

/-- The stationary zero analytic package stores the stationary zero flow data. -/
@[simp] theorem stationary_zero_ricci_flow_analytic_foundation_package_eq
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
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    ricci_flow_data_of_analytic_foundation_package
      (stationary_zero_ricci_flow_analytic_foundation_package
        metric identifiesRicci equationEvidence subobligations) =
      zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence := by
  exact
    zero_ricci_flow_analytic_foundation_package_eq
      identifiesRicci equationEvidence subobligations

/--
Zero Ricci-flow sub-obligation payload plus the explicit zero equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      (zero_ricci_flow_data g identifiesRicci equationEvidence)
      subobligations
      (zero_ricci_flow_equation_boundary_package
        identifiesDerivative identifiesRicci equationEvidence)

/--
The zero sub-obligation payload route delegates to the generic
payload-plus-boundary-package assembler for the zero Ricci-flow data.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            (zero_ricci_flow_data g identifiesRicci equationEvidence)
            subobligations
            (zero_ricci_flow_equation_boundary_package
              identifiesDerivative identifiesRicci equationEvidence)) := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow sub-obligation payload plus its equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence)
      subobligations
      (stationary_zero_ricci_flow_equation_boundary_package
        metric identifiesDerivative identifiesRicci equationEvidence)

/--
The stationary zero sub-obligation route delegates to the generic
payload-plus-boundary-package assembler.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_subobligations_payload_and_boundary_package
            (zero_ricci_flow_data
              (stationary_time_dependent_riemannian_metric metric)
              identifiesRicci equationEvidence)
            subobligations
            (stationary_zero_ricci_flow_equation_boundary_package
              metric identifiesDerivative identifiesRicci equationEvidence)) := by
  apply Subsingleton.elim

/--
Zero Ricci-flow analytic package data plus the explicit zero equation-boundary
package supplies the strengthened analytic equation-boundary statement.
-/
theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data g identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
      identifiesDerivative identifiesRicci equationEvidence subobligations

/--
The zero analytic equation-boundary route delegates to the zero
sub-obligation-payload plus boundary-package route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {g : TimeDependentRiemannianMetric I n M}
    (identifiesDerivative :
      IsMetricTimeDerivativeOf g (zero_metric_time_derivative_field g))
    (identifiesRicci : IsRicciTensorOf g (zero_ricci_tensor_field g))
    (equationEvidence :
      SatisfiesRicciFlowEquation g (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data g identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_zero_ricci_flow_analytic_foundation_package
      identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_zero_ricci_flow_subobligations_payload_and_boundary_package
            identifiesDerivative identifiesRicci equationEvidence
            subobligations) := by
  apply Subsingleton.elim

/--
Stationary zero Ricci-flow analytic package data plus the explicit stationary
equation-boundary package supplies the strengthened analytic statement.
-/
theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    AnalyticFoundationWithEquationBoundaryStatement
      (zero_ricci_flow_data
        (stationary_time_dependent_riemannian_metric metric)
        identifiesRicci equationEvidence) := by
  exact
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations

/--
The stationary zero analytic route delegates to the stationary sub-obligation
payload plus boundary-package route.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package_eq
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
          (stationary_time_dependent_riemannian_metric metric)))
    (equationEvidence :
      SatisfiesRicciFlowEquation
        (stationary_time_dependent_riemannian_metric metric)
        (zero_ricci_curvature_data identifiesRicci))
    (subobligations :
      AnalyticFoundationSubobligationsPayload
        (zero_ricci_flow_data
          (stationary_time_dependent_riemannian_metric metric)
          identifiesRicci equationEvidence)) :
    analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_analytic_foundation_package
      metric identifiesDerivative identifiesRicci equationEvidence subobligations =
      (by
        exact
          analytic_foundation_with_equation_boundary_of_stationary_zero_ricci_flow_subobligations_payload_and_boundary_package
            metric identifiesDerivative identifiesRicci equationEvidence
            subobligations) := by
  apply Subsingleton.elim

/--
A completed analytic-foundation package supplies the theorem-shaped analytic
foundation statement.
-/
theorem analytic_foundation_statement_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    RicciFlowAnalyticFoundationStatement I n M :=
  ⟨ricci_flow_data_of_analytic_foundation_package package,
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package⟩

/--
The analytic-foundation package statement is exactly the existential pair of
the projected flow data and assembled derivation statement.
-/
theorem analytic_foundation_statement_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_statement_of_analytic_foundation_package package =
      ⟨ricci_flow_data_of_analytic_foundation_package package,
        analytic_foundation_derivation_statement_of_analytic_foundation_package
          package⟩ :=
  rfl

/--
A completed analytic-foundation package exposes the theorem-shaped analytic
foundation statement, fixed-flow derivation statement, named analytic
sub-obligation payload, and Ricci-flow equation evidence.
-/
theorem analytic_foundation_payload_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    ∃ _statement : RicciFlowAnalyticFoundationStatement I n M,
    ∃ _derivationStatement :
      AnalyticFoundationDerivationStatement
        (ricci_flow_data_of_analytic_foundation_package package),
    ∃ _subobligations :
      AnalyticFoundationSubobligationsPayload
        (ricci_flow_data_of_analytic_foundation_package package),
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package))
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_analytic_foundation_package package)) := by
  let derivationStatement :=
    analytic_foundation_derivation_statement_of_analytic_foundation_package
      package
  exact ⟨analytic_foundation_statement_of_analytic_foundation_package
      package,
    derivationStatement,
    analytic_foundation_subobligations_of_derivation_statement
      (ricci_flow_data_of_analytic_foundation_package package)
      derivationStatement,
    equation_evidence_of_analytic_foundation_package package⟩

/--
The analytic-foundation package payload is exactly the theorem-shaped statement,
fixed-flow derivation statement, named sub-obligation payload, and equation
evidence assembled from the package projections.
-/
theorem analytic_foundation_payload_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_payload_of_analytic_foundation_package package =
      ⟨analytic_foundation_statement_of_analytic_foundation_package package,
        analytic_foundation_derivation_statement_of_analytic_foundation_package
          package,
        analytic_foundation_subobligations_of_derivation_statement
          (ricci_flow_data_of_analytic_foundation_package package)
          (analytic_foundation_derivation_statement_of_analytic_foundation_package
            package),
        equation_evidence_of_analytic_foundation_package package⟩ := by
  apply Subsingleton.elim

/--
A completed analytic-foundation package directly exposes the named analytic
sub-obligation payload for its projected Ricci-flow data.
-/
theorem analytic_foundation_subobligations_of_analytic_foundation_package
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    AnalyticFoundationSubobligationsPayload
      (ricci_flow_data_of_analytic_foundation_package package) :=
  analytic_foundation_subobligations_of_derivation_statement
    (ricci_flow_data_of_analytic_foundation_package package)
    (analytic_foundation_derivation_statement_of_analytic_foundation_package
      package)

/--
The package-level analytic sub-obligation bridge is exactly the derivation
statement bridge applied to the package's projected flow data and derivation
statement.
-/
theorem analytic_foundation_subobligations_of_analytic_foundation_package_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    analytic_foundation_subobligations_of_analytic_foundation_package
        package =
      analytic_foundation_subobligations_of_derivation_statement
        (ricci_flow_data_of_analytic_foundation_package package)
        (analytic_foundation_derivation_statement_of_analytic_foundation_package
          package) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-flow data
together with its fixed-flow derivation statement.
-/
theorem ricci_flow_data_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      AnalyticFoundationDerivationStatement flow := by
  rcases statement with ⟨flow, derivationStatement⟩
  exact ⟨flow, derivationStatement⟩

/--
The analytic-foundation statement flow-data bridge is exactly the destructuring
of the theorem-shaped statement into its stored flow and derivation statement.
-/
theorem ricci_flow_data_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ricci_flow_data_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, derivationStatement⟩
        exact ⟨flow, derivationStatement⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-identification
evidence for its projected Ricci-flow data.
-/
theorem ricci_identification_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      IsRicciTensorOf
        (metric_of_ricci_flow_data flow)
        (ricci_tensor_field_of_curvature_data
          (curvature_data_of_ricci_flow_data flow)) := by
  rcases statement with ⟨flow, _derivation⟩
  exact ⟨flow, ricci_identification_of_ricci_flow_data flow⟩

/--
The analytic-foundation statement Ricci-identification bridge is exactly the
destructuring of the theorem-shaped statement followed by the flow-level
Ricci-identification projection.
-/
theorem ricci_identification_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ricci_identification_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, _derivation⟩
        exact ⟨flow, ricci_identification_of_ricci_flow_data flow⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped analytic foundation statement supplies Ricci-flow equation
evidence for its projected Ricci-flow data.
-/
theorem equation_evidence_of_analytic_foundation_statement
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    ∃ flow : RicciFlowData I n M,
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data flow)
        (curvature_data_of_ricci_flow_data flow) := by
  rcases statement with ⟨flow, _derivation⟩
  exact ⟨flow, equation_evidence_of_ricci_flow_data flow⟩

/--
The analytic-foundation statement equation bridge is exactly the destructuring
of the theorem-shaped statement followed by the flow-level equation-evidence
projection.
-/
theorem equation_evidence_of_analytic_foundation_statement_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (statement : RicciFlowAnalyticFoundationStatement I n M) :
    equation_evidence_of_analytic_foundation_statement statement =
      (by
        rcases statement with ⟨flow, _derivation⟩
        exact ⟨flow, equation_evidence_of_ricci_flow_data flow⟩) := by
  apply Subsingleton.elim

end Poincare
