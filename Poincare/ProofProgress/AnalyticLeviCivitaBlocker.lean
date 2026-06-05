/-
Proof-progress slice for the analytic Levi-Civita blocker.

The current analytic foundation package requires a
`HasLeviCivitaConnectionExistence` witness before any curvature, DeTurck, or
continuation evidence can matter.  That first field is now backed by concrete
time-indexed tangent covariant-derivative data.  This legacy proof-progress
module records that positive bridge while deferring its negative boundary to
the current production analytic blocker:
`HasCurvatureEvolutionEquations`.
-/

import Poincare.ProofProgress.AnalyticProductionPackageLeviCivita

universe u v w

open Bundle
open scoped Manifold ContDiff

namespace Poincare

/--
The first analytic foundation sub-obligation for a fixed Ricci-flow datum.

This is just a named alias for the first component of
`AnalyticFoundationSubobligationsPayload`; it does not add new assumptions.
-/
def FirstAnalyticFoundationSubobligation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) : Prop :=
  HasLeviCivitaConnectionExistence (metric_of_ricci_flow_data flow)

/-- The named first analytic sub-obligation is definitionally Levi-Civita existence. -/
@[simp] theorem firstAnalyticFoundationSubobligation_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    FirstAnalyticFoundationSubobligation flow =
      HasLeviCivitaConnectionExistence
        (metric_of_ricci_flow_data flow) :=
  rfl

/-- A concrete connection field proves the first analytic foundation sub-obligation. -/
theorem first_analytic_foundation_subobligation_of_connectionField
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (connectionAtTime :
      TimeDependentTangentConnectionField (metric_of_ricci_flow_data flow)) :
    FirstAnalyticFoundationSubobligation flow :=
  hasLeviCivitaConnectionExistence_of_connectionField connectionAtTime

/-- The first analytic sub-obligation is exactly nonempty connection-field data. -/
theorem first_analytic_foundation_subobligation_iff_connectionField_nonempty
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    FirstAnalyticFoundationSubobligation flow ↔
      Nonempty
        (TimeDependentTangentConnectionField
          (metric_of_ricci_flow_data flow)) :=
  hasLeviCivitaConnectionExistence_iff_connectionField_nonempty
    (metric_of_ricci_flow_data flow)

/-- Any analytic sub-obligation payload exposes the first Levi-Civita obligation. -/
theorem first_analytic_foundation_subobligation_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    FirstAnalyticFoundationSubobligation flow :=
  subobligations.1

/-- Any analytic sub-obligation payload also exposes the next Levi-Civita field. -/
theorem levi_civita_uniqueness_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasLeviCivitaConnectionUniqueness
      (metric_of_ricci_flow_data flow) :=
  subobligations.2.1

/-- Any analytic sub-obligation payload exposes scalar-curvature theory. -/
theorem scalar_curvature_theory_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasScalarCurvatureTheory
      (curvature_data_of_ricci_flow_data flow) :=
  subobligations.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Any analytic sub-obligation payload exposes initial-metric compatibility. -/
theorem initial_metric_compatibility_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasInitialMetricCompatibility flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      initialMetricCompatibility, _⟩
  exact initialMetricCompatibility

/-- Any analytic sub-obligation payload exposes the DeTurck gauge witness. -/
theorem deturck_gauge_fixing_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckGaugeFixing flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, deturckGauge, _⟩
  exact deturckGauge

/-- Any analytic sub-obligation payload exposes DeTurck background compatibility. -/
theorem deturck_background_metric_compatibility_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckBackgroundMetricCompatibility flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, deturckBackgroundMetric, _⟩
  exact deturckBackgroundMetric

/-- Any analytic sub-obligation payload exposes DeTurck vector-field construction. -/
theorem deturck_vector_field_construction_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckVectorFieldConstruction flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, deturckVectorField, _⟩
  exact deturckVectorField

/-- Any analytic sub-obligation payload exposes Ricci-DeTurck equation derivation. -/
theorem deturck_equation_derivation_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckEquationDerivation flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, deturckEquation, _⟩
  exact deturckEquation

/-- Any analytic sub-obligation payload exposes Ricci-DeTurck linearization. -/
theorem ricci_deturck_linearization_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciDeTurckLinearization flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, deturckLinearization, _⟩
  exact deturckLinearization

/-- Any analytic sub-obligation payload exposes strict parabolicity. -/
theorem strictly_parabolic_deturck_system_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasStrictlyParabolicDeTurckSystem flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, strictlyParabolicDeturck, _⟩
  exact strictlyParabolicDeturck

/-- Any analytic sub-obligation payload exposes linear parabolic theory. -/
theorem parabolic_linear_theory_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasParabolicLinearTheory flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, parabolicLinearTheory, _⟩
  exact parabolicLinearTheory

/-- Any analytic sub-obligation payload exposes the fixed-point argument. -/
theorem parabolic_fixed_point_argument_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasParabolicFixedPointArgument flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, parabolicFixedPoint, _⟩
  exact parabolicFixedPoint

/-- Any analytic sub-obligation payload exposes DeTurck short-time existence. -/
theorem deturck_short_time_existence_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckShortTimeExistence flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, deturckShortTime, _⟩
  exact deturckShortTime

/-- Any analytic sub-obligation payload exposes the regularity bootstrap. -/
theorem short_time_regularity_bootstrap_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasShortTimeRegularityBootstrap flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, shortTimeRegularityBootstrap, _⟩
  exact shortTimeRegularityBootstrap

/-- Any analytic sub-obligation payload exposes the DeTurck diffeomorphism ODE. -/
theorem deturck_diffeomorphism_ode_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckDiffeomorphismODE flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, deturckDiffeomorphismODE, _⟩
  exact deturckDiffeomorphismODE

/-- Any analytic sub-obligation payload exposes the DeTurck pullback identity. -/
theorem deturck_pullback_equation_identity_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckPullbackEquationIdentity flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, deturckPullbackEquationIdentity, _⟩
  exact deturckPullbackEquationIdentity

/-- Any analytic sub-obligation payload exposes the DeTurck pullback-to-Ricci-flow field. -/
theorem deturck_pullback_to_ricci_flow_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasDeTurckPullbackToRicciFlow flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, deturckPullback, _⟩
  exact deturckPullback

/-- Any analytic sub-obligation payload exposes the short-time Ricci-flow solution field. -/
theorem short_time_ricci_flow_solution_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasShortTimeRicciFlowSolution flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, shortTimeExistence, _⟩
  exact shortTimeExistence

/-- Any analytic sub-obligation payload exposes the maximal-time interval field. -/
theorem ricci_flow_maximal_time_interval_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciFlowMaximalTimeInterval flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, maximalTimeInterval, _⟩
  exact maximalTimeInterval

/-- Any analytic sub-obligation payload exposes the continuation-criterion field. -/
theorem ricci_flow_continuation_criterion_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciFlowContinuationCriterion flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, continuationCriterion, _⟩
  exact continuationCriterion

/--
Any analytic sub-obligation payload exposes the curvature blow-up continuation
criterion field.
-/
theorem curvature_blow_up_continuation_criterion_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasCurvatureBlowUpContinuationCriterion flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, curvatureBlowUpCriterion, _⟩
  exact curvatureBlowUpCriterion

/--
Any analytic sub-obligation payload exposes the maximal solution extension
field.
-/
theorem maximal_solution_extension_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasMaximalSolutionExtension flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, maximalSolutionExtension, _⟩
  exact maximalSolutionExtension

/-- Any analytic sub-obligation payload exposes the parabolic Schauder estimate field. -/
theorem parabolic_schauder_estimates_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasParabolicSchauderEstimates flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, parabolicSchauder, _⟩
  exact parabolicSchauder

/--
Any analytic sub-obligation payload exposes the Ricci-flow parabolic regularity
field.
-/
theorem ricci_flow_parabolic_regularity_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciFlowParabolicRegularity flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      parabolicRegularity, _⟩
  exact parabolicRegularity

/--
Any analytic sub-obligation payload exposes the Shi derivative-estimate field.
-/
theorem shi_derivative_estimates_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasShiDerivativeEstimates flow := by
  rcases subobligations with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      shiDerivativeEstimates, _⟩
  exact shiDerivativeEstimates

/-- Any analytic sub-obligation payload exposes the curvature-derivative bootstrap field. -/
theorem curvature_derivative_bootstrap_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasCurvatureDerivativeBootstrap flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasCurvatureDerivativeBootstrap
        (ricci_flow_data_of_analytic_foundation_package package) :=
    curvature_derivative_bootstrap_of_analytic_foundation_package package
  change HasCurvatureDerivativeBootstrap package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the Hamilton maximum-principle field. -/
theorem hamilton_maximum_principle_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasHamiltonMaximumPrinciple flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasHamiltonMaximumPrinciple
        (ricci_flow_data_of_analytic_foundation_package package) :=
    hamilton_maximum_principle_of_analytic_foundation_package package
  change HasHamiltonMaximumPrinciple package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the Ricci-flow uniqueness field. -/
theorem uniqueness_theory_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciFlowUniquenessTheory flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasRicciFlowUniquenessTheory
        (ricci_flow_data_of_analytic_foundation_package package) :=
    uniqueness_theory_of_analytic_foundation_package package
  change HasRicciFlowUniquenessTheory package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the metric evolution-equation field. -/
theorem metric_evolution_equation_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasMetricEvolutionEquation flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasMetricEvolutionEquation
        (ricci_flow_data_of_analytic_foundation_package package) :=
    metric_evolution_equation_of_analytic_foundation_package package
  change HasMetricEvolutionEquation package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the Ricci tensor evolution field. -/
theorem ricci_tensor_evolution_equation_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasRicciTensorEvolutionEquation flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasRicciTensorEvolutionEquation
        (ricci_flow_data_of_analytic_foundation_package package) :=
    ricci_tensor_evolution_equation_of_analytic_foundation_package package
  change HasRicciTensorEvolutionEquation package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the scalar curvature evolution field. -/
theorem scalar_curvature_evolution_equation_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasScalarCurvatureEvolutionEquation flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasScalarCurvatureEvolutionEquation
        (ricci_flow_data_of_analytic_foundation_package package) :=
    scalar_curvature_evolution_equation_of_analytic_foundation_package package
  change HasScalarCurvatureEvolutionEquation package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the curvature-norm evolution field. -/
theorem curvature_norm_evolution_inequality_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasCurvatureNormEvolutionInequality flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasCurvatureNormEvolutionInequality
        (ricci_flow_data_of_analytic_foundation_package package) :=
    curvature_norm_evolution_inequality_of_analytic_foundation_package package
  change HasCurvatureNormEvolutionInequality package.flow at result
  rw [hflow] at result
  exact result

/-- Any analytic sub-obligation payload exposes the final curvature evolution field. -/
theorem curvature_evolution_of_payload
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {flow : RicciFlowData I n M}
    (subobligations : AnalyticFoundationSubobligationsPayload flow) :
    HasCurvatureEvolutionEquations flow := by
  let package :=
    analytic_foundation_package_of_subobligations_payload
      flow subobligations
  have hflow : package.flow = flow := by
    exact analytic_foundation_package_of_subobligations_payload_eq
      flow subobligations
  have result :
      HasCurvatureEvolutionEquations
        (ricci_flow_data_of_analytic_foundation_package package) :=
    curvature_evolution_of_analytic_foundation_package package
  change HasCurvatureEvolutionEquations package.flow at result
  rw [hflow] at result
  exact result

/--
An analytic sub-obligation payload now closes the final explicit analytic
package field.
-/
theorem analytic_foundation_subobligations_payload_closes_curvature_evolution_current_api
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationSubobligationsPayload flow →
      HasCurvatureEvolutionEquations flow :=
  curvature_evolution_of_payload

/--
The fixed-flow analytic derivation statement now exposes the final explicit
curvature evolution field.
-/
theorem analytic_foundation_derivation_statement_closes_curvature_evolution_current_api
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationDerivationStatement flow →
      HasCurvatureEvolutionEquations flow := by
  intro statement
  exact
    analytic_foundation_subobligations_payload_closes_curvature_evolution_current_api
      flow
      (analytic_foundation_subobligations_of_derivation_statement
        flow statement)

/--
The strengthened analytic-boundary statement also exposes the final explicit
curvature evolution field.
-/
theorem analytic_foundation_with_equation_boundary_closes_curvature_evolution_current_api
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (flow : RicciFlowData I n M) :
    AnalyticFoundationWithEquationBoundaryStatement flow →
      HasCurvatureEvolutionEquations flow := by
  intro statement
  exact
    analytic_foundation_derivation_statement_closes_curvature_evolution_current_api
      flow statement.1

/-- Project the final explicit analytic package field from a package. -/
theorem analytic_levi_civita_blocker_curvature_evolution_of_analytic_foundation_package_current_api
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (package : RicciFlowAnalyticFoundationPackage I n M) :
    HasCurvatureEvolutionEquations
      (ricci_flow_data_of_analytic_foundation_package package) :=
  curvature_evolution_of_analytic_foundation_package package

/--
The theorem-shaped analytic foundation statement exposes a flow whose final
explicit analytic package field is closed.
-/
theorem analytic_levi_civita_blocker_curvature_evolution_of_analytic_foundation_statement_current_api
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (M : Type w) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :
    RicciFlowAnalyticFoundationStatement I n M →
      ∃ flow : RicciFlowData I n M, HasCurvatureEvolutionEquations flow := by
  rintro ⟨flow, derivation⟩
  exact
    ⟨flow,
      analytic_foundation_derivation_statement_closes_curvature_evolution_current_api
        flow derivation⟩

end Poincare
