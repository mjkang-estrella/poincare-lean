/-
Typed interfaces for the Ricci-flow-with-surgery layer.

This module sits between the local Ricci-flow data API and the finite-extinction
interface used by the final Poincare assembly theorem. The predicates here have
no constructors; real geometric-analysis work must supply them.
-/

import Poincare.AnalyticFoundation

universe u

open scoped Manifold ContDiff

namespace Poincare

/-- The Euclidean model used for topological 3-manifolds in this project. -/
abbrev ThreeManifoldModel : Type :=
  EuclideanSpace ℝ (Fin 3)

/--
The project 3-manifold model is definitionally the standard 3-dimensional
Euclidean model.
-/
theorem threeManifoldModel_eq :
    ThreeManifoldModel = EuclideanSpace ℝ (Fin 3) :=
  rfl

/-- The standard smooth model-with-corners for 3-manifolds. -/
noncomputable abbrev ThreeManifoldModelWithCorners :
    ModelWithCorners ℝ ThreeManifoldModel ThreeManifoldModel :=
  𝓘(ℝ, ThreeManifoldModel)

/--
The project smooth model-with-corners is definitionally the standard smooth
model on the fixed 3-manifold Euclidean model.
-/
theorem threeManifoldModelWithCorners_eq :
    ThreeManifoldModelWithCorners = 𝓘(ℝ, ThreeManifoldModel) :=
  rfl

/-- Interface for a Ricci flow with surgery on a manifold. -/
inductive HasRicciFlowWithSurgery
    (n : ℕ∞ω)
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] : Prop

/-- Interface for choosing surgery scales and cutoff parameters. -/
inductive HasSurgeryParameterSelection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for constructing the surgery scale function. -/
inductive HasSurgeryScaleFunction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for continuity and controlled variation of the surgery scale function. -/
inductive HasSurgeryScaleContinuity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for separating surgery, cutoff, and canonical-neighborhood scales. -/
inductive HasSurgeryScaleSeparation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for controlling surgery cutoff parameters. -/
inductive HasSurgeryCutoffParameterControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for constructing smooth cutoff bump functions used in surgery. -/
inductive HasSurgeryCutoffSmoothBumpFunction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for detecting and decomposing surgery necks. -/
inductive HasSurgeryNeckDecomposition
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for detecting strong delta-necks at surgery scales. -/
inductive HasStrongDeltaNeckDetection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for separating selected surgery necks. -/
inductive HasSurgeryNeckSeparation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for parametrizing selected surgery necks by canonical cylinders. -/
inductive HasSurgeryNeckParametrization
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for canonical coordinates on surgery necks with controlled errors. -/
inductive HasSurgeryNeckCanonicalCoordinates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for constructing standard caps used in surgery. -/
inductive HasSurgeryCapConstruction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the standard cap model used in surgery. -/
inductive HasStandardCapModel
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for smooth gluing of standard caps into surgery necks. -/
inductive HasCapGluingSmoothness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for interpolating the neck and cap metrics across the gluing region. -/
inductive HasSurgeryCapMetricInterpolation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for curvature estimates on the inserted standard caps. -/
inductive HasSurgeryCapCurvatureEstimates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for metric estimates after the surgery modification. -/
inductive HasPostSurgeryMetricControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for post-surgery curvature pinching estimates. -/
inductive HasPostSurgeryCurvaturePinching
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for post-surgery noncollapsing control. -/
inductive HasPostSurgeryNoncollapsingControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for post-surgery derivative estimates needed to restart the flow. -/
inductive HasPostSurgeryDerivativeBounds
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for persistence of canonical-neighborhood control after surgery. -/
inductive HasPostSurgeryCanonicalNeighborhoodPersistence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for long-time continuation of the flow after repeated surgery. -/
inductive HasLongTimeSurgeryContinuation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for discreteness of surgery times. -/
inductive HasSurgeryTimeDiscreteness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for local finiteness of surgery times on bounded time intervals. -/
inductive HasSurgeryTimeLocalFiniteness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for iterating the post-surgery continuation argument for all time. -/
inductive HasLongTimeExistenceIteration
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for coherent surgery-parameter choices through the long-time iteration. -/
inductive HasLongTimeSurgeryParameterCoherence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface ruling out finite-time accumulation of long-time surgery events. -/
inductive HasLongTimeNonaccumulation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/--
Package for constructing Ricci flow with surgery.

The final `withSurgery` field remains an unconstructed interface; the preceding
fields expose the construction steps that a future formalization must prove.
-/
structure RicciFlowWithSurgeryConstructionPackage
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
  (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- Construction of the surgery scale function. -/
  scaleFunction : HasSurgeryScaleFunction flow
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
The fixed-flow surgery-construction statement: Ricci-flow-with-surgery evidence
is accompanied by the scale, neck, cap, post-surgery, and long-time
continuation inputs that justify the construction.
-/
def RicciFlowWithSurgeryConstructionStatement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop :=
  ∃ _scaleFunction : HasSurgeryScaleFunction flow,
  ∃ _scaleContinuity : HasSurgeryScaleContinuity flow,
  ∃ _scaleSeparation : HasSurgeryScaleSeparation flow,
  ∃ _cutoffParameterControl : HasSurgeryCutoffParameterControl flow,
  ∃ _cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow,
  ∃ _parameterSelection : HasSurgeryParameterSelection flow,
  ∃ _strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow,
  ∃ _neckSeparation : HasSurgeryNeckSeparation flow,
  ∃ _neckParametrization : HasSurgeryNeckParametrization flow,
  ∃ _neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow,
  ∃ _neckDecomposition : HasSurgeryNeckDecomposition flow,
  ∃ _standardCapModel : HasStandardCapModel flow,
  ∃ _capGluingSmoothness : HasCapGluingSmoothness flow,
  ∃ _capMetricInterpolation : HasSurgeryCapMetricInterpolation flow,
  ∃ _capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow,
  ∃ _capConstruction : HasSurgeryCapConstruction flow,
  ∃ _postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow,
  ∃ _postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow,
  ∃ _postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow,
  ∃ _postSurgeryCanonicalNeighborhoodPersistence :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow,
  ∃ _metricControl : HasPostSurgeryMetricControl flow,
  ∃ _surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow,
  ∃ _surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow,
  ∃ _longTimeExistenceIteration : HasLongTimeExistenceIteration flow,
  ∃ _longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow,
  ∃ _longTimeNonaccumulation : HasLongTimeNonaccumulation flow,
  ∃ _longTimeContinuation : HasLongTimeSurgeryContinuation flow,
    HasRicciFlowWithSurgery n M

/--
The fixed-flow surgery-construction statement is exactly the listed scale,
cutoff, neck, cap, post-surgery, surgery-time, long-time, and aggregate
Ricci-flow-with-surgery witness stack.
-/
theorem ricciFlowWithSurgeryConstructionStatement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    RicciFlowWithSurgeryConstructionStatement flow =
      (∃ _scaleFunction : HasSurgeryScaleFunction flow,
      ∃ _scaleContinuity : HasSurgeryScaleContinuity flow,
      ∃ _scaleSeparation : HasSurgeryScaleSeparation flow,
      ∃ _cutoffParameterControl : HasSurgeryCutoffParameterControl flow,
      ∃ _cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow,
      ∃ _parameterSelection : HasSurgeryParameterSelection flow,
      ∃ _strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow,
      ∃ _neckSeparation : HasSurgeryNeckSeparation flow,
      ∃ _neckParametrization : HasSurgeryNeckParametrization flow,
      ∃ _neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow,
      ∃ _neckDecomposition : HasSurgeryNeckDecomposition flow,
      ∃ _standardCapModel : HasStandardCapModel flow,
      ∃ _capGluingSmoothness : HasCapGluingSmoothness flow,
      ∃ _capMetricInterpolation : HasSurgeryCapMetricInterpolation flow,
      ∃ _capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow,
      ∃ _capConstruction : HasSurgeryCapConstruction flow,
      ∃ _postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow,
      ∃ _postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow,
      ∃ _postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow,
      ∃ _postSurgeryCanonicalNeighborhoodPersistence :
        HasPostSurgeryCanonicalNeighborhoodPersistence flow,
      ∃ _metricControl : HasPostSurgeryMetricControl flow,
      ∃ _surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow,
      ∃ _surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow,
      ∃ _longTimeExistenceIteration : HasLongTimeExistenceIteration flow,
      ∃ _longTimeParameterCoherence :
        HasLongTimeSurgeryParameterCoherence flow,
      ∃ _longTimeNonaccumulation : HasLongTimeNonaccumulation flow,
      ∃ _longTimeContinuation : HasLongTimeSurgeryContinuation flow,
        HasRicciFlowWithSurgery n M) :=
  rfl

/--
Assemble the fixed-flow surgery-construction statement from the named
construction components.
-/
theorem ricci_flow_with_surgery_construction_statement_of_components
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (scaleFunction : HasSurgeryScaleFunction flow)
    (scaleContinuity : HasSurgeryScaleContinuity flow)
    (scaleSeparation : HasSurgeryScaleSeparation flow)
    (cutoffParameterControl : HasSurgeryCutoffParameterControl flow)
    (cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow)
    (parameterSelection : HasSurgeryParameterSelection flow)
    (strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow)
    (neckSeparation : HasSurgeryNeckSeparation flow)
    (neckParametrization : HasSurgeryNeckParametrization flow)
    (neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow)
    (neckDecomposition : HasSurgeryNeckDecomposition flow)
    (standardCapModel : HasStandardCapModel flow)
    (capGluingSmoothness : HasCapGluingSmoothness flow)
    (capMetricInterpolation : HasSurgeryCapMetricInterpolation flow)
    (capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow)
    (capConstruction : HasSurgeryCapConstruction flow)
    (postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow)
    (postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow)
    (postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow)
    (postSurgeryCanonicalNeighborhoodPersistence :
      HasPostSurgeryCanonicalNeighborhoodPersistence flow)
    (metricControl : HasPostSurgeryMetricControl flow)
    (surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow)
    (surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow)
    (longTimeExistenceIteration : HasLongTimeExistenceIteration flow)
    (longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow)
    (longTimeNonaccumulation : HasLongTimeNonaccumulation flow)
    (longTimeContinuation : HasLongTimeSurgeryContinuation flow)
    (withSurgery : HasRicciFlowWithSurgery n M) :
    RicciFlowWithSurgeryConstructionStatement flow :=
  ⟨scaleFunction, scaleContinuity, scaleSeparation, cutoffParameterControl,
    cutoffSmoothBump, parameterSelection, strongDeltaNeckDetection,
    neckSeparation, neckParametrization, neckCanonicalCoordinates,
    neckDecomposition, standardCapModel, capGluingSmoothness,
    capMetricInterpolation, capCurvatureEstimates, capConstruction,
    postSurgeryCurvaturePinching, postSurgeryNoncollapsing,
    postSurgeryDerivativeBounds, postSurgeryCanonicalNeighborhoodPersistence,
    metricControl, surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
    longTimeExistenceIteration, longTimeParameterCoherence,
    longTimeNonaccumulation, longTimeContinuation, withSurgery⟩

/--
The fixed-flow surgery-construction component assembler is exactly the tuple of
scale, cutoff, neck, cap, post-surgery, surgery-time, long-time, and aggregate
surgery witnesses.
-/
theorem ricci_flow_with_surgery_construction_statement_of_components_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (scaleFunction : HasSurgeryScaleFunction flow)
    (scaleContinuity : HasSurgeryScaleContinuity flow)
    (scaleSeparation : HasSurgeryScaleSeparation flow)
    (cutoffParameterControl : HasSurgeryCutoffParameterControl flow)
    (cutoffSmoothBump : HasSurgeryCutoffSmoothBumpFunction flow)
    (parameterSelection : HasSurgeryParameterSelection flow)
    (strongDeltaNeckDetection : HasStrongDeltaNeckDetection flow)
    (neckSeparation : HasSurgeryNeckSeparation flow)
    (neckParametrization : HasSurgeryNeckParametrization flow)
    (neckCanonicalCoordinates : HasSurgeryNeckCanonicalCoordinates flow)
    (neckDecomposition : HasSurgeryNeckDecomposition flow)
    (standardCapModel : HasStandardCapModel flow)
    (capGluingSmoothness : HasCapGluingSmoothness flow)
    (capMetricInterpolation : HasSurgeryCapMetricInterpolation flow)
    (capCurvatureEstimates : HasSurgeryCapCurvatureEstimates flow)
    (capConstruction : HasSurgeryCapConstruction flow)
    (postSurgeryCurvaturePinching : HasPostSurgeryCurvaturePinching flow)
    (postSurgeryNoncollapsing : HasPostSurgeryNoncollapsingControl flow)
    (postSurgeryDerivativeBounds : HasPostSurgeryDerivativeBounds flow)
    (postSurgeryCanonicalNeighborhoodPersistence :
      HasPostSurgeryCanonicalNeighborhoodPersistence flow)
    (metricControl : HasPostSurgeryMetricControl flow)
    (surgeryTimeDiscreteness : HasSurgeryTimeDiscreteness flow)
    (surgeryTimeLocalFiniteness : HasSurgeryTimeLocalFiniteness flow)
    (longTimeExistenceIteration : HasLongTimeExistenceIteration flow)
    (longTimeParameterCoherence : HasLongTimeSurgeryParameterCoherence flow)
    (longTimeNonaccumulation : HasLongTimeNonaccumulation flow)
    (longTimeContinuation : HasLongTimeSurgeryContinuation flow)
    (withSurgery : HasRicciFlowWithSurgery n M) :
    ricci_flow_with_surgery_construction_statement_of_components flow
        scaleFunction scaleContinuity scaleSeparation cutoffParameterControl
        cutoffSmoothBump parameterSelection strongDeltaNeckDetection
        neckSeparation neckParametrization neckCanonicalCoordinates
        neckDecomposition standardCapModel capGluingSmoothness
        capMetricInterpolation capCurvatureEstimates capConstruction
        postSurgeryCurvaturePinching postSurgeryNoncollapsing
        postSurgeryDerivativeBounds postSurgeryCanonicalNeighborhoodPersistence
        metricControl surgeryTimeDiscreteness surgeryTimeLocalFiniteness
        longTimeExistenceIteration longTimeParameterCoherence
        longTimeNonaccumulation longTimeContinuation withSurgery =
      (by
        exact ⟨scaleFunction, scaleContinuity, scaleSeparation,
          cutoffParameterControl, cutoffSmoothBump, parameterSelection,
          strongDeltaNeckDetection, neckSeparation, neckParametrization,
          neckCanonicalCoordinates, neckDecomposition, standardCapModel,
          capGluingSmoothness, capMetricInterpolation, capCurvatureEstimates,
          capConstruction, postSurgeryCurvaturePinching,
          postSurgeryNoncollapsing, postSurgeryDerivativeBounds,
          postSurgeryCanonicalNeighborhoodPersistence, metricControl,
          surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
          longTimeExistenceIteration, longTimeParameterCoherence,
          longTimeNonaccumulation, longTimeContinuation, withSurgery⟩) := by
  apply Subsingleton.elim

/--
A completed construction package assembles the fixed-flow construction
statement.
-/
theorem ricci_flow_with_surgery_construction_statement_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    RicciFlowWithSurgeryConstructionStatement flow :=
  ricci_flow_with_surgery_construction_statement_of_components flow
    package.scaleFunction package.scaleContinuity package.scaleSeparation
    package.cutoffParameterControl package.cutoffSmoothBump
    package.parameterSelection package.strongDeltaNeckDetection
    package.neckSeparation package.neckParametrization
    package.neckCanonicalCoordinates package.neckDecomposition
    package.standardCapModel package.capGluingSmoothness
    package.capMetricInterpolation package.capCurvatureEstimates
    package.capConstruction package.postSurgeryCurvaturePinching
    package.postSurgeryNoncollapsing package.postSurgeryDerivativeBounds
    package.postSurgeryCanonicalNeighborhoodPersistence package.metricControl
    package.surgeryTimeDiscreteness package.surgeryTimeLocalFiniteness
    package.longTimeExistenceIteration package.longTimeParameterCoherence
    package.longTimeNonaccumulation package.longTimeContinuation
    package.withSurgery

/--
The construction-package route to the theorem-shaped construction statement is
exactly the component assembly route applied to the package fields.
-/
theorem ricci_flow_with_surgery_construction_statement_of_construction_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    ricci_flow_with_surgery_construction_statement_of_construction_package
      package =
      ricci_flow_with_surgery_construction_statement_of_components flow
        package.scaleFunction package.scaleContinuity package.scaleSeparation
        package.cutoffParameterControl package.cutoffSmoothBump
        package.parameterSelection package.strongDeltaNeckDetection
        package.neckSeparation package.neckParametrization
        package.neckCanonicalCoordinates package.neckDecomposition
        package.standardCapModel package.capGluingSmoothness
        package.capMetricInterpolation package.capCurvatureEstimates
        package.capConstruction package.postSurgeryCurvaturePinching
        package.postSurgeryNoncollapsing package.postSurgeryDerivativeBounds
        package.postSurgeryCanonicalNeighborhoodPersistence
        package.metricControl package.surgeryTimeDiscreteness
        package.surgeryTimeLocalFiniteness
        package.longTimeExistenceIteration package.longTimeParameterCoherence
        package.longTimeNonaccumulation package.longTimeContinuation
        package.withSurgery := by
  apply Subsingleton.elim

/--
The theorem-shaped surgery-construction statement supplies the aggregate
Ricci-flow-with-surgery interface.
-/
theorem ricci_flow_with_surgery_of_construction_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : RicciFlowWithSurgeryConstructionStatement flow) :
    HasRicciFlowWithSurgery n M := by
  rcases statement with
    ⟨_scaleFunction, _scaleContinuity, _scaleSeparation,
      _cutoffParameterControl, _cutoffSmoothBump, _parameterSelection,
      _strongDeltaNeckDetection, _neckSeparation, _neckParametrization,
      _neckCanonicalCoordinates, _neckDecomposition, _standardCapModel,
      _capGluingSmoothness, _capMetricInterpolation, _capCurvatureEstimates,
      _capConstruction, _postSurgeryCurvaturePinching,
      _postSurgeryNoncollapsing, _postSurgeryDerivativeBounds,
      _postSurgeryCanonicalNeighborhoodPersistence, _metricControl,
      _surgeryTimeDiscreteness, _surgeryTimeLocalFiniteness,
      _longTimeExistenceIteration, _longTimeParameterCoherence,
      _longTimeNonaccumulation, _longTimeContinuation, withSurgery⟩
  exact withSurgery

/--
The construction-statement aggregate bridge is exactly the final
Ricci-flow-with-surgery witness stored in the theorem-shaped construction
statement.
-/
theorem ricci_flow_with_surgery_of_construction_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : RicciFlowWithSurgeryConstructionStatement flow) :
    ricci_flow_with_surgery_of_construction_statement statement =
      (by
        rcases statement with
          ⟨_scaleFunction, _scaleContinuity, _scaleSeparation,
            _cutoffParameterControl, _cutoffSmoothBump, _parameterSelection,
            _strongDeltaNeckDetection, _neckSeparation, _neckParametrization,
            _neckCanonicalCoordinates, _neckDecomposition, _standardCapModel,
            _capGluingSmoothness, _capMetricInterpolation,
            _capCurvatureEstimates, _capConstruction,
            _postSurgeryCurvaturePinching, _postSurgeryNoncollapsing,
            _postSurgeryDerivativeBounds,
            _postSurgeryCanonicalNeighborhoodPersistence, _metricControl,
            _surgeryTimeDiscreteness, _surgeryTimeLocalFiniteness,
            _longTimeExistenceIteration, _longTimeParameterCoherence,
            _longTimeNonaccumulation, _longTimeContinuation, withSurgery⟩
        exact withSurgery) := by
  apply Subsingleton.elim

/--
Semantic alias for the named surgery-construction sub-obligation payload exposed
by a theorem-shaped construction statement.
-/
abbrev RicciFlowWithSurgeryConstructionSubobligationsPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop :=
  HasSurgeryScaleFunction flow ∧
  HasSurgeryScaleContinuity flow ∧
  HasSurgeryScaleSeparation flow ∧
  HasSurgeryCutoffParameterControl flow ∧
  HasSurgeryCutoffSmoothBumpFunction flow ∧
  HasSurgeryParameterSelection flow ∧
  HasStrongDeltaNeckDetection flow ∧
  HasSurgeryNeckSeparation flow ∧
  HasSurgeryNeckParametrization flow ∧
  HasSurgeryNeckCanonicalCoordinates flow ∧
  HasSurgeryNeckDecomposition flow ∧
  HasStandardCapModel flow ∧
  HasCapGluingSmoothness flow ∧
  HasSurgeryCapMetricInterpolation flow ∧
  HasSurgeryCapCurvatureEstimates flow ∧
  HasSurgeryCapConstruction flow ∧
  HasPostSurgeryCurvaturePinching flow ∧
  HasPostSurgeryNoncollapsingControl flow ∧
  HasPostSurgeryDerivativeBounds flow ∧
  HasPostSurgeryCanonicalNeighborhoodPersistence flow ∧
  HasPostSurgeryMetricControl flow ∧
  HasSurgeryTimeDiscreteness flow ∧
  HasSurgeryTimeLocalFiniteness flow ∧
  HasLongTimeExistenceIteration flow ∧
  HasLongTimeSurgeryParameterCoherence flow ∧
  HasLongTimeNonaccumulation flow ∧
  HasLongTimeSurgeryContinuation flow ∧
  HasRicciFlowWithSurgery n M

/--
The surgery-construction sub-obligation payload alias is definitionally the
scale, cutoff, neck, cap, post-surgery, surgery-time, long-time, and aggregate
surgery witness stack for the fixed flow.
-/
theorem ricciFlowWithSurgeryConstructionSubobligationsPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    RicciFlowWithSurgeryConstructionSubobligationsPayload flow =
      (HasSurgeryScaleFunction flow ∧
      HasSurgeryScaleContinuity flow ∧
      HasSurgeryScaleSeparation flow ∧
      HasSurgeryCutoffParameterControl flow ∧
      HasSurgeryCutoffSmoothBumpFunction flow ∧
      HasSurgeryParameterSelection flow ∧
      HasStrongDeltaNeckDetection flow ∧
      HasSurgeryNeckSeparation flow ∧
      HasSurgeryNeckParametrization flow ∧
      HasSurgeryNeckCanonicalCoordinates flow ∧
      HasSurgeryNeckDecomposition flow ∧
      HasStandardCapModel flow ∧
      HasCapGluingSmoothness flow ∧
      HasSurgeryCapMetricInterpolation flow ∧
      HasSurgeryCapCurvatureEstimates flow ∧
      HasSurgeryCapConstruction flow ∧
      HasPostSurgeryCurvaturePinching flow ∧
      HasPostSurgeryNoncollapsingControl flow ∧
      HasPostSurgeryDerivativeBounds flow ∧
      HasPostSurgeryCanonicalNeighborhoodPersistence flow ∧
      HasPostSurgeryMetricControl flow ∧
      HasSurgeryTimeDiscreteness flow ∧
      HasSurgeryTimeLocalFiniteness flow ∧
      HasLongTimeExistenceIteration flow ∧
      HasLongTimeSurgeryParameterCoherence flow ∧
      HasLongTimeNonaccumulation flow ∧
      HasLongTimeSurgeryContinuation flow ∧
      HasRicciFlowWithSurgery n M) :=
  rfl

/--
The theorem-shaped surgery-construction statement exposes the named scale,
neck, cap, post-surgery, long-time continuation, and aggregate surgery
sub-obligations.
-/
theorem surgery_construction_subobligations_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : RicciFlowWithSurgeryConstructionStatement flow) :
    RicciFlowWithSurgeryConstructionSubobligationsPayload flow := by
  rcases statement with
    ⟨scaleFunction, scaleContinuity, scaleSeparation, cutoffParameterControl,
      cutoffSmoothBump, parameterSelection, strongDeltaNeckDetection,
      neckSeparation, neckParametrization, neckCanonicalCoordinates,
      neckDecomposition, standardCapModel, capGluingSmoothness,
      capMetricInterpolation, capCurvatureEstimates, capConstruction,
      postSurgeryCurvaturePinching, postSurgeryNoncollapsing,
      postSurgeryDerivativeBounds, postSurgeryCanonicalNeighborhoodPersistence,
      metricControl, surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
      longTimeExistenceIteration, longTimeParameterCoherence,
      longTimeNonaccumulation, longTimeContinuation, withSurgery⟩
  exact ⟨scaleFunction, scaleContinuity, scaleSeparation, cutoffParameterControl,
    cutoffSmoothBump, parameterSelection, strongDeltaNeckDetection,
    neckSeparation, neckParametrization, neckCanonicalCoordinates,
    neckDecomposition, standardCapModel, capGluingSmoothness,
    capMetricInterpolation, capCurvatureEstimates, capConstruction,
    postSurgeryCurvaturePinching, postSurgeryNoncollapsing,
    postSurgeryDerivativeBounds, postSurgeryCanonicalNeighborhoodPersistence,
    metricControl, surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
    longTimeExistenceIteration, longTimeParameterCoherence,
    longTimeNonaccumulation, longTimeContinuation, withSurgery⟩

/--
The surgery-construction statement bridge exposes exactly the scale, cutoff,
neck, cap, post-surgery, surgery-time, long-time, and aggregate surgery
components stored in the theorem-shaped construction statement.
-/
theorem surgery_construction_subobligations_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : RicciFlowWithSurgeryConstructionStatement flow) :
    surgery_construction_subobligations_of_statement statement =
      (by
        rcases statement with
          ⟨scaleFunction, scaleContinuity, scaleSeparation,
            cutoffParameterControl, cutoffSmoothBump, parameterSelection,
            strongDeltaNeckDetection, neckSeparation, neckParametrization,
            neckCanonicalCoordinates, neckDecomposition, standardCapModel,
            capGluingSmoothness, capMetricInterpolation, capCurvatureEstimates,
            capConstruction, postSurgeryCurvaturePinching,
            postSurgeryNoncollapsing, postSurgeryDerivativeBounds,
            postSurgeryCanonicalNeighborhoodPersistence, metricControl,
            surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
            longTimeExistenceIteration, longTimeParameterCoherence,
            longTimeNonaccumulation, longTimeContinuation, withSurgery⟩
        exact ⟨scaleFunction, scaleContinuity, scaleSeparation,
          cutoffParameterControl, cutoffSmoothBump, parameterSelection,
          strongDeltaNeckDetection, neckSeparation, neckParametrization,
          neckCanonicalCoordinates, neckDecomposition, standardCapModel,
          capGluingSmoothness, capMetricInterpolation, capCurvatureEstimates,
          capConstruction, postSurgeryCurvaturePinching,
          postSurgeryNoncollapsing, postSurgeryDerivativeBounds,
          postSurgeryCanonicalNeighborhoodPersistence, metricControl,
          surgeryTimeDiscreteness, surgeryTimeLocalFiniteness,
          longTimeExistenceIteration, longTimeParameterCoherence,
          longTimeNonaccumulation, longTimeContinuation, withSurgery⟩) := by
  apply Subsingleton.elim

/--
A completed construction package exposes the theorem-shaped construction
statement, the statement-mediated sub-obligation payload, and the aggregate
Ricci-flow-with-surgery witness together.
-/
theorem surgery_construction_payload_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    ∃ _statement : RicciFlowWithSurgeryConstructionStatement flow,
    ∃ _subobligations :
      RicciFlowWithSurgeryConstructionSubobligationsPayload flow,
      HasRicciFlowWithSurgery n M := by
  let statement :=
    ricci_flow_with_surgery_construction_statement_of_construction_package
      package
  let subobligations :=
    surgery_construction_subobligations_of_statement statement
  exact ⟨statement, subobligations,
    ricci_flow_with_surgery_of_construction_statement statement⟩

/--
The construction-package payload is exactly the named construction statement,
its statement-mediated sub-obligation payload, and the aggregate surgery
witness extracted from that statement.
-/
theorem surgery_construction_payload_of_construction_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    surgery_construction_payload_of_construction_package package =
      (by
        let statement :=
          ricci_flow_with_surgery_construction_statement_of_construction_package
            package
        let subobligations :=
          surgery_construction_subobligations_of_statement statement
        exact ⟨statement, subobligations,
          ricci_flow_with_surgery_of_construction_statement statement⟩) := by
  apply Subsingleton.elim

/--
A completed surgery-construction package directly exposes the named
construction sub-obligation payload for its fixed Ricci-flow data.
-/
theorem surgery_construction_subobligations_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    RicciFlowWithSurgeryConstructionSubobligationsPayload flow :=
  surgery_construction_subobligations_of_statement
    (ricci_flow_with_surgery_construction_statement_of_construction_package
      package)

/--
The package-level surgery-construction sub-obligation bridge is exactly the
statement bridge applied to the package's theorem-shaped construction statement.
-/
theorem surgery_construction_subobligations_of_construction_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    surgery_construction_subobligations_of_construction_package package =
      surgery_construction_subobligations_of_statement
        (ricci_flow_with_surgery_construction_statement_of_construction_package
          package) := by
  apply Subsingleton.elim

/-- Project surgery-scale-function evidence from a construction package. -/
theorem surgery_scale_function_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryScaleFunction flow :=
  package.scaleFunction

/-- Project surgery-scale continuity from a construction package. -/
theorem surgery_scale_continuity_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryScaleContinuity flow :=
  package.scaleContinuity

/-- Project surgery-scale separation from a construction package. -/
theorem surgery_scale_separation_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryScaleSeparation flow :=
  package.scaleSeparation

/-- Project surgery cutoff-parameter control from a construction package. -/
theorem surgery_cutoff_parameter_control_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryCutoffParameterControl flow :=
  package.cutoffParameterControl

/-- Project smooth surgery cutoff bump functions from a construction package. -/
theorem surgery_cutoff_smooth_bump_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryCutoffSmoothBumpFunction flow :=
  package.cutoffSmoothBump

/-- Project surgery-parameter evidence from a construction package. -/
theorem surgery_parameter_selection_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryParameterSelection flow :=
  package.parameterSelection

/-- Project strong-delta-neck detection from a construction package. -/
theorem strong_delta_neck_detection_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasStrongDeltaNeckDetection flow :=
  package.strongDeltaNeckDetection

/-- Project surgery-neck separation from a construction package. -/
theorem surgery_neck_separation_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryNeckSeparation flow :=
  package.neckSeparation

/-- Project surgery-neck parametrization from a construction package. -/
theorem surgery_neck_parametrization_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryNeckParametrization flow :=
  package.neckParametrization

/-- Project canonical neck-coordinate evidence from a construction package. -/
theorem surgery_neck_canonical_coordinates_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryNeckCanonicalCoordinates flow :=
  package.neckCanonicalCoordinates

/-- Project neck-decomposition evidence from a construction package. -/
theorem surgery_neck_decomposition_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryNeckDecomposition flow :=
  package.neckDecomposition

/-- Project the standard-cap model from a construction package. -/
theorem standard_cap_model_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasStandardCapModel flow :=
  package.standardCapModel

/-- Project cap-gluing smoothness from a construction package. -/
theorem cap_gluing_smoothness_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasCapGluingSmoothness flow :=
  package.capGluingSmoothness

/-- Project cap metric-interpolation evidence from a construction package. -/
theorem surgery_cap_metric_interpolation_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryCapMetricInterpolation flow :=
  package.capMetricInterpolation

/-- Project cap curvature-estimate evidence from a construction package. -/
theorem surgery_cap_curvature_estimates_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryCapCurvatureEstimates flow :=
  package.capCurvatureEstimates

/-- Project cap-construction evidence from a construction package. -/
theorem surgery_cap_construction_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryCapConstruction flow :=
  package.capConstruction

/-- Project post-surgery curvature pinching from a construction package. -/
theorem post_surgery_curvature_pinching_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasPostSurgeryCurvaturePinching flow :=
  package.postSurgeryCurvaturePinching

/-- Project post-surgery noncollapsing control from a construction package. -/
theorem post_surgery_noncollapsing_control_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasPostSurgeryNoncollapsingControl flow :=
  package.postSurgeryNoncollapsing

/-- Project post-surgery derivative bounds from a construction package. -/
theorem post_surgery_derivative_bounds_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasPostSurgeryDerivativeBounds flow :=
  package.postSurgeryDerivativeBounds

/-- Project post-surgery canonical-neighborhood persistence from a package. -/
theorem post_surgery_canonical_neighborhood_persistence_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasPostSurgeryCanonicalNeighborhoodPersistence flow :=
  package.postSurgeryCanonicalNeighborhoodPersistence

/-- Project post-surgery metric-control evidence from a construction package. -/
theorem post_surgery_metric_control_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasPostSurgeryMetricControl flow :=
  package.metricControl

/-- Project surgery-time discreteness from a construction package. -/
theorem surgery_time_discreteness_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryTimeDiscreteness flow :=
  package.surgeryTimeDiscreteness

/-- Project surgery-time local finiteness from a construction package. -/
theorem surgery_time_local_finiteness_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasSurgeryTimeLocalFiniteness flow :=
  package.surgeryTimeLocalFiniteness

/-- Project long-time existence iteration from a construction package. -/
theorem long_time_existence_iteration_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasLongTimeExistenceIteration flow :=
  package.longTimeExistenceIteration

/-- Project long-time surgery-parameter coherence from a construction package. -/
theorem long_time_surgery_parameter_coherence_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasLongTimeSurgeryParameterCoherence flow :=
  package.longTimeParameterCoherence

/-- Project nonaccumulation of long-time surgery events from a construction package. -/
theorem long_time_nonaccumulation_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasLongTimeNonaccumulation flow :=
  package.longTimeNonaccumulation

/-- Project long-time continuation evidence from a construction package. -/
theorem long_time_surgery_continuation_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasLongTimeSurgeryContinuation flow :=
  package.longTimeContinuation

/-- Project aggregate Ricci-flow-with-surgery evidence from a construction package. -/
theorem ricci_flow_with_surgery_of_construction_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : RicciFlowWithSurgeryConstructionPackage flow) :
    HasRicciFlowWithSurgery n M :=
  package.withSurgery

section ConstructionPackageProjectionEqualities

variable {n : ℕ∞ω}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
variable [IsManifold ThreeManifoldModelWithCorners 1 M]
variable {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
variable (package : RicciFlowWithSurgeryConstructionPackage flow)

/-- The named surgery-scale-function projection is the stored construction field. -/
theorem surgery_scale_function_of_construction_package_eq :
    surgery_scale_function_of_construction_package package =
      package.scaleFunction :=
  rfl

/-- The named surgery-scale-continuity projection is the stored construction field. -/
theorem surgery_scale_continuity_of_construction_package_eq :
    surgery_scale_continuity_of_construction_package package =
      package.scaleContinuity :=
  rfl

/-- The named surgery-scale-separation projection is the stored construction field. -/
theorem surgery_scale_separation_of_construction_package_eq :
    surgery_scale_separation_of_construction_package package =
      package.scaleSeparation :=
  rfl

/-- The named cutoff-parameter-control projection is the stored construction field. -/
theorem surgery_cutoff_parameter_control_of_construction_package_eq :
    surgery_cutoff_parameter_control_of_construction_package package =
      package.cutoffParameterControl :=
  rfl

/-- The named cutoff smooth-bump projection is the stored construction field. -/
theorem surgery_cutoff_smooth_bump_of_construction_package_eq :
    surgery_cutoff_smooth_bump_of_construction_package package =
      package.cutoffSmoothBump :=
  rfl

/-- The named surgery-parameter-selection projection is the stored construction field. -/
theorem surgery_parameter_selection_of_construction_package_eq :
    surgery_parameter_selection_of_construction_package package =
      package.parameterSelection :=
  rfl

/-- The named strong-delta-neck detection projection is the stored construction field. -/
theorem strong_delta_neck_detection_of_construction_package_eq :
    strong_delta_neck_detection_of_construction_package package =
      package.strongDeltaNeckDetection :=
  rfl

/-- The named neck-separation projection is the stored construction field. -/
theorem surgery_neck_separation_of_construction_package_eq :
    surgery_neck_separation_of_construction_package package =
      package.neckSeparation :=
  rfl

/-- The named neck-parametrization projection is the stored construction field. -/
theorem surgery_neck_parametrization_of_construction_package_eq :
    surgery_neck_parametrization_of_construction_package package =
      package.neckParametrization :=
  rfl

/-- The named neck-coordinate projection is the stored construction field. -/
theorem surgery_neck_canonical_coordinates_of_construction_package_eq :
    surgery_neck_canonical_coordinates_of_construction_package package =
      package.neckCanonicalCoordinates :=
  rfl

/-- The named neck-decomposition projection is the stored construction field. -/
theorem surgery_neck_decomposition_of_construction_package_eq :
    surgery_neck_decomposition_of_construction_package package =
      package.neckDecomposition :=
  rfl

/-- The named standard-cap model projection is the stored construction field. -/
theorem standard_cap_model_of_construction_package_eq :
    standard_cap_model_of_construction_package package =
      package.standardCapModel :=
  rfl

/-- The named cap-gluing smoothness projection is the stored construction field. -/
theorem cap_gluing_smoothness_of_construction_package_eq :
    cap_gluing_smoothness_of_construction_package package =
      package.capGluingSmoothness :=
  rfl

/-- The named cap metric-interpolation projection is the stored construction field. -/
theorem surgery_cap_metric_interpolation_of_construction_package_eq :
    surgery_cap_metric_interpolation_of_construction_package package =
      package.capMetricInterpolation :=
  rfl

/-- The named cap curvature-estimates projection is the stored construction field. -/
theorem surgery_cap_curvature_estimates_of_construction_package_eq :
    surgery_cap_curvature_estimates_of_construction_package package =
      package.capCurvatureEstimates :=
  rfl

/-- The named cap-construction projection is the stored construction field. -/
theorem surgery_cap_construction_of_construction_package_eq :
    surgery_cap_construction_of_construction_package package =
      package.capConstruction :=
  rfl

/-- The named post-surgery curvature-pinching projection is the stored construction field. -/
theorem post_surgery_curvature_pinching_of_construction_package_eq :
    post_surgery_curvature_pinching_of_construction_package package =
      package.postSurgeryCurvaturePinching :=
  rfl

/-- The named post-surgery noncollapsing projection is the stored construction field. -/
theorem post_surgery_noncollapsing_control_of_construction_package_eq :
    post_surgery_noncollapsing_control_of_construction_package package =
      package.postSurgeryNoncollapsing :=
  rfl

/-- The named post-surgery derivative-bounds projection is the stored construction field. -/
theorem post_surgery_derivative_bounds_of_construction_package_eq :
    post_surgery_derivative_bounds_of_construction_package package =
      package.postSurgeryDerivativeBounds :=
  rfl

/-- The named post-surgery canonical-neighborhood projection is the stored construction field. -/
theorem post_surgery_canonical_neighborhood_persistence_of_construction_package_eq :
    post_surgery_canonical_neighborhood_persistence_of_construction_package
      package =
      package.postSurgeryCanonicalNeighborhoodPersistence :=
  rfl

/-- The named post-surgery metric-control projection is the stored construction field. -/
theorem post_surgery_metric_control_of_construction_package_eq :
    post_surgery_metric_control_of_construction_package package =
      package.metricControl :=
  rfl

/-- The named surgery-time discreteness projection is the stored construction field. -/
theorem surgery_time_discreteness_of_construction_package_eq :
    surgery_time_discreteness_of_construction_package package =
      package.surgeryTimeDiscreteness :=
  rfl

/-- The named surgery-time local-finiteness projection is the stored construction field. -/
theorem surgery_time_local_finiteness_of_construction_package_eq :
    surgery_time_local_finiteness_of_construction_package package =
      package.surgeryTimeLocalFiniteness :=
  rfl

/-- The named long-time existence-iteration projection is the stored construction field. -/
theorem long_time_existence_iteration_of_construction_package_eq :
    long_time_existence_iteration_of_construction_package package =
      package.longTimeExistenceIteration :=
  rfl

/-- The named long-time parameter-coherence projection is the stored construction field. -/
theorem long_time_surgery_parameter_coherence_of_construction_package_eq :
    long_time_surgery_parameter_coherence_of_construction_package package =
      package.longTimeParameterCoherence :=
  rfl

/-- The named long-time nonaccumulation projection is the stored construction field. -/
theorem long_time_nonaccumulation_of_construction_package_eq :
    long_time_nonaccumulation_of_construction_package package =
      package.longTimeNonaccumulation :=
  rfl

/-- The named long-time continuation projection is the stored construction field. -/
theorem long_time_surgery_continuation_of_construction_package_eq :
    long_time_surgery_continuation_of_construction_package package =
      package.longTimeContinuation :=
  rfl

/-- The named Ricci-flow-with-surgery projection is the stored construction field. -/
theorem ricci_flow_with_surgery_of_construction_package_eq :
    ricci_flow_with_surgery_of_construction_package package =
      package.withSurgery :=
  rfl

end ConstructionPackageProjectionEqualities

/--
Interface for Perelman's singularity-control package: non-collapsing,
canonical neighborhoods, and the estimates needed to control surgery.
-/
inductive HasPerelmanSingularityControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for Perelman's entropy functional and its basic variational setup. -/
inductive HasPerelmanEntropyFunctional
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for Perelman's F-functional and normalization constraints. -/
inductive HasPerelmanFFunctionalSetup
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for entropy normalization choices in Perelman's functional. -/
inductive HasPerelmanEntropyNormalization
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for existence of entropy minimizers at controlled scales. -/
inductive HasPerelmanEntropyMinimizerExistence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the log-Sobolev control behind Perelman's entropy bounds. -/
inductive HasPerelmanEntropyLogSobolevControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the conjugate heat equation used in Perelman's monotonicity. -/
inductive HasConjugateHeatEquationTheory
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for constructing adjoint heat kernels along the backward flow. -/
inductive HasAdjointHeatKernelConstruction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for adjoint/conjugate heat-kernel estimates used in noncollapsing. -/
inductive HasPerelmanConjugateHeatKernelEstimates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the W-functional setup behind Perelman's entropy. -/
inductive HasPerelmanWFunctionalSetup
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the entropy-gradient formula driving monotonicity. -/
inductive HasPerelmanEntropyGradientFormula
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the first-variation formula for Perelman's entropy. -/
inductive HasPerelmanEntropyFirstVariation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for monotonicity of Perelman's entropy functional. -/
inductive HasPerelmanEntropyMonotonicity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for propagating entropy lower bounds along the flow. -/
inductive HasPerelmanEntropyLowerBoundPropagation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for reduced distance along the backward Ricci-flow spacetime. -/
inductive HasPerelmanReducedDistanceTheory
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the first-variation formula for reduced length. -/
inductive HasPerelmanReducedLengthFirstVariation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for existence of reduced-distance minimizers or L-geodesics. -/
inductive HasPerelmanReducedDistanceExistence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the differential inequality satisfied by reduced distance. -/
inductive HasPerelmanReducedDistanceDifferentialInequality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for estimates on reduced distance used in blow-up analysis. -/
inductive HasPerelmanReducedDistanceEstimates
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for cut-locus and barrier control in reduced-distance arguments. -/
inductive HasPerelmanReducedDistanceCutLocusControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the reduced-Jacobian comparison used in reduced-volume monotonicity. -/
inductive HasPerelmanReducedJacobianComparison
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the nonincreasing or monotonicity formula for reduced volume. -/
inductive HasPerelmanReducedVolumeNonincreasing
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for defining reduced volume from reduced distance. -/
inductive HasPerelmanReducedVolumeDefinition
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the reduced-volume derivative formula. -/
inductive HasPerelmanReducedVolumeDerivativeFormula
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the reduced-volume rigidity/equality case input. -/
inductive HasPerelmanReducedVolumeRigidity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for positive lower bounds on reduced volume at controlled scales. -/
inductive HasPerelmanReducedVolumePositiveLowerBound
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for reduced-volume limit rigidity in equality or almost-equality cases. -/
inductive HasPerelmanReducedVolumeLimitRigidity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for quantified kappa-noncollapsing constants and scale ranges. -/
inductive HasPerelmanKappaNoncollapsingQuantification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the contradiction setup in the no-local-collapsing theorem. -/
inductive HasPerelmanNoLocalCollapsingContradictionSetup
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for blowing up a collapsed ball in Perelman's contradiction argument. -/
inductive HasPerelmanCollapsedBallBlowup
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for deriving the volume-ratio contradiction in no-local-collapsing. -/
inductive HasPerelmanVolumeRatioContradiction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface deriving kappa-noncollapsing from reduced-volume control. -/
inductive HasPerelmanKappaNoncollapsingFromReducedVolume
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the local volume lower bound in no-local-collapsing. -/
inductive HasNoLocalCollapsingVolumeLowerBound
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for Hamilton compactness for pointed Ricci-flow sequences. -/
inductive HasHamiltonCompactnessTheorem
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for compactness of ancient kappa-solutions used as blow-up limits. -/
inductive HasAncientKappaSolutionCompactness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for extracting ancient kappa-solution limits from high-curvature blow-ups. -/
inductive HasAncientKappaSolutionLimitExtraction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for pointed parabolic rescalings used to form kappa-solution limits. -/
inductive HasKappaSolutionPointedRescaling
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for curvature normalization in kappa-solution blow-up limits. -/
inductive HasKappaSolutionCurvatureNormalization
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the structure theory of three-dimensional ancient kappa-solutions. -/
inductive HasKappaSolutionStructureTheory
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for nonnegative curvature-operator control in kappa-solutions. -/
inductive HasKappaSolutionNonnegativeCurvatureOperator
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for asymptotic soliton analysis of ancient kappa-solutions. -/
inductive HasKappaSolutionAsymptoticSoliton
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the classification input behind canonical neighborhoods. -/
inductive HasCanonicalNeighborhoodClassification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the epsilon-neck/epsilon-cap dichotomy in canonical neighborhoods. -/
inductive HasCanonicalNeighborhoodNeckCapDichotomy
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for scale control in the canonical-neighborhood theorem. -/
inductive HasCanonicalNeighborhoodScaleControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for stability of canonical-neighborhood models under blow-up limits. -/
inductive HasCanonicalNeighborhoodStability
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for persistence of canonical-neighborhood control across scales. -/
inductive HasCanonicalNeighborhoodPersistenceAcrossScales
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for Perelman's no-local-collapsing theorem. -/
inductive HasPerelmanNoLocalCollapsing
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for Perelman's reduced-volume/reduced-distance monotonicity input. -/
inductive HasPerelmanReducedVolumeMonotonicity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for the canonical-neighborhood theorem used in the surgery analysis. -/
inductive HasCanonicalNeighborhoodTheorem
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for classification of singularity models needed by surgery control. -/
inductive HasSingularityModelClassification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/-- Interface for classifying the singularity models obtained from blow-up limits. -/
inductive HasSingularityModelBlowupClassification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (_flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop

/--
Package for the Perelman singularity-control inputs used by surgery.

The final `control` field is still an unconstructed interface; the preceding
fields make the standard sub-obligations explicit and separately auditable.
-/
structure PerelmanSingularityControlPackage
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) where
  /-- F-functional setup and normalization. -/
  fFunctionalSetup : HasPerelmanFFunctionalSetup flow
  /-- Entropy normalization choices for the F/W functionals. -/
  entropyNormalization : HasPerelmanEntropyNormalization flow
  /-- Existence of entropy minimizers at controlled scales. -/
  entropyMinimizerExistence : HasPerelmanEntropyMinimizerExistence flow
  /-- Log-Sobolev control behind entropy lower bounds. -/
  entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow
  /-- Conjugate heat equation theory for entropy monotonicity. -/
  conjugateHeatEquation : HasConjugateHeatEquationTheory flow
  /-- Adjoint heat kernel construction. -/
  adjointHeatKernel : HasAdjointHeatKernelConstruction flow
  /-- Adjoint/conjugate heat-kernel estimates used by noncollapsing. -/
  conjugateHeatKernelEstimates : HasPerelmanConjugateHeatKernelEstimates flow
  /-- W-functional setup behind entropy. -/
  wFunctionalSetup : HasPerelmanWFunctionalSetup flow
  /-- Entropy-gradient formula. -/
  entropyGradientFormula : HasPerelmanEntropyGradientFormula flow
  /-- First-variation formula for entropy. -/
  entropyFirstVariation : HasPerelmanEntropyFirstVariation flow
  /-- Entropy monotonicity input. -/
  entropyMonotonicity : HasPerelmanEntropyMonotonicity flow
  /-- Propagation of entropy lower bounds along the flow. -/
  entropyLowerBoundPropagation : HasPerelmanEntropyLowerBoundPropagation flow
  /-- Entropy functional and its variational setup. -/
  entropyFunctional : HasPerelmanEntropyFunctional flow
  /-- Reduced-length first-variation formula. -/
  reducedLengthFirstVariation : HasPerelmanReducedLengthFirstVariation flow
  /-- Existence of reduced-distance minimizers or L-geodesics. -/
  reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow
  /-- Differential inequality for reduced distance. -/
  reducedDistanceDifferentialInequality :
    HasPerelmanReducedDistanceDifferentialInequality flow
  /-- Reduced-distance estimates used in blow-up analysis. -/
  reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow
  /-- Cut-locus/barrier control for reduced distance. -/
  reducedDistanceCutLocusControl :
    HasPerelmanReducedDistanceCutLocusControl flow
  /-- Reduced-Jacobian comparison input. -/
  reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow
  /-- Reduced-distance theory for the evolving geometry. -/
  reducedDistance : HasPerelmanReducedDistanceTheory flow
  /-- Definition of reduced volume from reduced distance. -/
  reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow
  /-- Reduced-volume derivative formula. -/
  reducedVolumeDerivativeFormula : HasPerelmanReducedVolumeDerivativeFormula flow
  /-- Reduced-volume rigidity/equality-case input. -/
  reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow
  /-- Positive lower bounds for reduced volume at controlled scales. -/
  reducedVolumePositiveLowerBound :
    HasPerelmanReducedVolumePositiveLowerBound flow
  /-- Limit rigidity for reduced-volume equality and almost-equality cases. -/
  reducedVolumeLimitRigidity : HasPerelmanReducedVolumeLimitRigidity flow
  /-- Reduced-volume monotonicity/nonincreasing formula. -/
  reducedVolumeNonincreasing : HasPerelmanReducedVolumeNonincreasing flow
  /-- Derivation of kappa-noncollapsing from reduced-volume control. -/
  kappaNoncollapsingFromReducedVolume :
    HasPerelmanKappaNoncollapsingFromReducedVolume flow
  /-- Contradiction setup for no-local-collapsing. -/
  noLocalCollapsingContradictionSetup :
    HasPerelmanNoLocalCollapsingContradictionSetup flow
  /-- Collapsed-ball blow-up construction in the noncollapsing proof. -/
  collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow
  /-- Volume-ratio contradiction derived from entropy/reduced-volume bounds. -/
  volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow
  /-- Local volume lower bound used in no-local-collapsing. -/
  noLocalCollapsingVolumeLowerBound : HasNoLocalCollapsingVolumeLowerBound flow
  /-- Quantified kappa-noncollapsing scale control. -/
  kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow
  /-- Hamilton compactness theorem for pointed flow sequences. -/
  hamiltonCompactness : HasHamiltonCompactnessTheorem flow
  /-- Extraction of ancient kappa-solution limits from high-curvature blow-ups. -/
  ancientKappaSolutionLimitExtraction :
    HasAncientKappaSolutionLimitExtraction flow
  /-- Pointed parabolic rescalings used in the blow-up limit extraction. -/
  kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow
  /-- Curvature normalization for kappa-solution limits. -/
  kappaSolutionCurvatureNormalization :
    HasKappaSolutionCurvatureNormalization flow
  /-- Structure theory of three-dimensional ancient kappa-solutions. -/
  kappaSolutionStructure : HasKappaSolutionStructureTheory flow
  /-- Nonnegative curvature-operator control for kappa-solutions. -/
  kappaSolutionNonnegativeCurvatureOperator :
    HasKappaSolutionNonnegativeCurvatureOperator flow
  /-- Asymptotic soliton analysis for ancient kappa-solutions. -/
  kappaSolutionAsymptoticSoliton : HasKappaSolutionAsymptoticSoliton flow
  /-- Compactness theory for ancient kappa-solution blow-up limits. -/
  ancientKappaSolutionCompactness : HasAncientKappaSolutionCompactness flow
  /-- Scale control used by the canonical-neighborhood theorem. -/
  canonicalNeighborhoodScaleControl : HasCanonicalNeighborhoodScaleControl flow
  /-- Stability of canonical-neighborhood models under blow-up limits. -/
  canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow
  /-- Persistence of canonical-neighborhood control across scales. -/
  canonicalNeighborhoodPersistenceAcrossScales :
    HasCanonicalNeighborhoodPersistenceAcrossScales flow
  /-- Epsilon-neck/epsilon-cap dichotomy for canonical neighborhoods. -/
  canonicalNeighborhoodNeckCapDichotomy :
    HasCanonicalNeighborhoodNeckCapDichotomy flow
  /-- Classification input behind the canonical-neighborhood theorem. -/
  canonicalNeighborhoodClassification :
    HasCanonicalNeighborhoodClassification flow
  /-- Perelman's no-local-collapsing input. -/
  noLocalCollapsing : HasPerelmanNoLocalCollapsing flow
  /-- Reduced-volume/reduced-distance monotonicity input. -/
  reducedVolume : HasPerelmanReducedVolumeMonotonicity flow
  /-- Canonical-neighborhood input. -/
  canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow
  /-- Singularity-model classification input. -/
  singularityModelClassification : HasSingularityModelClassification flow
  /-- Blow-up classification input for singularity models. -/
  singularityModelBlowupClassification :
    HasSingularityModelBlowupClassification flow
  /-- The aggregate singularity-control theorem needed by surgery. -/
  control : HasPerelmanSingularityControl flow

/--
The fixed-flow Perelman singularity-control statement: entropy, reduced-volume,
noncollapsing, compactness, canonical-neighborhood, and singularity-model
inputs are bundled with the aggregate singularity-control theorem.
-/
def PerelmanSingularityControlStatement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop :=
  ∃ _fFunctionalSetup : HasPerelmanFFunctionalSetup flow,
  ∃ _entropyNormalization : HasPerelmanEntropyNormalization flow,
  ∃ _entropyMinimizerExistence : HasPerelmanEntropyMinimizerExistence flow,
  ∃ _entropyLogSobolevControl : HasPerelmanEntropyLogSobolevControl flow,
  ∃ _conjugateHeatEquation : HasConjugateHeatEquationTheory flow,
  ∃ _adjointHeatKernel : HasAdjointHeatKernelConstruction flow,
  ∃ _conjugateHeatKernelEstimates :
    HasPerelmanConjugateHeatKernelEstimates flow,
  ∃ _wFunctionalSetup : HasPerelmanWFunctionalSetup flow,
  ∃ _entropyGradientFormula : HasPerelmanEntropyGradientFormula flow,
  ∃ _entropyFirstVariation : HasPerelmanEntropyFirstVariation flow,
  ∃ _entropyMonotonicity : HasPerelmanEntropyMonotonicity flow,
  ∃ _entropyLowerBoundPropagation :
    HasPerelmanEntropyLowerBoundPropagation flow,
  ∃ _entropyFunctional : HasPerelmanEntropyFunctional flow,
  ∃ _reducedLengthFirstVariation :
    HasPerelmanReducedLengthFirstVariation flow,
  ∃ _reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow,
  ∃ _reducedDistanceDifferentialInequality :
    HasPerelmanReducedDistanceDifferentialInequality flow,
  ∃ _reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow,
  ∃ _reducedDistanceCutLocusControl :
    HasPerelmanReducedDistanceCutLocusControl flow,
  ∃ _reducedJacobianComparison : HasPerelmanReducedJacobianComparison flow,
  ∃ _reducedDistance : HasPerelmanReducedDistanceTheory flow,
  ∃ _reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow,
  ∃ _reducedVolumeDerivativeFormula :
    HasPerelmanReducedVolumeDerivativeFormula flow,
  ∃ _reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow,
  ∃ _reducedVolumePositiveLowerBound :
    HasPerelmanReducedVolumePositiveLowerBound flow,
  ∃ _reducedVolumeLimitRigidity :
    HasPerelmanReducedVolumeLimitRigidity flow,
  ∃ _reducedVolumeNonincreasing :
    HasPerelmanReducedVolumeNonincreasing flow,
  ∃ _kappaNoncollapsingFromReducedVolume :
    HasPerelmanKappaNoncollapsingFromReducedVolume flow,
  ∃ _noLocalCollapsingContradictionSetup :
    HasPerelmanNoLocalCollapsingContradictionSetup flow,
  ∃ _collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow,
  ∃ _volumeRatioContradiction : HasPerelmanVolumeRatioContradiction flow,
  ∃ _noLocalCollapsingVolumeLowerBound :
    HasNoLocalCollapsingVolumeLowerBound flow,
  ∃ _kappaNoncollapsing : HasPerelmanKappaNoncollapsingQuantification flow,
  ∃ _hamiltonCompactness : HasHamiltonCompactnessTheorem flow,
  ∃ _ancientKappaSolutionLimitExtraction :
    HasAncientKappaSolutionLimitExtraction flow,
  ∃ _kappaSolutionPointedRescaling : HasKappaSolutionPointedRescaling flow,
  ∃ _kappaSolutionCurvatureNormalization :
    HasKappaSolutionCurvatureNormalization flow,
  ∃ _kappaSolutionStructure : HasKappaSolutionStructureTheory flow,
  ∃ _kappaSolutionNonnegativeCurvatureOperator :
    HasKappaSolutionNonnegativeCurvatureOperator flow,
  ∃ _kappaSolutionAsymptoticSoliton :
    HasKappaSolutionAsymptoticSoliton flow,
  ∃ _ancientKappaSolutionCompactness :
    HasAncientKappaSolutionCompactness flow,
  ∃ _canonicalNeighborhoodScaleControl :
    HasCanonicalNeighborhoodScaleControl flow,
  ∃ _canonicalNeighborhoodStability : HasCanonicalNeighborhoodStability flow,
  ∃ _canonicalNeighborhoodPersistenceAcrossScales :
    HasCanonicalNeighborhoodPersistenceAcrossScales flow,
  ∃ _canonicalNeighborhoodNeckCapDichotomy :
    HasCanonicalNeighborhoodNeckCapDichotomy flow,
  ∃ _canonicalNeighborhoodClassification :
    HasCanonicalNeighborhoodClassification flow,
  ∃ _noLocalCollapsing : HasPerelmanNoLocalCollapsing flow,
  ∃ _reducedVolume : HasPerelmanReducedVolumeMonotonicity flow,
  ∃ _canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow,
  ∃ _singularityModelClassification : HasSingularityModelClassification flow,
  ∃ _singularityModelBlowupClassification :
    HasSingularityModelBlowupClassification flow,
    HasPerelmanSingularityControl flow

/--
The fixed-flow Perelman singularity-control statement is exactly the listed
entropy, conjugate-heat, reduced-distance, reduced-volume, noncollapsing,
kappa-solution, canonical-neighborhood, singularity-model, and aggregate
control witness stack.
-/
theorem perelmanSingularityControlStatement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    PerelmanSingularityControlStatement flow =
      (∃ _fFunctionalSetup : HasPerelmanFFunctionalSetup flow,
      ∃ _entropyNormalization : HasPerelmanEntropyNormalization flow,
      ∃ _entropyMinimizerExistence :
        HasPerelmanEntropyMinimizerExistence flow,
      ∃ _entropyLogSobolevControl :
        HasPerelmanEntropyLogSobolevControl flow,
      ∃ _conjugateHeatEquation : HasConjugateHeatEquationTheory flow,
      ∃ _adjointHeatKernel : HasAdjointHeatKernelConstruction flow,
      ∃ _conjugateHeatKernelEstimates :
        HasPerelmanConjugateHeatKernelEstimates flow,
      ∃ _wFunctionalSetup : HasPerelmanWFunctionalSetup flow,
      ∃ _entropyGradientFormula : HasPerelmanEntropyGradientFormula flow,
      ∃ _entropyFirstVariation : HasPerelmanEntropyFirstVariation flow,
      ∃ _entropyMonotonicity : HasPerelmanEntropyMonotonicity flow,
      ∃ _entropyLowerBoundPropagation :
        HasPerelmanEntropyLowerBoundPropagation flow,
      ∃ _entropyFunctional : HasPerelmanEntropyFunctional flow,
      ∃ _reducedLengthFirstVariation :
        HasPerelmanReducedLengthFirstVariation flow,
      ∃ _reducedDistanceExistence : HasPerelmanReducedDistanceExistence flow,
      ∃ _reducedDistanceDifferentialInequality :
        HasPerelmanReducedDistanceDifferentialInequality flow,
      ∃ _reducedDistanceEstimates : HasPerelmanReducedDistanceEstimates flow,
      ∃ _reducedDistanceCutLocusControl :
        HasPerelmanReducedDistanceCutLocusControl flow,
      ∃ _reducedJacobianComparison :
        HasPerelmanReducedJacobianComparison flow,
      ∃ _reducedDistance : HasPerelmanReducedDistanceTheory flow,
      ∃ _reducedVolumeDefinition : HasPerelmanReducedVolumeDefinition flow,
      ∃ _reducedVolumeDerivativeFormula :
        HasPerelmanReducedVolumeDerivativeFormula flow,
      ∃ _reducedVolumeRigidity : HasPerelmanReducedVolumeRigidity flow,
      ∃ _reducedVolumePositiveLowerBound :
        HasPerelmanReducedVolumePositiveLowerBound flow,
      ∃ _reducedVolumeLimitRigidity :
        HasPerelmanReducedVolumeLimitRigidity flow,
      ∃ _reducedVolumeNonincreasing :
        HasPerelmanReducedVolumeNonincreasing flow,
      ∃ _kappaNoncollapsingFromReducedVolume :
        HasPerelmanKappaNoncollapsingFromReducedVolume flow,
      ∃ _noLocalCollapsingContradictionSetup :
        HasPerelmanNoLocalCollapsingContradictionSetup flow,
      ∃ _collapsedBallBlowup : HasPerelmanCollapsedBallBlowup flow,
      ∃ _volumeRatioContradiction :
        HasPerelmanVolumeRatioContradiction flow,
      ∃ _noLocalCollapsingVolumeLowerBound :
        HasNoLocalCollapsingVolumeLowerBound flow,
      ∃ _kappaNoncollapsing :
        HasPerelmanKappaNoncollapsingQuantification flow,
      ∃ _hamiltonCompactness : HasHamiltonCompactnessTheorem flow,
      ∃ _ancientKappaSolutionLimitExtraction :
        HasAncientKappaSolutionLimitExtraction flow,
      ∃ _kappaSolutionPointedRescaling :
        HasKappaSolutionPointedRescaling flow,
      ∃ _kappaSolutionCurvatureNormalization :
        HasKappaSolutionCurvatureNormalization flow,
      ∃ _kappaSolutionStructure : HasKappaSolutionStructureTheory flow,
      ∃ _kappaSolutionNonnegativeCurvatureOperator :
        HasKappaSolutionNonnegativeCurvatureOperator flow,
      ∃ _kappaSolutionAsymptoticSoliton :
        HasKappaSolutionAsymptoticSoliton flow,
      ∃ _ancientKappaSolutionCompactness :
        HasAncientKappaSolutionCompactness flow,
      ∃ _canonicalNeighborhoodScaleControl :
        HasCanonicalNeighborhoodScaleControl flow,
      ∃ _canonicalNeighborhoodStability :
        HasCanonicalNeighborhoodStability flow,
      ∃ _canonicalNeighborhoodPersistenceAcrossScales :
        HasCanonicalNeighborhoodPersistenceAcrossScales flow,
      ∃ _canonicalNeighborhoodNeckCapDichotomy :
        HasCanonicalNeighborhoodNeckCapDichotomy flow,
      ∃ _canonicalNeighborhoodClassification :
        HasCanonicalNeighborhoodClassification flow,
      ∃ _noLocalCollapsing : HasPerelmanNoLocalCollapsing flow,
      ∃ _reducedVolume : HasPerelmanReducedVolumeMonotonicity flow,
      ∃ _canonicalNeighborhood : HasCanonicalNeighborhoodTheorem flow,
      ∃ _singularityModelClassification :
        HasSingularityModelClassification flow,
      ∃ _singularityModelBlowupClassification :
        HasSingularityModelBlowupClassification flow,
        HasPerelmanSingularityControl flow) :=
  rfl

/--
Assemble the fixed-flow Perelman singularity-control statement from the named
control components.
-/
theorem perelman_singularity_control_statement_of_components
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
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
    (singularityModelClassification : HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (control : HasPerelmanSingularityControl flow) :
    PerelmanSingularityControlStatement flow :=
  ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
    entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
    conjugateHeatKernelEstimates, wFunctionalSetup, entropyGradientFormula,
    entropyFirstVariation, entropyMonotonicity, entropyLowerBoundPropagation,
    entropyFunctional, reducedLengthFirstVariation, reducedDistanceExistence,
    reducedDistanceDifferentialInequality, reducedDistanceEstimates,
    reducedDistanceCutLocusControl, reducedJacobianComparison, reducedDistance,
    reducedVolumeDefinition, reducedVolumeDerivativeFormula,
    reducedVolumeRigidity, reducedVolumePositiveLowerBound,
    reducedVolumeLimitRigidity, reducedVolumeNonincreasing,
    kappaNoncollapsingFromReducedVolume,
    noLocalCollapsingContradictionSetup, collapsedBallBlowup,
    volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
    kappaNoncollapsing, hamiltonCompactness,
    ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
    kappaSolutionCurvatureNormalization, kappaSolutionStructure,
    kappaSolutionNonnegativeCurvatureOperator, kappaSolutionAsymptoticSoliton,
    ancientKappaSolutionCompactness, canonicalNeighborhoodScaleControl,
    canonicalNeighborhoodStability,
    canonicalNeighborhoodPersistenceAcrossScales,
    canonicalNeighborhoodNeckCapDichotomy, canonicalNeighborhoodClassification,
    noLocalCollapsing, reducedVolume, canonicalNeighborhood,
    singularityModelClassification, singularityModelBlowupClassification,
    control⟩

/--
The fixed-flow Perelman singularity-control component assembler is exactly the
tuple of entropy, conjugate-heat, reduced-distance, reduced-volume,
noncollapsing, kappa-solution, canonical-neighborhood, singularity-model, and
aggregate control witnesses.
-/
theorem perelman_singularity_control_statement_of_components_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
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
    (singularityModelClassification : HasSingularityModelClassification flow)
    (singularityModelBlowupClassification :
      HasSingularityModelBlowupClassification flow)
    (control : HasPerelmanSingularityControl flow) :
    perelman_singularity_control_statement_of_components flow
        fFunctionalSetup entropyNormalization entropyMinimizerExistence
        entropyLogSobolevControl conjugateHeatEquation adjointHeatKernel
        conjugateHeatKernelEstimates wFunctionalSetup entropyGradientFormula
        entropyFirstVariation entropyMonotonicity entropyLowerBoundPropagation
        entropyFunctional reducedLengthFirstVariation reducedDistanceExistence
        reducedDistanceDifferentialInequality reducedDistanceEstimates
        reducedDistanceCutLocusControl reducedJacobianComparison
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
        canonicalNeighborhoodStability
        canonicalNeighborhoodPersistenceAcrossScales
        canonicalNeighborhoodNeckCapDichotomy canonicalNeighborhoodClassification
        noLocalCollapsing reducedVolume canonicalNeighborhood
        singularityModelClassification singularityModelBlowupClassification
        control =
      (by
        exact ⟨fFunctionalSetup, entropyNormalization,
          entropyMinimizerExistence, entropyLogSobolevControl,
          conjugateHeatEquation, adjointHeatKernel,
          conjugateHeatKernelEstimates, wFunctionalSetup,
          entropyGradientFormula, entropyFirstVariation, entropyMonotonicity,
          entropyLowerBoundPropagation, entropyFunctional,
          reducedLengthFirstVariation, reducedDistanceExistence,
          reducedDistanceDifferentialInequality, reducedDistanceEstimates,
          reducedDistanceCutLocusControl, reducedJacobianComparison,
          reducedDistance, reducedVolumeDefinition,
          reducedVolumeDerivativeFormula, reducedVolumeRigidity,
          reducedVolumePositiveLowerBound, reducedVolumeLimitRigidity,
          reducedVolumeNonincreasing, kappaNoncollapsingFromReducedVolume,
          noLocalCollapsingContradictionSetup, collapsedBallBlowup,
          volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
          kappaNoncollapsing, hamiltonCompactness,
          ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
          kappaSolutionCurvatureNormalization, kappaSolutionStructure,
          kappaSolutionNonnegativeCurvatureOperator,
          kappaSolutionAsymptoticSoliton, ancientKappaSolutionCompactness,
          canonicalNeighborhoodScaleControl, canonicalNeighborhoodStability,
          canonicalNeighborhoodPersistenceAcrossScales,
          canonicalNeighborhoodNeckCapDichotomy,
          canonicalNeighborhoodClassification, noLocalCollapsing,
          reducedVolume, canonicalNeighborhood, singularityModelClassification,
          singularityModelBlowupClassification, control⟩) := by
  apply Subsingleton.elim

/--
A completed Perelman package assembles the fixed-flow singularity-control
statement.
-/
theorem perelman_singularity_control_statement_of_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    PerelmanSingularityControlStatement flow :=
  perelman_singularity_control_statement_of_components flow
    package.fFunctionalSetup package.entropyNormalization
    package.entropyMinimizerExistence package.entropyLogSobolevControl
    package.conjugateHeatEquation package.adjointHeatKernel
    package.conjugateHeatKernelEstimates package.wFunctionalSetup
    package.entropyGradientFormula package.entropyFirstVariation
    package.entropyMonotonicity package.entropyLowerBoundPropagation
    package.entropyFunctional package.reducedLengthFirstVariation
    package.reducedDistanceExistence package.reducedDistanceDifferentialInequality
    package.reducedDistanceEstimates package.reducedDistanceCutLocusControl
    package.reducedJacobianComparison package.reducedDistance
    package.reducedVolumeDefinition package.reducedVolumeDerivativeFormula
    package.reducedVolumeRigidity package.reducedVolumePositiveLowerBound
    package.reducedVolumeLimitRigidity package.reducedVolumeNonincreasing
    package.kappaNoncollapsingFromReducedVolume
    package.noLocalCollapsingContradictionSetup package.collapsedBallBlowup
    package.volumeRatioContradiction package.noLocalCollapsingVolumeLowerBound
    package.kappaNoncollapsing package.hamiltonCompactness
    package.ancientKappaSolutionLimitExtraction
    package.kappaSolutionPointedRescaling
    package.kappaSolutionCurvatureNormalization package.kappaSolutionStructure
    package.kappaSolutionNonnegativeCurvatureOperator
    package.kappaSolutionAsymptoticSoliton
    package.ancientKappaSolutionCompactness
    package.canonicalNeighborhoodScaleControl
    package.canonicalNeighborhoodStability
    package.canonicalNeighborhoodPersistenceAcrossScales
    package.canonicalNeighborhoodNeckCapDichotomy
  package.canonicalNeighborhoodClassification package.noLocalCollapsing
  package.reducedVolume package.canonicalNeighborhood
  package.singularityModelClassification
  package.singularityModelBlowupClassification package.control

/--
The completed Perelman package route to the theorem-shaped singularity-control
statement is exactly the component assembly route applied to the package fields.
-/
theorem perelman_singularity_control_statement_of_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    perelman_singularity_control_statement_of_package package =
      perelman_singularity_control_statement_of_components flow
        package.fFunctionalSetup package.entropyNormalization
        package.entropyMinimizerExistence package.entropyLogSobolevControl
        package.conjugateHeatEquation package.adjointHeatKernel
        package.conjugateHeatKernelEstimates package.wFunctionalSetup
        package.entropyGradientFormula package.entropyFirstVariation
        package.entropyMonotonicity package.entropyLowerBoundPropagation
        package.entropyFunctional package.reducedLengthFirstVariation
        package.reducedDistanceExistence
        package.reducedDistanceDifferentialInequality
        package.reducedDistanceEstimates package.reducedDistanceCutLocusControl
        package.reducedJacobianComparison package.reducedDistance
        package.reducedVolumeDefinition package.reducedVolumeDerivativeFormula
        package.reducedVolumeRigidity package.reducedVolumePositiveLowerBound
        package.reducedVolumeLimitRigidity package.reducedVolumeNonincreasing
        package.kappaNoncollapsingFromReducedVolume
        package.noLocalCollapsingContradictionSetup package.collapsedBallBlowup
        package.volumeRatioContradiction package.noLocalCollapsingVolumeLowerBound
        package.kappaNoncollapsing package.hamiltonCompactness
        package.ancientKappaSolutionLimitExtraction
        package.kappaSolutionPointedRescaling
        package.kappaSolutionCurvatureNormalization package.kappaSolutionStructure
        package.kappaSolutionNonnegativeCurvatureOperator
        package.kappaSolutionAsymptoticSoliton
        package.ancientKappaSolutionCompactness
        package.canonicalNeighborhoodScaleControl
        package.canonicalNeighborhoodStability
        package.canonicalNeighborhoodPersistenceAcrossScales
        package.canonicalNeighborhoodNeckCapDichotomy
        package.canonicalNeighborhoodClassification package.noLocalCollapsing
        package.reducedVolume package.canonicalNeighborhood
        package.singularityModelClassification
        package.singularityModelBlowupClassification package.control := by
  rfl

/--
The theorem-shaped Perelman statement supplies the aggregate singularity-control
interface.
-/
theorem perelman_singularity_control_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    HasPerelmanSingularityControl flow := by
  rcases statement with
    ⟨_fFunctionalSetup, _entropyNormalization,
      _entropyMinimizerExistence, _entropyLogSobolevControl,
      _conjugateHeatEquation, _adjointHeatKernel,
      _conjugateHeatKernelEstimates, _wFunctionalSetup,
      _entropyGradientFormula, _entropyFirstVariation,
      _entropyMonotonicity, _entropyLowerBoundPropagation,
      _entropyFunctional, _reducedLengthFirstVariation,
      _reducedDistanceExistence, _reducedDistanceDifferentialInequality,
      _reducedDistanceEstimates, _reducedDistanceCutLocusControl,
      _reducedJacobianComparison, _reducedDistance,
      _reducedVolumeDefinition, _reducedVolumeDerivativeFormula,
      _reducedVolumeRigidity, _reducedVolumePositiveLowerBound,
      _reducedVolumeLimitRigidity, _reducedVolumeNonincreasing,
      _kappaNoncollapsingFromReducedVolume,
      _noLocalCollapsingContradictionSetup, _collapsedBallBlowup,
      _volumeRatioContradiction, _noLocalCollapsingVolumeLowerBound,
      _kappaNoncollapsing, _hamiltonCompactness,
      _ancientKappaSolutionLimitExtraction, _kappaSolutionPointedRescaling,
      _kappaSolutionCurvatureNormalization, _kappaSolutionStructure,
      _kappaSolutionNonnegativeCurvatureOperator,
      _kappaSolutionAsymptoticSoliton, _ancientKappaSolutionCompactness,
      _canonicalNeighborhoodScaleControl, _canonicalNeighborhoodStability,
      _canonicalNeighborhoodPersistenceAcrossScales,
      _canonicalNeighborhoodNeckCapDichotomy,
      _canonicalNeighborhoodClassification, _noLocalCollapsing,
      _reducedVolume, _canonicalNeighborhood,
      _singularityModelClassification, _singularityModelBlowupClassification,
      control⟩
  exact control

/--
The Perelman statement aggregate bridge is exactly the final
singularity-control witness stored in the theorem-shaped Perelman statement.
-/
theorem perelman_singularity_control_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    perelman_singularity_control_of_statement statement =
      (by
        rcases statement with
          ⟨_fFunctionalSetup, _entropyNormalization,
            _entropyMinimizerExistence, _entropyLogSobolevControl,
            _conjugateHeatEquation, _adjointHeatKernel,
            _conjugateHeatKernelEstimates, _wFunctionalSetup,
            _entropyGradientFormula, _entropyFirstVariation,
            _entropyMonotonicity, _entropyLowerBoundPropagation,
            _entropyFunctional, _reducedLengthFirstVariation,
            _reducedDistanceExistence, _reducedDistanceDifferentialInequality,
            _reducedDistanceEstimates, _reducedDistanceCutLocusControl,
            _reducedJacobianComparison, _reducedDistance,
            _reducedVolumeDefinition, _reducedVolumeDerivativeFormula,
            _reducedVolumeRigidity, _reducedVolumePositiveLowerBound,
            _reducedVolumeLimitRigidity, _reducedVolumeNonincreasing,
            _kappaNoncollapsingFromReducedVolume,
            _noLocalCollapsingContradictionSetup, _collapsedBallBlowup,
            _volumeRatioContradiction, _noLocalCollapsingVolumeLowerBound,
            _kappaNoncollapsing, _hamiltonCompactness,
            _ancientKappaSolutionLimitExtraction, _kappaSolutionPointedRescaling,
            _kappaSolutionCurvatureNormalization, _kappaSolutionStructure,
            _kappaSolutionNonnegativeCurvatureOperator,
            _kappaSolutionAsymptoticSoliton, _ancientKappaSolutionCompactness,
            _canonicalNeighborhoodScaleControl, _canonicalNeighborhoodStability,
            _canonicalNeighborhoodPersistenceAcrossScales,
            _canonicalNeighborhoodNeckCapDichotomy,
            _canonicalNeighborhoodClassification, _noLocalCollapsing,
            _reducedVolume, _canonicalNeighborhood,
            _singularityModelClassification,
            _singularityModelBlowupClassification, control⟩
        exact control) := by
  apply Subsingleton.elim

/--
Semantic alias for the complete Perelman sub-obligation payload exposed by a
theorem-shaped singularity-control statement.
-/
abbrev PerelmanSingularityControlSubobligationsPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop :=
  HasPerelmanFFunctionalSetup flow ∧
  HasPerelmanEntropyNormalization flow ∧
  HasPerelmanEntropyMinimizerExistence flow ∧
  HasPerelmanEntropyLogSobolevControl flow ∧
  HasConjugateHeatEquationTheory flow ∧
  HasAdjointHeatKernelConstruction flow ∧
  HasPerelmanConjugateHeatKernelEstimates flow ∧
  HasPerelmanWFunctionalSetup flow ∧
  HasPerelmanEntropyGradientFormula flow ∧
  HasPerelmanEntropyFirstVariation flow ∧
  HasPerelmanEntropyMonotonicity flow ∧
  HasPerelmanEntropyLowerBoundPropagation flow ∧
  HasPerelmanEntropyFunctional flow ∧
  HasPerelmanReducedLengthFirstVariation flow ∧
  HasPerelmanReducedDistanceExistence flow ∧
  HasPerelmanReducedDistanceDifferentialInequality flow ∧
  HasPerelmanReducedDistanceEstimates flow ∧
  HasPerelmanReducedDistanceCutLocusControl flow ∧
  HasPerelmanReducedJacobianComparison flow ∧
  HasPerelmanReducedDistanceTheory flow ∧
  HasPerelmanReducedVolumeDefinition flow ∧
  HasPerelmanReducedVolumeDerivativeFormula flow ∧
  HasPerelmanReducedVolumeRigidity flow ∧
  HasPerelmanReducedVolumePositiveLowerBound flow ∧
  HasPerelmanReducedVolumeLimitRigidity flow ∧
  HasPerelmanReducedVolumeNonincreasing flow ∧
  HasPerelmanKappaNoncollapsingFromReducedVolume flow ∧
  HasPerelmanNoLocalCollapsingContradictionSetup flow ∧
  HasPerelmanCollapsedBallBlowup flow ∧
  HasPerelmanVolumeRatioContradiction flow ∧
  HasNoLocalCollapsingVolumeLowerBound flow ∧
  HasPerelmanKappaNoncollapsingQuantification flow ∧
  HasHamiltonCompactnessTheorem flow ∧
  HasAncientKappaSolutionLimitExtraction flow ∧
  HasKappaSolutionPointedRescaling flow ∧
  HasKappaSolutionCurvatureNormalization flow ∧
  HasKappaSolutionStructureTheory flow ∧
  HasKappaSolutionNonnegativeCurvatureOperator flow ∧
  HasKappaSolutionAsymptoticSoliton flow ∧
  HasAncientKappaSolutionCompactness flow ∧
  HasCanonicalNeighborhoodScaleControl flow ∧
  HasCanonicalNeighborhoodStability flow ∧
  HasCanonicalNeighborhoodPersistenceAcrossScales flow ∧
  HasCanonicalNeighborhoodNeckCapDichotomy flow ∧
  HasCanonicalNeighborhoodClassification flow ∧
  HasPerelmanNoLocalCollapsing flow ∧
  HasPerelmanReducedVolumeMonotonicity flow ∧
  HasCanonicalNeighborhoodTheorem flow ∧
  HasSingularityModelClassification flow ∧
  HasSingularityModelBlowupClassification flow ∧
  HasPerelmanSingularityControl (n := n) (M := M) flow

/--
The complete Perelman sub-obligation payload alias is definitionally the
entropy, conjugate-heat, reduced-distance, reduced-volume, noncollapsing,
kappa-solution, canonical-neighborhood, singularity-model, and aggregate
singularity-control witness stack for the fixed flow.
-/
theorem perelmanSingularityControlSubobligationsPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    PerelmanSingularityControlSubobligationsPayload flow =
      (HasPerelmanFFunctionalSetup flow ∧
      HasPerelmanEntropyNormalization flow ∧
      HasPerelmanEntropyMinimizerExistence flow ∧
      HasPerelmanEntropyLogSobolevControl flow ∧
      HasConjugateHeatEquationTheory flow ∧
      HasAdjointHeatKernelConstruction flow ∧
      HasPerelmanConjugateHeatKernelEstimates flow ∧
      HasPerelmanWFunctionalSetup flow ∧
      HasPerelmanEntropyGradientFormula flow ∧
      HasPerelmanEntropyFirstVariation flow ∧
      HasPerelmanEntropyMonotonicity flow ∧
      HasPerelmanEntropyLowerBoundPropagation flow ∧
      HasPerelmanEntropyFunctional flow ∧
      HasPerelmanReducedLengthFirstVariation flow ∧
      HasPerelmanReducedDistanceExistence flow ∧
      HasPerelmanReducedDistanceDifferentialInequality flow ∧
      HasPerelmanReducedDistanceEstimates flow ∧
      HasPerelmanReducedDistanceCutLocusControl flow ∧
      HasPerelmanReducedJacobianComparison flow ∧
      HasPerelmanReducedDistanceTheory flow ∧
      HasPerelmanReducedVolumeDefinition flow ∧
      HasPerelmanReducedVolumeDerivativeFormula flow ∧
      HasPerelmanReducedVolumeRigidity flow ∧
      HasPerelmanReducedVolumePositiveLowerBound flow ∧
      HasPerelmanReducedVolumeLimitRigidity flow ∧
      HasPerelmanReducedVolumeNonincreasing flow ∧
      HasPerelmanKappaNoncollapsingFromReducedVolume flow ∧
      HasPerelmanNoLocalCollapsingContradictionSetup flow ∧
      HasPerelmanCollapsedBallBlowup flow ∧
      HasPerelmanVolumeRatioContradiction flow ∧
      HasNoLocalCollapsingVolumeLowerBound flow ∧
      HasPerelmanKappaNoncollapsingQuantification flow ∧
      HasHamiltonCompactnessTheorem flow ∧
      HasAncientKappaSolutionLimitExtraction flow ∧
      HasKappaSolutionPointedRescaling flow ∧
      HasKappaSolutionCurvatureNormalization flow ∧
      HasKappaSolutionStructureTheory flow ∧
      HasKappaSolutionNonnegativeCurvatureOperator flow ∧
      HasKappaSolutionAsymptoticSoliton flow ∧
      HasAncientKappaSolutionCompactness flow ∧
      HasCanonicalNeighborhoodScaleControl flow ∧
      HasCanonicalNeighborhoodStability flow ∧
      HasCanonicalNeighborhoodPersistenceAcrossScales flow ∧
      HasCanonicalNeighborhoodNeckCapDichotomy flow ∧
      HasCanonicalNeighborhoodClassification flow ∧
      HasPerelmanNoLocalCollapsing flow ∧
      HasPerelmanReducedVolumeMonotonicity flow ∧
      HasCanonicalNeighborhoodTheorem flow ∧
      HasSingularityModelClassification flow ∧
      HasSingularityModelBlowupClassification flow ∧
      HasPerelmanSingularityControl (n := n) (M := M) flow) :=
  rfl

/--
Semantic alias for the Perelman monotonicity, blow-up, compactness, and
canonical-neighborhood payload before the aggregate singularity-control theorem.
-/
abbrev PerelmanMonotonicityBlowupSubobligationsPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) : Prop :=
  HasPerelmanFFunctionalSetup flow ∧
  HasPerelmanEntropyNormalization flow ∧
  HasPerelmanEntropyMinimizerExistence flow ∧
  HasPerelmanEntropyLogSobolevControl flow ∧
  HasConjugateHeatEquationTheory flow ∧
  HasAdjointHeatKernelConstruction flow ∧
  HasPerelmanConjugateHeatKernelEstimates flow ∧
  HasPerelmanWFunctionalSetup flow ∧
  HasPerelmanEntropyGradientFormula flow ∧
  HasPerelmanEntropyFirstVariation flow ∧
  HasPerelmanEntropyMonotonicity flow ∧
  HasPerelmanEntropyLowerBoundPropagation flow ∧
  HasPerelmanEntropyFunctional flow ∧
  HasPerelmanReducedLengthFirstVariation flow ∧
  HasPerelmanReducedDistanceExistence flow ∧
  HasPerelmanReducedDistanceDifferentialInequality flow ∧
  HasPerelmanReducedDistanceEstimates flow ∧
  HasPerelmanReducedDistanceCutLocusControl flow ∧
  HasPerelmanReducedJacobianComparison flow ∧
  HasPerelmanReducedDistanceTheory flow ∧
  HasPerelmanReducedVolumeDefinition flow ∧
  HasPerelmanReducedVolumeDerivativeFormula flow ∧
  HasPerelmanReducedVolumeRigidity flow ∧
  HasPerelmanReducedVolumePositiveLowerBound flow ∧
  HasPerelmanReducedVolumeLimitRigidity flow ∧
  HasPerelmanReducedVolumeNonincreasing flow ∧
  HasPerelmanKappaNoncollapsingFromReducedVolume flow ∧
  HasPerelmanNoLocalCollapsingContradictionSetup flow ∧
  HasPerelmanCollapsedBallBlowup flow ∧
  HasPerelmanVolumeRatioContradiction flow ∧
  HasNoLocalCollapsingVolumeLowerBound flow ∧
  HasPerelmanKappaNoncollapsingQuantification flow ∧
  HasHamiltonCompactnessTheorem flow ∧
  HasAncientKappaSolutionLimitExtraction flow ∧
  HasKappaSolutionPointedRescaling flow ∧
  HasKappaSolutionCurvatureNormalization flow ∧
  HasKappaSolutionStructureTheory flow ∧
  HasKappaSolutionNonnegativeCurvatureOperator flow ∧
  HasKappaSolutionAsymptoticSoliton flow ∧
  HasAncientKappaSolutionCompactness flow ∧
  HasCanonicalNeighborhoodScaleControl flow ∧
  HasCanonicalNeighborhoodStability flow ∧
  HasCanonicalNeighborhoodPersistenceAcrossScales flow ∧
  HasCanonicalNeighborhoodNeckCapDichotomy flow ∧
  HasCanonicalNeighborhoodClassification flow

/--
The Perelman monotonicity/blow-up sub-obligation payload alias is
definitionally the entropy, conjugate-heat, reduced-distance, reduced-volume,
noncollapsing, compactness, kappa-solution, and canonical-neighborhood witness
stack before aggregate singularity control.
-/
theorem perelmanMonotonicityBlowupSubobligationsPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M) :
    PerelmanMonotonicityBlowupSubobligationsPayload flow =
      (HasPerelmanFFunctionalSetup flow ∧
      HasPerelmanEntropyNormalization flow ∧
      HasPerelmanEntropyMinimizerExistence flow ∧
      HasPerelmanEntropyLogSobolevControl flow ∧
      HasConjugateHeatEquationTheory flow ∧
      HasAdjointHeatKernelConstruction flow ∧
      HasPerelmanConjugateHeatKernelEstimates flow ∧
      HasPerelmanWFunctionalSetup flow ∧
      HasPerelmanEntropyGradientFormula flow ∧
      HasPerelmanEntropyFirstVariation flow ∧
      HasPerelmanEntropyMonotonicity flow ∧
      HasPerelmanEntropyLowerBoundPropagation flow ∧
      HasPerelmanEntropyFunctional flow ∧
      HasPerelmanReducedLengthFirstVariation flow ∧
      HasPerelmanReducedDistanceExistence flow ∧
      HasPerelmanReducedDistanceDifferentialInequality flow ∧
      HasPerelmanReducedDistanceEstimates flow ∧
      HasPerelmanReducedDistanceCutLocusControl flow ∧
      HasPerelmanReducedJacobianComparison flow ∧
      HasPerelmanReducedDistanceTheory flow ∧
      HasPerelmanReducedVolumeDefinition flow ∧
      HasPerelmanReducedVolumeDerivativeFormula flow ∧
      HasPerelmanReducedVolumeRigidity flow ∧
      HasPerelmanReducedVolumePositiveLowerBound flow ∧
      HasPerelmanReducedVolumeLimitRigidity flow ∧
      HasPerelmanReducedVolumeNonincreasing flow ∧
      HasPerelmanKappaNoncollapsingFromReducedVolume flow ∧
      HasPerelmanNoLocalCollapsingContradictionSetup flow ∧
      HasPerelmanCollapsedBallBlowup flow ∧
      HasPerelmanVolumeRatioContradiction flow ∧
      HasNoLocalCollapsingVolumeLowerBound flow ∧
      HasPerelmanKappaNoncollapsingQuantification flow ∧
      HasHamiltonCompactnessTheorem flow ∧
      HasAncientKappaSolutionLimitExtraction flow ∧
      HasKappaSolutionPointedRescaling flow ∧
      HasKappaSolutionCurvatureNormalization flow ∧
      HasKappaSolutionStructureTheory flow ∧
      HasKappaSolutionNonnegativeCurvatureOperator flow ∧
      HasKappaSolutionAsymptoticSoliton flow ∧
      HasAncientKappaSolutionCompactness flow ∧
      HasCanonicalNeighborhoodScaleControl flow ∧
      HasCanonicalNeighborhoodStability flow ∧
      HasCanonicalNeighborhoodPersistenceAcrossScales flow ∧
      HasCanonicalNeighborhoodNeckCapDichotomy flow ∧
      HasCanonicalNeighborhoodClassification flow) :=
  rfl

/--
The theorem-shaped Perelman statement exposes the complete named
sub-obligation stack used by dependency projections.
-/
theorem perelman_subobligations_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    PerelmanSingularityControlSubobligationsPayload flow := by
  rcases statement with
    ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
      entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
      conjugateHeatKernelEstimates, wFunctionalSetup, entropyGradientFormula,
      entropyFirstVariation, entropyMonotonicity, entropyLowerBoundPropagation,
      entropyFunctional, reducedLengthFirstVariation, reducedDistanceExistence,
      reducedDistanceDifferentialInequality, reducedDistanceEstimates,
      reducedDistanceCutLocusControl, reducedJacobianComparison,
      reducedDistance, reducedVolumeDefinition, reducedVolumeDerivativeFormula,
      reducedVolumeRigidity, reducedVolumePositiveLowerBound,
      reducedVolumeLimitRigidity, reducedVolumeNonincreasing,
      kappaNoncollapsingFromReducedVolume,
      noLocalCollapsingContradictionSetup, collapsedBallBlowup,
      volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
      kappaNoncollapsing, hamiltonCompactness,
      ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
      kappaSolutionCurvatureNormalization, kappaSolutionStructure,
      kappaSolutionNonnegativeCurvatureOperator, kappaSolutionAsymptoticSoliton,
      ancientKappaSolutionCompactness, canonicalNeighborhoodScaleControl,
      canonicalNeighborhoodStability,
      canonicalNeighborhoodPersistenceAcrossScales,
      canonicalNeighborhoodNeckCapDichotomy, canonicalNeighborhoodClassification,
      noLocalCollapsing, reducedVolume, canonicalNeighborhood,
      singularityModelClassification, singularityModelBlowupClassification,
      control⟩
  exact ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
    entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
    conjugateHeatKernelEstimates, wFunctionalSetup, entropyGradientFormula,
    entropyFirstVariation, entropyMonotonicity, entropyLowerBoundPropagation,
    entropyFunctional, reducedLengthFirstVariation, reducedDistanceExistence,
    reducedDistanceDifferentialInequality, reducedDistanceEstimates,
    reducedDistanceCutLocusControl, reducedJacobianComparison, reducedDistance,
    reducedVolumeDefinition, reducedVolumeDerivativeFormula,
    reducedVolumeRigidity, reducedVolumePositiveLowerBound,
    reducedVolumeLimitRigidity, reducedVolumeNonincreasing,
    kappaNoncollapsingFromReducedVolume,
    noLocalCollapsingContradictionSetup, collapsedBallBlowup,
    volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
    kappaNoncollapsing, hamiltonCompactness,
    ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
    kappaSolutionCurvatureNormalization, kappaSolutionStructure,
    kappaSolutionNonnegativeCurvatureOperator, kappaSolutionAsymptoticSoliton,
    ancientKappaSolutionCompactness, canonicalNeighborhoodScaleControl,
    canonicalNeighborhoodStability,
    canonicalNeighborhoodPersistenceAcrossScales,
    canonicalNeighborhoodNeckCapDichotomy, canonicalNeighborhoodClassification,
    noLocalCollapsing, reducedVolume, canonicalNeighborhood,
    singularityModelClassification, singularityModelBlowupClassification,
    control⟩

/--
The Perelman statement bridge exposes exactly the full entropy,
conjugate-heat, reduced-distance, reduced-volume, noncollapsing,
kappa-solution, canonical-neighborhood, singularity-model, and aggregate
sub-obligation stack stored in the theorem-shaped Perelman statement.
-/
theorem perelman_subobligations_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    perelman_subobligations_of_statement statement =
      (by
        rcases statement with
          ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
            entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
            conjugateHeatKernelEstimates, wFunctionalSetup,
            entropyGradientFormula, entropyFirstVariation, entropyMonotonicity,
            entropyLowerBoundPropagation, entropyFunctional,
            reducedLengthFirstVariation, reducedDistanceExistence,
            reducedDistanceDifferentialInequality, reducedDistanceEstimates,
            reducedDistanceCutLocusControl, reducedJacobianComparison,
            reducedDistance, reducedVolumeDefinition,
            reducedVolumeDerivativeFormula, reducedVolumeRigidity,
            reducedVolumePositiveLowerBound, reducedVolumeLimitRigidity,
            reducedVolumeNonincreasing, kappaNoncollapsingFromReducedVolume,
            noLocalCollapsingContradictionSetup, collapsedBallBlowup,
            volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
            kappaNoncollapsing, hamiltonCompactness,
            ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
            kappaSolutionCurvatureNormalization, kappaSolutionStructure,
            kappaSolutionNonnegativeCurvatureOperator,
            kappaSolutionAsymptoticSoliton, ancientKappaSolutionCompactness,
            canonicalNeighborhoodScaleControl, canonicalNeighborhoodStability,
            canonicalNeighborhoodPersistenceAcrossScales,
            canonicalNeighborhoodNeckCapDichotomy,
            canonicalNeighborhoodClassification, noLocalCollapsing,
            reducedVolume, canonicalNeighborhood, singularityModelClassification,
            singularityModelBlowupClassification, control⟩
        exact ⟨fFunctionalSetup, entropyNormalization,
          entropyMinimizerExistence, entropyLogSobolevControl,
          conjugateHeatEquation, adjointHeatKernel,
          conjugateHeatKernelEstimates, wFunctionalSetup,
          entropyGradientFormula, entropyFirstVariation, entropyMonotonicity,
          entropyLowerBoundPropagation, entropyFunctional,
          reducedLengthFirstVariation, reducedDistanceExistence,
          reducedDistanceDifferentialInequality, reducedDistanceEstimates,
          reducedDistanceCutLocusControl, reducedJacobianComparison,
          reducedDistance, reducedVolumeDefinition,
          reducedVolumeDerivativeFormula, reducedVolumeRigidity,
          reducedVolumePositiveLowerBound, reducedVolumeLimitRigidity,
          reducedVolumeNonincreasing, kappaNoncollapsingFromReducedVolume,
          noLocalCollapsingContradictionSetup, collapsedBallBlowup,
          volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
          kappaNoncollapsing, hamiltonCompactness,
          ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
          kappaSolutionCurvatureNormalization, kappaSolutionStructure,
          kappaSolutionNonnegativeCurvatureOperator,
          kappaSolutionAsymptoticSoliton, ancientKappaSolutionCompactness,
          canonicalNeighborhoodScaleControl, canonicalNeighborhoodStability,
          canonicalNeighborhoodPersistenceAcrossScales,
          canonicalNeighborhoodNeckCapDichotomy,
          canonicalNeighborhoodClassification, noLocalCollapsing,
          reducedVolume, canonicalNeighborhood, singularityModelClassification,
          singularityModelBlowupClassification, control⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped Perelman statement exposes the monotonicity, blow-up, and
canonical-neighborhood inputs used before the aggregate theorem.
-/
theorem perelman_monotonicity_blowup_subobligations_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    PerelmanMonotonicityBlowupSubobligationsPayload flow := by
  rcases statement with
    ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
      entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
      conjugateHeatKernelEstimates, wFunctionalSetup, entropyGradientFormula,
      entropyFirstVariation, entropyMonotonicity, entropyLowerBoundPropagation,
      entropyFunctional, reducedLengthFirstVariation, reducedDistanceExistence,
      reducedDistanceDifferentialInequality, reducedDistanceEstimates,
      reducedDistanceCutLocusControl, reducedJacobianComparison,
      reducedDistance, reducedVolumeDefinition, reducedVolumeDerivativeFormula,
      reducedVolumeRigidity, reducedVolumePositiveLowerBound,
      reducedVolumeLimitRigidity, reducedVolumeNonincreasing,
      kappaNoncollapsingFromReducedVolume,
      noLocalCollapsingContradictionSetup, collapsedBallBlowup,
      volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
      kappaNoncollapsing, hamiltonCompactness,
      ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
      kappaSolutionCurvatureNormalization, kappaSolutionStructure,
      kappaSolutionNonnegativeCurvatureOperator, kappaSolutionAsymptoticSoliton,
      ancientKappaSolutionCompactness, canonicalNeighborhoodScaleControl,
      canonicalNeighborhoodStability,
      canonicalNeighborhoodPersistenceAcrossScales,
      canonicalNeighborhoodNeckCapDichotomy, canonicalNeighborhoodClassification,
      _noLocalCollapsing, _reducedVolume, _canonicalNeighborhood,
      _singularityModelClassification, _singularityModelBlowupClassification,
      _control⟩
  exact ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
    entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
    conjugateHeatKernelEstimates, wFunctionalSetup, entropyGradientFormula,
    entropyFirstVariation, entropyMonotonicity, entropyLowerBoundPropagation,
    entropyFunctional, reducedLengthFirstVariation, reducedDistanceExistence,
    reducedDistanceDifferentialInequality, reducedDistanceEstimates,
    reducedDistanceCutLocusControl, reducedJacobianComparison, reducedDistance,
    reducedVolumeDefinition, reducedVolumeDerivativeFormula,
    reducedVolumeRigidity, reducedVolumePositiveLowerBound,
    reducedVolumeLimitRigidity, reducedVolumeNonincreasing,
    kappaNoncollapsingFromReducedVolume,
    noLocalCollapsingContradictionSetup, collapsedBallBlowup,
    volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
    kappaNoncollapsing, hamiltonCompactness,
    ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
    kappaSolutionCurvatureNormalization, kappaSolutionStructure,
    kappaSolutionNonnegativeCurvatureOperator, kappaSolutionAsymptoticSoliton,
    ancientKappaSolutionCompactness, canonicalNeighborhoodScaleControl,
    canonicalNeighborhoodStability,
    canonicalNeighborhoodPersistenceAcrossScales,
    canonicalNeighborhoodNeckCapDichotomy, canonicalNeighborhoodClassification⟩

/--
The Perelman monotonicity/blow-up statement bridge exposes exactly the
entropy, conjugate-heat, reduced-distance, reduced-volume, noncollapsing,
kappa-solution compactness, and canonical-neighborhood inputs stored before the
aggregate singularity-control witness.
-/
theorem perelman_monotonicity_blowup_subobligations_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (statement : PerelmanSingularityControlStatement flow) :
    perelman_monotonicity_blowup_subobligations_of_statement statement =
      (by
        rcases statement with
          ⟨fFunctionalSetup, entropyNormalization, entropyMinimizerExistence,
            entropyLogSobolevControl, conjugateHeatEquation, adjointHeatKernel,
            conjugateHeatKernelEstimates, wFunctionalSetup,
            entropyGradientFormula, entropyFirstVariation, entropyMonotonicity,
            entropyLowerBoundPropagation, entropyFunctional,
            reducedLengthFirstVariation, reducedDistanceExistence,
            reducedDistanceDifferentialInequality, reducedDistanceEstimates,
            reducedDistanceCutLocusControl, reducedJacobianComparison,
            reducedDistance, reducedVolumeDefinition,
            reducedVolumeDerivativeFormula, reducedVolumeRigidity,
            reducedVolumePositiveLowerBound, reducedVolumeLimitRigidity,
            reducedVolumeNonincreasing, kappaNoncollapsingFromReducedVolume,
            noLocalCollapsingContradictionSetup, collapsedBallBlowup,
            volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
            kappaNoncollapsing, hamiltonCompactness,
            ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
            kappaSolutionCurvatureNormalization, kappaSolutionStructure,
            kappaSolutionNonnegativeCurvatureOperator,
            kappaSolutionAsymptoticSoliton, ancientKappaSolutionCompactness,
            canonicalNeighborhoodScaleControl, canonicalNeighborhoodStability,
            canonicalNeighborhoodPersistenceAcrossScales,
            canonicalNeighborhoodNeckCapDichotomy,
            canonicalNeighborhoodClassification, _noLocalCollapsing,
            _reducedVolume, _canonicalNeighborhood,
            _singularityModelClassification,
            _singularityModelBlowupClassification, _control⟩
        exact ⟨fFunctionalSetup, entropyNormalization,
          entropyMinimizerExistence, entropyLogSobolevControl,
          conjugateHeatEquation, adjointHeatKernel,
          conjugateHeatKernelEstimates, wFunctionalSetup,
          entropyGradientFormula, entropyFirstVariation, entropyMonotonicity,
          entropyLowerBoundPropagation, entropyFunctional,
          reducedLengthFirstVariation, reducedDistanceExistence,
          reducedDistanceDifferentialInequality, reducedDistanceEstimates,
          reducedDistanceCutLocusControl, reducedJacobianComparison,
          reducedDistance, reducedVolumeDefinition,
          reducedVolumeDerivativeFormula, reducedVolumeRigidity,
          reducedVolumePositiveLowerBound, reducedVolumeLimitRigidity,
          reducedVolumeNonincreasing, kappaNoncollapsingFromReducedVolume,
          noLocalCollapsingContradictionSetup, collapsedBallBlowup,
          volumeRatioContradiction, noLocalCollapsingVolumeLowerBound,
          kappaNoncollapsing, hamiltonCompactness,
          ancientKappaSolutionLimitExtraction, kappaSolutionPointedRescaling,
          kappaSolutionCurvatureNormalization, kappaSolutionStructure,
          kappaSolutionNonnegativeCurvatureOperator,
          kappaSolutionAsymptoticSoliton, ancientKappaSolutionCompactness,
          canonicalNeighborhoodScaleControl, canonicalNeighborhoodStability,
          canonicalNeighborhoodPersistenceAcrossScales,
          canonicalNeighborhoodNeckCapDichotomy,
          canonicalNeighborhoodClassification⟩) := by
  apply Subsingleton.elim

/--
A completed Perelman package exposes the theorem-shaped singularity-control
statement, the full statement-mediated sub-obligation payload, the
monotonicity/blow-up payload, and the aggregate singularity-control witness
together.
-/
theorem perelman_control_payload_of_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    ∃ _statement : PerelmanSingularityControlStatement flow,
    ∃ _subobligations : PerelmanSingularityControlSubobligationsPayload flow,
    ∃ _monotonicityBlowupSubobligations :
      PerelmanMonotonicityBlowupSubobligationsPayload flow,
      HasPerelmanSingularityControl (n := n) (M := M) flow := by
  let statement := perelman_singularity_control_statement_of_package package
  let subobligations := perelman_subobligations_of_statement statement
  let monotonicityBlowupSubobligations :=
    perelman_monotonicity_blowup_subobligations_of_statement statement
  exact ⟨statement, subobligations, monotonicityBlowupSubobligations,
    perelman_singularity_control_of_statement statement⟩

/--
The completed Perelman package payload is exactly the named package statement,
its statement-mediated sub-obligation payloads, and the aggregate
singularity-control witness extracted from that statement.
-/
theorem perelman_control_payload_of_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    perelman_control_payload_of_package package =
      (by
        let statement := perelman_singularity_control_statement_of_package package
        let subobligations := perelman_subobligations_of_statement statement
        let monotonicityBlowupSubobligations :=
          perelman_monotonicity_blowup_subobligations_of_statement statement
        exact ⟨statement, subobligations, monotonicityBlowupSubobligations,
          perelman_singularity_control_of_statement statement⟩) := by
  apply Subsingleton.elim

/--
A completed Perelman package directly exposes the full named singularity-control
sub-obligation payload through its theorem-shaped statement.
-/
theorem perelman_subobligations_of_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    PerelmanSingularityControlSubobligationsPayload flow :=
  perelman_subobligations_of_statement
    (perelman_singularity_control_statement_of_package package)

/--
The package-level full Perelman sub-obligation bridge is exactly the statement
bridge applied to the package's theorem-shaped singularity-control statement.
-/
theorem perelman_subobligations_of_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    perelman_subobligations_of_package package =
      perelman_subobligations_of_statement
        (perelman_singularity_control_statement_of_package package) := by
  apply Subsingleton.elim

/--
A completed Perelman package directly exposes the monotonicity, blow-up,
compactness, and canonical-neighborhood sub-obligation payload.
-/
theorem perelman_monotonicity_blowup_subobligations_of_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    PerelmanMonotonicityBlowupSubobligationsPayload flow :=
  perelman_monotonicity_blowup_subobligations_of_statement
    (perelman_singularity_control_statement_of_package package)

/--
The package-level Perelman monotonicity/blow-up bridge is exactly the statement
bridge applied to the package's theorem-shaped singularity-control statement.
-/
theorem perelman_monotonicity_blowup_subobligations_of_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    perelman_monotonicity_blowup_subobligations_of_package package =
      perelman_monotonicity_blowup_subobligations_of_statement
        (perelman_singularity_control_statement_of_package package) := by
  apply Subsingleton.elim

/-- Project F-functional setup evidence from a Perelman control package. -/
theorem f_functional_setup_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanFFunctionalSetup flow :=
  package.fFunctionalSetup

/-- Project entropy normalization evidence from a Perelman control package. -/
theorem entropy_normalization_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyNormalization flow :=
  package.entropyNormalization

/-- Project entropy-minimizer existence from a Perelman control package. -/
theorem entropy_minimizer_existence_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyMinimizerExistence flow :=
  package.entropyMinimizerExistence

/-- Project entropy log-Sobolev control from a Perelman control package. -/
theorem entropy_log_sobolev_control_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyLogSobolevControl flow :=
  package.entropyLogSobolevControl

/-- Project conjugate heat equation theory from a Perelman control package. -/
theorem conjugate_heat_equation_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasConjugateHeatEquationTheory flow :=
  package.conjugateHeatEquation

/-- Project adjoint heat kernel construction from a Perelman control package. -/
theorem adjoint_heat_kernel_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasAdjointHeatKernelConstruction flow :=
  package.adjointHeatKernel

/-- Project conjugate heat-kernel estimates from a Perelman control package. -/
theorem conjugate_heat_kernel_estimates_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanConjugateHeatKernelEstimates flow :=
  package.conjugateHeatKernelEstimates

/-- Project W-functional setup evidence from a Perelman control package. -/
theorem w_functional_setup_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanWFunctionalSetup flow :=
  package.wFunctionalSetup

/-- Project entropy-gradient formula evidence from a Perelman control package. -/
theorem entropy_gradient_formula_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyGradientFormula flow :=
  package.entropyGradientFormula

/-- Project entropy first-variation evidence from a Perelman control package. -/
theorem entropy_first_variation_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyFirstVariation flow :=
  package.entropyFirstVariation

/-- Project entropy monotonicity evidence from a Perelman control package. -/
theorem entropy_monotonicity_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyMonotonicity flow :=
  package.entropyMonotonicity

/-- Project entropy lower-bound propagation from a Perelman control package. -/
theorem entropy_lower_bound_propagation_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyLowerBoundPropagation flow :=
  package.entropyLowerBoundPropagation

/-- Project entropy-functional evidence from a Perelman control package. -/
theorem entropy_functional_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanEntropyFunctional flow :=
  package.entropyFunctional

/-- Project reduced-length first variation from a Perelman control package. -/
theorem reduced_length_first_variation_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedLengthFirstVariation flow :=
  package.reducedLengthFirstVariation

/-- Project reduced-distance existence evidence from a Perelman control package. -/
theorem reduced_distance_existence_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedDistanceExistence flow :=
  package.reducedDistanceExistence

/-- Project reduced-distance differential inequality from a Perelman package. -/
theorem reduced_distance_differential_inequality_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedDistanceDifferentialInequality flow :=
  package.reducedDistanceDifferentialInequality

/-- Project reduced-distance estimates from a Perelman control package. -/
theorem reduced_distance_estimates_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedDistanceEstimates flow :=
  package.reducedDistanceEstimates

/-- Project reduced-distance cut-locus control from a Perelman package. -/
theorem reduced_distance_cut_locus_control_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedDistanceCutLocusControl flow :=
  package.reducedDistanceCutLocusControl

/-- Project reduced-Jacobian comparison from a Perelman package. -/
theorem reduced_jacobian_comparison_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedJacobianComparison flow :=
  package.reducedJacobianComparison

/-- Project reduced-distance evidence from a Perelman control package. -/
theorem reduced_distance_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedDistanceTheory flow :=
  package.reducedDistance

/-- Project reduced-volume definition evidence from a Perelman control package. -/
theorem reduced_volume_definition_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeDefinition flow :=
  package.reducedVolumeDefinition

/-- Project the reduced-volume derivative formula from a Perelman package. -/
theorem reduced_volume_derivative_formula_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeDerivativeFormula flow :=
  package.reducedVolumeDerivativeFormula

/-- Project reduced-volume rigidity evidence from a Perelman control package. -/
theorem reduced_volume_rigidity_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeRigidity flow :=
  package.reducedVolumeRigidity

/-- Project reduced-volume positive lower bounds from a Perelman package. -/
theorem reduced_volume_positive_lower_bound_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumePositiveLowerBound flow :=
  package.reducedVolumePositiveLowerBound

/-- Project reduced-volume limit rigidity from a Perelman package. -/
theorem reduced_volume_limit_rigidity_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeLimitRigidity flow :=
  package.reducedVolumeLimitRigidity

/-- Project reduced-volume nonincreasing evidence from a Perelman package. -/
theorem reduced_volume_nonincreasing_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeNonincreasing flow :=
  package.reducedVolumeNonincreasing

/-- Project reduced-volume-to-kappa evidence from a Perelman package. -/
theorem kappa_noncollapsing_from_reduced_volume_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanKappaNoncollapsingFromReducedVolume flow :=
  package.kappaNoncollapsingFromReducedVolume

/-- Project no-local-collapsing contradiction setup from a Perelman package. -/
theorem no_local_collapsing_contradiction_setup_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanNoLocalCollapsingContradictionSetup flow :=
  package.noLocalCollapsingContradictionSetup

/-- Project collapsed-ball blow-up evidence from a Perelman package. -/
theorem collapsed_ball_blowup_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanCollapsedBallBlowup flow :=
  package.collapsedBallBlowup

/-- Project volume-ratio contradiction evidence from a Perelman package. -/
theorem volume_ratio_contradiction_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanVolumeRatioContradiction flow :=
  package.volumeRatioContradiction

/-- Project the no-local-collapsing volume lower bound from a package. -/
theorem no_local_collapsing_volume_lower_bound_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasNoLocalCollapsingVolumeLowerBound flow :=
  package.noLocalCollapsingVolumeLowerBound

/-- Project quantified kappa-noncollapsing evidence from a Perelman package. -/
theorem kappa_noncollapsing_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanKappaNoncollapsingQuantification flow :=
  package.kappaNoncollapsing

/-- Project Hamilton compactness from a Perelman package. -/
theorem hamilton_compactness_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasHamiltonCompactnessTheorem flow :=
  package.hamiltonCompactness

/-- Project ancient-kappa limit-extraction evidence from a Perelman package. -/
theorem ancient_kappa_solution_limit_extraction_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasAncientKappaSolutionLimitExtraction flow :=
  package.ancientKappaSolutionLimitExtraction

/-- Project pointed-rescaling evidence from a Perelman package. -/
theorem kappa_solution_pointed_rescaling_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasKappaSolutionPointedRescaling flow :=
  package.kappaSolutionPointedRescaling

/-- Project kappa-solution curvature normalization from a Perelman package. -/
theorem kappa_solution_curvature_normalization_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasKappaSolutionCurvatureNormalization flow :=
  package.kappaSolutionCurvatureNormalization

/-- Project kappa-solution structure theory from a Perelman package. -/
theorem kappa_solution_structure_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasKappaSolutionStructureTheory flow :=
  package.kappaSolutionStructure

/-- Project nonnegative curvature-operator evidence from a Perelman package. -/
theorem kappa_solution_nonnegative_curvature_operator_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasKappaSolutionNonnegativeCurvatureOperator flow :=
  package.kappaSolutionNonnegativeCurvatureOperator

/-- Project asymptotic soliton analysis from a Perelman package. -/
theorem kappa_solution_asymptotic_soliton_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasKappaSolutionAsymptoticSoliton flow :=
  package.kappaSolutionAsymptoticSoliton

/-- Project ancient-kappa-solution compactness evidence from a Perelman package. -/
theorem ancient_kappa_solution_compactness_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasAncientKappaSolutionCompactness flow :=
  package.ancientKappaSolutionCompactness

/-- Project canonical-neighborhood scale control from a Perelman package. -/
theorem canonical_neighborhood_scale_control_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodScaleControl flow :=
  package.canonicalNeighborhoodScaleControl

/-- Project canonical-neighborhood stability from a Perelman package. -/
theorem canonical_neighborhood_stability_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodStability flow :=
  package.canonicalNeighborhoodStability

/-- Project cross-scale canonical-neighborhood persistence from a Perelman package. -/
theorem canonical_neighborhood_persistence_across_scales_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodPersistenceAcrossScales flow :=
  package.canonicalNeighborhoodPersistenceAcrossScales

/-- Project the neck/cap dichotomy from a Perelman package. -/
theorem canonical_neighborhood_neck_cap_dichotomy_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodNeckCapDichotomy flow :=
  package.canonicalNeighborhoodNeckCapDichotomy

/-- Project canonical-neighborhood classification evidence from a package. -/
theorem canonical_neighborhood_classification_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodClassification flow :=
  package.canonicalNeighborhoodClassification

/-- Project no-local-collapsing evidence from a Perelman control package. -/
theorem no_local_collapsing_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanNoLocalCollapsing flow :=
  package.noLocalCollapsing

/-- Project reduced-volume evidence from a Perelman control package. -/
theorem reduced_volume_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanReducedVolumeMonotonicity flow :=
  package.reducedVolume

/-- Project canonical-neighborhood evidence from a Perelman control package. -/
theorem canonical_neighborhood_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasCanonicalNeighborhoodTheorem flow :=
  package.canonicalNeighborhood

/-- Project singularity-model classification evidence from a Perelman package. -/
theorem singularity_model_classification_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasSingularityModelClassification flow :=
  package.singularityModelClassification

/-- Project blow-up classification of singularity models from a package. -/
theorem singularity_model_blowup_classification_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasSingularityModelBlowupClassification flow :=
  package.singularityModelBlowupClassification

/-- Project aggregate singularity-control evidence from a Perelman package. -/
theorem singularity_control_of_perelman_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    (package : PerelmanSingularityControlPackage flow) :
    HasPerelmanSingularityControl flow :=
  package.control

section PerelmanPackageProjectionEqualities

variable {n : ℕ∞ω}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeManifoldModel M]
variable [IsManifold ThreeManifoldModelWithCorners 1 M]
variable {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
variable (package : PerelmanSingularityControlPackage flow)

/-- The named F-functional projection is the stored Perelman package field. -/
theorem f_functional_setup_of_perelman_package_eq :
    f_functional_setup_of_perelman_package package =
      package.fFunctionalSetup :=
  rfl

/-- The named entropy-normalization projection is the stored Perelman package field. -/
theorem entropy_normalization_of_perelman_package_eq :
    entropy_normalization_of_perelman_package package =
      package.entropyNormalization :=
  rfl

/-- The named entropy-minimizer projection is the stored Perelman package field. -/
theorem entropy_minimizer_existence_of_perelman_package_eq :
    entropy_minimizer_existence_of_perelman_package package =
      package.entropyMinimizerExistence :=
  rfl

/-- The named entropy log-Sobolev projection is the stored Perelman package field. -/
theorem entropy_log_sobolev_control_of_perelman_package_eq :
    entropy_log_sobolev_control_of_perelman_package package =
      package.entropyLogSobolevControl :=
  rfl

/-- The named conjugate-heat-equation projection is the stored Perelman package field. -/
theorem conjugate_heat_equation_of_perelman_package_eq :
    conjugate_heat_equation_of_perelman_package package =
      package.conjugateHeatEquation :=
  rfl

/-- The named adjoint-heat-kernel projection is the stored Perelman package field. -/
theorem adjoint_heat_kernel_of_perelman_package_eq :
    adjoint_heat_kernel_of_perelman_package package =
      package.adjointHeatKernel :=
  rfl

/-- The named conjugate heat-kernel-estimates projection is the stored Perelman package field. -/
theorem conjugate_heat_kernel_estimates_of_perelman_package_eq :
    conjugate_heat_kernel_estimates_of_perelman_package package =
      package.conjugateHeatKernelEstimates :=
  rfl

/-- The named W-functional projection is the stored Perelman package field. -/
theorem w_functional_setup_of_perelman_package_eq :
    w_functional_setup_of_perelman_package package =
      package.wFunctionalSetup :=
  rfl

/-- The named entropy-gradient projection is the stored Perelman package field. -/
theorem entropy_gradient_formula_of_perelman_package_eq :
    entropy_gradient_formula_of_perelman_package package =
      package.entropyGradientFormula :=
  rfl

/-- The named entropy first-variation projection is the stored Perelman package field. -/
theorem entropy_first_variation_of_perelman_package_eq :
    entropy_first_variation_of_perelman_package package =
      package.entropyFirstVariation :=
  rfl

/-- The named entropy-monotonicity projection is the stored Perelman package field. -/
theorem entropy_monotonicity_of_perelman_package_eq :
    entropy_monotonicity_of_perelman_package package =
      package.entropyMonotonicity :=
  rfl

/-- The named entropy lower-bound projection is the stored Perelman package field. -/
theorem entropy_lower_bound_propagation_of_perelman_package_eq :
    entropy_lower_bound_propagation_of_perelman_package package =
      package.entropyLowerBoundPropagation :=
  rfl

/-- The named entropy-functional projection is the stored Perelman package field. -/
theorem entropy_functional_of_perelman_package_eq :
    entropy_functional_of_perelman_package package =
      package.entropyFunctional :=
  rfl

/-- The named reduced-length first-variation projection is the stored Perelman package field. -/
theorem reduced_length_first_variation_of_perelman_package_eq :
    reduced_length_first_variation_of_perelman_package package =
      package.reducedLengthFirstVariation :=
  rfl

/-- The named reduced-distance existence projection is the stored Perelman package field. -/
theorem reduced_distance_existence_of_perelman_package_eq :
    reduced_distance_existence_of_perelman_package package =
      package.reducedDistanceExistence :=
  rfl

/-- The named reduced-distance differential-inequality projection is the stored field. -/
theorem reduced_distance_differential_inequality_of_perelman_package_eq :
    reduced_distance_differential_inequality_of_perelman_package package =
      package.reducedDistanceDifferentialInequality :=
  rfl

/-- The named reduced-distance estimates projection is the stored Perelman package field. -/
theorem reduced_distance_estimates_of_perelman_package_eq :
    reduced_distance_estimates_of_perelman_package package =
      package.reducedDistanceEstimates :=
  rfl

/-- The named reduced-distance cut-locus control projection is the stored field. -/
theorem reduced_distance_cut_locus_control_of_perelman_package_eq :
    reduced_distance_cut_locus_control_of_perelman_package package =
      package.reducedDistanceCutLocusControl :=
  rfl

/-- The named reduced-Jacobian comparison projection is the stored Perelman package field. -/
theorem reduced_jacobian_comparison_of_perelman_package_eq :
    reduced_jacobian_comparison_of_perelman_package package =
      package.reducedJacobianComparison :=
  rfl

/-- The named reduced-distance projection is the stored Perelman package field. -/
theorem reduced_distance_of_perelman_package_eq :
    reduced_distance_of_perelman_package package =
      package.reducedDistance :=
  rfl

/-- The named reduced-volume definition projection is the stored Perelman package field. -/
theorem reduced_volume_definition_of_perelman_package_eq :
    reduced_volume_definition_of_perelman_package package =
      package.reducedVolumeDefinition :=
  rfl

/-- The named reduced-volume derivative projection is the stored Perelman package field. -/
theorem reduced_volume_derivative_formula_of_perelman_package_eq :
    reduced_volume_derivative_formula_of_perelman_package package =
      package.reducedVolumeDerivativeFormula :=
  rfl

/-- The named reduced-volume rigidity projection is the stored Perelman package field. -/
theorem reduced_volume_rigidity_of_perelman_package_eq :
    reduced_volume_rigidity_of_perelman_package package =
      package.reducedVolumeRigidity :=
  rfl

/-- The named reduced-volume lower-bound projection is the stored Perelman package field. -/
theorem reduced_volume_positive_lower_bound_of_perelman_package_eq :
    reduced_volume_positive_lower_bound_of_perelman_package package =
      package.reducedVolumePositiveLowerBound :=
  rfl

/-- The named reduced-volume limit-rigidity projection is the stored package field. -/
theorem reduced_volume_limit_rigidity_of_perelman_package_eq :
    reduced_volume_limit_rigidity_of_perelman_package package =
      package.reducedVolumeLimitRigidity :=
  rfl

/-- The named reduced-volume nonincreasing projection is the stored Perelman package field. -/
theorem reduced_volume_nonincreasing_of_perelman_package_eq :
    reduced_volume_nonincreasing_of_perelman_package package =
      package.reducedVolumeNonincreasing :=
  rfl

/-- The named kappa-from-reduced-volume projection is the stored Perelman package field. -/
theorem kappa_noncollapsing_from_reduced_volume_of_perelman_package_eq :
    kappa_noncollapsing_from_reduced_volume_of_perelman_package package =
      package.kappaNoncollapsingFromReducedVolume :=
  rfl

/-- The named no-local-collapsing setup projection is the stored Perelman package field. -/
theorem no_local_collapsing_contradiction_setup_of_perelman_package_eq :
    no_local_collapsing_contradiction_setup_of_perelman_package package =
      package.noLocalCollapsingContradictionSetup :=
  rfl

/-- The named collapsed-ball blowup projection is the stored Perelman package field. -/
theorem collapsed_ball_blowup_of_perelman_package_eq :
    collapsed_ball_blowup_of_perelman_package package =
      package.collapsedBallBlowup :=
  rfl

/-- The named volume-ratio contradiction projection is the stored Perelman package field. -/
theorem volume_ratio_contradiction_of_perelman_package_eq :
    volume_ratio_contradiction_of_perelman_package package =
      package.volumeRatioContradiction :=
  rfl

/-- The named no-local-collapsing lower-bound projection is the stored package field. -/
theorem no_local_collapsing_volume_lower_bound_of_perelman_package_eq :
    no_local_collapsing_volume_lower_bound_of_perelman_package package =
      package.noLocalCollapsingVolumeLowerBound :=
  rfl

/-- The named kappa-noncollapsing projection is the stored Perelman package field. -/
theorem kappa_noncollapsing_of_perelman_package_eq :
    kappa_noncollapsing_of_perelman_package package =
      package.kappaNoncollapsing :=
  rfl

/-- The named Hamilton-compactness projection is the stored Perelman package field. -/
theorem hamilton_compactness_of_perelman_package_eq :
    hamilton_compactness_of_perelman_package package =
      package.hamiltonCompactness :=
  rfl

/-- The named ancient-kappa limit-extraction projection is the stored package field. -/
theorem ancient_kappa_solution_limit_extraction_of_perelman_package_eq :
    ancient_kappa_solution_limit_extraction_of_perelman_package package =
      package.ancientKappaSolutionLimitExtraction :=
  rfl

/-- The named kappa-solution rescaling projection is the stored Perelman package field. -/
theorem kappa_solution_pointed_rescaling_of_perelman_package_eq :
    kappa_solution_pointed_rescaling_of_perelman_package package =
      package.kappaSolutionPointedRescaling :=
  rfl

/-- The named kappa-solution normalization projection is the stored package field. -/
theorem kappa_solution_curvature_normalization_of_perelman_package_eq :
    kappa_solution_curvature_normalization_of_perelman_package package =
      package.kappaSolutionCurvatureNormalization :=
  rfl

/-- The named kappa-solution structure projection is the stored Perelman package field. -/
theorem kappa_solution_structure_of_perelman_package_eq :
    kappa_solution_structure_of_perelman_package package =
      package.kappaSolutionStructure :=
  rfl

/-- The named kappa-solution curvature-operator projection is the stored field. -/
theorem kappa_solution_nonnegative_curvature_operator_of_perelman_package_eq :
    kappa_solution_nonnegative_curvature_operator_of_perelman_package package =
      package.kappaSolutionNonnegativeCurvatureOperator :=
  rfl

/-- The named kappa-solution asymptotic-soliton projection is the stored field. -/
theorem kappa_solution_asymptotic_soliton_of_perelman_package_eq :
    kappa_solution_asymptotic_soliton_of_perelman_package package =
      package.kappaSolutionAsymptoticSoliton :=
  rfl

/-- The named ancient-kappa compactness projection is the stored Perelman package field. -/
theorem ancient_kappa_solution_compactness_of_perelman_package_eq :
    ancient_kappa_solution_compactness_of_perelman_package package =
      package.ancientKappaSolutionCompactness :=
  rfl

/-- The named canonical-neighborhood scale-control projection is the stored field. -/
theorem canonical_neighborhood_scale_control_of_perelman_package_eq :
    canonical_neighborhood_scale_control_of_perelman_package package =
      package.canonicalNeighborhoodScaleControl :=
  rfl

/-- The named canonical-neighborhood stability projection is the stored package field. -/
theorem canonical_neighborhood_stability_of_perelman_package_eq :
    canonical_neighborhood_stability_of_perelman_package package =
      package.canonicalNeighborhoodStability :=
  rfl

/-- The named cross-scale canonical-neighborhood projection is the stored field. -/
theorem canonical_neighborhood_persistence_across_scales_of_perelman_package_eq :
    canonical_neighborhood_persistence_across_scales_of_perelman_package
      package =
      package.canonicalNeighborhoodPersistenceAcrossScales :=
  rfl

/-- The named neck/cap dichotomy projection is the stored Perelman package field. -/
theorem canonical_neighborhood_neck_cap_dichotomy_of_perelman_package_eq :
    canonical_neighborhood_neck_cap_dichotomy_of_perelman_package package =
      package.canonicalNeighborhoodNeckCapDichotomy :=
  rfl

/-- The named canonical-neighborhood classification projection is the stored field. -/
theorem canonical_neighborhood_classification_of_perelman_package_eq :
    canonical_neighborhood_classification_of_perelman_package package =
      package.canonicalNeighborhoodClassification :=
  rfl

/-- The named no-local-collapsing projection is the stored Perelman package field. -/
theorem no_local_collapsing_of_perelman_package_eq :
    no_local_collapsing_of_perelman_package package =
      package.noLocalCollapsing :=
  rfl

/-- The named reduced-volume projection is the stored Perelman package field. -/
theorem reduced_volume_of_perelman_package_eq :
    reduced_volume_of_perelman_package package =
      package.reducedVolume :=
  rfl

/-- The named canonical-neighborhood projection is the stored Perelman package field. -/
theorem canonical_neighborhood_of_perelman_package_eq :
    canonical_neighborhood_of_perelman_package package =
      package.canonicalNeighborhood :=
  rfl

/-- The named singularity-model classification projection is the stored field. -/
theorem singularity_model_classification_of_perelman_package_eq :
    singularity_model_classification_of_perelman_package package =
      package.singularityModelClassification :=
  rfl

/-- The named singularity-model blowup classification projection is the stored field. -/
theorem singularity_model_blowup_classification_of_perelman_package_eq :
    singularity_model_blowup_classification_of_perelman_package package =
      package.singularityModelBlowupClassification :=
  rfl

/-- The named aggregate singularity-control projection is the stored package field. -/
theorem singularity_control_of_perelman_package_eq :
    singularity_control_of_perelman_package package =
      package.control :=
  rfl

end PerelmanPackageProjectionEqualities

/--
Interface for deriving finite extinction from Ricci flow with surgery and
Perelman singularity control.
-/
inductive HasFiniteExtinctionFundamentalGroupInput
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M] : Prop

/-- Interface for producing the sweepout family used by the width argument. -/
inductive HasFiniteExtinctionSweepoutExistence
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (_fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M) : Prop

/-- Interface for the parameter space used to index the finite-extinction sweepout. -/
inductive HasFiniteExtinctionSweepoutParameterSpace
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (_fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M) : Prop

/-- Interface for continuity/compactness of the sweepout family used by width. -/
inductive HasFiniteExtinctionSweepoutContinuity
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (_sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup) : Prop

/-- Interface for uniform area bounds on the finite-extinction sweepout family. -/
inductive HasFiniteExtinctionSweepoutAreaBound
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (_sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup) : Prop

/-- Interface for the nontrivial sweepout class that gives positive width. -/
inductive HasFiniteExtinctionSweepoutNontriviality
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
    [CompactSpace M]
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (_sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup) : Prop

/-- Interface for setting up the area functional on the sweepout class. -/
inductive HasFiniteExtinctionAreaFunctionalSetup
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (_sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup) : Prop

/-- Interface for defining the min-max width from the sweepout family. -/
inductive HasFiniteExtinctionMinMaxWidthDefinition
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (_sweepout : HasFiniteExtinctionSweepoutExistence M
      fundamentalGroup) : Prop

/-- Interface for compactness of width-minimizing sweepout sequences. -/
inductive HasFiniteExtinctionWidthCompactness
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for lower semicontinuity of width under limiting sweepouts. -/
inductive HasFiniteExtinctionWidthLowerSemicontinuity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for extracting a minimizing sequence realizing the width. -/
inductive HasFiniteExtinctionMinimizingSequence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for the pull-tight argument in the finite-extinction min-max setup. -/
inductive HasFiniteExtinctionPullTightArgument
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for stationarity of the min-max limit realizing width. -/
inductive HasFiniteExtinctionMinMaxStationarity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for regularity of the min-max surfaces realizing width. -/
inductive HasFiniteExtinctionMinSurfaceRegularity
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for positivity/nontriviality of the width before extinction. -/
inductive HasFiniteExtinctionPositiveWidth
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (fundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout : HasFiniteExtinctionSweepoutExistence M fundamentalGroup)
    (_widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition flow surgery control
        fundamentalGroup sweepout) : Prop

/-- Interface for the min-max or width theory used in finite extinction. -/
inductive HasFiniteExtinctionWidthTheory
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (_surgery : HasRicciFlowWithSurgery n M)
    (_control : HasPerelmanSingularityControl (n := n) (M := M) flow) : Prop

/-- Interface for the first-variation formula for the width-realizing surfaces. -/
inductive HasFiniteExtinctionFirstVariationFormula
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the second-variation/stability inequality in the width argument. -/
inductive HasFiniteExtinctionSecondVariationInequality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the Gauss-Bonnet estimate used in the width derivative bound. -/
inductive HasFiniteExtinctionGaussBonnetEstimate
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the scalar-curvature contribution to the width bound. -/
inductive HasFiniteExtinctionScalarCurvatureWidthBound
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the differential/monotonicity inequality controlling width. -/
inductive HasFiniteExtinctionWidthEvolution
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the width differential inequality along the smooth flow pieces. -/
inductive HasFiniteExtinctionWidthDifferentialInequality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_widthTheory : HasFiniteExtinctionWidthTheory flow surgery control) : Prop

/-- Interface for the width drop/nonincrease across surgery times. -/
inductive HasFiniteExtinctionSurgeryWidthDrop
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (_widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory) : Prop

/-- Interface for comparing the metric across a surgery time in the width argument. -/
inductive HasFiniteExtinctionSurgeryMetricComparison
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (_widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory) : Prop

/-- Interface for pushing sweepouts through the surgery metric comparison map. -/
inductive HasFiniteExtinctionSurgeryWidthComparisonMap
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (_widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory) : Prop

/-- Interface for showing surgery and discarded components preserve the width argument. -/
inductive HasFiniteExtinctionSurgeryDiscardControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (_widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory) : Prop

/-- Interface for proving discarded components do not carry the target sweepout width. -/
inductive HasFiniteExtinctionDiscardedComponentWidthNeutrality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (_discardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution) : Prop

/-- Interface for proving discarded components carry only trivial sweepout classes. -/
inductive HasFiniteExtinctionDiscardedComponentSweepoutTriviality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (_discardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution) : Prop

/-- Interface for classifying discarded components in the finite-extinction argument. -/
inductive HasFiniteExtinctionDiscardedComponentClassification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (_discardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution) : Prop

/-- Interface for tracking the components that survive surgery before extinction. -/
inductive HasFiniteExtinctionSurvivingComponentTracking
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (_discardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution) : Prop

/-- Interface for topological control of components that survive before extinction. -/
inductive HasFiniteExtinctionComponentTopology
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (_discardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution) : Prop

inductive HasFiniteExtinctionDerivation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (_surgery : HasRicciFlowWithSurgery n M)
    (_control : HasPerelmanSingularityControl (n := n) (M := M) flow) : Prop

/-- Interface for the curvature pinching input used in finite extinction. -/
inductive HasFiniteExtinctionCurvaturePinching
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (_surgery : HasRicciFlowWithSurgery n M)
    (_control : HasPerelmanSingularityControl (n := n) (M := M) flow) : Prop

/-- Interface for preserving positive scalar curvature/pinching under the flow with surgery. -/
inductive HasFiniteExtinctionPositiveScalarCurvaturePersistence
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_pinching : HasFiniteExtinctionCurvaturePinching flow surgery control) : Prop

/-- Interface for extracting a scalar-curvature lower bound from pinching. -/
inductive HasFiniteExtinctionPositiveScalarCurvatureLowerBound
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_pinching : HasFiniteExtinctionCurvaturePinching flow surgery control) : Prop

/--
Interface for controlling the topological components that remain during the
finite-extinction argument.
-/
inductive HasFiniteExtinctionComponentControl
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (_pinching : HasFiniteExtinctionCurvaturePinching flow surgery control) : Prop

/-- Interface for the volume evolution formula along smooth flow intervals. -/
inductive HasFiniteExtinctionVolumeEvolutionFormula
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for nonincrease of volume through surgery and discarded components. -/
inductive HasFiniteExtinctionSurgeryVolumeNonincrease
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for the scalar-curvature differential inequality used in extinction. -/
inductive HasFiniteExtinctionScalarCurvatureDifferentialInequality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for the volume differential inequality behind finite extinction. -/
inductive HasFiniteExtinctionVolumeDifferentialInequality
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for the time-bound or volume-decay input in finite extinction. -/
inductive HasFiniteExtinctionTimeBound
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for the volume-decay estimate used to bound the extinction time. -/
inductive HasFiniteExtinctionVolumeDecayEstimate
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (_componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching) : Prop

/-- Interface for integrating the decay estimate to obtain finite-time extinction. -/
inductive HasFiniteExtinctionFiniteTimeIntegration
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (_timeBound :
      HasFiniteExtinctionTimeBound flow surgery control pinching componentControl) : Prop

/-- Interface for summability of surgery-time losses in the extinction estimate. -/
inductive HasFiniteExtinctionSurgeryTimeSummability
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (_timeBound :
      HasFiniteExtinctionTimeBound flow surgery control pinching componentControl) : Prop

/-- Interface for the contradiction step forcing extinction before the time bound. -/
inductive HasFiniteExtinctionExtinctionTimeContradiction
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (_timeBound :
      HasFiniteExtinctionTimeBound flow surgery control pinching componentControl) : Prop

/-- Interface for integrating the volume/width differential inequality. -/
inductive HasFiniteExtinctionDifferentialInequalityIntegration
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (_timeBound :
      HasFiniteExtinctionTimeBound flow surgery control pinching componentControl) : Prop

/--
Interface certifying that the named finite-extinction sub-obligations derive the
projected finite-extinction conclusion.
-/
inductive HasFiniteExtinctionConclusionDerivation
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (timeBound :
      HasFiniteExtinctionTimeBound flow surgery control pinching componentControl)
    (_derivation : HasFiniteExtinctionDerivation flow surgery control)
    (_finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop

/--
The fixed-flow finite-extinction conclusion statement: the finite-extinction
proof is accompanied by the width, surgery-discard, curvature, time-bound,
derivation, and conclusion-derivation evidence that justifies it.
-/
def FiniteExtinctionConclusionStatement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M) : Prop :=
  ∃ finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
  ∃ _sweepout :
    HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup,
  ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
  ∃ widthEvolution :
    HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
  ∃ _surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      flow surgery control widthTheory widthEvolution,
  ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
  ∃ componentControl :
    HasFiniteExtinctionComponentControl flow surgery control pinching,
  ∃ timeBound :
    HasFiniteExtinctionTimeBound
      flow surgery control pinching componentControl,
  ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
    HasFiniteExtinctionConclusionDerivation
      flow surgery control pinching componentControl timeBound derivation
      finiteExtinction

/--
The fixed-flow finite-extinction conclusion statement is exactly the listed
fundamental-group, sweepout, width, surgery-discard, curvature, time-bound,
derivation, and conclusion-derivation witness stack.
-/
theorem finiteExtinctionConclusionStatement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M) :
    FiniteExtinctionConclusionStatement
        flow surgery control finiteExtinction =
      (∃ finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
      ∃ _sweepout :
        HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup,
      ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
      ∃ widthEvolution :
        HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
      ∃ _surgeryDiscardControl :
        HasFiniteExtinctionSurgeryDiscardControl
          flow surgery control widthTheory widthEvolution,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound
          flow surgery control pinching componentControl,
      ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
        HasFiniteExtinctionConclusionDerivation
          flow surgery control pinching componentControl timeBound derivation
          finiteExtinction) :=
  rfl

/--
The theorem-shaped finite-extinction input supplied by a completed surgery
package: it returns finite extinction together with the conclusion statement
that accounts for its proof components.
-/
def FiniteExtinctionStatement
    (n : ℕ∞ω)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] : Prop :=
  ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
  ∃ surgery : HasRicciFlowWithSurgery n M,
  ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
  ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
    FiniteExtinctionConclusionStatement
      flow surgery control finiteExtinction

/--
The theorem-shaped finite-extinction interface is exactly existence of a flow,
surgery construction, Perelman control, finite-extinction witness, and checked
finite-extinction conclusion statement.
-/
theorem finiteExtinctionStatement_eq
    (n : ℕ∞ω)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] :
    FiniteExtinctionStatement n M =
      (∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
      ∃ surgery : HasRicciFlowWithSurgery n M,
      ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
      ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
        FiniteExtinctionConclusionStatement
          flow surgery control finiteExtinction) :=
  rfl

/--
Assemble the fixed-flow finite-extinction conclusion statement from the named
finite-extinction components.
-/
theorem finite_extinction_conclusion_statement_of_components
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout :
      HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (timeBound :
      HasFiniteExtinctionTimeBound
        flow surgery control pinching componentControl)
    (derivation : HasFiniteExtinctionDerivation flow surgery control)
    (conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        flow surgery control pinching componentControl timeBound derivation
        finiteExtinction) :
    FiniteExtinctionConclusionStatement
      flow surgery control finiteExtinction :=
  ⟨finiteFundamentalGroup, sweepout, widthTheory, widthEvolution,
    surgeryDiscardControl, pinching, componentControl, timeBound,
    derivation, conclusionDerivation⟩

/--
The fixed-flow finite-extinction conclusion component assembler is exactly the
tuple of width, surgery-discard, curvature, time-bound, derivation, and
conclusion-derivation witnesses.
-/
theorem finite_extinction_conclusion_statement_of_components_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow)
    (finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M)
    (finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M)
    (sweepout :
      HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup)
    (widthTheory : HasFiniteExtinctionWidthTheory flow surgery control)
    (widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory)
    (surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution)
    (pinching : HasFiniteExtinctionCurvaturePinching flow surgery control)
    (componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching)
    (timeBound :
      HasFiniteExtinctionTimeBound
        flow surgery control pinching componentControl)
    (derivation : HasFiniteExtinctionDerivation flow surgery control)
    (conclusionDerivation :
      HasFiniteExtinctionConclusionDerivation
        flow surgery control pinching componentControl timeBound derivation
        finiteExtinction) :
    finite_extinction_conclusion_statement_of_components
        flow surgery control finiteExtinction finiteFundamentalGroup sweepout
        widthTheory widthEvolution surgeryDiscardControl pinching
        componentControl timeBound derivation conclusionDerivation =
      (by
        exact ⟨finiteFundamentalGroup, sweepout, widthTheory, widthEvolution,
          surgeryDiscardControl, pinching, componentControl, timeBound,
          derivation, conclusionDerivation⟩) := by
  apply Subsingleton.elim

/--
A package of future geometric-analysis inputs sufficient to produce finite
extinction for a smooth compact simply connected 3-manifold.
-/
structure FiniteExtinctionSurgeryPackage
    (n : ℕ∞ω)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  /-- Analytic Ricci-flow foundation before the surgery argument is applied. -/
  analyticFoundation :
    RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M
  /-- Existence and control package for the surgery construction. -/
  surgeryConstruction :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
  /-- Perelman's singularity-control package for the flow. -/
  perelmanControl :
    PerelmanSingularityControlPackage (n := n) (M := M)
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
  /-- Fundamental-group/topological input for the finite-extinction theorem. -/
  extinctionFundamentalGroupInput :
    HasFiniteExtinctionFundamentalGroupInput M
  /-- Sweepout family used by the finite-extinction width argument. -/
  extinctionSweepout :
    HasFiniteExtinctionSweepoutExistence M extinctionFundamentalGroupInput
  /-- Parameter space indexing the finite-extinction sweepout. -/
  extinctionSweepoutParameterSpace :
    HasFiniteExtinctionSweepoutParameterSpace M extinctionFundamentalGroupInput
  /-- Continuity and compactness of the sweepout family. -/
  extinctionSweepoutContinuity :
    HasFiniteExtinctionSweepoutContinuity M
      extinctionFundamentalGroupInput extinctionSweepout
  /-- Uniform area bounds for the finite-extinction sweepout family. -/
  extinctionSweepoutAreaBound :
    HasFiniteExtinctionSweepoutAreaBound M
      extinctionFundamentalGroupInput extinctionSweepout
  /-- Nontriviality of the sweepout class. -/
  extinctionSweepoutNontriviality :
    HasFiniteExtinctionSweepoutNontriviality M
      extinctionFundamentalGroupInput extinctionSweepout
  /-- Area-functional setup for the sweepout class. -/
  extinctionAreaFunctional :
    HasFiniteExtinctionAreaFunctionalSetup
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout
  /-- Min-max width definition from the sweepout family. -/
  extinctionMinMaxWidth :
    HasFiniteExtinctionMinMaxWidthDefinition
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout
  /-- Compactness of width-minimizing sweepout sequences. -/
  extinctionWidthCompactness :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Lower semicontinuity of width under limiting sweepouts. -/
  extinctionWidthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Extracted minimizing sequence for width. -/
  extinctionMinimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Pull-tight argument for the min-max sweepout sequence. -/
  extinctionPullTightArgument :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Stationarity of the min-max limit realizing width. -/
  extinctionMinMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Regularity of the min-max surfaces realizing width. -/
  extinctionMinSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Positivity/nontriviality of the finite-extinction width before extinction. -/
  extinctionPositiveWidth :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionFundamentalGroupInput extinctionSweepout extinctionMinMaxWidth
  /-- Min-max or width theory used by finite extinction. -/
  extinctionWidthTheory :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- First-variation formula for the width-realizing surfaces. -/
  extinctionFirstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Second-variation/stability inequality for the width argument. -/
  extinctionSecondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Gauss-Bonnet estimate used in the width derivative bound. -/
  extinctionGaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Scalar-curvature contribution to the width derivative bound. -/
  extinctionScalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Width monotonicity/evolution input used by finite extinction. -/
  extinctionWidthEvolution :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Width differential inequality along the smooth flow pieces. -/
  extinctionWidthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory
  /-- Surgery metric comparison used by the width drop. -/
  extinctionSurgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
  /-- Sweepout comparison map across a surgery time. -/
  extinctionSurgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
  /-- Width drop/nonincrease across surgery times. -/
  extinctionSurgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
  /-- Control of surgery and discarded components in the width argument. -/
  extinctionSurgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
  /-- Discarded components do not carry the target sweepout width. -/
  extinctionDiscardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
      extinctionSurgeryDiscardControl
  /-- Discarded components carry only trivial sweepout classes. -/
  extinctionDiscardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
      extinctionSurgeryDiscardControl
  /-- Classification of components discarded during surgery. -/
  extinctionDiscardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
      extinctionSurgeryDiscardControl
  /-- Tracking of components that survive surgery before extinction. -/
  extinctionSurvivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
      extinctionSurgeryDiscardControl
  /-- Topological control of components before extinction. -/
  extinctionComponentTopology :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionWidthTheory extinctionWidthEvolution
      extinctionSurgeryDiscardControl
  /-- Curvature pinching input for finite extinction. -/
  extinctionCurvaturePinching :
    HasFiniteExtinctionCurvaturePinching
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- Scalar-curvature lower bound extracted from pinching. -/
  extinctionPositiveScalarCurvatureLowerBound :
    HasFiniteExtinctionPositiveScalarCurvatureLowerBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching
  /-- Positive scalar curvature or pinching persistence under surgery. -/
  extinctionPositiveScalarCurvaturePersistence :
    HasFiniteExtinctionPositiveScalarCurvaturePersistence
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching
  /-- Component-control input for finite extinction. -/
  extinctionComponentControl :
    HasFiniteExtinctionComponentControl
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching
  /-- Volume evolution formula on smooth intervals. -/
  extinctionVolumeEvolutionFormula :
    HasFiniteExtinctionVolumeEvolutionFormula
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Nonincrease of volume through surgery and discarded components. -/
  extinctionSurgeryVolumeNonincrease :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Scalar-curvature differential inequality used in the extinction bound. -/
  extinctionScalarCurvatureDifferentialInequality :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Volume differential inequality behind the extinction estimate. -/
  extinctionVolumeDifferentialInequality :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Volume-decay estimate used to bound extinction time. -/
  extinctionVolumeDecayEstimate :
    HasFiniteExtinctionVolumeDecayEstimate
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Time-bound or decay input for finite extinction. -/
  extinctionTimeBound :
    HasFiniteExtinctionTimeBound
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl
  /-- Integration of the differential inequality behind the extinction time bound. -/
  extinctionDifferentialInequalityIntegration :
    HasFiniteExtinctionDifferentialInequalityIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl extinctionTimeBound
  /-- Integration of the decay estimate to finite-time extinction. -/
  extinctionFiniteTimeIntegration :
    HasFiniteExtinctionFiniteTimeIntegration
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl extinctionTimeBound
  /-- Summability of surgery-time losses in the extinction estimate. -/
  extinctionSurgeryTimeSummability :
    HasFiniteExtinctionSurgeryTimeSummability
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl extinctionTimeBound
  /-- Contradiction step forcing extinction by the time bound. -/
  extinctionExtinctionTimeContradiction :
    HasFiniteExtinctionExtinctionTimeContradiction
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl extinctionTimeBound
  /-- Derivation of finite extinction from the preceding data. -/
  extinctionDerivation :
    HasFiniteExtinctionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
  /-- The finite-extinction conclusion used by the topological assembly layer. -/
  finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M
  /-- Certificate tying the finite-extinction sub-obligations to the conclusion. -/
  extinctionConclusionDerivation :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_analytic_foundation_package analyticFoundation)
      surgeryConstruction.withSurgery perelmanControl.control
      extinctionCurvaturePinching extinctionComponentControl extinctionTimeBound
      extinctionDerivation finiteExtinction

/-- A completed surgery package supplies its analytic Ricci-flow foundation. -/
noncomputable def analytic_foundation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    RicciFlowAnalyticFoundationPackage ThreeManifoldModelWithCorners n M :=
  package.analyticFoundation

/-- The named surgery analytic-foundation projection is the stored package field. -/
@[simp] theorem analytic_foundation_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    analytic_foundation_of_surgery_package package = package.analyticFoundation :=
  rfl

/-- A completed surgery package supplies the underlying Ricci-flow data. -/
noncomputable def ricci_flow_data_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    RicciFlowData ThreeManifoldModelWithCorners n M :=
  ricci_flow_data_of_analytic_foundation_package
    (analytic_foundation_of_surgery_package package)

/-- The named surgery Ricci-flow projection is the stored analytic flow field. -/
@[simp] theorem ricci_flow_data_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ricci_flow_data_of_surgery_package package =
      package.analyticFoundation.flow :=
  rfl

/--
A completed surgery package exposes its theorem-shaped analytic statement,
fixed-flow analytic derivation statement, named analytic sub-obligation payload,
and Ricci-flow equation evidence for its projected Ricci-flow data together.
-/
theorem analytic_foundation_payload_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ∃ _statement :
      RicciFlowAnalyticFoundationStatement ThreeManifoldModelWithCorners n M,
    ∃ _derivationStatement :
      AnalyticFoundationDerivationStatement
        (ricci_flow_data_of_surgery_package package),
    ∃ _subobligations :
      AnalyticFoundationSubobligationsPayload
        (ricci_flow_data_of_surgery_package package),
      SatisfiesRicciFlowEquation
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package)) := by
  let analyticPackage := analytic_foundation_of_surgery_package package
  rcases analytic_foundation_payload_of_analytic_foundation_package
      analyticPackage with
    ⟨statement, derivationStatement, subobligations, equationEvidence⟩
  exact ⟨statement, derivationStatement, subobligations, equationEvidence⟩

/--
The surgery-level analytic payload bridge delegates exactly to the stored
analytic-foundation package payload.
-/
theorem analytic_foundation_payload_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    analytic_foundation_payload_of_surgery_package package =
      analytic_foundation_payload_of_analytic_foundation_package
        (analytic_foundation_of_surgery_package package) := by
  apply Subsingleton.elim

/-- A completed surgery package supplies Ricci-flow equation evidence. -/
theorem equation_evidence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    SatisfiesRicciFlowEquation
      (metric_of_ricci_flow_data (ricci_flow_data_of_surgery_package package))
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_surgery_package package)) := by
  rcases analytic_foundation_payload_of_surgery_package package with
    ⟨_statement, _derivationStatement, _subobligations, equationEvidence⟩
  exact equationEvidence

/-- The surgery equation projection agrees with the stored analytic-foundation evidence. -/
theorem equation_evidence_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    equation_evidence_of_surgery_package package =
      equation_evidence_of_analytic_foundation_package
        package.analyticFoundation := by
  apply Subsingleton.elim

/-- A completed surgery package supplies its surgery-construction package. -/
noncomputable def surgery_construction_package_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    RicciFlowWithSurgeryConstructionPackage (n := n) (M := M)
      (ricci_flow_data_of_surgery_package package) :=
  package.surgeryConstruction

/-- The named surgery-construction projection is the stored package field. -/
@[simp] theorem surgery_construction_package_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    surgery_construction_package_of_surgery_package package =
      package.surgeryConstruction :=
  rfl

/--
A completed surgery package assembles the fixed-flow surgery-construction
statement for its projected Ricci-flow data.
-/
theorem ricci_flow_with_surgery_construction_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    RicciFlowWithSurgeryConstructionStatement
      (ricci_flow_data_of_surgery_package package) :=
  ricci_flow_with_surgery_construction_statement_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies the Ricci-flow-with-surgery evidence. -/
theorem ricci_flow_with_surgery_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasRicciFlowWithSurgery n M :=
  ricci_flow_with_surgery_of_construction_statement
    (ricci_flow_with_surgery_construction_statement_of_surgery_package
      package)

/-- A completed surgery package supplies surgery scale-function evidence. -/
theorem surgery_scale_function_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryScaleFunction (ricci_flow_data_of_surgery_package package) :=
  surgery_scale_function_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-scale continuity evidence. -/
theorem surgery_scale_continuity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryScaleContinuity (ricci_flow_data_of_surgery_package package) :=
  surgery_scale_continuity_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-scale separation evidence. -/
theorem surgery_scale_separation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryScaleSeparation (ricci_flow_data_of_surgery_package package) :=
  surgery_scale_separation_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies cutoff-parameter control. -/
theorem surgery_cutoff_parameter_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryCutoffParameterControl (ricci_flow_data_of_surgery_package package) :=
  surgery_cutoff_parameter_control_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies smooth cutoff bump functions. -/
theorem surgery_cutoff_smooth_bump_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryCutoffSmoothBumpFunction
      (ricci_flow_data_of_surgery_package package) :=
  surgery_cutoff_smooth_bump_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-parameter evidence. -/
theorem surgery_parameter_selection_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryParameterSelection (ricci_flow_data_of_surgery_package package) :=
  surgery_parameter_selection_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies strong-delta-neck detection. -/
theorem strong_delta_neck_detection_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasStrongDeltaNeckDetection (ricci_flow_data_of_surgery_package package) :=
  strong_delta_neck_detection_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery neck-separation evidence. -/
theorem surgery_neck_separation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryNeckSeparation (ricci_flow_data_of_surgery_package package) :=
  surgery_neck_separation_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-neck parametrization. -/
theorem surgery_neck_parametrization_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryNeckParametrization (ricci_flow_data_of_surgery_package package) :=
  surgery_neck_parametrization_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies canonical neck-coordinate evidence. -/
theorem surgery_neck_canonical_coordinates_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryNeckCanonicalCoordinates
      (ricci_flow_data_of_surgery_package package) :=
  surgery_neck_canonical_coordinates_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies neck-decomposition evidence. -/
theorem surgery_neck_decomposition_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryNeckDecomposition (ricci_flow_data_of_surgery_package package) :=
  surgery_neck_decomposition_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies the standard-cap model. -/
theorem standard_cap_model_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasStandardCapModel (ricci_flow_data_of_surgery_package package) :=
  standard_cap_model_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies cap-gluing smoothness. -/
theorem cap_gluing_smoothness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCapGluingSmoothness (ricci_flow_data_of_surgery_package package) :=
  cap_gluing_smoothness_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies cap metric-interpolation evidence. -/
theorem surgery_cap_metric_interpolation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryCapMetricInterpolation
      (ricci_flow_data_of_surgery_package package) :=
  surgery_cap_metric_interpolation_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies cap curvature-estimate evidence. -/
theorem surgery_cap_curvature_estimates_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryCapCurvatureEstimates
      (ricci_flow_data_of_surgery_package package) :=
  surgery_cap_curvature_estimates_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies cap-construction evidence. -/
theorem surgery_cap_construction_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryCapConstruction (ricci_flow_data_of_surgery_package package) :=
  surgery_cap_construction_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies post-surgery curvature pinching. -/
theorem post_surgery_curvature_pinching_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPostSurgeryCurvaturePinching (ricci_flow_data_of_surgery_package package) :=
  post_surgery_curvature_pinching_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies post-surgery noncollapsing control. -/
theorem post_surgery_noncollapsing_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPostSurgeryNoncollapsingControl
      (ricci_flow_data_of_surgery_package package) :=
  post_surgery_noncollapsing_control_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies post-surgery derivative bounds. -/
theorem post_surgery_derivative_bounds_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPostSurgeryDerivativeBounds
      (ricci_flow_data_of_surgery_package package) :=
  post_surgery_derivative_bounds_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies post-surgery canonical-neighborhood persistence. -/
theorem post_surgery_canonical_neighborhood_persistence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPostSurgeryCanonicalNeighborhoodPersistence
      (ricci_flow_data_of_surgery_package package) :=
  post_surgery_canonical_neighborhood_persistence_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies post-surgery metric-control evidence. -/
theorem post_surgery_metric_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPostSurgeryMetricControl (ricci_flow_data_of_surgery_package package) :=
  post_surgery_metric_control_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-time discreteness. -/
theorem surgery_time_discreteness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryTimeDiscreteness (ricci_flow_data_of_surgery_package package) :=
  surgery_time_discreteness_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies surgery-time local finiteness. -/
theorem surgery_time_local_finiteness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSurgeryTimeLocalFiniteness (ricci_flow_data_of_surgery_package package) :=
  surgery_time_local_finiteness_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies long-time existence iteration. -/
theorem long_time_existence_iteration_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasLongTimeExistenceIteration (ricci_flow_data_of_surgery_package package) :=
  long_time_existence_iteration_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies long-time surgery-parameter coherence. -/
theorem long_time_surgery_parameter_coherence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasLongTimeSurgeryParameterCoherence
      (ricci_flow_data_of_surgery_package package) :=
  long_time_surgery_parameter_coherence_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies long-time surgery nonaccumulation. -/
theorem long_time_nonaccumulation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasLongTimeNonaccumulation (ricci_flow_data_of_surgery_package package) :=
  long_time_nonaccumulation_of_construction_package
    (surgery_construction_package_of_surgery_package package)

/-- A completed surgery package supplies long-time surgery continuation evidence. -/
theorem long_time_surgery_continuation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasLongTimeSurgeryContinuation (ricci_flow_data_of_surgery_package package) :=
  long_time_surgery_continuation_of_construction_package
    (surgery_construction_package_of_surgery_package package)

section SurgeryPackageConstructionProjectionEqualities

variable {n : ℕ∞ω}
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
variable [CompactSpace M]
variable [IsManifold ThreeManifoldModelWithCorners 1 M]
variable (package : FiniteExtinctionSurgeryPackage n M)

/-- The surgery-package construction statement is the construction-package route. -/
theorem ricci_flow_with_surgery_construction_statement_of_surgery_package_eq :
    ricci_flow_with_surgery_construction_statement_of_surgery_package package =
      ricci_flow_with_surgery_construction_statement_of_construction_package
        (surgery_construction_package_of_surgery_package package) := by
  apply Subsingleton.elim

/-- The surgery-package aggregate surgery projection is the stored construction field. -/
theorem ricci_flow_with_surgery_of_surgery_package_eq :
    ricci_flow_with_surgery_of_surgery_package package =
      package.surgeryConstruction.withSurgery := by
  apply Subsingleton.elim

/-- The surgery-package scale-function projection is the stored construction field. -/
theorem surgery_scale_function_of_surgery_package_eq :
    surgery_scale_function_of_surgery_package package =
      package.surgeryConstruction.scaleFunction := by
  apply Subsingleton.elim

/-- The surgery-package scale-continuity projection is the stored construction field. -/
theorem surgery_scale_continuity_of_surgery_package_eq :
    surgery_scale_continuity_of_surgery_package package =
      package.surgeryConstruction.scaleContinuity := by
  apply Subsingleton.elim

/-- The surgery-package scale-separation projection is the stored construction field. -/
theorem surgery_scale_separation_of_surgery_package_eq :
    surgery_scale_separation_of_surgery_package package =
      package.surgeryConstruction.scaleSeparation := by
  apply Subsingleton.elim

/-- The surgery-package cutoff-parameter projection is the stored construction field. -/
theorem surgery_cutoff_parameter_control_of_surgery_package_eq :
    surgery_cutoff_parameter_control_of_surgery_package package =
      package.surgeryConstruction.cutoffParameterControl := by
  apply Subsingleton.elim

/-- The surgery-package cutoff smooth-bump projection is the stored construction field. -/
theorem surgery_cutoff_smooth_bump_of_surgery_package_eq :
    surgery_cutoff_smooth_bump_of_surgery_package package =
      package.surgeryConstruction.cutoffSmoothBump := by
  apply Subsingleton.elim

/-- The surgery-package parameter-selection projection is the stored construction field. -/
theorem surgery_parameter_selection_of_surgery_package_eq :
    surgery_parameter_selection_of_surgery_package package =
      package.surgeryConstruction.parameterSelection := by
  apply Subsingleton.elim

/-- The surgery-package strong-neck detection projection is the stored construction field. -/
theorem strong_delta_neck_detection_of_surgery_package_eq :
    strong_delta_neck_detection_of_surgery_package package =
      package.surgeryConstruction.strongDeltaNeckDetection := by
  apply Subsingleton.elim

/-- The surgery-package neck-separation projection is the stored construction field. -/
theorem surgery_neck_separation_of_surgery_package_eq :
    surgery_neck_separation_of_surgery_package package =
      package.surgeryConstruction.neckSeparation := by
  apply Subsingleton.elim

/-- The surgery-package neck-parametrization projection is the stored construction field. -/
theorem surgery_neck_parametrization_of_surgery_package_eq :
    surgery_neck_parametrization_of_surgery_package package =
      package.surgeryConstruction.neckParametrization := by
  apply Subsingleton.elim

/-- The surgery-package neck-coordinate projection is the stored construction field. -/
theorem surgery_neck_canonical_coordinates_of_surgery_package_eq :
    surgery_neck_canonical_coordinates_of_surgery_package package =
      package.surgeryConstruction.neckCanonicalCoordinates := by
  apply Subsingleton.elim

/-- The surgery-package neck-decomposition projection is the stored construction field. -/
theorem surgery_neck_decomposition_of_surgery_package_eq :
    surgery_neck_decomposition_of_surgery_package package =
      package.surgeryConstruction.neckDecomposition := by
  apply Subsingleton.elim

/-- The surgery-package standard-cap projection is the stored construction field. -/
theorem standard_cap_model_of_surgery_package_eq :
    standard_cap_model_of_surgery_package package =
      package.surgeryConstruction.standardCapModel := by
  apply Subsingleton.elim

/-- The surgery-package cap-gluing projection is the stored construction field. -/
theorem cap_gluing_smoothness_of_surgery_package_eq :
    cap_gluing_smoothness_of_surgery_package package =
      package.surgeryConstruction.capGluingSmoothness := by
  apply Subsingleton.elim

/-- The surgery-package cap metric-interpolation projection is the stored field. -/
theorem surgery_cap_metric_interpolation_of_surgery_package_eq :
    surgery_cap_metric_interpolation_of_surgery_package package =
      package.surgeryConstruction.capMetricInterpolation := by
  apply Subsingleton.elim

/-- The surgery-package cap curvature-estimates projection is the stored field. -/
theorem surgery_cap_curvature_estimates_of_surgery_package_eq :
    surgery_cap_curvature_estimates_of_surgery_package package =
      package.surgeryConstruction.capCurvatureEstimates := by
  apply Subsingleton.elim

/-- The surgery-package cap-construction projection is the stored construction field. -/
theorem surgery_cap_construction_of_surgery_package_eq :
    surgery_cap_construction_of_surgery_package package =
      package.surgeryConstruction.capConstruction := by
  apply Subsingleton.elim

/-- The surgery-package post-surgery curvature projection is the stored field. -/
theorem post_surgery_curvature_pinching_of_surgery_package_eq :
    post_surgery_curvature_pinching_of_surgery_package package =
      package.surgeryConstruction.postSurgeryCurvaturePinching := by
  apply Subsingleton.elim

/-- The surgery-package post-surgery noncollapsing projection is the stored field. -/
theorem post_surgery_noncollapsing_control_of_surgery_package_eq :
    post_surgery_noncollapsing_control_of_surgery_package package =
      package.surgeryConstruction.postSurgeryNoncollapsing := by
  apply Subsingleton.elim

/-- The surgery-package post-surgery derivative-bounds projection is the stored field. -/
theorem post_surgery_derivative_bounds_of_surgery_package_eq :
    post_surgery_derivative_bounds_of_surgery_package package =
      package.surgeryConstruction.postSurgeryDerivativeBounds := by
  apply Subsingleton.elim

/-- The surgery-package post-surgery canonical-neighborhood projection is stored. -/
theorem post_surgery_canonical_neighborhood_persistence_of_surgery_package_eq :
    post_surgery_canonical_neighborhood_persistence_of_surgery_package package =
      package.surgeryConstruction.postSurgeryCanonicalNeighborhoodPersistence := by
  apply Subsingleton.elim

/-- The surgery-package post-surgery metric-control projection is the stored field. -/
theorem post_surgery_metric_control_of_surgery_package_eq :
    post_surgery_metric_control_of_surgery_package package =
      package.surgeryConstruction.metricControl := by
  apply Subsingleton.elim

/-- The surgery-package surgery-time discreteness projection is the stored field. -/
theorem surgery_time_discreteness_of_surgery_package_eq :
    surgery_time_discreteness_of_surgery_package package =
      package.surgeryConstruction.surgeryTimeDiscreteness := by
  apply Subsingleton.elim

/-- The surgery-package surgery-time local-finiteness projection is the stored field. -/
theorem surgery_time_local_finiteness_of_surgery_package_eq :
    surgery_time_local_finiteness_of_surgery_package package =
      package.surgeryConstruction.surgeryTimeLocalFiniteness := by
  apply Subsingleton.elim

/-- The surgery-package long-time existence projection is the stored field. -/
theorem long_time_existence_iteration_of_surgery_package_eq :
    long_time_existence_iteration_of_surgery_package package =
      package.surgeryConstruction.longTimeExistenceIteration := by
  apply Subsingleton.elim

/-- The surgery-package long-time parameter-coherence projection is stored. -/
theorem long_time_surgery_parameter_coherence_of_surgery_package_eq :
    long_time_surgery_parameter_coherence_of_surgery_package package =
      package.surgeryConstruction.longTimeParameterCoherence := by
  apply Subsingleton.elim

/-- The surgery-package long-time nonaccumulation projection is the stored field. -/
theorem long_time_nonaccumulation_of_surgery_package_eq :
    long_time_nonaccumulation_of_surgery_package package =
      package.surgeryConstruction.longTimeNonaccumulation := by
  apply Subsingleton.elim

/-- The surgery-package long-time continuation projection is the stored field. -/
theorem long_time_surgery_continuation_of_surgery_package_eq :
    long_time_surgery_continuation_of_surgery_package package =
      package.surgeryConstruction.longTimeContinuation := by
  apply Subsingleton.elim

end SurgeryPackageConstructionProjectionEqualities

/-- A completed surgery package supplies its Perelman control package. -/
noncomputable def perelman_control_package_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    PerelmanSingularityControlPackage (n := n) (M := M)
      (ricci_flow_data_of_surgery_package package) :=
  package.perelmanControl

/-- The named Perelman-control projection is the stored package field. -/
@[simp] theorem perelman_control_package_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    perelman_control_package_of_surgery_package package =
      package.perelmanControl :=
  rfl

/-- A completed surgery package supplies its Perelman control statement. -/
theorem perelman_singularity_control_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    PerelmanSingularityControlStatement
      (ricci_flow_data_of_surgery_package package) :=
  perelman_singularity_control_statement_of_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies F-functional setup input. -/
theorem f_functional_setup_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanFFunctionalSetup (ricci_flow_data_of_surgery_package package) :=
  f_functional_setup_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies conjugate heat equation input. -/
theorem conjugate_heat_equation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasConjugateHeatEquationTheory (ricci_flow_data_of_surgery_package package) :=
  conjugate_heat_equation_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies adjoint heat kernel construction. -/
theorem adjoint_heat_kernel_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasAdjointHeatKernelConstruction
      (ricci_flow_data_of_surgery_package package) :=
  adjoint_heat_kernel_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies W-functional setup input. -/
theorem w_functional_setup_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanWFunctionalSetup (ricci_flow_data_of_surgery_package package) :=
  w_functional_setup_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy-gradient formula input. -/
theorem entropy_gradient_formula_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyGradientFormula
      (ricci_flow_data_of_surgery_package package) :=
  entropy_gradient_formula_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy first-variation input. -/
theorem entropy_first_variation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyFirstVariation
      (ricci_flow_data_of_surgery_package package) :=
  entropy_first_variation_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy monotonicity input. -/
theorem entropy_monotonicity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyMonotonicity
      (ricci_flow_data_of_surgery_package package) :=
  entropy_monotonicity_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Perelman's entropy-functional input. -/
theorem entropy_functional_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyFunctional (ricci_flow_data_of_surgery_package package) :=
  entropy_functional_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-length first variation. -/
theorem reduced_length_first_variation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedLengthFirstVariation
      (ricci_flow_data_of_surgery_package package) :=
  reduced_length_first_variation_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-distance existence input. -/
theorem reduced_distance_existence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedDistanceExistence
      (ricci_flow_data_of_surgery_package package) :=
  reduced_distance_existence_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-distance differential inequality. -/
theorem reduced_distance_differential_inequality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedDistanceDifferentialInequality
      (ricci_flow_data_of_surgery_package package) :=
  reduced_distance_differential_inequality_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-distance estimates. -/
theorem reduced_distance_estimates_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedDistanceEstimates
      (ricci_flow_data_of_surgery_package package) :=
  reduced_distance_estimates_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Perelman's reduced-distance input. -/
theorem reduced_distance_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedDistanceTheory (ricci_flow_data_of_surgery_package package) :=
  reduced_distance_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-volume definition input. -/
theorem reduced_volume_definition_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeDefinition
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_definition_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies the reduced-volume derivative formula. -/
theorem reduced_volume_derivative_formula_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeDerivativeFormula
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_derivative_formula_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-volume rigidity input. -/
theorem reduced_volume_rigidity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeRigidity
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_rigidity_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies the reduced-volume monotonicity formula. -/
theorem reduced_volume_nonincreasing_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeNonincreasing
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_nonincreasing_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-volume-to-kappa input. -/
theorem kappa_noncollapsing_from_reduced_volume_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanKappaNoncollapsingFromReducedVolume
      (ricci_flow_data_of_surgery_package package) :=
  kappa_noncollapsing_from_reduced_volume_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies the no-local-collapsing volume lower bound. -/
theorem no_local_collapsing_volume_lower_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasNoLocalCollapsingVolumeLowerBound
      (ricci_flow_data_of_surgery_package package) :=
  no_local_collapsing_volume_lower_bound_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies quantified kappa-noncollapsing input. -/
theorem kappa_noncollapsing_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanKappaNoncollapsingQuantification
      (ricci_flow_data_of_surgery_package package) :=
  kappa_noncollapsing_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Hamilton compactness. -/
theorem hamilton_compactness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasHamiltonCompactnessTheorem (ricci_flow_data_of_surgery_package package) :=
  hamilton_compactness_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies ancient-kappa limit extraction. -/
theorem ancient_kappa_solution_limit_extraction_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasAncientKappaSolutionLimitExtraction
      (ricci_flow_data_of_surgery_package package) :=
  ancient_kappa_solution_limit_extraction_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies kappa-solution structure theory. -/
theorem kappa_solution_structure_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasKappaSolutionStructureTheory
      (ricci_flow_data_of_surgery_package package) :=
  kappa_solution_structure_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies asymptotic soliton analysis. -/
theorem kappa_solution_asymptotic_soliton_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasKappaSolutionAsymptoticSoliton
      (ricci_flow_data_of_surgery_package package) :=
  kappa_solution_asymptotic_soliton_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies ancient-kappa-solution compactness. -/
theorem ancient_kappa_solution_compactness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasAncientKappaSolutionCompactness
      (ricci_flow_data_of_surgery_package package) :=
  ancient_kappa_solution_compactness_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies canonical-neighborhood scale control. -/
theorem canonical_neighborhood_scale_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodScaleControl
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_scale_control_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies the canonical-neighborhood neck/cap dichotomy. -/
theorem canonical_neighborhood_neck_cap_dichotomy_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodNeckCapDichotomy
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_neck_cap_dichotomy_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies canonical-neighborhood classification. -/
theorem canonical_neighborhood_classification_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodClassification
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_classification_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Perelman's no-local-collapsing input. -/
theorem no_local_collapsing_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanNoLocalCollapsing (ricci_flow_data_of_surgery_package package) :=
  no_local_collapsing_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Perelman's reduced-volume input. -/
theorem reduced_volume_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeMonotonicity
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies the canonical-neighborhood input. -/
theorem canonical_neighborhood_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodTheorem
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies singularity-model classification. -/
theorem singularity_model_classification_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSingularityModelClassification
      (ricci_flow_data_of_surgery_package package) :=
  singularity_model_classification_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy normalization evidence. -/
theorem entropy_normalization_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyNormalization
      (ricci_flow_data_of_surgery_package package) :=
  entropy_normalization_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy-minimizer existence. -/
theorem entropy_minimizer_existence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyMinimizerExistence
      (ricci_flow_data_of_surgery_package package) :=
  entropy_minimizer_existence_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy log-Sobolev control. -/
theorem entropy_log_sobolev_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyLogSobolevControl
      (ricci_flow_data_of_surgery_package package) :=
  entropy_log_sobolev_control_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies conjugate heat-kernel estimates. -/
theorem conjugate_heat_kernel_estimates_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanConjugateHeatKernelEstimates
      (ricci_flow_data_of_surgery_package package) :=
  conjugate_heat_kernel_estimates_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies entropy lower-bound propagation. -/
theorem entropy_lower_bound_propagation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanEntropyLowerBoundPropagation
      (ricci_flow_data_of_surgery_package package) :=
  entropy_lower_bound_propagation_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-distance cut-locus control. -/
theorem reduced_distance_cut_locus_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedDistanceCutLocusControl
      (ricci_flow_data_of_surgery_package package) :=
  reduced_distance_cut_locus_control_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-Jacobian comparison. -/
theorem reduced_jacobian_comparison_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedJacobianComparison
      (ricci_flow_data_of_surgery_package package) :=
  reduced_jacobian_comparison_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-volume positive lower bounds. -/
theorem reduced_volume_positive_lower_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumePositiveLowerBound
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_positive_lower_bound_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies reduced-volume limit rigidity. -/
theorem reduced_volume_limit_rigidity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanReducedVolumeLimitRigidity
      (ricci_flow_data_of_surgery_package package) :=
  reduced_volume_limit_rigidity_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies no-local-collapsing contradiction setup. -/
theorem no_local_collapsing_contradiction_setup_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanNoLocalCollapsingContradictionSetup
      (ricci_flow_data_of_surgery_package package) :=
  no_local_collapsing_contradiction_setup_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies collapsed-ball blow-up evidence. -/
theorem collapsed_ball_blowup_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanCollapsedBallBlowup
      (ricci_flow_data_of_surgery_package package) :=
  collapsed_ball_blowup_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies volume-ratio contradiction evidence. -/
theorem volume_ratio_contradiction_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanVolumeRatioContradiction
      (ricci_flow_data_of_surgery_package package) :=
  volume_ratio_contradiction_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies kappa-solution pointed rescaling. -/
theorem kappa_solution_pointed_rescaling_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasKappaSolutionPointedRescaling
      (ricci_flow_data_of_surgery_package package) :=
  kappa_solution_pointed_rescaling_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies kappa-solution curvature normalization. -/
theorem kappa_solution_curvature_normalization_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasKappaSolutionCurvatureNormalization
      (ricci_flow_data_of_surgery_package package) :=
  kappa_solution_curvature_normalization_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies nonnegative curvature-operator control. -/
theorem kappa_solution_nonnegative_curvature_operator_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasKappaSolutionNonnegativeCurvatureOperator
      (ricci_flow_data_of_surgery_package package) :=
  kappa_solution_nonnegative_curvature_operator_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies canonical-neighborhood stability. -/
theorem canonical_neighborhood_stability_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodStability
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_stability_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies cross-scale canonical-neighborhood persistence. -/
theorem canonical_neighborhood_persistence_across_scales_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasCanonicalNeighborhoodPersistenceAcrossScales
      (ricci_flow_data_of_surgery_package package) :=
  canonical_neighborhood_persistence_across_scales_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies singularity-model blow-up classification. -/
theorem singularity_model_blowup_classification_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasSingularityModelBlowupClassification
      (ricci_flow_data_of_surgery_package package) :=
  singularity_model_blowup_classification_of_perelman_package
    (perelman_control_package_of_surgery_package package)

/-- A completed surgery package supplies Perelman's singularity-control input. -/
theorem perelman_singularity_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasPerelmanSingularityControl
      (n := n) (M := M) (ricci_flow_data_of_surgery_package package) :=
  perelman_singularity_control_of_statement
    (perelman_singularity_control_statement_of_surgery_package package)

section SurgeryPackagePerelmanProjectionEqualities

variable {n : ℕ∞ω}
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
variable [CompactSpace M]
variable [IsManifold ThreeManifoldModelWithCorners 1 M]
variable (package : FiniteExtinctionSurgeryPackage n M)

/-- The surgery-package Perelman statement is the Perelman-package route. -/
theorem perelman_singularity_control_statement_of_surgery_package_eq :
    perelman_singularity_control_statement_of_surgery_package package =
      perelman_singularity_control_statement_of_package
        (perelman_control_package_of_surgery_package package) := by
  apply Subsingleton.elim

/-- The surgery-package F-functional projection is the stored Perelman field. -/
theorem f_functional_setup_of_surgery_package_eq :
    f_functional_setup_of_surgery_package package =
      package.perelmanControl.fFunctionalSetup := by
  apply Subsingleton.elim

/-- The surgery-package entropy-normalization projection is the stored field. -/
theorem entropy_normalization_of_surgery_package_eq :
    entropy_normalization_of_surgery_package package =
      package.perelmanControl.entropyNormalization := by
  apply Subsingleton.elim

/-- The surgery-package entropy-minimizer projection is the stored field. -/
theorem entropy_minimizer_existence_of_surgery_package_eq :
    entropy_minimizer_existence_of_surgery_package package =
      package.perelmanControl.entropyMinimizerExistence := by
  apply Subsingleton.elim

/-- The surgery-package entropy log-Sobolev projection is the stored field. -/
theorem entropy_log_sobolev_control_of_surgery_package_eq :
    entropy_log_sobolev_control_of_surgery_package package =
      package.perelmanControl.entropyLogSobolevControl := by
  apply Subsingleton.elim

/-- The surgery-package conjugate-heat projection is the stored Perelman field. -/
theorem conjugate_heat_equation_of_surgery_package_eq :
    conjugate_heat_equation_of_surgery_package package =
      package.perelmanControl.conjugateHeatEquation := by
  apply Subsingleton.elim

/-- The surgery-package adjoint heat-kernel projection is the stored field. -/
theorem adjoint_heat_kernel_of_surgery_package_eq :
    adjoint_heat_kernel_of_surgery_package package =
      package.perelmanControl.adjointHeatKernel := by
  apply Subsingleton.elim

/-- The surgery-package conjugate heat-kernel estimate projection is stored. -/
theorem conjugate_heat_kernel_estimates_of_surgery_package_eq :
    conjugate_heat_kernel_estimates_of_surgery_package package =
      package.perelmanControl.conjugateHeatKernelEstimates := by
  apply Subsingleton.elim

/-- The surgery-package W-functional projection is the stored Perelman field. -/
theorem w_functional_setup_of_surgery_package_eq :
    w_functional_setup_of_surgery_package package =
      package.perelmanControl.wFunctionalSetup := by
  apply Subsingleton.elim

/-- The surgery-package entropy-gradient projection is the stored field. -/
theorem entropy_gradient_formula_of_surgery_package_eq :
    entropy_gradient_formula_of_surgery_package package =
      package.perelmanControl.entropyGradientFormula := by
  apply Subsingleton.elim

/-- The surgery-package entropy first-variation projection is the stored field. -/
theorem entropy_first_variation_of_surgery_package_eq :
    entropy_first_variation_of_surgery_package package =
      package.perelmanControl.entropyFirstVariation := by
  apply Subsingleton.elim

/-- The surgery-package entropy monotonicity projection is the stored field. -/
theorem entropy_monotonicity_of_surgery_package_eq :
    entropy_monotonicity_of_surgery_package package =
      package.perelmanControl.entropyMonotonicity := by
  apply Subsingleton.elim

/-- The surgery-package entropy lower-bound projection is the stored field. -/
theorem entropy_lower_bound_propagation_of_surgery_package_eq :
    entropy_lower_bound_propagation_of_surgery_package package =
      package.perelmanControl.entropyLowerBoundPropagation := by
  apply Subsingleton.elim

/-- The surgery-package entropy-functional projection is the stored field. -/
theorem entropy_functional_of_surgery_package_eq :
    entropy_functional_of_surgery_package package =
      package.perelmanControl.entropyFunctional := by
  apply Subsingleton.elim

/-- The surgery-package reduced-length projection is the stored field. -/
theorem reduced_length_first_variation_of_surgery_package_eq :
    reduced_length_first_variation_of_surgery_package package =
      package.perelmanControl.reducedLengthFirstVariation := by
  apply Subsingleton.elim

/-- The surgery-package reduced-distance existence projection is stored. -/
theorem reduced_distance_existence_of_surgery_package_eq :
    reduced_distance_existence_of_surgery_package package =
      package.perelmanControl.reducedDistanceExistence := by
  apply Subsingleton.elim

/-- The surgery-package reduced-distance inequality projection is stored. -/
theorem reduced_distance_differential_inequality_of_surgery_package_eq :
    reduced_distance_differential_inequality_of_surgery_package package =
      package.perelmanControl.reducedDistanceDifferentialInequality := by
  apply Subsingleton.elim

/-- The surgery-package reduced-distance estimates projection is stored. -/
theorem reduced_distance_estimates_of_surgery_package_eq :
    reduced_distance_estimates_of_surgery_package package =
      package.perelmanControl.reducedDistanceEstimates := by
  apply Subsingleton.elim

/-- The surgery-package reduced-distance cut-locus projection is stored. -/
theorem reduced_distance_cut_locus_control_of_surgery_package_eq :
    reduced_distance_cut_locus_control_of_surgery_package package =
      package.perelmanControl.reducedDistanceCutLocusControl := by
  apply Subsingleton.elim

/-- The surgery-package reduced-Jacobian projection is the stored field. -/
theorem reduced_jacobian_comparison_of_surgery_package_eq :
    reduced_jacobian_comparison_of_surgery_package package =
      package.perelmanControl.reducedJacobianComparison := by
  apply Subsingleton.elim

/-- The surgery-package reduced-distance projection is the stored field. -/
theorem reduced_distance_of_surgery_package_eq :
    reduced_distance_of_surgery_package package =
      package.perelmanControl.reducedDistance := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume definition projection is stored. -/
theorem reduced_volume_definition_of_surgery_package_eq :
    reduced_volume_definition_of_surgery_package package =
      package.perelmanControl.reducedVolumeDefinition := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume derivative projection is stored. -/
theorem reduced_volume_derivative_formula_of_surgery_package_eq :
    reduced_volume_derivative_formula_of_surgery_package package =
      package.perelmanControl.reducedVolumeDerivativeFormula := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume rigidity projection is stored. -/
theorem reduced_volume_rigidity_of_surgery_package_eq :
    reduced_volume_rigidity_of_surgery_package package =
      package.perelmanControl.reducedVolumeRigidity := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume lower-bound projection is stored. -/
theorem reduced_volume_positive_lower_bound_of_surgery_package_eq :
    reduced_volume_positive_lower_bound_of_surgery_package package =
      package.perelmanControl.reducedVolumePositiveLowerBound := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume limit-rigidity projection is stored. -/
theorem reduced_volume_limit_rigidity_of_surgery_package_eq :
    reduced_volume_limit_rigidity_of_surgery_package package =
      package.perelmanControl.reducedVolumeLimitRigidity := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume monotonicity projection is stored. -/
theorem reduced_volume_nonincreasing_of_surgery_package_eq :
    reduced_volume_nonincreasing_of_surgery_package package =
      package.perelmanControl.reducedVolumeNonincreasing := by
  apply Subsingleton.elim

/-- The surgery-package kappa-from-reduced-volume projection is stored. -/
theorem kappa_noncollapsing_from_reduced_volume_of_surgery_package_eq :
    kappa_noncollapsing_from_reduced_volume_of_surgery_package package =
      package.perelmanControl.kappaNoncollapsingFromReducedVolume := by
  apply Subsingleton.elim

/-- The surgery-package no-local-collapsing setup projection is stored. -/
theorem no_local_collapsing_contradiction_setup_of_surgery_package_eq :
    no_local_collapsing_contradiction_setup_of_surgery_package package =
      package.perelmanControl.noLocalCollapsingContradictionSetup := by
  apply Subsingleton.elim

/-- The surgery-package collapsed-ball blowup projection is stored. -/
theorem collapsed_ball_blowup_of_surgery_package_eq :
    collapsed_ball_blowup_of_surgery_package package =
      package.perelmanControl.collapsedBallBlowup := by
  apply Subsingleton.elim

/-- The surgery-package volume-ratio contradiction projection is stored. -/
theorem volume_ratio_contradiction_of_surgery_package_eq :
    volume_ratio_contradiction_of_surgery_package package =
      package.perelmanControl.volumeRatioContradiction := by
  apply Subsingleton.elim

/-- The surgery-package no-local-collapsing lower-bound projection is stored. -/
theorem no_local_collapsing_volume_lower_bound_of_surgery_package_eq :
    no_local_collapsing_volume_lower_bound_of_surgery_package package =
      package.perelmanControl.noLocalCollapsingVolumeLowerBound := by
  apply Subsingleton.elim

/-- The surgery-package kappa-noncollapsing projection is stored. -/
theorem kappa_noncollapsing_of_surgery_package_eq :
    kappa_noncollapsing_of_surgery_package package =
      package.perelmanControl.kappaNoncollapsing := by
  apply Subsingleton.elim

/-- The surgery-package Hamilton compactness projection is stored. -/
theorem hamilton_compactness_of_surgery_package_eq :
    hamilton_compactness_of_surgery_package package =
      package.perelmanControl.hamiltonCompactness := by
  apply Subsingleton.elim

/-- The surgery-package ancient-kappa limit projection is stored. -/
theorem ancient_kappa_solution_limit_extraction_of_surgery_package_eq :
    ancient_kappa_solution_limit_extraction_of_surgery_package package =
      package.perelmanControl.ancientKappaSolutionLimitExtraction := by
  apply Subsingleton.elim

/-- The surgery-package kappa-solution rescaling projection is stored. -/
theorem kappa_solution_pointed_rescaling_of_surgery_package_eq :
    kappa_solution_pointed_rescaling_of_surgery_package package =
      package.perelmanControl.kappaSolutionPointedRescaling := by
  apply Subsingleton.elim

/-- The surgery-package kappa-solution normalization projection is stored. -/
theorem kappa_solution_curvature_normalization_of_surgery_package_eq :
    kappa_solution_curvature_normalization_of_surgery_package package =
      package.perelmanControl.kappaSolutionCurvatureNormalization := by
  apply Subsingleton.elim

/-- The surgery-package kappa-solution structure projection is stored. -/
theorem kappa_solution_structure_of_surgery_package_eq :
    kappa_solution_structure_of_surgery_package package =
      package.perelmanControl.kappaSolutionStructure := by
  apply Subsingleton.elim

/-- The surgery-package nonnegative curvature-operator projection is stored. -/
theorem kappa_solution_nonnegative_curvature_operator_of_surgery_package_eq :
    kappa_solution_nonnegative_curvature_operator_of_surgery_package package =
      package.perelmanControl.kappaSolutionNonnegativeCurvatureOperator := by
  apply Subsingleton.elim

/-- The surgery-package asymptotic soliton projection is stored. -/
theorem kappa_solution_asymptotic_soliton_of_surgery_package_eq :
    kappa_solution_asymptotic_soliton_of_surgery_package package =
      package.perelmanControl.kappaSolutionAsymptoticSoliton := by
  apply Subsingleton.elim

/-- The surgery-package ancient-kappa compactness projection is stored. -/
theorem ancient_kappa_solution_compactness_of_surgery_package_eq :
    ancient_kappa_solution_compactness_of_surgery_package package =
      package.perelmanControl.ancientKappaSolutionCompactness := by
  apply Subsingleton.elim

/-- The surgery-package canonical-neighborhood scale projection is stored. -/
theorem canonical_neighborhood_scale_control_of_surgery_package_eq :
    canonical_neighborhood_scale_control_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhoodScaleControl := by
  apply Subsingleton.elim

/-- The surgery-package canonical-neighborhood stability projection is stored. -/
theorem canonical_neighborhood_stability_of_surgery_package_eq :
    canonical_neighborhood_stability_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhoodStability := by
  apply Subsingleton.elim

/-- The surgery-package cross-scale canonical-neighborhood projection is stored. -/
theorem canonical_neighborhood_persistence_across_scales_of_surgery_package_eq :
    canonical_neighborhood_persistence_across_scales_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhoodPersistenceAcrossScales := by
  apply Subsingleton.elim

/-- The surgery-package canonical-neighborhood dichotomy projection is stored. -/
theorem canonical_neighborhood_neck_cap_dichotomy_of_surgery_package_eq :
    canonical_neighborhood_neck_cap_dichotomy_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhoodNeckCapDichotomy := by
  apply Subsingleton.elim

/-- The surgery-package canonical-neighborhood classification projection is stored. -/
theorem canonical_neighborhood_classification_of_surgery_package_eq :
    canonical_neighborhood_classification_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhoodClassification := by
  apply Subsingleton.elim

/-- The surgery-package no-local-collapsing projection is stored. -/
theorem no_local_collapsing_of_surgery_package_eq :
    no_local_collapsing_of_surgery_package package =
      package.perelmanControl.noLocalCollapsing := by
  apply Subsingleton.elim

/-- The surgery-package reduced-volume projection is the stored field. -/
theorem reduced_volume_of_surgery_package_eq :
    reduced_volume_of_surgery_package package =
      package.perelmanControl.reducedVolume := by
  apply Subsingleton.elim

/-- The surgery-package canonical-neighborhood projection is the stored field. -/
theorem canonical_neighborhood_of_surgery_package_eq :
    canonical_neighborhood_of_surgery_package package =
      package.perelmanControl.canonicalNeighborhood := by
  apply Subsingleton.elim

/-- The surgery-package singularity-model projection is the stored field. -/
theorem singularity_model_classification_of_surgery_package_eq :
    singularity_model_classification_of_surgery_package package =
      package.perelmanControl.singularityModelClassification := by
  apply Subsingleton.elim

/-- The surgery-package singularity-model blowup projection is the stored field. -/
theorem singularity_model_blowup_classification_of_surgery_package_eq :
    singularity_model_blowup_classification_of_surgery_package package =
      package.perelmanControl.singularityModelBlowupClassification := by
  apply Subsingleton.elim

/-- The surgery-package aggregate Perelman-control projection is the stored field. -/
theorem perelman_singularity_control_of_surgery_package_eq :
    perelman_singularity_control_of_surgery_package package =
      package.perelmanControl.control := by
  apply Subsingleton.elim

end SurgeryPackagePerelmanProjectionEqualities

/-- A completed surgery package supplies finite fundamental-group input. -/
theorem finite_extinction_fundamental_group_input_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionFundamentalGroupInput M :=
  package.extinctionFundamentalGroupInput

/-- A completed surgery package supplies the sweepout family used by width. -/
theorem finite_extinction_sweepout_existence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutExistence M
      (finite_extinction_fundamental_group_input_of_surgery_package package) :=
  package.extinctionSweepout

/-- A completed surgery package supplies the sweepout parameter space. -/
theorem finite_extinction_sweepout_parameter_space_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutParameterSpace M
      (finite_extinction_fundamental_group_input_of_surgery_package package) :=
  package.extinctionSweepoutParameterSpace

/-- A completed surgery package supplies sweepout continuity and compactness. -/
theorem finite_extinction_sweepout_continuity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutContinuity M
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package) :=
  package.extinctionSweepoutContinuity

/-- A completed surgery package supplies uniform sweepout area bounds. -/
theorem finite_extinction_sweepout_area_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutAreaBound M
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package) :=
  package.extinctionSweepoutAreaBound

/-- A completed surgery package supplies nontriviality of the sweepout class. -/
theorem finite_extinction_sweepout_nontriviality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSweepoutNontriviality M
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package) :=
  package.extinctionSweepoutNontriviality

/-- A completed surgery package supplies the area-functional setup for width. -/
theorem finite_extinction_area_functional_setup_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionAreaFunctionalSetup
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package) :=
  package.extinctionAreaFunctional

/-- A completed surgery package supplies the min-max width definition. -/
theorem finite_extinction_minmax_width_definition_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionMinMaxWidthDefinition
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package) :=
  package.extinctionMinMaxWidth

/-- A completed surgery package supplies compactness for width-minimizing sequences. -/
theorem finite_extinction_width_compactness_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionWidthCompactness
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionWidthCompactness

/-- A completed surgery package supplies lower semicontinuity of width. -/
theorem finite_extinction_width_lower_semicontinuity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionWidthLowerSemicontinuity
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionWidthLowerSemicontinuity

/-- A completed surgery package supplies a width-minimizing sequence. -/
theorem finite_extinction_minimizing_sequence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionMinimizingSequence
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionMinimizingSequence

/-- A completed surgery package supplies the pull-tight argument. -/
theorem finite_extinction_pull_tight_argument_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionPullTightArgument
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionPullTightArgument

/-- A completed surgery package supplies stationarity of the min-max limit. -/
theorem finite_extinction_minmax_stationarity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionMinMaxStationarity
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionMinMaxStationarity

/-- A completed surgery package supplies regularity for the min-max surfaces. -/
theorem finite_extinction_min_surface_regularity_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionMinSurfaceRegularity
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionMinSurfaceRegularity

/-- A completed surgery package supplies positive-width/nontriviality input. -/
theorem finite_extinction_positive_width_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionPositiveWidth
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_fundamental_group_input_of_surgery_package package)
      (finite_extinction_sweepout_existence_of_surgery_package package)
      (finite_extinction_minmax_width_definition_of_surgery_package package) :=
  package.extinctionPositiveWidth

/-- A completed surgery package supplies the finite-extinction width theory. -/
theorem finite_extinction_width_theory_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionWidthTheory
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  package.extinctionWidthTheory

/-- A completed surgery package supplies the first-variation formula for width. -/
theorem finite_extinction_first_variation_formula_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionFirstVariationFormula
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionFirstVariationFormula

/-- A completed surgery package supplies the second-variation/stability inequality. -/
theorem finite_extinction_second_variation_inequality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSecondVariationInequality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionSecondVariationInequality

/-- A completed surgery package supplies the Gauss-Bonnet estimate for width. -/
theorem finite_extinction_gauss_bonnet_estimate_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionGaussBonnetEstimate
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionGaussBonnetEstimate

/-- A completed surgery package supplies the scalar-curvature width bound. -/
theorem finite_extinction_scalar_curvature_width_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionScalarCurvatureWidthBound
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionScalarCurvatureWidthBound

/-- A completed surgery package supplies the finite-extinction width evolution. -/
theorem finite_extinction_width_evolution_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionWidthEvolution
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionWidthEvolution

/-- A completed surgery package supplies the width differential inequality. -/
theorem finite_extinction_width_differential_inequality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionWidthDifferentialInequality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package) :=
  package.extinctionWidthDifferentialInequality

/-- A completed surgery package supplies surgery metric comparison for width. -/
theorem finite_extinction_surgery_metric_comparison_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryMetricComparison
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package) :=
  package.extinctionSurgeryMetricComparison

/-- A completed surgery package supplies the surgery width-comparison map. -/
theorem finite_extinction_surgery_width_comparison_map_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package) :=
  package.extinctionSurgeryWidthComparisonMap

/-- A completed surgery package supplies width drop/nonincrease across surgeries. -/
theorem finite_extinction_surgery_width_drop_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryWidthDrop
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package) :=
  package.extinctionSurgeryWidthDrop

/-- A completed surgery package supplies surgery/discard control for width. -/
theorem finite_extinction_surgery_discard_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryDiscardControl
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package) :=
  package.extinctionSurgeryDiscardControl

/-- A completed surgery package supplies discarded-component width neutrality. -/
theorem finite_extinction_discarded_component_width_neutrality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package)
      (finite_extinction_surgery_discard_control_of_surgery_package package) :=
  package.extinctionDiscardedComponentWidthNeutrality

/-- A completed surgery package supplies discarded-component sweepout triviality. -/
theorem finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package)
      (finite_extinction_surgery_discard_control_of_surgery_package package) :=
  package.extinctionDiscardedComponentSweepoutTriviality

/-- A completed surgery package supplies discarded-component classification. -/
theorem finite_extinction_discarded_component_classification_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionDiscardedComponentClassification
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package)
      (finite_extinction_surgery_discard_control_of_surgery_package package) :=
  package.extinctionDiscardedComponentClassification

/-- A completed surgery package supplies tracking for surviving components. -/
theorem finite_extinction_surviving_component_tracking_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurvivingComponentTracking
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package)
      (finite_extinction_surgery_discard_control_of_surgery_package package) :=
  package.extinctionSurvivingComponentTracking

/-- A completed surgery package supplies component topology control. -/
theorem finite_extinction_component_topology_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionComponentTopology
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_width_theory_of_surgery_package package)
      (finite_extinction_width_evolution_of_surgery_package package)
      (finite_extinction_surgery_discard_control_of_surgery_package package) :=
  package.extinctionComponentTopology

/-- A completed surgery package supplies finite-extinction curvature pinching. -/
theorem finite_extinction_curvature_pinching_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionCurvaturePinching
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  package.extinctionCurvaturePinching

/-- A completed surgery package supplies a scalar-curvature lower bound. -/
theorem finite_extinction_positive_scalar_curvature_lower_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionPositiveScalarCurvatureLowerBound
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package) :=
  package.extinctionPositiveScalarCurvatureLowerBound

/-- A completed surgery package supplies positive scalar curvature persistence. -/
theorem finite_extinction_positive_scalar_curvature_persistence_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionPositiveScalarCurvaturePersistence
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package) :=
  package.extinctionPositiveScalarCurvaturePersistence

/-- A completed surgery package supplies finite-extinction component control. -/
theorem finite_extinction_component_control_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionComponentControl
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package) :=
  package.extinctionComponentControl

/-- A completed surgery package supplies volume evolution on smooth intervals. -/
theorem finite_extinction_volume_evolution_formula_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionVolumeEvolutionFormula
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionVolumeEvolutionFormula

/-- A completed surgery package supplies volume nonincrease through surgery. -/
theorem finite_extinction_surgery_volume_nonincrease_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionSurgeryVolumeNonincrease

/-- A completed surgery package supplies scalar-curvature differential inequality. -/
theorem finite_extinction_scalar_curvature_differential_inequality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionScalarCurvatureDifferentialInequality

/-- A completed surgery package supplies volume differential inequality. -/
theorem finite_extinction_volume_differential_inequality_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionVolumeDifferentialInequality
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionVolumeDifferentialInequality

/-- A completed surgery package supplies the volume-decay estimate. -/
theorem finite_extinction_volume_decay_estimate_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionVolumeDecayEstimate
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionVolumeDecayEstimate

/-- A completed surgery package supplies the finite-extinction time-bound input. -/
theorem finite_extinction_time_bound_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionTimeBound
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package) :=
  package.extinctionTimeBound

/-- A completed surgery package supplies finite-time integration of the decay estimate. -/
theorem finite_extinction_finite_time_integration_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionFiniteTimeIntegration
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package)
      (finite_extinction_time_bound_of_surgery_package package) :=
  package.extinctionFiniteTimeIntegration

/-- A completed surgery package supplies surgery-time summability. -/
theorem finite_extinction_surgery_time_summability_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionSurgeryTimeSummability
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package)
      (finite_extinction_time_bound_of_surgery_package package) :=
  package.extinctionSurgeryTimeSummability

/-- A completed surgery package supplies the extinction-time contradiction step. -/
theorem finite_extinction_extinction_time_contradiction_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionExtinctionTimeContradiction
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package)
      (finite_extinction_time_bound_of_surgery_package package) :=
  package.extinctionExtinctionTimeContradiction

/-- A completed surgery package supplies differential-inequality integration. -/
theorem finite_extinction_differential_inequality_integration_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionDifferentialInequalityIntegration
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package)
      (finite_extinction_time_bound_of_surgery_package package) :=
  package.extinctionDifferentialInequalityIntegration

/--
A completed surgery package supplies the derivation of finite extinction from
flow, surgery, and singularity-control inputs.
-/
theorem finite_extinction_derivation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionDerivation
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  package.extinctionDerivation

/--
Any completed surgery package provides the finite-extinction evidence needed by
the existing Poincare assembly interface.
-/
theorem finite_extinction_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  package.finiteExtinction

/-- The named finite-extinction projection is the stored package field. -/
theorem finite_extinction_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_of_surgery_package package = package.finiteExtinction :=
  rfl

/--
A completed surgery package supplies the derivation certificate tying the named
finite-extinction inputs to its extinction conclusion.
-/
theorem finite_extinction_conclusion_derivation_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    HasFiniteExtinctionConclusionDerivation
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_curvature_pinching_of_surgery_package package)
      (finite_extinction_component_control_of_surgery_package package)
      (finite_extinction_time_bound_of_surgery_package package)
      (finite_extinction_derivation_of_surgery_package package)
      (finite_extinction_of_surgery_package package) :=
  package.extinctionConclusionDerivation

/--
A completed surgery package assembles the fixed-flow finite-extinction
conclusion statement for its projected extinction proof.
-/
theorem finite_extinction_conclusion_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionConclusionStatement
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package)
      (finite_extinction_of_surgery_package package) :=
  finite_extinction_conclusion_statement_of_components
    (ricci_flow_data_of_surgery_package package)
    (ricci_flow_with_surgery_of_surgery_package package)
    (perelman_singularity_control_of_surgery_package package)
    (finite_extinction_of_surgery_package package)
    (finite_extinction_fundamental_group_input_of_surgery_package package)
    (finite_extinction_sweepout_existence_of_surgery_package package)
    (finite_extinction_width_theory_of_surgery_package package)
    (finite_extinction_width_evolution_of_surgery_package package)
    (finite_extinction_surgery_discard_control_of_surgery_package package)
    (finite_extinction_curvature_pinching_of_surgery_package package)
    (finite_extinction_component_control_of_surgery_package package)
    (finite_extinction_time_bound_of_surgery_package package)
    (finite_extinction_derivation_of_surgery_package package)
    (finite_extinction_conclusion_derivation_of_surgery_package package)

/--
The completed surgery package route to the fixed-flow finite-extinction
conclusion statement is exactly the component assembly route applied to the
package projections.
-/
theorem finite_extinction_conclusion_statement_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_conclusion_statement_of_surgery_package package =
      finite_extinction_conclusion_statement_of_components
        (ricci_flow_data_of_surgery_package package)
        (ricci_flow_with_surgery_of_surgery_package package)
        (perelman_singularity_control_of_surgery_package package)
        (finite_extinction_of_surgery_package package)
        (finite_extinction_fundamental_group_input_of_surgery_package package)
        (finite_extinction_sweepout_existence_of_surgery_package package)
        (finite_extinction_width_theory_of_surgery_package package)
        (finite_extinction_width_evolution_of_surgery_package package)
        (finite_extinction_surgery_discard_control_of_surgery_package package)
        (finite_extinction_curvature_pinching_of_surgery_package package)
        (finite_extinction_component_control_of_surgery_package package)
        (finite_extinction_time_bound_of_surgery_package package)
        (finite_extinction_derivation_of_surgery_package package)
        (finite_extinction_conclusion_derivation_of_surgery_package package) := by
  apply Subsingleton.elim

/--
A completed surgery package supplies the theorem-shaped finite-extinction
statement.
-/
theorem finite_extinction_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionStatement n M :=
  ⟨ricci_flow_data_of_surgery_package package,
    ricci_flow_with_surgery_of_surgery_package package,
    perelman_singularity_control_of_surgery_package package,
    finite_extinction_of_surgery_package package,
    finite_extinction_conclusion_statement_of_surgery_package package⟩

/--
The completed surgery package route to the theorem-shaped finite-extinction
statement is exactly the bundled statement built from the package projections.
-/
theorem finite_extinction_statement_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_statement_of_surgery_package package =
      ⟨ricci_flow_data_of_surgery_package package,
        ricci_flow_with_surgery_of_surgery_package package,
        perelman_singularity_control_of_surgery_package package,
        finite_extinction_of_surgery_package package,
        finite_extinction_conclusion_statement_of_surgery_package package⟩ := by
  apply Subsingleton.elim

/--
The theorem-shaped finite-extinction statement exposes its fixed-flow
conclusion statement payload.
-/
theorem finite_extinction_conclusion_statement_of_finite_extinction_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (statement : FiniteExtinctionStatement n M) :
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
      FiniteExtinctionConclusionStatement
        flow surgery control finiteExtinction := by
  rcases statement with
    ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩
  exact ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩

/--
The theorem-shaped finite-extinction statement exposes exactly its stored
fixed-flow conclusion statement payload.
-/
theorem finite_extinction_conclusion_statement_of_finite_extinction_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (statement : FiniteExtinctionStatement n M) :
    finite_extinction_conclusion_statement_of_finite_extinction_statement
        statement =
      (by
        rcases statement with
          ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩
        exact ⟨flow, surgery, control, finiteExtinction,
          conclusionStatement⟩) := by
  apply Subsingleton.elim

/--
The theorem-shaped finite-extinction statement supplies the existing
finite-extinction interface.
-/
theorem finite_extinction_of_finite_extinction_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (statement : FiniteExtinctionStatement n M) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_conclusion_statement_of_finite_extinction_statement
      statement with
    ⟨_flow, _surgery, _control, finiteExtinction, _conclusionStatement⟩
  exact finiteExtinction

/--
The finite-extinction witness extracted from a theorem-shaped statement is
exactly the finite-extinction component exposed by its conclusion payload.
-/
theorem finite_extinction_of_finite_extinction_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (statement : FiniteExtinctionStatement n M) :
    finite_extinction_of_finite_extinction_statement statement =
      (by
        rcases finite_extinction_conclusion_statement_of_finite_extinction_statement
            statement with
          ⟨_flow, _surgery, _control, finiteExtinction,
            _conclusionStatement⟩
        exact finiteExtinction) := by
  apply Subsingleton.elim

/--
Statement-mediated projection of finite extinction from a completed surgery
package.
-/
theorem finite_extinction_via_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  finite_extinction_of_finite_extinction_statement
    (finite_extinction_statement_of_surgery_package package)

/--
The statement-mediated finite-extinction projection from a completed surgery
package is exactly finite-extinction extraction from the package statement.
-/
theorem finite_extinction_via_statement_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_via_statement_of_surgery_package package =
      finite_extinction_of_finite_extinction_statement
        (finite_extinction_statement_of_surgery_package package) := by
  apply Subsingleton.elim

/--
The fixed-flow finite-extinction width statement: the sweepout, min-max width,
width evolution, surgery comparison, discard-control, and component topology
inputs used before the final extinction derivation.
-/
def FiniteExtinctionWidthSubobligationsStatement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    Prop :=
  ∃ _finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
  ∃ sweepout :
    HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
  ∃ _sweepoutParameterSpace :
    HasFiniteExtinctionSweepoutParameterSpace M _finiteFundamentalGroup,
  ∃ _sweepoutContinuity :
    HasFiniteExtinctionSweepoutContinuity
      M _finiteFundamentalGroup sweepout,
  ∃ _sweepoutAreaBound :
    HasFiniteExtinctionSweepoutAreaBound
      M _finiteFundamentalGroup sweepout,
  ∃ _sweepoutNontriviality :
    HasFiniteExtinctionSweepoutNontriviality
      M _finiteFundamentalGroup sweepout,
  ∃ _areaFunctional :
    HasFiniteExtinctionAreaFunctionalSetup
      flow surgery control _finiteFundamentalGroup sweepout,
  ∃ widthDefinition :
    HasFiniteExtinctionMinMaxWidthDefinition
      flow surgery control _finiteFundamentalGroup sweepout,
  ∃ _widthCompactness :
    HasFiniteExtinctionWidthCompactness
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _positiveWidth :
    HasFiniteExtinctionPositiveWidth
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
  ∃ _firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      flow surgery control widthTheory,
  ∃ _secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      flow surgery control widthTheory,
  ∃ _gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      flow surgery control widthTheory,
  ∃ _scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      flow surgery control widthTheory,
  ∃ widthEvolution :
    HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
  ∃ _widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      flow surgery control widthTheory,
  ∃ _surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      flow surgery control widthTheory widthEvolution,
  ∃ _surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      flow surgery control widthTheory widthEvolution,
  ∃ _surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      flow surgery control widthTheory widthEvolution,
  ∃ surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      flow surgery control widthTheory widthEvolution,
  ∃ _discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    HasFiniteExtinctionComponentTopology
      flow surgery control widthTheory widthEvolution surgeryDiscardControl

/--
The fixed-flow finite-extinction width sub-obligation statement is exactly the
listed sweepout, min-max width, width evolution, surgery comparison,
discard-control, and component-topology witness stack.
-/
theorem finiteExtinctionWidthSubobligationsStatement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    FiniteExtinctionWidthSubobligationsStatement flow surgery control =
      (∃ _finiteFundamentalGroup :
        HasFiniteExtinctionFundamentalGroupInput M,
      ∃ sweepout :
        HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
      ∃ _sweepoutParameterSpace :
        HasFiniteExtinctionSweepoutParameterSpace M _finiteFundamentalGroup,
      ∃ _sweepoutContinuity :
        HasFiniteExtinctionSweepoutContinuity
          M _finiteFundamentalGroup sweepout,
      ∃ _sweepoutAreaBound :
        HasFiniteExtinctionSweepoutAreaBound
          M _finiteFundamentalGroup sweepout,
      ∃ _sweepoutNontriviality :
        HasFiniteExtinctionSweepoutNontriviality
          M _finiteFundamentalGroup sweepout,
      ∃ _areaFunctional :
        HasFiniteExtinctionAreaFunctionalSetup
          flow surgery control _finiteFundamentalGroup sweepout,
      ∃ widthDefinition :
        HasFiniteExtinctionMinMaxWidthDefinition
          flow surgery control _finiteFundamentalGroup sweepout,
      ∃ _widthCompactness :
        HasFiniteExtinctionWidthCompactness
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _widthLowerSemicontinuity :
        HasFiniteExtinctionWidthLowerSemicontinuity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minimizingSequence :
        HasFiniteExtinctionMinimizingSequence
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _pullTightArgument :
        HasFiniteExtinctionPullTightArgument
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minMaxStationarity :
        HasFiniteExtinctionMinMaxStationarity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minSurfaceRegularity :
        HasFiniteExtinctionMinSurfaceRegularity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _positiveWidth :
        HasFiniteExtinctionPositiveWidth
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
      ∃ _firstVariationFormula :
        HasFiniteExtinctionFirstVariationFormula
          flow surgery control widthTheory,
      ∃ _secondVariationInequality :
        HasFiniteExtinctionSecondVariationInequality
          flow surgery control widthTheory,
      ∃ _gaussBonnetEstimate :
        HasFiniteExtinctionGaussBonnetEstimate
          flow surgery control widthTheory,
      ∃ _scalarCurvatureWidthBound :
        HasFiniteExtinctionScalarCurvatureWidthBound
          flow surgery control widthTheory,
      ∃ widthEvolution :
        HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
      ∃ _widthDifferentialInequality :
        HasFiniteExtinctionWidthDifferentialInequality
          flow surgery control widthTheory,
      ∃ _surgeryMetricComparison :
        HasFiniteExtinctionSurgeryMetricComparison
          flow surgery control widthTheory widthEvolution,
      ∃ _surgeryWidthComparisonMap :
        HasFiniteExtinctionSurgeryWidthComparisonMap
          flow surgery control widthTheory widthEvolution,
      ∃ _surgeryWidthDrop :
        HasFiniteExtinctionSurgeryWidthDrop
          flow surgery control widthTheory widthEvolution,
      ∃ surgeryDiscardControl :
        HasFiniteExtinctionSurgeryDiscardControl
          flow surgery control widthTheory widthEvolution,
      ∃ _discardedComponentWidthNeutrality :
        HasFiniteExtinctionDiscardedComponentWidthNeutrality
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _discardedComponentSweepoutTriviality :
        HasFiniteExtinctionDiscardedComponentSweepoutTriviality
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _discardedComponentClassification :
        HasFiniteExtinctionDiscardedComponentClassification
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _survivingComponentTracking :
        HasFiniteExtinctionSurvivingComponentTracking
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
        HasFiniteExtinctionComponentTopology
          flow surgery control widthTheory widthEvolution
          surgeryDiscardControl) :=
  rfl

/--
The fixed-flow finite-extinction full sub-obligation statement: the complete
width, curvature, volume-decay, derivation, extinction, and conclusion
certificate stack.
-/
def FiniteExtinctionSubobligationsStatement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    Prop :=
  ∃ _finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
  ∃ sweepout :
    HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
  ∃ _sweepoutParameterSpace :
    HasFiniteExtinctionSweepoutParameterSpace M _finiteFundamentalGroup,
  ∃ _sweepoutContinuity :
    HasFiniteExtinctionSweepoutContinuity
      M _finiteFundamentalGroup sweepout,
  ∃ _sweepoutAreaBound :
    HasFiniteExtinctionSweepoutAreaBound
      M _finiteFundamentalGroup sweepout,
  ∃ _sweepoutNontriviality :
    HasFiniteExtinctionSweepoutNontriviality
      M _finiteFundamentalGroup sweepout,
  ∃ _areaFunctional :
    HasFiniteExtinctionAreaFunctionalSetup
      flow surgery control _finiteFundamentalGroup sweepout,
  ∃ widthDefinition :
    HasFiniteExtinctionMinMaxWidthDefinition
      flow surgery control _finiteFundamentalGroup sweepout,
  ∃ _widthCompactness :
    HasFiniteExtinctionWidthCompactness
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _widthLowerSemicontinuity :
    HasFiniteExtinctionWidthLowerSemicontinuity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minimizingSequence :
    HasFiniteExtinctionMinimizingSequence
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _pullTightArgument :
    HasFiniteExtinctionPullTightArgument
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minMaxStationarity :
    HasFiniteExtinctionMinMaxStationarity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _minSurfaceRegularity :
    HasFiniteExtinctionMinSurfaceRegularity
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ _positiveWidth :
    HasFiniteExtinctionPositiveWidth
      flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
  ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
  ∃ _firstVariationFormula :
    HasFiniteExtinctionFirstVariationFormula
      flow surgery control widthTheory,
  ∃ _secondVariationInequality :
    HasFiniteExtinctionSecondVariationInequality
      flow surgery control widthTheory,
  ∃ _gaussBonnetEstimate :
    HasFiniteExtinctionGaussBonnetEstimate
      flow surgery control widthTheory,
  ∃ _scalarCurvatureWidthBound :
    HasFiniteExtinctionScalarCurvatureWidthBound
      flow surgery control widthTheory,
  ∃ widthEvolution :
    HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
  ∃ _widthDifferentialInequality :
    HasFiniteExtinctionWidthDifferentialInequality
      flow surgery control widthTheory,
  ∃ _surgeryMetricComparison :
    HasFiniteExtinctionSurgeryMetricComparison
      flow surgery control widthTheory widthEvolution,
  ∃ _surgeryWidthComparisonMap :
    HasFiniteExtinctionSurgeryWidthComparisonMap
      flow surgery control widthTheory widthEvolution,
  ∃ _surgeryWidthDrop :
    HasFiniteExtinctionSurgeryWidthDrop
      flow surgery control widthTheory widthEvolution,
  ∃ surgeryDiscardControl :
    HasFiniteExtinctionSurgeryDiscardControl
      flow surgery control widthTheory widthEvolution,
  ∃ _discardedComponentWidthNeutrality :
    HasFiniteExtinctionDiscardedComponentWidthNeutrality
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _discardedComponentSweepoutTriviality :
    HasFiniteExtinctionDiscardedComponentSweepoutTriviality
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _discardedComponentClassification :
    HasFiniteExtinctionDiscardedComponentClassification
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _survivingComponentTracking :
    HasFiniteExtinctionSurvivingComponentTracking
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ _componentTopology :
    HasFiniteExtinctionComponentTopology
      flow surgery control widthTheory widthEvolution surgeryDiscardControl,
  ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
  ∃ _positiveScalarCurvatureLowerBound :
    HasFiniteExtinctionPositiveScalarCurvatureLowerBound
      flow surgery control pinching,
  ∃ _positiveScalarCurvaturePersistence :
    HasFiniteExtinctionPositiveScalarCurvaturePersistence
      flow surgery control pinching,
  ∃ componentControl :
    HasFiniteExtinctionComponentControl flow surgery control pinching,
  ∃ _volumeEvolutionFormula :
    HasFiniteExtinctionVolumeEvolutionFormula
      flow surgery control pinching componentControl,
  ∃ _surgeryVolumeNonincrease :
    HasFiniteExtinctionSurgeryVolumeNonincrease
      flow surgery control pinching componentControl,
  ∃ _scalarCurvatureDifferentialInequality :
    HasFiniteExtinctionScalarCurvatureDifferentialInequality
      flow surgery control pinching componentControl,
  ∃ _volumeDifferentialInequality :
    HasFiniteExtinctionVolumeDifferentialInequality
      flow surgery control pinching componentControl,
  ∃ _volumeDecayEstimate :
    HasFiniteExtinctionVolumeDecayEstimate
      flow surgery control pinching componentControl,
  ∃ timeBound :
    HasFiniteExtinctionTimeBound
      flow surgery control pinching componentControl,
  ∃ _differentialInequalityIntegration :
    HasFiniteExtinctionDifferentialInequalityIntegration
      flow surgery control pinching componentControl timeBound,
  ∃ _finiteTimeIntegration :
    HasFiniteExtinctionFiniteTimeIntegration
      flow surgery control pinching componentControl timeBound,
  ∃ _surgeryTimeSummability :
    HasFiniteExtinctionSurgeryTimeSummability
      flow surgery control pinching componentControl timeBound,
  ∃ _extinctionTimeContradiction :
    HasFiniteExtinctionExtinctionTimeContradiction
      flow surgery control pinching componentControl timeBound,
  ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
  ∃ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
    HasFiniteExtinctionConclusionDerivation
      flow surgery control pinching componentControl timeBound derivation
      extinction

/--
The fixed-flow finite-extinction full sub-obligation statement is exactly the
listed width, curvature, volume-decay, derivation, extinction, and
conclusion-derivation witness stack.
-/
theorem finiteExtinctionSubobligationsStatement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    FiniteExtinctionSubobligationsStatement flow surgery control =
      (∃ _finiteFundamentalGroup :
        HasFiniteExtinctionFundamentalGroupInput M,
      ∃ sweepout :
        HasFiniteExtinctionSweepoutExistence M _finiteFundamentalGroup,
      ∃ _sweepoutParameterSpace :
        HasFiniteExtinctionSweepoutParameterSpace M _finiteFundamentalGroup,
      ∃ _sweepoutContinuity :
        HasFiniteExtinctionSweepoutContinuity
          M _finiteFundamentalGroup sweepout,
      ∃ _sweepoutAreaBound :
        HasFiniteExtinctionSweepoutAreaBound
          M _finiteFundamentalGroup sweepout,
      ∃ _sweepoutNontriviality :
        HasFiniteExtinctionSweepoutNontriviality
          M _finiteFundamentalGroup sweepout,
      ∃ _areaFunctional :
        HasFiniteExtinctionAreaFunctionalSetup
          flow surgery control _finiteFundamentalGroup sweepout,
      ∃ widthDefinition :
        HasFiniteExtinctionMinMaxWidthDefinition
          flow surgery control _finiteFundamentalGroup sweepout,
      ∃ _widthCompactness :
        HasFiniteExtinctionWidthCompactness
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _widthLowerSemicontinuity :
        HasFiniteExtinctionWidthLowerSemicontinuity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minimizingSequence :
        HasFiniteExtinctionMinimizingSequence
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _pullTightArgument :
        HasFiniteExtinctionPullTightArgument
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minMaxStationarity :
        HasFiniteExtinctionMinMaxStationarity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _minSurfaceRegularity :
        HasFiniteExtinctionMinSurfaceRegularity
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ _positiveWidth :
        HasFiniteExtinctionPositiveWidth
          flow surgery control _finiteFundamentalGroup sweepout widthDefinition,
      ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
      ∃ _firstVariationFormula :
        HasFiniteExtinctionFirstVariationFormula
          flow surgery control widthTheory,
      ∃ _secondVariationInequality :
        HasFiniteExtinctionSecondVariationInequality
          flow surgery control widthTheory,
      ∃ _gaussBonnetEstimate :
        HasFiniteExtinctionGaussBonnetEstimate
          flow surgery control widthTheory,
      ∃ _scalarCurvatureWidthBound :
        HasFiniteExtinctionScalarCurvatureWidthBound
          flow surgery control widthTheory,
      ∃ widthEvolution :
        HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
      ∃ _widthDifferentialInequality :
        HasFiniteExtinctionWidthDifferentialInequality
          flow surgery control widthTheory,
      ∃ _surgeryMetricComparison :
        HasFiniteExtinctionSurgeryMetricComparison
          flow surgery control widthTheory widthEvolution,
      ∃ _surgeryWidthComparisonMap :
        HasFiniteExtinctionSurgeryWidthComparisonMap
          flow surgery control widthTheory widthEvolution,
      ∃ _surgeryWidthDrop :
        HasFiniteExtinctionSurgeryWidthDrop
          flow surgery control widthTheory widthEvolution,
      ∃ surgeryDiscardControl :
        HasFiniteExtinctionSurgeryDiscardControl
          flow surgery control widthTheory widthEvolution,
      ∃ _discardedComponentWidthNeutrality :
        HasFiniteExtinctionDiscardedComponentWidthNeutrality
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _discardedComponentSweepoutTriviality :
        HasFiniteExtinctionDiscardedComponentSweepoutTriviality
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _discardedComponentClassification :
        HasFiniteExtinctionDiscardedComponentClassification
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _survivingComponentTracking :
        HasFiniteExtinctionSurvivingComponentTracking
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ _componentTopology :
        HasFiniteExtinctionComponentTopology
          flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
      ∃ _positiveScalarCurvatureLowerBound :
        HasFiniteExtinctionPositiveScalarCurvatureLowerBound
          flow surgery control pinching,
      ∃ _positiveScalarCurvaturePersistence :
        HasFiniteExtinctionPositiveScalarCurvaturePersistence
          flow surgery control pinching,
      ∃ componentControl :
        HasFiniteExtinctionComponentControl flow surgery control pinching,
      ∃ _volumeEvolutionFormula :
        HasFiniteExtinctionVolumeEvolutionFormula
          flow surgery control pinching componentControl,
      ∃ _surgeryVolumeNonincrease :
        HasFiniteExtinctionSurgeryVolumeNonincrease
          flow surgery control pinching componentControl,
      ∃ _scalarCurvatureDifferentialInequality :
        HasFiniteExtinctionScalarCurvatureDifferentialInequality
          flow surgery control pinching componentControl,
      ∃ _volumeDifferentialInequality :
        HasFiniteExtinctionVolumeDifferentialInequality
          flow surgery control pinching componentControl,
      ∃ _volumeDecayEstimate :
        HasFiniteExtinctionVolumeDecayEstimate
          flow surgery control pinching componentControl,
      ∃ timeBound :
        HasFiniteExtinctionTimeBound
          flow surgery control pinching componentControl,
      ∃ _differentialInequalityIntegration :
        HasFiniteExtinctionDifferentialInequalityIntegration
          flow surgery control pinching componentControl timeBound,
      ∃ _finiteTimeIntegration :
        HasFiniteExtinctionFiniteTimeIntegration
          flow surgery control pinching componentControl timeBound,
      ∃ _surgeryTimeSummability :
        HasFiniteExtinctionSurgeryTimeSummability
          flow surgery control pinching componentControl timeBound,
      ∃ _extinctionTimeContradiction :
        HasFiniteExtinctionExtinctionTimeContradiction
          flow surgery control pinching componentControl timeBound,
      ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
      ∃ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
        HasFiniteExtinctionConclusionDerivation
          flow surgery control pinching componentControl timeBound derivation
          extinction) :=
  rfl

/--
A completed surgery package assembles the theorem-shaped finite-extinction
width sub-obligation statement.
-/
theorem finite_extinction_width_subobligations_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionWidthSubobligationsStatement
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  ⟨finite_extinction_fundamental_group_input_of_surgery_package package,
    finite_extinction_sweepout_existence_of_surgery_package package,
    finite_extinction_sweepout_parameter_space_of_surgery_package package,
    finite_extinction_sweepout_continuity_of_surgery_package package,
    finite_extinction_sweepout_area_bound_of_surgery_package package,
    finite_extinction_sweepout_nontriviality_of_surgery_package package,
    finite_extinction_area_functional_setup_of_surgery_package package,
    finite_extinction_minmax_width_definition_of_surgery_package package,
    finite_extinction_width_compactness_of_surgery_package package,
    finite_extinction_width_lower_semicontinuity_of_surgery_package package,
    finite_extinction_minimizing_sequence_of_surgery_package package,
    finite_extinction_pull_tight_argument_of_surgery_package package,
    finite_extinction_minmax_stationarity_of_surgery_package package,
    finite_extinction_min_surface_regularity_of_surgery_package package,
    finite_extinction_positive_width_of_surgery_package package,
    finite_extinction_width_theory_of_surgery_package package,
    finite_extinction_first_variation_formula_of_surgery_package package,
    finite_extinction_second_variation_inequality_of_surgery_package package,
    finite_extinction_gauss_bonnet_estimate_of_surgery_package package,
    finite_extinction_scalar_curvature_width_bound_of_surgery_package package,
    finite_extinction_width_evolution_of_surgery_package package,
    finite_extinction_width_differential_inequality_of_surgery_package package,
    finite_extinction_surgery_metric_comparison_of_surgery_package package,
    finite_extinction_surgery_width_comparison_map_of_surgery_package package,
    finite_extinction_surgery_width_drop_of_surgery_package package,
    finite_extinction_surgery_discard_control_of_surgery_package package,
    finite_extinction_discarded_component_width_neutrality_of_surgery_package
      package,
    finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
      package,
    finite_extinction_discarded_component_classification_of_surgery_package
      package,
    finite_extinction_surviving_component_tracking_of_surgery_package package,
    finite_extinction_component_topology_of_surgery_package package⟩

/--
The completed surgery package route to the theorem-shaped finite-extinction
width sub-obligation statement is exactly the bundled package projections.
-/
theorem finite_extinction_width_subobligations_statement_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_width_subobligations_statement_of_surgery_package
        package =
      ⟨finite_extinction_fundamental_group_input_of_surgery_package package,
        finite_extinction_sweepout_existence_of_surgery_package package,
        finite_extinction_sweepout_parameter_space_of_surgery_package package,
        finite_extinction_sweepout_continuity_of_surgery_package package,
        finite_extinction_sweepout_area_bound_of_surgery_package package,
        finite_extinction_sweepout_nontriviality_of_surgery_package package,
        finite_extinction_area_functional_setup_of_surgery_package package,
        finite_extinction_minmax_width_definition_of_surgery_package package,
        finite_extinction_width_compactness_of_surgery_package package,
        finite_extinction_width_lower_semicontinuity_of_surgery_package package,
        finite_extinction_minimizing_sequence_of_surgery_package package,
        finite_extinction_pull_tight_argument_of_surgery_package package,
        finite_extinction_minmax_stationarity_of_surgery_package package,
        finite_extinction_min_surface_regularity_of_surgery_package package,
        finite_extinction_positive_width_of_surgery_package package,
        finite_extinction_width_theory_of_surgery_package package,
        finite_extinction_first_variation_formula_of_surgery_package package,
        finite_extinction_second_variation_inequality_of_surgery_package package,
        finite_extinction_gauss_bonnet_estimate_of_surgery_package package,
        finite_extinction_scalar_curvature_width_bound_of_surgery_package
          package,
        finite_extinction_width_evolution_of_surgery_package package,
        finite_extinction_width_differential_inequality_of_surgery_package
          package,
        finite_extinction_surgery_metric_comparison_of_surgery_package package,
        finite_extinction_surgery_width_comparison_map_of_surgery_package
          package,
        finite_extinction_surgery_width_drop_of_surgery_package package,
        finite_extinction_surgery_discard_control_of_surgery_package package,
        finite_extinction_discarded_component_width_neutrality_of_surgery_package
          package,
        finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
          package,
        finite_extinction_discarded_component_classification_of_surgery_package
          package,
        finite_extinction_surviving_component_tracking_of_surgery_package
          package,
        finite_extinction_component_topology_of_surgery_package package⟩ := by
  apply Subsingleton.elim

/--
A completed surgery package assembles the theorem-shaped finite-extinction full
sub-obligation statement.
-/
theorem finite_extinction_subobligations_statement_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionSubobligationsStatement
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  ⟨finite_extinction_fundamental_group_input_of_surgery_package package,
    finite_extinction_sweepout_existence_of_surgery_package package,
    finite_extinction_sweepout_parameter_space_of_surgery_package package,
    finite_extinction_sweepout_continuity_of_surgery_package package,
    finite_extinction_sweepout_area_bound_of_surgery_package package,
    finite_extinction_sweepout_nontriviality_of_surgery_package package,
    finite_extinction_area_functional_setup_of_surgery_package package,
    finite_extinction_minmax_width_definition_of_surgery_package package,
    finite_extinction_width_compactness_of_surgery_package package,
    finite_extinction_width_lower_semicontinuity_of_surgery_package package,
    finite_extinction_minimizing_sequence_of_surgery_package package,
    finite_extinction_pull_tight_argument_of_surgery_package package,
    finite_extinction_minmax_stationarity_of_surgery_package package,
    finite_extinction_min_surface_regularity_of_surgery_package package,
    finite_extinction_positive_width_of_surgery_package package,
    finite_extinction_width_theory_of_surgery_package package,
    finite_extinction_first_variation_formula_of_surgery_package package,
    finite_extinction_second_variation_inequality_of_surgery_package package,
    finite_extinction_gauss_bonnet_estimate_of_surgery_package package,
    finite_extinction_scalar_curvature_width_bound_of_surgery_package package,
    finite_extinction_width_evolution_of_surgery_package package,
    finite_extinction_width_differential_inequality_of_surgery_package package,
    finite_extinction_surgery_metric_comparison_of_surgery_package package,
    finite_extinction_surgery_width_comparison_map_of_surgery_package package,
    finite_extinction_surgery_width_drop_of_surgery_package package,
    finite_extinction_surgery_discard_control_of_surgery_package package,
    finite_extinction_discarded_component_width_neutrality_of_surgery_package
      package,
    finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
      package,
    finite_extinction_discarded_component_classification_of_surgery_package
      package,
    finite_extinction_surviving_component_tracking_of_surgery_package package,
    finite_extinction_component_topology_of_surgery_package package,
    finite_extinction_curvature_pinching_of_surgery_package package,
    finite_extinction_positive_scalar_curvature_lower_bound_of_surgery_package
      package,
    finite_extinction_positive_scalar_curvature_persistence_of_surgery_package
      package,
    finite_extinction_component_control_of_surgery_package package,
    finite_extinction_volume_evolution_formula_of_surgery_package package,
    finite_extinction_surgery_volume_nonincrease_of_surgery_package package,
    finite_extinction_scalar_curvature_differential_inequality_of_surgery_package
      package,
    finite_extinction_volume_differential_inequality_of_surgery_package package,
    finite_extinction_volume_decay_estimate_of_surgery_package package,
    finite_extinction_time_bound_of_surgery_package package,
    finite_extinction_differential_inequality_integration_of_surgery_package
      package,
    finite_extinction_finite_time_integration_of_surgery_package package,
    finite_extinction_surgery_time_summability_of_surgery_package package,
    finite_extinction_extinction_time_contradiction_of_surgery_package package,
    finite_extinction_derivation_of_surgery_package package,
    finite_extinction_of_surgery_package package,
    finite_extinction_conclusion_derivation_of_surgery_package package⟩

/--
The completed surgery package route to the theorem-shaped finite-extinction
full sub-obligation statement is exactly the bundled package projections.
-/
theorem finite_extinction_subobligations_statement_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_subobligations_statement_of_surgery_package package =
      ⟨finite_extinction_fundamental_group_input_of_surgery_package package,
        finite_extinction_sweepout_existence_of_surgery_package package,
        finite_extinction_sweepout_parameter_space_of_surgery_package package,
        finite_extinction_sweepout_continuity_of_surgery_package package,
        finite_extinction_sweepout_area_bound_of_surgery_package package,
        finite_extinction_sweepout_nontriviality_of_surgery_package package,
        finite_extinction_area_functional_setup_of_surgery_package package,
        finite_extinction_minmax_width_definition_of_surgery_package package,
        finite_extinction_width_compactness_of_surgery_package package,
        finite_extinction_width_lower_semicontinuity_of_surgery_package package,
        finite_extinction_minimizing_sequence_of_surgery_package package,
        finite_extinction_pull_tight_argument_of_surgery_package package,
        finite_extinction_minmax_stationarity_of_surgery_package package,
        finite_extinction_min_surface_regularity_of_surgery_package package,
        finite_extinction_positive_width_of_surgery_package package,
        finite_extinction_width_theory_of_surgery_package package,
        finite_extinction_first_variation_formula_of_surgery_package package,
        finite_extinction_second_variation_inequality_of_surgery_package package,
        finite_extinction_gauss_bonnet_estimate_of_surgery_package package,
        finite_extinction_scalar_curvature_width_bound_of_surgery_package
          package,
        finite_extinction_width_evolution_of_surgery_package package,
        finite_extinction_width_differential_inequality_of_surgery_package
          package,
        finite_extinction_surgery_metric_comparison_of_surgery_package package,
        finite_extinction_surgery_width_comparison_map_of_surgery_package
          package,
        finite_extinction_surgery_width_drop_of_surgery_package package,
        finite_extinction_surgery_discard_control_of_surgery_package package,
        finite_extinction_discarded_component_width_neutrality_of_surgery_package
          package,
        finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
          package,
        finite_extinction_discarded_component_classification_of_surgery_package
          package,
        finite_extinction_surviving_component_tracking_of_surgery_package
          package,
        finite_extinction_component_topology_of_surgery_package package,
        finite_extinction_curvature_pinching_of_surgery_package package,
        finite_extinction_positive_scalar_curvature_lower_bound_of_surgery_package
          package,
        finite_extinction_positive_scalar_curvature_persistence_of_surgery_package
          package,
        finite_extinction_component_control_of_surgery_package package,
        finite_extinction_volume_evolution_formula_of_surgery_package package,
        finite_extinction_surgery_volume_nonincrease_of_surgery_package package,
        finite_extinction_scalar_curvature_differential_inequality_of_surgery_package
          package,
        finite_extinction_volume_differential_inequality_of_surgery_package
          package,
        finite_extinction_volume_decay_estimate_of_surgery_package package,
        finite_extinction_time_bound_of_surgery_package package,
        finite_extinction_differential_inequality_integration_of_surgery_package
          package,
        finite_extinction_finite_time_integration_of_surgery_package package,
        finite_extinction_surgery_time_summability_of_surgery_package package,
        finite_extinction_extinction_time_contradiction_of_surgery_package
          package,
        finite_extinction_derivation_of_surgery_package package,
        finite_extinction_of_surgery_package package,
        finite_extinction_conclusion_derivation_of_surgery_package package⟩ := by
  apply Subsingleton.elim

/--
Semantic alias for the width-analysis sub-obligation payload exposed by a
theorem-shaped finite-extinction width statement.
-/
abbrev FiniteExtinctionWidthSubobligationsPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    Prop :=
  FiniteExtinctionWidthSubobligationsStatement flow surgery control

/--
The width-analysis payload alias is definitionally the theorem-shaped
finite-extinction width sub-obligation statement for the fixed flow, surgery
witness, and Perelman control witness.
-/
theorem finiteExtinctionWidthSubobligationsPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    FiniteExtinctionWidthSubobligationsPayload flow surgery control =
      FiniteExtinctionWidthSubobligationsStatement flow surgery control :=
  rfl

/--
Semantic alias for the full finite-extinction sub-obligation payload exposed by
a theorem-shaped finite-extinction full statement.
-/
abbrev FiniteExtinctionSubobligationsPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    Prop :=
  FiniteExtinctionSubobligationsStatement flow surgery control

/--
The full finite-extinction payload alias is definitionally the theorem-shaped
finite-extinction full sub-obligation statement for the fixed flow, surgery
witness, and Perelman control witness.
-/
theorem finiteExtinctionSubobligationsPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (flow : RicciFlowData ThreeManifoldModelWithCorners n M)
    (surgery : HasRicciFlowWithSurgery n M)
    (control : HasPerelmanSingularityControl (n := n) (M := M) flow) :
    FiniteExtinctionSubobligationsPayload flow surgery control =
      FiniteExtinctionSubobligationsStatement flow surgery control :=
  rfl

/-- The width statement exposes the named width/surgery-discard sub-obligations. -/
theorem finite_extinction_width_subobligations_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement :
      FiniteExtinctionWidthSubobligationsStatement flow surgery control) :
    ∃ finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
    ∃ sweepout :
      HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup,
    ∃ _sweepoutParameterSpace :
      HasFiniteExtinctionSweepoutParameterSpace M finiteFundamentalGroup,
    ∃ _sweepoutContinuity :
      HasFiniteExtinctionSweepoutContinuity M finiteFundamentalGroup sweepout,
    ∃ _sweepoutAreaBound :
      HasFiniteExtinctionSweepoutAreaBound M finiteFundamentalGroup sweepout,
    ∃ _sweepoutNontriviality :
      HasFiniteExtinctionSweepoutNontriviality M finiteFundamentalGroup sweepout,
    ∃ _areaFunctional :
      HasFiniteExtinctionAreaFunctionalSetup
        flow surgery control finiteFundamentalGroup sweepout,
    ∃ widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition
        flow surgery control finiteFundamentalGroup sweepout,
    ∃ _widthCompactness :
      HasFiniteExtinctionWidthCompactness
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _widthLowerSemicontinuity :
      HasFiniteExtinctionWidthLowerSemicontinuity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minimizingSequence :
      HasFiniteExtinctionMinimizingSequence
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _pullTightArgument :
      HasFiniteExtinctionPullTightArgument
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minMaxStationarity :
      HasFiniteExtinctionMinMaxStationarity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minSurfaceRegularity :
      HasFiniteExtinctionMinSurfaceRegularity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _positiveWidth :
      HasFiniteExtinctionPositiveWidth
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
    ∃ _firstVariationFormula :
      HasFiniteExtinctionFirstVariationFormula flow surgery control widthTheory,
    ∃ _secondVariationInequality :
      HasFiniteExtinctionSecondVariationInequality flow surgery control widthTheory,
    ∃ _gaussBonnetEstimate :
      HasFiniteExtinctionGaussBonnetEstimate flow surgery control widthTheory,
    ∃ _scalarCurvatureWidthBound :
      HasFiniteExtinctionScalarCurvatureWidthBound
        flow surgery control widthTheory,
    ∃ widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
    ∃ _widthDifferentialInequality :
      HasFiniteExtinctionWidthDifferentialInequality
        flow surgery control widthTheory,
    ∃ _surgeryMetricComparison :
      HasFiniteExtinctionSurgeryMetricComparison
        flow surgery control widthTheory widthEvolution,
    ∃ _surgeryWidthComparisonMap :
      HasFiniteExtinctionSurgeryWidthComparisonMap
        flow surgery control widthTheory widthEvolution,
    ∃ _surgeryWidthDrop :
      HasFiniteExtinctionSurgeryWidthDrop
        flow surgery control widthTheory widthEvolution,
    ∃ surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution,
    ∃ _discardedComponentWidthNeutrality :
      HasFiniteExtinctionDiscardedComponentWidthNeutrality
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _discardedComponentSweepoutTriviality :
      HasFiniteExtinctionDiscardedComponentSweepoutTriviality
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _discardedComponentClassification :
      HasFiniteExtinctionDiscardedComponentClassification
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _survivingComponentTracking :
      HasFiniteExtinctionSurvivingComponentTracking
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
      HasFiniteExtinctionComponentTopology
        flow surgery control widthTheory widthEvolution surgeryDiscardControl := by
  rcases statement with
    ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
      sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
      areaFunctional, widthDefinition, widthCompactness,
      widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
      minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
      firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
      scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
      surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
      surgeryDiscardControl, discardedComponentWidthNeutrality,
      discardedComponentSweepoutTriviality, discardedComponentClassification,
      survivingComponentTracking, componentTopology⟩
  exact ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
    sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
    areaFunctional, widthDefinition, widthCompactness,
    widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
    minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
    firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
    scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
    surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
    surgeryDiscardControl, discardedComponentWidthNeutrality,
    discardedComponentSweepoutTriviality, discardedComponentClassification,
    survivingComponentTracking, componentTopology⟩

/--
The width statement bridge exposes exactly the width and surgery-discard
sub-obligation components stored in the theorem-shaped width statement.
-/
theorem finite_extinction_width_subobligations_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement :
      FiniteExtinctionWidthSubobligationsStatement flow surgery control) :
    finite_extinction_width_subobligations_of_statement statement =
      (by
        rcases statement with
          ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
            sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
            areaFunctional, widthDefinition, widthCompactness,
            widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
            minMaxStationarity, minSurfaceRegularity, positiveWidth,
            widthTheory, firstVariationFormula, secondVariationInequality,
            gaussBonnetEstimate, scalarCurvatureWidthBound, widthEvolution,
            widthDifferentialInequality, surgeryMetricComparison,
            surgeryWidthComparisonMap, surgeryWidthDrop, surgeryDiscardControl,
            discardedComponentWidthNeutrality,
            discardedComponentSweepoutTriviality,
            discardedComponentClassification, survivingComponentTracking,
            componentTopology⟩
        exact ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
          sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
          areaFunctional, widthDefinition, widthCompactness,
          widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
          minMaxStationarity, minSurfaceRegularity, positiveWidth,
          widthTheory, firstVariationFormula, secondVariationInequality,
          gaussBonnetEstimate, scalarCurvatureWidthBound, widthEvolution,
          widthDifferentialInequality, surgeryMetricComparison,
          surgeryWidthComparisonMap, surgeryWidthDrop, surgeryDiscardControl,
          discardedComponentWidthNeutrality,
          discardedComponentSweepoutTriviality,
          discardedComponentClassification, survivingComponentTracking,
          componentTopology⟩) := by
  apply Subsingleton.elim

/-- The full statement exposes the named finite-extinction sub-obligations. -/
theorem finite_extinction_subobligations_of_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    ∃ finiteFundamentalGroup : HasFiniteExtinctionFundamentalGroupInput M,
    ∃ sweepout :
      HasFiniteExtinctionSweepoutExistence M finiteFundamentalGroup,
    ∃ _sweepoutParameterSpace :
      HasFiniteExtinctionSweepoutParameterSpace M finiteFundamentalGroup,
    ∃ _sweepoutContinuity :
      HasFiniteExtinctionSweepoutContinuity M finiteFundamentalGroup sweepout,
    ∃ _sweepoutAreaBound :
      HasFiniteExtinctionSweepoutAreaBound M finiteFundamentalGroup sweepout,
    ∃ _sweepoutNontriviality :
      HasFiniteExtinctionSweepoutNontriviality M finiteFundamentalGroup sweepout,
    ∃ _areaFunctional :
      HasFiniteExtinctionAreaFunctionalSetup
        flow surgery control finiteFundamentalGroup sweepout,
    ∃ widthDefinition :
      HasFiniteExtinctionMinMaxWidthDefinition
        flow surgery control finiteFundamentalGroup sweepout,
    ∃ _widthCompactness :
      HasFiniteExtinctionWidthCompactness
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _widthLowerSemicontinuity :
      HasFiniteExtinctionWidthLowerSemicontinuity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minimizingSequence :
      HasFiniteExtinctionMinimizingSequence
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _pullTightArgument :
      HasFiniteExtinctionPullTightArgument
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minMaxStationarity :
      HasFiniteExtinctionMinMaxStationarity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _minSurfaceRegularity :
      HasFiniteExtinctionMinSurfaceRegularity
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ _positiveWidth :
      HasFiniteExtinctionPositiveWidth
        flow surgery control finiteFundamentalGroup sweepout widthDefinition,
    ∃ widthTheory : HasFiniteExtinctionWidthTheory flow surgery control,
    ∃ _firstVariationFormula :
      HasFiniteExtinctionFirstVariationFormula flow surgery control widthTheory,
    ∃ _secondVariationInequality :
      HasFiniteExtinctionSecondVariationInequality flow surgery control widthTheory,
    ∃ _gaussBonnetEstimate :
      HasFiniteExtinctionGaussBonnetEstimate flow surgery control widthTheory,
    ∃ _scalarCurvatureWidthBound :
      HasFiniteExtinctionScalarCurvatureWidthBound
        flow surgery control widthTheory,
    ∃ widthEvolution :
      HasFiniteExtinctionWidthEvolution flow surgery control widthTheory,
    ∃ _widthDifferentialInequality :
      HasFiniteExtinctionWidthDifferentialInequality
        flow surgery control widthTheory,
    ∃ _surgeryMetricComparison :
      HasFiniteExtinctionSurgeryMetricComparison
        flow surgery control widthTheory widthEvolution,
    ∃ _surgeryWidthComparisonMap :
      HasFiniteExtinctionSurgeryWidthComparisonMap
        flow surgery control widthTheory widthEvolution,
    ∃ _surgeryWidthDrop :
      HasFiniteExtinctionSurgeryWidthDrop
        flow surgery control widthTheory widthEvolution,
    ∃ surgeryDiscardControl :
      HasFiniteExtinctionSurgeryDiscardControl
        flow surgery control widthTheory widthEvolution,
    ∃ _discardedComponentWidthNeutrality :
      HasFiniteExtinctionDiscardedComponentWidthNeutrality
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _discardedComponentSweepoutTriviality :
      HasFiniteExtinctionDiscardedComponentSweepoutTriviality
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _discardedComponentClassification :
      HasFiniteExtinctionDiscardedComponentClassification
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _survivingComponentTracking :
      HasFiniteExtinctionSurvivingComponentTracking
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ _componentTopology :
      HasFiniteExtinctionComponentTopology
        flow surgery control widthTheory widthEvolution surgeryDiscardControl,
    ∃ pinching : HasFiniteExtinctionCurvaturePinching flow surgery control,
    ∃ _positiveScalarCurvatureLowerBound :
      HasFiniteExtinctionPositiveScalarCurvatureLowerBound
        flow surgery control pinching,
    ∃ _positiveScalarCurvaturePersistence :
      HasFiniteExtinctionPositiveScalarCurvaturePersistence
        flow surgery control pinching,
    ∃ componentControl :
      HasFiniteExtinctionComponentControl flow surgery control pinching,
    ∃ _volumeEvolutionFormula :
      HasFiniteExtinctionVolumeEvolutionFormula
        flow surgery control pinching componentControl,
    ∃ _surgeryVolumeNonincrease :
      HasFiniteExtinctionSurgeryVolumeNonincrease
        flow surgery control pinching componentControl,
    ∃ _scalarCurvatureDifferentialInequality :
      HasFiniteExtinctionScalarCurvatureDifferentialInequality
        flow surgery control pinching componentControl,
    ∃ _volumeDifferentialInequality :
      HasFiniteExtinctionVolumeDifferentialInequality
        flow surgery control pinching componentControl,
    ∃ _volumeDecayEstimate :
      HasFiniteExtinctionVolumeDecayEstimate
        flow surgery control pinching componentControl,
    ∃ timeBound :
      HasFiniteExtinctionTimeBound
        flow surgery control pinching componentControl,
    ∃ _differentialInequalityIntegration :
      HasFiniteExtinctionDifferentialInequalityIntegration
        flow surgery control pinching componentControl timeBound,
    ∃ _finiteTimeIntegration :
      HasFiniteExtinctionFiniteTimeIntegration
        flow surgery control pinching componentControl timeBound,
    ∃ _surgeryTimeSummability :
      HasFiniteExtinctionSurgeryTimeSummability
        flow surgery control pinching componentControl timeBound,
    ∃ _extinctionTimeContradiction :
      HasFiniteExtinctionExtinctionTimeContradiction
        flow surgery control pinching componentControl timeBound,
    ∃ derivation : HasFiniteExtinctionDerivation flow surgery control,
    ∃ extinction : FiniteExtinctionByRicciFlowWithSurgery M,
      HasFiniteExtinctionConclusionDerivation
        flow surgery control pinching componentControl timeBound derivation
        extinction := by
  rcases statement with
    ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
      sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
      areaFunctional, widthDefinition, widthCompactness,
      widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
      minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
      firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
      scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
      surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
      surgeryDiscardControl, discardedComponentWidthNeutrality,
      discardedComponentSweepoutTriviality, discardedComponentClassification,
      survivingComponentTracking, componentTopology, pinching,
      positiveScalarCurvatureLowerBound, positiveScalarCurvaturePersistence,
      componentControl, volumeEvolutionFormula, surgeryVolumeNonincrease,
      scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
      volumeDecayEstimate, timeBound, differentialInequalityIntegration,
      finiteTimeIntegration, surgeryTimeSummability, extinctionTimeContradiction,
      derivation, extinction, conclusionDerivation⟩
  exact ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
    sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
    areaFunctional, widthDefinition, widthCompactness,
    widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
    minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
    firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
    scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
    surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
    surgeryDiscardControl, discardedComponentWidthNeutrality,
    discardedComponentSweepoutTriviality, discardedComponentClassification,
    survivingComponentTracking, componentTopology, pinching,
    positiveScalarCurvatureLowerBound, positiveScalarCurvaturePersistence,
    componentControl, volumeEvolutionFormula, surgeryVolumeNonincrease,
    scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
    volumeDecayEstimate, timeBound, differentialInequalityIntegration,
    finiteTimeIntegration, surgeryTimeSummability, extinctionTimeContradiction,
    derivation, extinction, conclusionDerivation⟩

/--
The full statement bridge exposes exactly the finite-extinction
sub-obligation components stored in the theorem-shaped full statement.
-/
theorem finite_extinction_subobligations_of_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    finite_extinction_subobligations_of_statement statement =
      (by
        rcases statement with
          ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
            sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
            areaFunctional, widthDefinition, widthCompactness,
            widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
            minMaxStationarity, minSurfaceRegularity, positiveWidth,
            widthTheory, firstVariationFormula, secondVariationInequality,
            gaussBonnetEstimate, scalarCurvatureWidthBound, widthEvolution,
            widthDifferentialInequality, surgeryMetricComparison,
            surgeryWidthComparisonMap, surgeryWidthDrop, surgeryDiscardControl,
            discardedComponentWidthNeutrality,
            discardedComponentSweepoutTriviality,
            discardedComponentClassification, survivingComponentTracking,
            componentTopology, pinching, positiveScalarCurvatureLowerBound,
            positiveScalarCurvaturePersistence, componentControl,
            volumeEvolutionFormula, surgeryVolumeNonincrease,
            scalarCurvatureDifferentialInequality,
            volumeDifferentialInequality, volumeDecayEstimate, timeBound,
            differentialInequalityIntegration, finiteTimeIntegration,
            surgeryTimeSummability, extinctionTimeContradiction, derivation,
            extinction, conclusionDerivation⟩
        exact ⟨finiteFundamentalGroup, sweepout, sweepoutParameterSpace,
          sweepoutContinuity, sweepoutAreaBound, sweepoutNontriviality,
          areaFunctional, widthDefinition, widthCompactness,
          widthLowerSemicontinuity, minimizingSequence, pullTightArgument,
          minMaxStationarity, minSurfaceRegularity, positiveWidth, widthTheory,
          firstVariationFormula, secondVariationInequality, gaussBonnetEstimate,
          scalarCurvatureWidthBound, widthEvolution, widthDifferentialInequality,
          surgeryMetricComparison, surgeryWidthComparisonMap, surgeryWidthDrop,
          surgeryDiscardControl, discardedComponentWidthNeutrality,
          discardedComponentSweepoutTriviality, discardedComponentClassification,
          survivingComponentTracking, componentTopology, pinching,
          positiveScalarCurvatureLowerBound, positiveScalarCurvaturePersistence,
          componentControl, volumeEvolutionFormula, surgeryVolumeNonincrease,
          scalarCurvatureDifferentialInequality, volumeDifferentialInequality,
          volumeDecayEstimate, timeBound, differentialInequalityIntegration,
          finiteTimeIntegration, surgeryTimeSummability,
          extinctionTimeContradiction, derivation, extinction,
          conclusionDerivation⟩) := by
  apply Subsingleton.elim

/--
A completed surgery package exposes the theorem-shaped finite-extinction width
and full sub-obligation statements, their named statement-mediated payloads, and
the package-level finite-extinction statement together.
-/
theorem finite_extinction_subobligations_payload_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ _widthStatement :
      FiniteExtinctionWidthSubobligationsStatement flow surgery control,
    ∃ _subobligationsStatement :
      FiniteExtinctionSubobligationsStatement flow surgery control,
    ∃ _widthSubobligations :
      FiniteExtinctionWidthSubobligationsPayload flow surgery control,
    ∃ _subobligations :
      FiniteExtinctionSubobligationsPayload flow surgery control,
      FiniteExtinctionStatement n M := by
  let flow := ricci_flow_data_of_surgery_package package
  let surgery := ricci_flow_with_surgery_of_surgery_package package
  let control := perelman_singularity_control_of_surgery_package package
  let widthStatement :=
    finite_extinction_width_subobligations_statement_of_surgery_package
      package
  let subobligationsStatement :=
    finite_extinction_subobligations_statement_of_surgery_package package
  let widthSubobligations :=
    finite_extinction_width_subobligations_of_statement widthStatement
  let subobligations :=
    finite_extinction_subobligations_of_statement subobligationsStatement
  exact ⟨flow, surgery, control, widthStatement, subobligationsStatement,
    widthSubobligations, subobligations,
    finite_extinction_statement_of_surgery_package package⟩

/--
The completed surgery package route to the finite-extinction sub-obligation
payload is exactly the statement-mediated width/full sub-obligation payload
bundle and package statement extraction.
-/
theorem finite_extinction_subobligations_payload_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_subobligations_payload_of_surgery_package package =
      (by
        let flow := ricci_flow_data_of_surgery_package package
        let surgery := ricci_flow_with_surgery_of_surgery_package package
        let control := perelman_singularity_control_of_surgery_package package
        let widthStatement :=
          finite_extinction_width_subobligations_statement_of_surgery_package
            package
        let subobligationsStatement :=
          finite_extinction_subobligations_statement_of_surgery_package package
        let widthSubobligations :=
          finite_extinction_width_subobligations_of_statement widthStatement
        let subobligations :=
          finite_extinction_subobligations_of_statement subobligationsStatement
        exact ⟨flow, surgery, control, widthStatement,
          subobligationsStatement, widthSubobligations, subobligations,
          finite_extinction_statement_of_surgery_package package⟩) := by
  apply Subsingleton.elim

/--
A completed surgery package exposes the finite-extinction width
sub-obligation payload directly through its theorem-shaped width statement.
-/
theorem finite_extinction_width_subobligations_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionWidthSubobligationsPayload
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  finite_extinction_width_subobligations_of_statement
    (finite_extinction_width_subobligations_statement_of_surgery_package
      package)

/--
The direct surgery-package width sub-obligation route is exactly the
statement-mediated route through the package's theorem-shaped width statement.
-/
theorem finite_extinction_width_subobligations_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_width_subobligations_of_surgery_package package =
      finite_extinction_width_subobligations_of_statement
        (finite_extinction_width_subobligations_statement_of_surgery_package
          package) := by
  apply Subsingleton.elim

/--
A completed surgery package exposes the full finite-extinction sub-obligation
payload directly through its theorem-shaped full sub-obligation statement.
-/
theorem finite_extinction_subobligations_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    FiniteExtinctionSubobligationsPayload
      (ricci_flow_data_of_surgery_package package)
      (ricci_flow_with_surgery_of_surgery_package package)
      (perelman_singularity_control_of_surgery_package package) :=
  finite_extinction_subobligations_of_statement
    (finite_extinction_subobligations_statement_of_surgery_package package)

/--
The direct surgery-package full sub-obligation route is exactly the
statement-mediated route through the package's theorem-shaped full statement.
-/
theorem finite_extinction_subobligations_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_subobligations_of_surgery_package package =
      finite_extinction_subobligations_of_statement
        (finite_extinction_subobligations_statement_of_surgery_package
          package) := by
  apply Subsingleton.elim

/-- The full finite-extinction statement exposes the derivation certificate. -/
theorem finite_extinction_derivation_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    HasFiniteExtinctionDerivation flow surgery control := by
  rcases statement with
    ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth,
      _widthTheory, _firstVariationFormula, _secondVariationInequality,
      _gaussBonnetEstimate, _scalarCurvatureWidthBound, _widthEvolution,
      _widthDifferentialInequality, _surgeryMetricComparison,
      _surgeryWidthComparisonMap, _surgeryWidthDrop, _surgeryDiscardControl,
      _discardedComponentWidthNeutrality, _discardedComponentSweepoutTriviality,
      _discardedComponentClassification, _survivingComponentTracking,
      _componentTopology, _pinching, _positiveScalarCurvatureLowerBound,
      _positiveScalarCurvaturePersistence, _componentControl,
      _volumeEvolutionFormula, _surgeryVolumeNonincrease,
      _scalarCurvatureDifferentialInequality, _volumeDifferentialInequality,
      _volumeDecayEstimate, _timeBound, _differentialInequalityIntegration,
      _finiteTimeIntegration, _surgeryTimeSummability,
      _extinctionTimeContradiction, derivation, _extinction,
      _conclusionDerivation⟩
  exact derivation

/--
The derivation extracted from a full finite-extinction sub-obligation statement
is exactly its stored derivation component.
-/
theorem finite_extinction_derivation_of_subobligations_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    finite_extinction_derivation_of_subobligations_statement statement =
      (by
        rcases statement with
          ⟨_finiteFundamentalGroup, _sweepout, _sweepoutParameterSpace,
            _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
            _areaFunctional, _widthDefinition, _widthCompactness,
            _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
            _minMaxStationarity, _minSurfaceRegularity, _positiveWidth,
            _widthTheory, _firstVariationFormula, _secondVariationInequality,
            _gaussBonnetEstimate, _scalarCurvatureWidthBound, _widthEvolution,
            _widthDifferentialInequality, _surgeryMetricComparison,
            _surgeryWidthComparisonMap, _surgeryWidthDrop,
            _surgeryDiscardControl, _discardedComponentWidthNeutrality,
            _discardedComponentSweepoutTriviality,
            _discardedComponentClassification, _survivingComponentTracking,
            _componentTopology, _pinching, _positiveScalarCurvatureLowerBound,
            _positiveScalarCurvaturePersistence, _componentControl,
            _volumeEvolutionFormula, _surgeryVolumeNonincrease,
            _scalarCurvatureDifferentialInequality,
            _volumeDifferentialInequality, _volumeDecayEstimate, _timeBound,
            _differentialInequalityIntegration, _finiteTimeIntegration,
            _surgeryTimeSummability, _extinctionTimeContradiction, derivation,
            _extinction, _conclusionDerivation⟩
        exact derivation) := by
  apply Subsingleton.elim

/--
The full finite-extinction sub-obligation statement assembles the
theorem-shaped conclusion statement for its projected extinction proof.
-/
theorem finite_extinction_conclusion_statement_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    ∃ finiteExtinction : FiniteExtinctionByRicciFlowWithSurgery M,
      FiniteExtinctionConclusionStatement
        flow surgery control finiteExtinction := by
  rcases statement with
    ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
      _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
      _areaFunctional, _widthDefinition, _widthCompactness,
      _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
      _minMaxStationarity, _minSurfaceRegularity, _positiveWidth,
      widthTheory, _firstVariationFormula, _secondVariationInequality,
      _gaussBonnetEstimate, _scalarCurvatureWidthBound, widthEvolution,
      _widthDifferentialInequality, _surgeryMetricComparison,
      _surgeryWidthComparisonMap, _surgeryWidthDrop, surgeryDiscardControl,
      _discardedComponentWidthNeutrality, _discardedComponentSweepoutTriviality,
      _discardedComponentClassification, _survivingComponentTracking,
      _componentTopology, pinching, _positiveScalarCurvatureLowerBound,
      _positiveScalarCurvaturePersistence, componentControl,
      _volumeEvolutionFormula, _surgeryVolumeNonincrease,
      _scalarCurvatureDifferentialInequality, _volumeDifferentialInequality,
      _volumeDecayEstimate, timeBound, _differentialInequalityIntegration,
      _finiteTimeIntegration, _surgeryTimeSummability,
      _extinctionTimeContradiction, derivation, extinction,
      conclusionDerivation⟩
  exact ⟨extinction,
    finite_extinction_conclusion_statement_of_components
      flow surgery control extinction finiteFundamentalGroup sweepout
      widthTheory widthEvolution surgeryDiscardControl pinching
      componentControl timeBound derivation conclusionDerivation⟩

/--
The fixed-flow conclusion statement rebuilt from a full finite-extinction
sub-obligation statement is exactly the component assembly route applied to its
stored components.
-/
theorem finite_extinction_conclusion_statement_of_subobligations_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    finite_extinction_conclusion_statement_of_subobligations_statement
        statement =
      (by
        rcases statement with
          ⟨finiteFundamentalGroup, sweepout, _sweepoutParameterSpace,
            _sweepoutContinuity, _sweepoutAreaBound, _sweepoutNontriviality,
            _areaFunctional, _widthDefinition, _widthCompactness,
            _widthLowerSemicontinuity, _minimizingSequence, _pullTightArgument,
            _minMaxStationarity, _minSurfaceRegularity, _positiveWidth,
            widthTheory, _firstVariationFormula, _secondVariationInequality,
            _gaussBonnetEstimate, _scalarCurvatureWidthBound, widthEvolution,
            _widthDifferentialInequality, _surgeryMetricComparison,
            _surgeryWidthComparisonMap, _surgeryWidthDrop,
            surgeryDiscardControl, _discardedComponentWidthNeutrality,
            _discardedComponentSweepoutTriviality,
            _discardedComponentClassification, _survivingComponentTracking,
            _componentTopology, pinching, _positiveScalarCurvatureLowerBound,
            _positiveScalarCurvaturePersistence, componentControl,
            _volumeEvolutionFormula, _surgeryVolumeNonincrease,
            _scalarCurvatureDifferentialInequality,
            _volumeDifferentialInequality, _volumeDecayEstimate, timeBound,
            _differentialInequalityIntegration, _finiteTimeIntegration,
            _surgeryTimeSummability, _extinctionTimeContradiction, derivation,
            extinction, conclusionDerivation⟩
        exact ⟨extinction,
          finite_extinction_conclusion_statement_of_components
            flow surgery control extinction finiteFundamentalGroup sweepout
            widthTheory widthEvolution surgeryDiscardControl pinching
            componentControl timeBound derivation conclusionDerivation⟩) := by
  apply Subsingleton.elim

/--
The full finite-extinction sub-obligation statement assembles the
theorem-shaped finite-extinction statement, rather than only exposing the raw
extinction witness.
-/
theorem finite_extinction_statement_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    FiniteExtinctionStatement n M := by
  rcases finite_extinction_conclusion_statement_of_subobligations_statement
      statement with
    ⟨finiteExtinction, conclusionStatement⟩
  exact ⟨flow, surgery, control, finiteExtinction, conclusionStatement⟩

/--
The theorem-shaped finite-extinction statement rebuilt from a full
sub-obligation statement is exactly the package of the fixed flow, surgery,
control, extracted finite-extinction witness, and rebuilt conclusion statement.
-/
theorem finite_extinction_statement_of_subobligations_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    finite_extinction_statement_of_subobligations_statement statement =
      (by
        rcases finite_extinction_conclusion_statement_of_subobligations_statement
            statement with
          ⟨finiteExtinction, conclusionStatement⟩
        exact ⟨flow, surgery, control, finiteExtinction,
          conclusionStatement⟩) := by
  apply Subsingleton.elim

/-- The full finite-extinction statement exposes the extinction conclusion. -/
theorem finite_extinction_of_subobligations_statement
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  exact finite_extinction_of_finite_extinction_statement
    (finite_extinction_statement_of_subobligations_statement statement)

/--
The finite-extinction witness extracted from a full sub-obligation statement is
exactly the witness extracted from the theorem-shaped statement rebuilt from it.
-/
theorem finite_extinction_of_subobligations_statement_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {flow : RicciFlowData ThreeManifoldModelWithCorners n M}
    {surgery : HasRicciFlowWithSurgery n M}
    {control : HasPerelmanSingularityControl (n := n) (M := M) flow}
    (statement : FiniteExtinctionSubobligationsStatement flow surgery control) :
    finite_extinction_of_subobligations_statement statement =
      finite_extinction_of_finite_extinction_statement
        (finite_extinction_statement_of_subobligations_statement statement) := by
  apply Subsingleton.elim

/--
A completed surgery package exposes the package-level finite-extinction
statement, the full sub-obligation statement, the finite-extinction statement
rebuilt through that sub-obligation route, the derivation certificate, and the
resulting extinction witness together.
-/
theorem finite_extinction_statement_payload_of_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    ∃ flow : RicciFlowData ThreeManifoldModelWithCorners n M,
    ∃ surgery : HasRicciFlowWithSurgery n M,
    ∃ control : HasPerelmanSingularityControl (n := n) (M := M) flow,
    ∃ _packageStatement : FiniteExtinctionStatement n M,
    ∃ _subobligationsStatement :
      FiniteExtinctionSubobligationsStatement flow surgery control,
    ∃ _viaSubobligationsStatement : FiniteExtinctionStatement n M,
    ∃ _derivation : HasFiniteExtinctionDerivation flow surgery control,
      FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases finite_extinction_subobligations_payload_of_surgery_package
      package with
    ⟨flow, surgery, control, _widthStatement, subobligationsStatement,
      _widthSubobligations, _subobligations, packageStatement⟩
  let viaSubobligationsStatement :=
    finite_extinction_statement_of_subobligations_statement
      subobligationsStatement
  let derivation :=
    finite_extinction_derivation_of_subobligations_statement
      subobligationsStatement
  exact ⟨flow, surgery, control, packageStatement, subobligationsStatement,
    viaSubobligationsStatement, derivation,
    finite_extinction_of_subobligations_statement subobligationsStatement⟩

/--
The completed surgery package route to the finite-extinction statement payload
is exactly the statement payload, full sub-obligation statement, rebuilt
statement, derivation certificate, and extinction witness extracted from the
sub-obligation route.
-/
theorem finite_extinction_statement_payload_of_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M) :
    finite_extinction_statement_payload_of_surgery_package package =
      (by
        rcases finite_extinction_subobligations_payload_of_surgery_package
            package with
          ⟨flow, surgery, control, _widthStatement, subobligationsStatement,
            _widthSubobligations, _subobligations, packageStatement⟩
        let viaSubobligationsStatement :=
          finite_extinction_statement_of_subobligations_statement
            subobligationsStatement
        let derivation :=
          finite_extinction_derivation_of_subobligations_statement
            subobligationsStatement
        exact ⟨flow, surgery, control, packageStatement,
          subobligationsStatement, viaSubobligationsStatement, derivation,
          finite_extinction_of_subobligations_statement
            subobligationsStatement⟩) := by
  apply Subsingleton.elim

/--
A finite-extinction surgery package strengthened with the explicit smooth-piece
Ricci-flow equation boundary.

The existing surgery package still carries the finite-extinction conclusion;
this wrapper records the additional analytic proof object needed to identify
the concrete equation `∂ₜ g = -2 Ricci` for the same projected flow.
-/
structure FiniteExtinctionSurgeryPackageWithEquationBoundary
    (n : ℕ∞ω)
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M] where
  /-- The underlying finite-extinction surgery package. -/
  package : FiniteExtinctionSurgeryPackage n M
  /-- Explicit smooth-piece equation boundary for the package's projected flow. -/
  equationBoundary :
    RicciFlowEquationBoundaryPackage (ricci_flow_data_of_surgery_package package)

/--
Build a strengthened surgery package from an ordinary finite-extinction
surgery package and an already assembled equation-boundary package for its
projected Ricci-flow data.
-/
noncomputable def surgery_package_with_equation_boundary_of_boundary_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (boundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package package)) :
    FiniteExtinctionSurgeryPackageWithEquationBoundary n M :=
  { package := package
    equationBoundary := boundary }

/--
The boundary-built strengthened surgery package is exactly the pair of the
ordinary package and the supplied equation boundary.
-/
@[simp] theorem surgery_package_with_equation_boundary_of_boundary_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (boundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package package)) :
    surgery_package_with_equation_boundary_of_boundary_package
      package boundary =
      ({ package := package
         equationBoundary := boundary } :
        FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :=
  rfl

/--
Build a strengthened surgery package directly from an ordinary
finite-extinction surgery package and an explicit Ricci-flow equation
verification for the package's projected Ricci-flow data.
-/
noncomputable def surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    FiniteExtinctionSurgeryPackageWithEquationBoundary n M :=
  surgery_package_with_equation_boundary_of_boundary_package
    package
    (equation_boundary_package_of_ricci_flow_equation_verification
      (ricci_flow_data_of_surgery_package package) verification)

/--
The verification-built strengthened surgery package delegates to the
boundary-package constructor after packaging the explicit verification with the
ordinary package's equation evidence.
-/
@[simp] theorem surgery_package_with_equation_boundary_of_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
      package verification =
      surgery_package_with_equation_boundary_of_boundary_package
        package
        (equation_boundary_package_of_ricci_flow_equation_verification
          (ricci_flow_data_of_surgery_package package) verification) :=
  rfl

/-- Forget the explicit equation boundary from a strengthened surgery package. -/
noncomputable def surgery_package_of_equation_boundary_surgery_package
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    FiniteExtinctionSurgeryPackage n M :=
  package.package

/-- The strengthened surgery-package forgetful projection is the stored package. -/
@[simp] theorem surgery_package_of_equation_boundary_surgery_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_of_equation_boundary_surgery_package package =
      package.package :=
  rfl

/--
Forgetting the boundary from a boundary-built strengthened surgery package
recovers the original ordinary surgery package.
-/
@[simp] theorem surgery_package_of_surgery_package_with_equation_boundary_of_boundary_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (boundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package package)) :
    surgery_package_of_equation_boundary_surgery_package
      (surgery_package_with_equation_boundary_of_boundary_package
        package boundary) =
      package :=
  rfl

/--
Forgetting the boundary from a verification-built strengthened surgery package
recovers the original ordinary surgery package.
-/
@[simp] theorem surgery_package_of_surgery_package_with_equation_boundary_of_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    surgery_package_of_equation_boundary_surgery_package
      (surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
        package verification) =
      package :=
  rfl

/--
Project the explicit equation boundary from a strengthened surgery package.
-/
def equation_boundary_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    RicciFlowEquationBoundaryPackage
      (ricci_flow_data_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package)) :=
  package.equationBoundary

/-- The strengthened surgery-package equation-boundary projection is stored data. -/
@[simp] theorem equation_boundary_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    equation_boundary_of_surgery_package_with_equation_boundary package =
      package.equationBoundary :=
  rfl

/--
Projecting the boundary from a boundary-built strengthened surgery package
returns the supplied boundary package.
-/
@[simp] theorem equation_boundary_of_surgery_package_with_equation_boundary_of_boundary_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (boundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package package)) :
    equation_boundary_of_surgery_package_with_equation_boundary
      (surgery_package_with_equation_boundary_of_boundary_package
        package boundary) =
      boundary :=
  rfl

/--
Projecting the boundary from a verification-built strengthened surgery package
returns the boundary package obtained from that explicit verification.
-/
@[simp] theorem equation_boundary_of_surgery_package_with_equation_boundary_of_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    equation_boundary_of_surgery_package_with_equation_boundary
      (surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
        package verification) =
      equation_boundary_package_of_ricci_flow_equation_verification
        (ricci_flow_data_of_surgery_package package) verification :=
  rfl

/-- Project explicit equation verification from a strengthened surgery package. -/
noncomputable def ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    RicciFlowEquationVerification
      (curvature_data_of_ricci_flow_data
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package))) :=
  ricci_flow_equation_verification_of_boundary_package
    (equation_boundary_of_surgery_package_with_equation_boundary package)

/-- The strengthened surgery-package equation-verification projection delegates to its boundary. -/
@[simp] theorem ricci_flow_equation_verification_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
      package =
      ricci_flow_equation_verification_of_boundary_package
        (equation_boundary_of_surgery_package_with_equation_boundary package) :=
  rfl

/--
The stored equation-boundary package is recovered from its projected explicit
equation verification and the underlying flow's equation evidence.
-/
theorem equation_boundary_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    equation_boundary_of_surgery_package_with_equation_boundary package =
      equation_boundary_package_of_ricci_flow_equation_verification
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package))
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) := by
  cases package with
  | mk package boundary =>
    cases boundary with
    | mk verification equationEvidence =>
      simp [equation_boundary_package_of_ricci_flow_equation_verification]

/-- Project metric-derivative data from a strengthened surgery package. -/
noncomputable def metric_derivative_data_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    MetricTimeDerivativeData
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package))) :=
  metric_derivative_data_of_equation_boundary_package
    (equation_boundary_of_surgery_package_with_equation_boundary package)

/-- The strengthened surgery-package metric-derivative projection delegates to its boundary. -/
@[simp] theorem metric_derivative_data_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    metric_derivative_data_of_surgery_package_with_equation_boundary package =
      metric_derivative_data_of_equation_boundary_package
        (equation_boundary_of_surgery_package_with_equation_boundary package) :=
  rfl

/--
The strengthened surgery package's metric-derivative data is the metric
derivative carried by its projected explicit equation verification.
-/
@[simp] theorem metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    metric_derivative_data_of_surgery_package_with_equation_boundary package =
      metric_derivative_data_of_ricci_flow_equation_verification
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) :=
  rfl

/-- A strengthened surgery package carries metric-derivative identification evidence. -/
theorem metric_time_derivative_identification_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    IsMetricTimeDerivativeOf
      (metric_of_ricci_flow_data
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package)))
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_surgery_package_with_equation_boundary package)) :=
  metric_time_derivative_identification_of_equation_boundary_package
    (equation_boundary_of_surgery_package_with_equation_boundary package)

/-- The strengthened surgery-package derivative-identification theorem is boundary evidence. -/
@[simp] theorem metric_time_derivative_identification_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    metric_time_derivative_identification_of_surgery_package_with_equation_boundary
      package =
      metric_time_derivative_identification_of_equation_boundary_package
        (equation_boundary_of_surgery_package_with_equation_boundary package) :=
  rfl

/--
The strengthened surgery package's derivative-identification evidence is the
evidence carried by its projected explicit equation verification.
-/
theorem metric_time_derivative_identification_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    metric_time_derivative_identification_of_surgery_package_with_equation_boundary
      package =
      metric_time_derivative_identification_of_ricci_flow_equation_verification
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) :=
  rfl

/--
The strengthened surgery package supplies the projection-routed explicit
Ricci-flow equation at time `t`.
-/
theorem equation_at_time_of_surgery_package_with_equation_boundary_projection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) (t : ℝ) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_surgery_package_with_equation_boundary
          package)) t =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))) t :=
  equation_at_time_of_equation_boundary_package_projection
    (equation_boundary_of_surgery_package_with_equation_boundary package) t

/-- The strengthened surgery-package projection-routed equation theorem is boundary evidence. -/
@[simp] theorem equation_at_time_of_surgery_package_with_equation_boundary_projection_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) (t : ℝ) :
    equation_at_time_of_surgery_package_with_equation_boundary_projection
      package t =
      equation_at_time_of_equation_boundary_package_projection
        (equation_boundary_of_surgery_package_with_equation_boundary package) t :=
  rfl

/--
The strengthened surgery package's projection-routed equation is the projected
equation carried by its explicit equation verification.
-/
theorem equation_at_time_of_surgery_package_with_equation_boundary_projection_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) (t : ℝ) :
    equation_at_time_of_surgery_package_with_equation_boundary_projection
      package t =
      equation_at_time_of_ricci_flow_equation_verification_projection
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) t :=
  rfl

/--
The strengthened surgery package supplies the projection-routed explicit
Ricci-flow equation pointwise at a point and pair of tangent vectors.
-/
theorem equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (metric_time_derivative_field_of_metric_derivative_data
        (metric_derivative_data_of_surgery_package_with_equation_boundary
          package)) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))) t x v w :=
  equation_at_time_apply_of_equation_boundary_package_projection
    (equation_boundary_of_surgery_package_with_equation_boundary package) t x v w

/-- The strengthened surgery-package pointwise equation theorem is boundary evidence. -/
@[simp] theorem equation_at_time_apply_of_surgery_package_with_equation_boundary_projection_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
      package t x v w =
      equation_at_time_apply_of_equation_boundary_package_projection
        (equation_boundary_of_surgery_package_with_equation_boundary package)
        t x v w :=
  rfl

/--
The strengthened surgery-package pointwise equation is the pointwise equation
carried by its projected explicit equation verification.
-/
@[simp] theorem equation_at_time_apply_of_surgery_package_with_equation_boundary_projection_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
      package t x v w =
      equation_at_time_apply_of_ricci_flow_equation_verification_projection
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) t x v w :=
  rfl

/--
The strengthened surgery package supplies the stored explicit Ricci-flow
equation pointwise before the metric-derivative projection wrapper is applied.
-/
theorem equation_at_time_apply_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    metric_time_derivative_at_time_of_metric_derivative_field
      (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
        package).metricDerivative.derivative t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))) t x v w :=
  equation_at_time_apply_of_equation_boundary_package
    (equation_boundary_of_surgery_package_with_equation_boundary package) t x v w

/-- The direct surgery-package pointwise equation theorem is boundary evidence. -/
@[simp] theorem equation_at_time_apply_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    equation_at_time_apply_of_surgery_package_with_equation_boundary
      package t x v w =
      equation_at_time_apply_of_equation_boundary_package
        (equation_boundary_of_surgery_package_with_equation_boundary package)
        t x v w := by
  apply Subsingleton.elim

/--
The strengthened surgery-package direct pointwise equation is the pointwise
equation carried by its projected explicit equation verification.
-/
@[simp] theorem equation_at_time_apply_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M)
    (t : ℝ) (x : M) (v w : TangentSpace ThreeManifoldModelWithCorners x) :
    equation_at_time_apply_of_surgery_package_with_equation_boundary
      package t x v w =
      equation_at_time_apply_of_ricci_flow_equation_verification
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) t x v w := by
  apply Subsingleton.elim

/--
A strengthened surgery package exposes its stored verification as a reusable
pointwise scalar equation payload.
-/
theorem pointwise_equation_payload_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    ∀ t x v w,
      metric_time_derivative_at_time_of_metric_derivative_field
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package).metricDerivative.derivative t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))) t x v w :=
  pointwise_equation_payload_of_equation_boundary_package
    (equation_boundary_of_surgery_package_with_equation_boundary package)

/-- The surgery-package pointwise equation payload is boundary-package payload. -/
@[simp] theorem pointwise_equation_payload_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    pointwise_equation_payload_of_surgery_package_with_equation_boundary
      package =
      pointwise_equation_payload_of_equation_boundary_package
        (equation_boundary_of_surgery_package_with_equation_boundary package) := by
  apply Subsingleton.elim

/--
The direct scalar-pointwise equation shape carried by a boundary-carrying
surgery package, before routing through the named metric-derivative projection.
-/
abbrev SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) : Prop :=
    ∀ (t : ℝ) (x : M)
      (v w : TangentSpace ThreeManifoldModelWithCorners x),
      metric_time_derivative_at_time_of_metric_derivative_field
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package).metricDerivative.derivative t x v w =
      ricci_flow_rhs_tensor
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)))
        t x v w

/--
The direct scalar-pointwise surgery payload expands to the equation stored in
the package's explicit Ricci-flow verification.
-/
theorem surgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package =
      (∀ (t : ℝ) (x : M)
        (v w : TangentSpace ThreeManifoldModelWithCorners x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
            package).metricDerivative.derivative t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)))
          t x v w) :=
  rfl

/--
A strengthened surgery package exposes the direct pointwise equation payload
stored by its explicit Ricci-flow verification.
-/
theorem surgery_package_with_equation_boundary_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package :=
  pointwise_equation_payload_of_surgery_package_with_equation_boundary package

/-- The direct surgery payload is the stored-verification pointwise payload. -/
@[simp] theorem surgery_package_with_equation_boundary_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_direct_pointwise_equation_payload
        package =
      pointwise_equation_payload_of_surgery_package_with_equation_boundary
        package :=
  rfl

/--
A strengthened surgery package supplies the analytic foundation together with
the explicit equation boundary for its projected flow.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package)) :=
  analytic_foundation_with_equation_boundary_of_package
    (analytic_foundation_of_surgery_package
      (surgery_package_of_equation_boundary_surgery_package package))
    (equation_boundary_of_surgery_package_with_equation_boundary package)

/--
The strengthened surgery-package analytic-boundary statement is assembled from
the underlying analytic-foundation package and stored equation boundary.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package =
      analytic_foundation_with_equation_boundary_of_package
        (analytic_foundation_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package))
        (equation_boundary_of_surgery_package_with_equation_boundary package) :=
  rfl

/--
The strengthened surgery package's analytic-boundary statement can be assembled
directly from the underlying analytic package and its projected explicit
equation verification.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
      package =
      analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
        (analytic_foundation_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package))
        (ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package) := by
  apply Subsingleton.elim

/--
An ordinary surgery package plus an explicit Ricci-flow equation verification
supplies the strengthened analytic-boundary statement for the package's
projected Ricci-flow data.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_and_ricci_flow_equation_verification
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_surgery_package package) :=
  analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
    (surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
      package verification)

/--
The ordinary-package-plus-verification analytic-boundary route delegates
through the verification-built strengthened surgery package.
-/
@[simp] theorem analytic_foundation_with_equation_boundary_of_surgery_package_and_ricci_flow_equation_verification_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    analytic_foundation_with_equation_boundary_of_surgery_package_and_ricci_flow_equation_verification
      package verification =
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        (surgery_package_with_equation_boundary_of_ricci_flow_equation_verification
          package verification) :=
  rfl

/--
The ordinary-package-plus-verification route agrees with assembling directly
from the stored analytic package and supplied verification.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_and_ricci_flow_equation_verification_to_analytic_package_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackage n M)
    (verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package package))) :
    analytic_foundation_with_equation_boundary_of_surgery_package_and_ricci_flow_equation_verification
      package verification =
      analytic_foundation_with_equation_boundary_of_package_and_ricci_flow_equation_verification
        (analytic_foundation_of_surgery_package package)
        verification := by
  apply Subsingleton.elim

/-- A strengthened surgery package still supplies the finite-extinction result. -/
theorem finite_extinction_of_surgery_package_with_equation_boundary
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  finite_extinction_of_surgery_package
    (surgery_package_of_equation_boundary_surgery_package package)

/--
The strengthened surgery-package finite-extinction projection delegates to the
underlying surgery package.
-/
@[simp] theorem finite_extinction_of_surgery_package_with_equation_boundary_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    finite_extinction_of_surgery_package_with_equation_boundary package =
      finite_extinction_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package) :=
  rfl

/--
A strengthened surgery package exposes the ordinary package, equation-boundary
package, analytic-boundary statement, and finite-extinction result together.
-/
theorem surgery_package_with_equation_boundary_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
    ∃ _equationBoundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package basePackage),
    ∃ _analyticBoundary :
      AnalyticFoundationWithEquationBoundaryStatement
        (ricci_flow_data_of_surgery_package basePackage),
      FiniteExtinctionByRicciFlowWithSurgery M := by
  exact
    ⟨surgery_package_of_equation_boundary_surgery_package package,
      equation_boundary_of_surgery_package_with_equation_boundary package,
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The strengthened surgery-package payload is exactly the tuple of the underlying
package, stored equation boundary, assembled analytic-boundary statement, and
finite-extinction result.
-/
theorem surgery_package_with_equation_boundary_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_payload package =
      (by
        exact
          ⟨surgery_package_of_equation_boundary_surgery_package package,
            equation_boundary_of_surgery_package_with_equation_boundary package,
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The full derivative-strengthened payload shape of a boundary-carrying surgery
package.  It pins the ordinary surgery package to the forgetful projection and
then carries the equation boundary, equation verification, metric derivative,
pointwise Ricci-flow equation, analytic-boundary statement, and finite
extinction result.
-/
abbrev SurgeryPackageWithEquationBoundaryDerivativePayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) : Prop :=
    ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
    ∃ _basePackage_eq :
      basePackage =
        surgery_package_of_equation_boundary_surgery_package package,
    ∃ _equationBoundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package)),
    ∃ verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package))),
    ∃ _verification_eq :
      verification =
        ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package,
    ∃ metricDerivative :
      MetricTimeDerivativeData
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package))),
    ∃ _metricDerivative_eq :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package,
      IsMetricTimeDerivativeOf
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)))
        (metric_time_derivative_field_of_metric_derivative_data
          metricDerivative) ∧
      (∀ t : ℝ,
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            metricDerivative) t =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))) t) ∧
      ∃ _analyticBoundary :
        AnalyticFoundationWithEquationBoundaryStatement
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)),
        FiniteExtinctionByRicciFlowWithSurgery M

/--
The full derivative-strengthened surgery payload is the explicit pinned
existential tuple of the forgetful base package, equation-boundary evidence,
derivative evidence, analytic-boundary statement, and finite-extinction result.
-/
theorem surgeryPackageWithEquationBoundaryDerivativePayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryDerivativePayload package =
      (∃ basePackage : FiniteExtinctionSurgeryPackage n M,
      ∃ _basePackage_eq :
        basePackage =
          surgery_package_of_equation_boundary_surgery_package package,
      ∃ _equationBoundary :
        RicciFlowEquationBoundaryPackage
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)),
      ∃ verification :
        RicciFlowEquationVerification
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))),
      ∃ _verification_eq :
        verification =
          ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
            package,
      ∃ metricDerivative :
        MetricTimeDerivativeData
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))),
      ∃ _metricDerivative_eq :
        metricDerivative =
          metric_derivative_data_of_surgery_package_with_equation_boundary
            package,
        IsMetricTimeDerivativeOf
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)))
          (metric_time_derivative_field_of_metric_derivative_data
            metricDerivative) ∧
        (∀ t : ℝ,
          metric_time_derivative_at_time_of_metric_derivative_field
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) t =
            ricci_flow_rhs_tensor
              (curvature_data_of_ricci_flow_data
                (ricci_flow_data_of_surgery_package
                  (surgery_package_of_equation_boundary_surgery_package
                    package))) t) ∧
        ∃ _analyticBoundary :
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)),
          FiniteExtinctionByRicciFlowWithSurgery M) :=
  rfl

/--
A strengthened surgery package exposes the ordinary package, equation boundary,
explicit equation verification, metric derivative data, derivative
identification, pointwise equation, analytic-boundary statement, and
finite-extinction result together.
-/
theorem surgery_package_with_equation_boundary_derivative_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryDerivativePayload package := by
  exact
    ⟨surgery_package_of_equation_boundary_surgery_package package,
      rfl,
      equation_boundary_of_surgery_package_with_equation_boundary package,
      ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
        package,
      rfl,
      metric_derivative_data_of_surgery_package_with_equation_boundary package,
      rfl,
      metric_time_derivative_identification_of_surgery_package_with_equation_boundary
        package,
      equation_at_time_of_surgery_package_with_equation_boundary_projection
        package,
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The strengthened surgery-package derivative payload is exactly the tuple of
the underlying package, boundary evidence, derivative evidence,
analytic-boundary statement, and finite-extinction result.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_derivative_payload package =
      (by
        exact
          ⟨surgery_package_of_equation_boundary_surgery_package package,
            rfl,
            equation_boundary_of_surgery_package_with_equation_boundary package,
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_derivative_data_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_time_derivative_identification_of_surgery_package_with_equation_boundary
              package,
            equation_at_time_of_surgery_package_with_equation_boundary_projection
              package,
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The scalar-pointwise version of the full boundary-carrying surgery payload.  It
keeps the same package, equation boundary, verification, metric derivative,
analytic-boundary statement, and finite-extinction conclusion as the derivative
payload, but records the Ricci-flow equation after applying the tensor equation
to every point and pair of tangent vectors.
-/
abbrev SurgeryPackageWithEquationBoundaryPointwiseEquationPayload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) : Prop :=
    ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
    ∃ _basePackage_eq :
      basePackage =
        surgery_package_of_equation_boundary_surgery_package package,
    ∃ _equationBoundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package
          (surgery_package_of_equation_boundary_surgery_package package)),
    ∃ verification :
      RicciFlowEquationVerification
        (curvature_data_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package))),
    ∃ _verification_eq :
      verification =
        ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
          package,
    ∃ metricDerivative :
      MetricTimeDerivativeData
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package))),
    ∃ _metricDerivative_eq :
      metricDerivative =
        metric_derivative_data_of_surgery_package_with_equation_boundary
          package,
      IsMetricTimeDerivativeOf
        (metric_of_ricci_flow_data
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)))
        (metric_time_derivative_field_of_metric_derivative_data
          metricDerivative) ∧
      (∀ (t : ℝ) (x : M)
        (v w : TangentSpace ThreeManifoldModelWithCorners x),
        metric_time_derivative_at_time_of_metric_derivative_field
          (metric_time_derivative_field_of_metric_derivative_data
            metricDerivative) t x v w =
        ricci_flow_rhs_tensor
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package
                package))) t x v w) ∧
      ∃ _analyticBoundary :
        AnalyticFoundationWithEquationBoundaryStatement
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)),
        FiniteExtinctionByRicciFlowWithSurgery M

/--
The pointwise surgery payload expands to its explicit package, boundary,
verification, metric-derivative, scalar equation, analytic-boundary, and
finite-extinction tuple.
-/
theorem surgeryPackageWithEquationBoundaryPointwiseEquationPayload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package =
      (∃ basePackage : FiniteExtinctionSurgeryPackage n M,
      ∃ _basePackage_eq :
        basePackage =
          surgery_package_of_equation_boundary_surgery_package package,
      ∃ _equationBoundary :
        RicciFlowEquationBoundaryPackage
          (ricci_flow_data_of_surgery_package
            (surgery_package_of_equation_boundary_surgery_package package)),
      ∃ verification :
        RicciFlowEquationVerification
          (curvature_data_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))),
      ∃ _verification_eq :
        verification =
          ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
            package,
      ∃ metricDerivative :
        MetricTimeDerivativeData
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package))),
      ∃ _metricDerivative_eq :
        metricDerivative =
          metric_derivative_data_of_surgery_package_with_equation_boundary
            package,
        IsMetricTimeDerivativeOf
          (metric_of_ricci_flow_data
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)))
          (metric_time_derivative_field_of_metric_derivative_data
            metricDerivative) ∧
        (∀ (t : ℝ) (x : M)
          (v w : TangentSpace ThreeManifoldModelWithCorners x),
          metric_time_derivative_at_time_of_metric_derivative_field
            (metric_time_derivative_field_of_metric_derivative_data
              metricDerivative) t x v w =
          ricci_flow_rhs_tensor
            (curvature_data_of_ricci_flow_data
              (ricci_flow_data_of_surgery_package
                (surgery_package_of_equation_boundary_surgery_package
                  package))) t x v w) ∧
        ∃ _analyticBoundary :
          AnalyticFoundationWithEquationBoundaryStatement
            (ricci_flow_data_of_surgery_package
              (surgery_package_of_equation_boundary_surgery_package package)),
          FiniteExtinctionByRicciFlowWithSurgery M) :=
  rfl

/--
A strengthened surgery package exposes the scalar-pointwise equation payload
alongside the same boundary and extinction data carried by the derivative
payload.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package := by
  exact
    ⟨surgery_package_of_equation_boundary_surgery_package package,
      rfl,
      equation_boundary_of_surgery_package_with_equation_boundary package,
      ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
        package,
      rfl,
      metric_derivative_data_of_surgery_package_with_equation_boundary package,
      rfl,
      metric_time_derivative_identification_of_surgery_package_with_equation_boundary
        package,
      equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
        package,
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The named pointwise surgery payload is exactly the tuple assembled from the
package projections and the pointwise equation projection.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_pointwise_equation_payload package =
      (by
        exact
          ⟨surgery_package_of_equation_boundary_surgery_package package,
            rfl,
            equation_boundary_of_surgery_package_with_equation_boundary package,
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_derivative_data_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_time_derivative_identification_of_surgery_package_with_equation_boundary
              package,
            equation_at_time_apply_of_surgery_package_with_equation_boundary_projection
              package,
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The direct stored-verification scalar equation reconstructs the full
scalar-pointwise surgery payload by reusing the same package, equation
boundary, analytic-boundary statement, and finite-extinction fields.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package := by
  exact
    ⟨surgery_package_of_equation_boundary_surgery_package package,
      rfl,
      equation_boundary_of_surgery_package_with_equation_boundary package,
      ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
        package,
      rfl,
      metric_derivative_data_of_surgery_package_with_equation_boundary package,
      rfl,
      metric_time_derivative_identification_of_surgery_package_with_equation_boundary
        package,
      (by
        intro t x v w
        simpa
          [metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq]
          using payload t x v w),
      analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package,
      finite_extinction_of_surgery_package_with_equation_boundary package⟩

/--
The pointwise payload reconstructed from a direct scalar equation is exactly
the tuple assembled from the package projections and that direct equation.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
        payload =
      (by
        exact
          ⟨surgery_package_of_equation_boundary_surgery_package package,
            rfl,
            equation_boundary_of_surgery_package_with_equation_boundary package,
            ricci_flow_equation_verification_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_derivative_data_of_surgery_package_with_equation_boundary
              package,
            rfl,
            metric_time_derivative_identification_of_surgery_package_with_equation_boundary
              package,
            (by
              intro t x v w
              simpa
                [metric_derivative_data_of_surgery_package_with_equation_boundary_to_ricci_flow_equation_verification_eq]
                using payload t x v w),
            analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
              package,
            finite_extinction_of_surgery_package_with_equation_boundary
              package⟩) := by
  apply Subsingleton.elim

/--
The named scalar-pointwise surgery payload can be reconstructed from the named
direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_to_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_pointwise_equation_payload package =
      surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
        (surgery_package_with_equation_boundary_direct_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The scalar-pointwise payload reconstructs the tensor-level derivative payload by
function extensionality.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    SurgeryPackageWithEquationBoundaryDerivativePayload package := by
  rcases payload with
    ⟨basePackage, basePackage_eq, equationBoundary, verification,
      verification_eq, metricDerivative, metricDerivative_eq, derivativeId,
      pointwiseEquation, analyticBoundary, finiteExtinction⟩
  exact
    ⟨basePackage, basePackage_eq, equationBoundary, verification,
      verification_eq, metricDerivative, metricDerivative_eq, derivativeId,
      (fun t => by
        funext x
        ext v w
        exact pointwiseEquation t x v w),
      analyticBoundary, finiteExtinction⟩

/--
The derivative reconstruction from a scalar-pointwise payload is the explicit
tuple obtained by tensor extensionality from the pointwise equation field.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
        payload =
      (by
        rcases payload with
          ⟨basePackage, basePackage_eq, equationBoundary, verification,
            verification_eq, metricDerivative, metricDerivative_eq,
            derivativeId, pointwiseEquation, analyticBoundary,
            finiteExtinction⟩
        exact
          ⟨basePackage, basePackage_eq, equationBoundary, verification,
            verification_eq, metricDerivative, metricDerivative_eq,
            derivativeId,
            (fun t => by
              funext x
              ext v w
              exact pointwiseEquation t x v w),
            analyticBoundary, finiteExtinction⟩) := by
  apply Subsingleton.elim

/--
Reconstructing the derivative payload from the named pointwise payload agrees
with the existing package-level derivative payload theorem.
-/
theorem surgery_package_with_equation_boundary_pointwise_equation_payload_to_derivative_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_derivative_payload package =
      surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The direct stored-verification scalar equation reconstructs the tensor-level
derivative surgery payload by first rebuilding the scalar-pointwise payload and
then applying tensor extensionality.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    SurgeryPackageWithEquationBoundaryDerivativePayload package :=
  surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
    (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
      payload)

/--
The derivative payload reconstructed from a direct scalar equation is the
pointwise reconstruction applied to the direct-payload scalar-pointwise tuple.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
        payload =
      surgery_package_with_equation_boundary_derivative_payload_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
          payload) :=
  rfl

/--
The named tensor-level derivative surgery payload can be reconstructed from the
named direct stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_derivative_payload_to_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_derivative_payload package =
      surgery_package_with_equation_boundary_derivative_payload_of_direct_pointwise_equation_payload
        (surgery_package_with_equation_boundary_direct_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The scalar-pointwise surgery payload forgets to the older boundary surgery
payload by keeping the projected package, equation boundary, analytic-boundary
statement, and finite-extinction conclusion.
-/
theorem surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
    ∃ _equationBoundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package basePackage),
    ∃ _analyticBoundary :
      AnalyticFoundationWithEquationBoundaryStatement
        (ricci_flow_data_of_surgery_package basePackage),
      FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with
    ⟨_basePackage, _basePackage_eq, equationBoundary, _verification,
      _verification_eq, _metricDerivative, _metricDerivative_eq, _derivativeId,
      _pointwiseEquation, analyticBoundary, finiteExtinction⟩
  exact
    ⟨surgery_package_of_equation_boundary_surgery_package package,
      equationBoundary, analyticBoundary, finiteExtinction⟩

/--
Forgetting a scalar-pointwise surgery payload is the explicit tuple of projected
base package, equation boundary, analytic-boundary statement, and extinction.
-/
theorem surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
        payload =
      (by
        rcases payload with
          ⟨_basePackage, _basePackage_eq, equationBoundary, _verification,
            _verification_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _pointwiseEquation, analyticBoundary,
            finiteExtinction⟩
        exact
          ⟨surgery_package_of_equation_boundary_surgery_package package,
            equationBoundary, analyticBoundary, finiteExtinction⟩) := by
  apply Subsingleton.elim

/--
The named boundary surgery payload is the forgetful projection of the named
scalar-pointwise surgery payload.
-/
theorem surgery_package_with_equation_boundary_payload_to_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_payload package =
      surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The direct stored-verification scalar equation reconstructs the older boundary
surgery payload through the scalar-pointwise payload.
-/
theorem surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    ∃ basePackage : FiniteExtinctionSurgeryPackage n M,
    ∃ _equationBoundary :
      RicciFlowEquationBoundaryPackage
        (ricci_flow_data_of_surgery_package basePackage),
    ∃ _analyticBoundary :
      AnalyticFoundationWithEquationBoundaryStatement
        (ricci_flow_data_of_surgery_package basePackage),
      FiniteExtinctionByRicciFlowWithSurgery M :=
  surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
    (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
      payload)

/--
The boundary payload reconstructed from a direct scalar equation is the
pointwise forgetful projection applied to the direct-payload scalar-pointwise
tuple.
-/
theorem surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload
        payload =
      surgery_package_with_equation_boundary_payload_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
          payload) :=
  rfl

/--
The named boundary surgery payload can be reconstructed from the named direct
stored-verification scalar equation payload.
-/
theorem surgery_package_with_equation_boundary_payload_to_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    surgery_package_with_equation_boundary_payload package =
      surgery_package_with_equation_boundary_payload_of_direct_pointwise_equation_payload
        (surgery_package_with_equation_boundary_direct_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The scalar-pointwise surgery payload exposes the analytic-boundary statement
it carries for the projected Ricci-flow data.
-/
theorem analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package)) := by
  rcases payload with
    ⟨_basePackage, _basePackage_eq, _equationBoundary, _verification,
      _verification_eq, _metricDerivative, _metricDerivative_eq, _derivativeId,
      _pointwiseEquation, analyticBoundary, _finiteExtinction⟩
  exact analyticBoundary

/--
Projecting the analytic-boundary statement from a scalar-pointwise surgery
payload is the stored analytic-boundary field.
-/
theorem analytic_foundation_with_equation_boundary_of_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
        payload =
      (by
        rcases payload with
          ⟨_basePackage, _basePackage_eq, _equationBoundary, _verification,
            _verification_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _pointwiseEquation, analyticBoundary,
            _finiteExtinction⟩
        exact analyticBoundary) := by
  apply Subsingleton.elim

/--
The named strengthened surgery-package analytic-boundary projection is the
analytic projection of the named scalar-pointwise surgery payload.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary_to_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package =
      analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The direct stored-verification scalar equation reconstructs the analytic
equation-boundary statement through the scalar-pointwise payload.
-/
theorem analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    AnalyticFoundationWithEquationBoundaryStatement
      (ricci_flow_data_of_surgery_package
        (surgery_package_of_equation_boundary_surgery_package package)) :=
  analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
    (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
      payload)

/--
The analytic statement reconstructed from a direct scalar equation is the
analytic projection applied to the direct-payload scalar-pointwise tuple.
-/
theorem analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload
        payload =
      analytic_foundation_with_equation_boundary_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
          payload) :=
  rfl

/--
The named strengthened surgery-package analytic-boundary projection can be
reconstructed from the named direct stored-verification scalar equation payload.
-/
theorem analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary_to_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    analytic_foundation_with_equation_boundary_of_surgery_package_with_equation_boundary
        package =
      analytic_foundation_with_equation_boundary_of_direct_pointwise_equation_payload
        (surgery_package_with_equation_boundary_direct_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The scalar-pointwise surgery payload exposes the finite-extinction conclusion
it carries for the target manifold.
-/
theorem finite_extinction_of_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    FiniteExtinctionByRicciFlowWithSurgery M := by
  rcases payload with
    ⟨_basePackage, _basePackage_eq, _equationBoundary, _verification,
      _verification_eq, _metricDerivative, _metricDerivative_eq, _derivativeId,
      _pointwiseEquation, _analyticBoundary, finiteExtinction⟩
  exact finiteExtinction

/--
Projecting finite extinction from a scalar-pointwise surgery payload is exactly
the stored finite-extinction field.
-/
theorem finite_extinction_of_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryPointwiseEquationPayload package) :
    finite_extinction_of_pointwise_equation_payload payload =
      (by
        rcases payload with
          ⟨_basePackage, _basePackage_eq, _equationBoundary, _verification,
            _verification_eq, _metricDerivative, _metricDerivative_eq,
            _derivativeId, _pointwiseEquation, _analyticBoundary,
            finiteExtinction⟩
        exact finiteExtinction) := by
  apply Subsingleton.elim

/--
The named strengthened surgery-package finite-extinction projection is the
finite-extinction projection of the named scalar-pointwise surgery payload.
-/
theorem finite_extinction_of_surgery_package_with_equation_boundary_to_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    finite_extinction_of_surgery_package_with_equation_boundary package =
      finite_extinction_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

/--
The direct stored-verification scalar equation reconstructs the finite
extinction conclusion through the scalar-pointwise payload.
-/
theorem finite_extinction_of_direct_pointwise_equation_payload
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    FiniteExtinctionByRicciFlowWithSurgery M :=
  finite_extinction_of_pointwise_equation_payload
    (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
      payload)

/--
The finite-extinction conclusion reconstructed from a direct scalar equation is
the finite-extinction projection applied to the direct-payload scalar-pointwise
tuple.
-/
theorem finite_extinction_of_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    {package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M}
    (payload :
      SurgeryPackageWithEquationBoundaryDirectPointwiseEquationPayload package) :
    finite_extinction_of_direct_pointwise_equation_payload payload =
      finite_extinction_of_pointwise_equation_payload
        (surgery_package_with_equation_boundary_pointwise_equation_payload_of_direct_pointwise_equation_payload
          payload) :=
  rfl

/--
The named strengthened surgery-package finite-extinction projection can be
reconstructed from the named direct stored-verification scalar equation payload.
-/
theorem finite_extinction_of_surgery_package_with_equation_boundary_to_direct_pointwise_equation_payload_eq
    {n : ℕ∞ω}
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M] [CompactSpace M]
    [IsManifold ThreeManifoldModelWithCorners 1 M]
    (package : FiniteExtinctionSurgeryPackageWithEquationBoundary n M) :
    finite_extinction_of_surgery_package_with_equation_boundary package =
      finite_extinction_of_direct_pointwise_equation_payload
        (surgery_package_with_equation_boundary_direct_pointwise_equation_payload
          package) := by
  apply Subsingleton.elim

section SurgeryPackageFiniteExtinctionProjectionEqualities

variable {n : ℕ∞ω}
variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace ThreeManifoldModel M] [SimplyConnectedSpace M]
variable [CompactSpace M]
variable [IsManifold ThreeManifoldModelWithCorners 1 M]
variable (package : FiniteExtinctionSurgeryPackage n M)

/-- The surgery-package finite-extinction fundamental-group input is the stored field. -/
theorem finite_extinction_fundamental_group_input_of_surgery_package_eq :
    finite_extinction_fundamental_group_input_of_surgery_package package =
      package.extinctionFundamentalGroupInput := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction sweepout is the stored field. -/
theorem finite_extinction_sweepout_existence_of_surgery_package_eq :
    finite_extinction_sweepout_existence_of_surgery_package package =
      package.extinctionSweepout := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction sweepout parameter space is the stored field. -/
theorem finite_extinction_sweepout_parameter_space_of_surgery_package_eq :
    finite_extinction_sweepout_parameter_space_of_surgery_package package =
      package.extinctionSweepoutParameterSpace := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction sweepout continuity is the stored field. -/
theorem finite_extinction_sweepout_continuity_of_surgery_package_eq :
    finite_extinction_sweepout_continuity_of_surgery_package package =
      package.extinctionSweepoutContinuity := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction sweepout area bound is the stored field. -/
theorem finite_extinction_sweepout_area_bound_of_surgery_package_eq :
    finite_extinction_sweepout_area_bound_of_surgery_package package =
      package.extinctionSweepoutAreaBound := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction sweepout nontriviality is the stored field. -/
theorem finite_extinction_sweepout_nontriviality_of_surgery_package_eq :
    finite_extinction_sweepout_nontriviality_of_surgery_package package =
      package.extinctionSweepoutNontriviality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction area-functional setup is the stored field. -/
theorem finite_extinction_area_functional_setup_of_surgery_package_eq :
    finite_extinction_area_functional_setup_of_surgery_package package =
      package.extinctionAreaFunctional := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction min-max width definition is the stored field. -/
theorem finite_extinction_minmax_width_definition_of_surgery_package_eq :
    finite_extinction_minmax_width_definition_of_surgery_package package =
      package.extinctionMinMaxWidth := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction width compactness is the stored field. -/
theorem finite_extinction_width_compactness_of_surgery_package_eq :
    finite_extinction_width_compactness_of_surgery_package package =
      package.extinctionWidthCompactness := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction width lower semicontinuity is the stored field. -/
theorem finite_extinction_width_lower_semicontinuity_of_surgery_package_eq :
    finite_extinction_width_lower_semicontinuity_of_surgery_package package =
      package.extinctionWidthLowerSemicontinuity := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction minimizing sequence is the stored field. -/
theorem finite_extinction_minimizing_sequence_of_surgery_package_eq :
    finite_extinction_minimizing_sequence_of_surgery_package package =
      package.extinctionMinimizingSequence := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction pull-tight argument is the stored field. -/
theorem finite_extinction_pull_tight_argument_of_surgery_package_eq :
    finite_extinction_pull_tight_argument_of_surgery_package package =
      package.extinctionPullTightArgument := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction min-max stationarity is the stored field. -/
theorem finite_extinction_minmax_stationarity_of_surgery_package_eq :
    finite_extinction_minmax_stationarity_of_surgery_package package =
      package.extinctionMinMaxStationarity := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction minimal-surface regularity is the stored field. -/
theorem finite_extinction_min_surface_regularity_of_surgery_package_eq :
    finite_extinction_min_surface_regularity_of_surgery_package package =
      package.extinctionMinSurfaceRegularity := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction positive-width input is the stored field. -/
theorem finite_extinction_positive_width_of_surgery_package_eq :
    finite_extinction_positive_width_of_surgery_package package =
      package.extinctionPositiveWidth := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction width theory is the stored field. -/
theorem finite_extinction_width_theory_of_surgery_package_eq :
    finite_extinction_width_theory_of_surgery_package package =
      package.extinctionWidthTheory := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction first-variation formula is the stored field. -/
theorem finite_extinction_first_variation_formula_of_surgery_package_eq :
    finite_extinction_first_variation_formula_of_surgery_package package =
      package.extinctionFirstVariationFormula := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction second-variation inequality is the stored field. -/
theorem finite_extinction_second_variation_inequality_of_surgery_package_eq :
    finite_extinction_second_variation_inequality_of_surgery_package package =
      package.extinctionSecondVariationInequality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction Gauss-Bonnet estimate is the stored field. -/
theorem finite_extinction_gauss_bonnet_estimate_of_surgery_package_eq :
    finite_extinction_gauss_bonnet_estimate_of_surgery_package package =
      package.extinctionGaussBonnetEstimate := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction scalar-curvature width bound is the stored field. -/
theorem finite_extinction_scalar_curvature_width_bound_of_surgery_package_eq :
    finite_extinction_scalar_curvature_width_bound_of_surgery_package package =
      package.extinctionScalarCurvatureWidthBound := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction width evolution is the stored field. -/
theorem finite_extinction_width_evolution_of_surgery_package_eq :
    finite_extinction_width_evolution_of_surgery_package package =
      package.extinctionWidthEvolution := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction width differential inequality is the stored field. -/
theorem finite_extinction_width_differential_inequality_of_surgery_package_eq :
    finite_extinction_width_differential_inequality_of_surgery_package package =
      package.extinctionWidthDifferentialInequality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery metric comparison is the stored field. -/
theorem finite_extinction_surgery_metric_comparison_of_surgery_package_eq :
    finite_extinction_surgery_metric_comparison_of_surgery_package package =
      package.extinctionSurgeryMetricComparison := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery width-comparison map is the stored field. -/
theorem finite_extinction_surgery_width_comparison_map_of_surgery_package_eq :
    finite_extinction_surgery_width_comparison_map_of_surgery_package package =
      package.extinctionSurgeryWidthComparisonMap := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery width drop is the stored field. -/
theorem finite_extinction_surgery_width_drop_of_surgery_package_eq :
    finite_extinction_surgery_width_drop_of_surgery_package package =
      package.extinctionSurgeryWidthDrop := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery-discard control is the stored field. -/
theorem finite_extinction_surgery_discard_control_of_surgery_package_eq :
    finite_extinction_surgery_discard_control_of_surgery_package package =
      package.extinctionSurgeryDiscardControl := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction discarded-component width neutrality is the stored field. -/
theorem finite_extinction_discarded_component_width_neutrality_of_surgery_package_eq :
    finite_extinction_discarded_component_width_neutrality_of_surgery_package
        package =
      package.extinctionDiscardedComponentWidthNeutrality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction discarded-component sweepout triviality is the stored field. -/
theorem finite_extinction_discarded_component_sweepout_triviality_of_surgery_package_eq :
    finite_extinction_discarded_component_sweepout_triviality_of_surgery_package
        package =
      package.extinctionDiscardedComponentSweepoutTriviality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction discarded-component classification is the stored field. -/
theorem finite_extinction_discarded_component_classification_of_surgery_package_eq :
    finite_extinction_discarded_component_classification_of_surgery_package
        package =
      package.extinctionDiscardedComponentClassification := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surviving-component tracking is the stored field. -/
theorem finite_extinction_surviving_component_tracking_of_surgery_package_eq :
    finite_extinction_surviving_component_tracking_of_surgery_package package =
      package.extinctionSurvivingComponentTracking := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction component topology is the stored field. -/
theorem finite_extinction_component_topology_of_surgery_package_eq :
    finite_extinction_component_topology_of_surgery_package package =
      package.extinctionComponentTopology := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction curvature pinching is the stored field. -/
theorem finite_extinction_curvature_pinching_of_surgery_package_eq :
    finite_extinction_curvature_pinching_of_surgery_package package =
      package.extinctionCurvaturePinching := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction scalar-curvature lower bound is the stored field. -/
theorem finite_extinction_positive_scalar_curvature_lower_bound_of_surgery_package_eq :
    finite_extinction_positive_scalar_curvature_lower_bound_of_surgery_package
        package =
      package.extinctionPositiveScalarCurvatureLowerBound := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction positive scalar-curvature persistence is the stored field. -/
theorem finite_extinction_positive_scalar_curvature_persistence_of_surgery_package_eq :
    finite_extinction_positive_scalar_curvature_persistence_of_surgery_package
        package =
      package.extinctionPositiveScalarCurvaturePersistence := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction component control is the stored field. -/
theorem finite_extinction_component_control_of_surgery_package_eq :
    finite_extinction_component_control_of_surgery_package package =
      package.extinctionComponentControl := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction volume evolution formula is the stored field. -/
theorem finite_extinction_volume_evolution_formula_of_surgery_package_eq :
    finite_extinction_volume_evolution_formula_of_surgery_package package =
      package.extinctionVolumeEvolutionFormula := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery volume nonincrease is the stored field. -/
theorem finite_extinction_surgery_volume_nonincrease_of_surgery_package_eq :
    finite_extinction_surgery_volume_nonincrease_of_surgery_package package =
      package.extinctionSurgeryVolumeNonincrease := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction scalar-curvature differential inequality is the stored field. -/
theorem finite_extinction_scalar_curvature_differential_inequality_of_surgery_package_eq :
    finite_extinction_scalar_curvature_differential_inequality_of_surgery_package
        package =
      package.extinctionScalarCurvatureDifferentialInequality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction volume differential inequality is the stored field. -/
theorem finite_extinction_volume_differential_inequality_of_surgery_package_eq :
    finite_extinction_volume_differential_inequality_of_surgery_package
        package =
      package.extinctionVolumeDifferentialInequality := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction volume decay estimate is the stored field. -/
theorem finite_extinction_volume_decay_estimate_of_surgery_package_eq :
    finite_extinction_volume_decay_estimate_of_surgery_package package =
      package.extinctionVolumeDecayEstimate := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction time bound is the stored field. -/
theorem finite_extinction_time_bound_of_surgery_package_eq :
    finite_extinction_time_bound_of_surgery_package package =
      package.extinctionTimeBound := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction finite-time integration is the stored field. -/
theorem finite_extinction_finite_time_integration_of_surgery_package_eq :
    finite_extinction_finite_time_integration_of_surgery_package package =
      package.extinctionFiniteTimeIntegration := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction surgery-time summability is the stored field. -/
theorem finite_extinction_surgery_time_summability_of_surgery_package_eq :
    finite_extinction_surgery_time_summability_of_surgery_package package =
      package.extinctionSurgeryTimeSummability := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction extinction-time contradiction is the stored field. -/
theorem finite_extinction_extinction_time_contradiction_of_surgery_package_eq :
    finite_extinction_extinction_time_contradiction_of_surgery_package package =
      package.extinctionExtinctionTimeContradiction := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction differential-inequality integration is the stored field. -/
theorem finite_extinction_differential_inequality_integration_of_surgery_package_eq :
    finite_extinction_differential_inequality_integration_of_surgery_package
        package =
      package.extinctionDifferentialInequalityIntegration := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction derivation is the stored field. -/
theorem finite_extinction_derivation_of_surgery_package_eq :
    finite_extinction_derivation_of_surgery_package package =
      package.extinctionDerivation := by
  apply Subsingleton.elim

/-- The surgery-package finite-extinction conclusion derivation is the stored field. -/
theorem finite_extinction_conclusion_derivation_of_surgery_package_eq :
    finite_extinction_conclusion_derivation_of_surgery_package package =
      package.extinctionConclusionDerivation := by
  apply Subsingleton.elim

end SurgeryPackageFiniteExtinctionProjectionEqualities

end Poincare
