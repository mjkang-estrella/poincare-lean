import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity

/-!
# Continuity of scalar variance for compact moving metric families

Weak continuity of the finite Riemannian volume measures and joint
continuity of scalar curvature already give continuity of mean scalar
curvature.  Applying the same moving-integral theorem to
`(R - mean R)^2` therefore gives continuity of scalar variance.

This removes the standalone measurability premise from coercive-gap
finite-dissipation arguments whenever the flow is realized by a continuous
compact parameterization with weakly continuous volume measure.
-/

noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

variable {K : Type v} [TopologicalSpace K]

/-- Scalar variance is continuous on a moving compact metric family once
the finite volume measure is weakly continuous and scalar curvature is
jointly continuous. -/
theorem continuous_scalarVariance_of_continuous_finiteVolumeMeasure_of_joint_scalar
    [Nonempty M]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    Continuous (fun k ↦
      ∫ x, ((metric k).scalarAt x - meanScalar (metric k)) ^ 2
        ∂(volumeMeasure (metric k))) := by
  have hMean : Continuous (fun k ↦ meanScalar (metric k)) :=
    continuous_meanScalar_of_continuous_finiteVolumeMeasure_of_joint_scalar
      metric hMeasure hScalar
  have hCentered : Continuous
      (fun p : K × M ↦
        (metric p.1).scalarAt p.2 - meanScalar (metric p.1)) :=
    hScalar.sub (hMean.comp continuous_fst)
  exact
    continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)) hMeasure
      (fun k x ↦ ((metric k).scalarAt x - meanScalar (metric k)) ^ 2)
      (hCentered.pow 2)

/-- A continuous compact-family parameterization turns the preceding family
continuity into continuity of the physical scalar-variance track on the
forward ray. -/
theorem continuousOn_normalizedFlowScalarVarianceTrack_of_parameterization
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    ContinuousOn (normalizedFlowScalarVarianceTrack gt) (Ici 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hVarianceOnK : Continuous (fun k ↦
      ∫ x, ((metric k).scalarAt x - meanScalar (metric k)) ^ 2
        ∂(volumeMeasure (metric k))) :=
    continuous_scalarVariance_of_continuous_finiteVolumeMeasure_of_joint_scalar
      metric hMeasure hScalar
  have hComp : Continuous (fun t : Ici (0 : ℝ) ↦
      ∫ x,
        ((metric (parameter t)).scalarAt x -
          meanScalar (metric (parameter t))) ^ 2
        ∂(volumeMeasure (metric (parameter t)))) :=
    hVarianceOnK.comp hParameter
  have hEq :
      (fun t : Ici (0 : ℝ) ↦
        normalizedFlowScalarVarianceTrack gt t.1) =
      (fun t : Ici (0 : ℝ) ↦
        ∫ x,
          ((metric (parameter t)).scalarAt x -
            meanScalar (metric (parameter t))) ^ 2
          ∂(volumeMeasure (metric (parameter t)))) := by
    funext t
    rw [hRealizes t]
    rfl
  change Continuous (fun t : Ici (0 : ℝ) ↦
    normalizedFlowScalarVarianceTrack gt t.1)
  rw [hEq]
  exact hComp

/-- The compact continuity package supplies exactly the restricted
almost-everywhere strong measurability used by the coercive-gap argument. -/
theorem normalizedFlowScalarVarianceTrack_aestronglyMeasurable_of_compact_parameterization
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    AEStronglyMeasurable (normalizedFlowScalarVarianceTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)) := by
  exact
    (continuousOn_normalizedFlowScalarVarianceTrack_of_parameterization
      gt metric parameter hParameter hRealizes hMeasure hScalar)
      |>.aestronglyMeasurable measurableSet_Ici

end Poincare
