import Poincare.Global.NormalizedFlowInvariantCompactness
import Poincare.Global.NormalizedFlowForwardFiniteDissipationReduction
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.CompactOpen

/-!
# Continuity of compact mean-energy invariants from weak volume-measure continuity

This file supplies an intrinsic producer for the invariant-continuity hypothesis
used by the compact mean-energy endpoint.  On a compact spatial domain, weak
continuity of a family of finite measures and joint continuity of an integrand
imply continuity of the corresponding moving integral.  The proof uses the
sup-norm continuity obtained by currying the joint integrand; compactness of the
spatial domain supplies the required uniform control.

Applied to Riemannian volume measures, joint continuity of scalar curvature and
of squared traceless-Ricci norm then gives continuity of total volume, total
scalar curvature, traceless-Ricci energy, and hence the mean-energy pair.
-/

noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section MovingFiniteMeasureIntegral

variable {K : Type v} {X : Type u}
variable [TopologicalSpace K]
variable [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- On a compact spatial domain, a jointly continuous real integrand can be
integrated continuously against a weakly continuous family of finite measures.

No separate boundedness hypothesis is needed: joint continuity curries to a
continuous map into the sup-normed space `C(X, ℝ)`, while compactness of `X`
makes every fiber bounded. -/
theorem continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
    (mu : K → FiniteMeasure X)
    (hmu : Continuous mu)
    (f : K → X → ℝ)
    (hf : Continuous (fun p : K × X ↦ f p.1 p.2)) :
    Continuous (fun k ↦ ∫ x, f k x ∂(mu k : Measure X)) := by
  let F : C(K × X, ℝ) :=
    ⟨fun p ↦ f p.1 p.2, hf⟩
  let fc : K → C(X, ℝ) := F.curry
  have hfc : Continuous fc := F.curry.continuous
  change Continuous (fun k ↦ ∫ x, fc k x ∂(mu k : Measure X))
  rw [continuous_iff_continuousAt]
  intro k0
  have hfixed :
      Tendsto
        (fun k ↦ ∫ x, fc k0 x ∂(mu k : Measure X))
        (nhds k0)
        (nhds (∫ x, fc k0 x ∂(mu k0 : Measure X))) :=
    ((FiniteMeasure.continuous_integral_continuousMap (fc k0)).comp hmu).continuousAt
  have hmass : Continuous (fun k ↦ (mu k : Measure X).real univ) := by
    have hone :=
      (FiniteMeasure.continuous_integral_continuousMap (1 : C(X, ℝ))).comp hmu
    simpa using hone
  have hupper :
      Tendsto
        (fun k ↦ (mu k : Measure X).real univ * ‖fc k - fc k0‖)
        (nhds k0) (nhds 0) := by
    have hcontinuous : Continuous
        (fun k ↦ (mu k : Measure X).real univ * ‖fc k - fc k0‖) :=
      hmass.mul ((hfc.sub continuous_const).norm)
    have hzero :
        (mu k0 : Measure X).real univ * ‖fc k0 - fc k0‖ = 0 := by
      rw [sub_self, norm_zero, mul_zero]
    rw [← hzero]
    exact hcontinuous.continuousAt
  have herror :
      Tendsto
        (fun k ↦ ∫ x, (fc k - fc k0) x ∂(mu k : Measure X))
        (nhds k0) (nhds 0) := by
    apply squeeze_zero_norm
    · intro k
      exact
        (BoundedContinuousFunction.mkOfCompact (fc k - fc k0)).norm_integral_le_mul_norm
          (mu k : Measure X)
    · exact hupper
  have hsum := herror.add hfixed
  change Tendsto
    (fun k ↦ ∫ x, fc k x ∂(mu k : Measure X))
    (nhds k0) (nhds (∫ x, fc k0 x ∂(mu k0 : Measure X)))
  have hsum' :
      Tendsto
        (fun k ↦
          (∫ x, (fc k - fc k0) x ∂(mu k : Measure X)) +
            ∫ x, fc k0 x ∂(mu k : Measure X))
        (nhds k0) (nhds (∫ x, fc k0 x ∂(mu k0 : Measure X))) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards with k
  have hk : Integrable (fun x ↦ fc k x) (mu k : Measure X) :=
    (fc k).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace fun x ↦ fc k x)
  have hk0 : Integrable (fun x ↦ fc k0 x) (mu k : Measure X) :=
    (fc k0).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace fun x ↦ fc k0 x)
  change
    (∫ x, fc k x - fc k0 x ∂(mu k : Measure X)) +
      ∫ x, fc k0 x ∂(mu k : Measure X) =
        ∫ x, fc k x ∂(mu k : Measure X)
  rw [integral_sub hk hk0, sub_add_cancel]

end MovingFiniteMeasureIntegral

section ClosedMetricFamily

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The Riemannian volume measure, bundled as a finite measure so that it
carries Mathlib's weak finite-measure topology. -/
def closedMetricFiniteVolumeMeasure
    (g : ClosedSmoothRiemannianMetric 3 M) : FiniteMeasure M :=
  ⟨volumeMeasure g, volumeMeasure_isFiniteMeasure g⟩

@[simp]
theorem closedMetricFiniteVolumeMeasure_toMeasure
    (g : ClosedSmoothRiemannianMetric 3 M) :
    (closedMetricFiniteVolumeMeasure g : Measure M) = volumeMeasure g :=
  rfl

variable {K : Type v} [TopologicalSpace K]

/-- Weak continuity of the finite Riemannian volume measures implies
continuity of total volume. -/
theorem continuous_totalVolume_of_continuous_finiteVolumeMeasure
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k))) :
    Continuous (fun k ↦ totalVolume (metric k)) := by
  have h := continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
    (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)) hMeasure
    (fun _k _x ↦ (1 : ℝ)) continuous_const
  simpa [totalVolume, Measure.real] using h

/-- Weak continuity of the volume measures and joint continuity of scalar
curvature imply continuity of total scalar curvature. -/
theorem continuous_totalScalar_of_continuous_finiteVolumeMeasure_of_joint_scalar
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    Continuous (fun k ↦ totalScalar (metric k)) := by
  simpa [totalScalar] using
    (continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)) hMeasure
      (fun k x ↦ (metric k).scalarAt x) hScalar)

/-- Continuity of total volume and total scalar curvature gives continuity of
mean scalar curvature because a closed nonempty Riemannian manifold has
strictly positive volume. -/
theorem continuous_meanScalar_of_continuous_finiteVolumeMeasure_of_joint_scalar
    [Nonempty M]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2)) :
    Continuous (fun k ↦ meanScalar (metric k)) := by
  have hVolume :=
    continuous_totalVolume_of_continuous_finiteVolumeMeasure metric hMeasure
  have hScalarIntegral :=
    continuous_totalScalar_of_continuous_finiteVolumeMeasure_of_joint_scalar
      metric hMeasure hScalar
  exact hScalarIntegral.div hVolume fun k ↦ totalVolume_ne_zero (metric k)

/-- Weak continuity of the volume measures and joint continuity of squared
traceless-Ricci norm imply continuity of total traceless-Ricci energy. -/
theorem continuous_tracelessRicciEnergy_of_continuous_finiteVolumeMeasure_of_joint
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hTracelessRicci : Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)) :
    Continuous
      (fun k ↦ ∫ x, (metric k).tracelessRicciNormSqAt x
        ∂(volumeMeasure (metric k))) := by
  simpa using
    (continuous_movingIntegral_of_continuous_finiteMeasure_of_joint
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)) hMeasure
      (fun k x ↦ (metric k).tracelessRicciNormSqAt x) hTracelessRicci)

/-- A continuous compact-family parameterization turns weak volume-measure
continuity and joint traceless-curvature continuity into continuity of the
actual forward traceless-Ricci energy track.

This is the direct bridge from the compact moving-measure endpoint data to
the measurability hypothesis used by the forward exponential-integrability
argument. -/
theorem continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hParameter : Continuous parameter)
    (hRealizes : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hTracelessRicci : Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)) :
    ContinuousOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hEnergyOnK : Continuous
      (fun k ↦ ∫ x, (metric k).tracelessRicciNormSqAt x
        ∂(volumeMeasure (metric k))) :=
    continuous_tracelessRicciEnergy_of_continuous_finiteVolumeMeasure_of_joint
      metric hMeasure hTracelessRicci
  have hComp : Continuous
      (fun t : Ici (0 : ℝ) ↦
        ∫ x, (metric (parameter t)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (metric (parameter t)))) :=
    hEnergyOnK.comp hParameter
  have hEq :
      (fun t : Ici (0 : ℝ) ↦
        normalizedFlowTracelessRicciEnergyTrack gt t.1) =
      (fun t : Ici (0 : ℝ) ↦
        ∫ x, (metric (parameter t)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (metric (parameter t)))) := by
    funext t
    rw [hRealizes t]
    rfl
  change Continuous
    (fun t : Ici (0 : ℝ) ↦
      normalizedFlowTracelessRicciEnergyTrack gt t.1)
  rw [hEq]
  exact hComp

/-- The intrinsic continuity package needed by the compact mean-energy
endpoint.  No continuity structure on the type of metrics is required. -/
theorem continuous_closedMetricMeanTracelessEnergyPair_of_measure_of_joint
    [Nonempty M]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hMeasure : Continuous
      (fun k : K ↦ closedMetricFiniteVolumeMeasure (metric k)))
    (hScalar : Continuous
      (fun p : K × M ↦ (metric p.1).scalarAt p.2))
    (hTracelessRicci : Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)) :
    Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) := by
  have hMean :=
    continuous_meanScalar_of_continuous_finiteVolumeMeasure_of_joint_scalar
      metric hMeasure hScalar
  have hEnergy :=
    continuous_tracelessRicciEnergy_of_continuous_finiteVolumeMeasure_of_joint
      metric hMeasure hTracelessRicci
  exact hMean.prodMk hEnergy

end ClosedMetricFamily

end Poincare
