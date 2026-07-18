import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.MetricRescaleCurvature
import Poincare.Global.NormalizedFlowRescaling

/-!
# Constant metric rescaling through a fixed finite inverse atlas

This module proves the integral scaling laws needed by normalized-flow
rescaling without postulating a global distance-scaling theorem for the
Hausdorff-defined volume measure.

On each genuine inverse chart, `g.constSMul c hc` multiplies the coordinate
Gram matrix by `c`.  Its density therefore gains the explicit factor
`sqrt (c ^ n)`.  Applying the base and rescaled variable-metric pullback area
formulas on the same compactness-selected finite cover gives

* `totalVolume (c g) = sqrt (c^n) * totalVolume g`;
* `totalScalar (c g) = sqrt (c^n) * c⁻¹ * totalScalar g`; and
* `meanScalar (c g) = c⁻¹ * meanScalar g` when the base volume is
  nonzero.

The last identity rewrites the scale ODE in `NormalizedFlowRescaling` from
the mean scalar of the already-rescaled metric to the mean scalar of the
base unnormalized flow.  Both base and rescaled inverse-chart area formulas
remain explicit hypotheses.
-/

noncomputable section

open Bundle FiberBundle Filter Matrix MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- Constant rescaling multiplies every entry of the honest inverse-chart
Gram matrix by the same positive factor. -/
theorem inverseChartPullbackGramMatrix_constSMul
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x₀ : M) (z : (extChartAt I x₀).target) :
    inverseChartPullbackGramMatrix (g.constSMul c hc) x₀ z =
      c • inverseChartPullbackGramMatrix g x₀ z := by
  ext i j
  change
    (g.constSMul c hc).metricBilinAt
        (inverseExtendedChartParametrization
          (n := n) (M := M) x₀ z)
        (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2 i)
        (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2 j) =
      c * g.metricBilinAt
        (inverseExtendedChartParametrization
          (n := n) (M := M) x₀ z)
        (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2 i)
        (ClosedSmoothRiemannianMetric.inverseChartEuclideanTangentBasisAt
          (n := n) (M := M) x₀ z.2 j)
  rw [ClosedSmoothRiemannianMetric.constSMul_metricBilinAt]
  rfl

/-- The honest inverse-chart density gains `sqrt (c^n)` under positive
constant rescaling. -/
theorem inverseChartPullbackVolumeDensity_constSMul
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x₀ : M) (z : (extChartAt I x₀).target) :
    inverseChartPullbackVolumeDensity (g.constSMul c hc) x₀ z =
      Real.sqrt (c ^ n) * inverseChartPullbackVolumeDensity g x₀ z := by
  unfold inverseChartPullbackVolumeDensity VolumeDensity.chartVolumeDensity
    VolumeDensity.chartGramDet
  rw [inverseChartPullbackGramMatrix_constSMul]
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [abs_mul, abs_of_nonneg (pow_nonneg hc.le n)]
  rw [Real.sqrt_mul (pow_nonneg hc.le n)]

namespace FiniteExtendedChartCover

/-- Density scaling restricted to one disjoint coordinate piece of the fixed
finite inverse atlas. -/
theorem inverseChartDensity_constSMul
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (i : Fin C.chartCount) (z : C.coordinateDomain i) :
    C.inverseChartDensity (g.constSMul c hc) i z =
      Real.sqrt (c ^ n) * C.inverseChartDensity g i z :=
  inverseChartPullbackVolumeDensity_constSMul
    g c hc (C.anchor i) (C.coordinateTargetPoint i z)

end FiniteExtendedChartCover

/-- Base density-integrability data on the same finite inverse atlas.

Rescaled density integrability is derived from base density integrability and
the proved constant density factor; it is not stored separately.  The two
area-formula fields are retained as a compatibility surface, but the
constructor `ofBaseDensityIntegrable` below fills them automatically. -/
structure FiniteAtlasConstSMulAreaData
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c) where
  baseDensity_integrable : ∀ i : Fin C.chartCount,
    Integrable (C.inverseChartDensity g i)
      (coordinateLebesgueMeasure (C.coordinateDomain i))
  baseAreaFormula : ∀ i : Fin C.chartCount,
    C.RestrictedInverseChartPullbackHausdorffAreaFormula g i
  rescaledAreaFormula : ∀ i : Fin C.chartCount,
    C.RestrictedInverseChartPullbackHausdorffAreaFormula
      (g.constSMul c hc) i

namespace FiniteAtlasConstSMulAreaData

/-- Construct all finite-atlas constant-rescaling measure data from base
density integrability.  Both the base and rescaled area formulas are now
automatic consequences of the inverse-chart Hausdorff area theorem. -/
def ofBaseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c)
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity g i)
        (coordinateLebesgueMeasure (C.coordinateDomain i))) :
    FiniteAtlasConstSMulAreaData C g c hc where
  baseDensity_integrable := hDensity
  baseAreaFormula := fun i ↦
    C.restrictedInverseChartPullbackHausdorffAreaFormula g i
  rescaledAreaFormula := fun i ↦
    C.restrictedInverseChartPullbackHausdorffAreaFormula
      (g.constSMul c hc) i

/-- View the base static metric as all-time finite inverse-chart measure
data. -/
def baseMeasureData
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {g : ClosedSmoothRiemannianMetric n M} {c : ℝ} {hc : 0 < c}
    (H : FiniteAtlasConstSMulAreaData C g c hc) :
    FiniteExtendedChartFrameMeasureData C (fun _t : ℝ ↦ g) Set.univ where
  density_integrable := fun _t _ht i ↦ H.baseDensity_integrable i
  areaFormula := fun _t _ht i ↦
    C.restrictedInverseChartPullbackHausdorffAreaFormula g i

/-- View the rescaled static metric as all-time finite inverse-chart measure
data.  Its density integrability follows from the chartwise scaling law. -/
def rescaledMeasureData
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {g : ClosedSmoothRiemannianMetric n M} {c : ℝ} {hc : 0 < c}
    (H : FiniteAtlasConstSMulAreaData C g c hc) :
    FiniteExtendedChartFrameMeasureData C
      (fun _t : ℝ ↦ g.constSMul c hc) Set.univ where
  density_integrable := fun _t _ht i ↦ by
    rw [show C.inverseChartDensity (g.constSMul c hc) i =
        fun z ↦ Real.sqrt (c ^ n) * C.inverseChartDensity g i z by
      funext z
      exact C.inverseChartDensity_constSMul g c hc i z]
    exact (H.baseDensity_integrable i).const_mul (Real.sqrt (c ^ n))
  areaFormula := fun _t _ht i ↦
    C.restrictedInverseChartPullbackHausdorffAreaFormula
      (g.constSMul c hc) i

/-- The finite-atlas volume formula under constant metric rescaling. -/
theorem totalVolume_constSMul
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {g : ClosedSmoothRiemannianMetric n M} {c : ℝ} {hc : 0 < c}
    (H : FiniteAtlasConstSMulAreaData C g c hc) :
    totalVolume (g.constSMul c hc) =
      Real.sqrt (c ^ n) * totalVolume g := by
  have hbase :=
    totalVolume_eq_sum_integral_of_finiteChartDensityDecomposition
      H.baseMeasureData.toDecomposition (t := 0) (Set.mem_univ 0)
  have hrescaled :=
    totalVolume_eq_sum_integral_of_finiteChartDensityDecomposition
      H.rescaledMeasureData.toDecomposition (t := 0) (Set.mem_univ 0)
  change totalVolume g =
      ∑ i : Fin C.chartCount,
        ∫ z : C.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) * C.inverseChartDensity g i z
          ∂(coordinateLebesgueMeasure (C.coordinateDomain i)) at hbase
  change totalVolume (g.constSMul c hc) =
      ∑ i : Fin C.chartCount,
        ∫ z : C.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) *
            C.inverseChartDensity (g.constSMul c hc) i z
          ∂(coordinateLebesgueMeasure (C.coordinateDomain i)) at hrescaled
  rw [hrescaled, hbase]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by
    change
      (rawHausdorffLebesgueScale n : ℝ) *
          C.inverseChartDensity (g.constSMul c hc) i z =
        Real.sqrt (c ^ n) *
          ((rawHausdorffLebesgueScale n : ℝ) *
            C.inverseChartDensity g i z)
    rw [C.inverseChartDensity_constSMul g c hc i z]
    ring

/-- The finite-atlas total-scalar formula under constant metric rescaling. -/
theorem totalScalar_constSMul
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {g : ClosedSmoothRiemannianMetric n M} {c : ℝ} {hc : 0 < c}
    (H : FiniteAtlasConstSMulAreaData C g c hc) :
    totalScalar (g.constSMul c hc) =
      Real.sqrt (c ^ n) * c⁻¹ * totalScalar g := by
  have hbase :=
    totalScalar_eq_sum_coordinateScalarDensity
      H.baseMeasureData.toDecomposition (t := 0) (Set.mem_univ 0)
  have hrescaled :=
    totalScalar_eq_sum_coordinateScalarDensity
      H.rescaledMeasureData.toDecomposition (t := 0) (Set.mem_univ 0)
  change totalScalar g =
      ∑ i : Fin C.chartCount,
        ∫ z : C.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) *
            (C.inverseChartDensity g i z * g.scalarAt (C.inverseChart i z))
          ∂(coordinateLebesgueMeasure (C.coordinateDomain i)) at hbase
  change totalScalar (g.constSMul c hc) =
      ∑ i : Fin C.chartCount,
        ∫ z : C.coordinateDomain i,
          (rawHausdorffLebesgueScale n : ℝ) *
            (C.inverseChartDensity (g.constSMul c hc) i z *
              (g.constSMul c hc).scalarAt (C.inverseChart i z))
          ∂(coordinateLebesgueMeasure (C.coordinateDomain i)) at hrescaled
  rw [hrescaled, hbase]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z ↦ by
    change
      (rawHausdorffLebesgueScale n : ℝ) *
          (C.inverseChartDensity (g.constSMul c hc) i z *
            (g.constSMul c hc).scalarAt (C.inverseChart i z)) =
        Real.sqrt (c ^ n) * c⁻¹ *
          ((rawHausdorffLebesgueScale n : ℝ) *
            (C.inverseChartDensity g i z * g.scalarAt (C.inverseChart i z)))
    rw [C.inverseChartDensity_constSMul g c hc i z]
    rw [ClosedSmoothRiemannianMetric.constSMul_scalarAt]
    ring

/-- Mean scalar curvature scales by `c⁻¹`.  Nonzero base volume is kept
explicit because `meanScalar` is defined by real division. -/
theorem meanScalar_constSMul
    {C : FiniteExtendedChartCover (n := n) (M := M)}
    {g : ClosedSmoothRiemannianMetric n M} {c : ℝ} {hc : 0 < c}
    (H : FiniteAtlasConstSMulAreaData C g c hc)
    (hVolume : totalVolume g ≠ 0) :
    meanScalar (g.constSMul c hc) = c⁻¹ * meanScalar g := by
  have hscalePos : 0 < Real.sqrt (c ^ n) :=
    Real.sqrt_pos.2 (pow_pos hc n)
  rw [meanScalar, meanScalar]
  change totalScalar (g.constSMul c hc) /
      totalVolume (g.constSMul c hc) =
    c⁻¹ * (totalScalar g / totalVolume g)
  rw [H.totalScalar_constSMul, H.totalVolume_constSMul]
  field_simp [hVolume, hscalePos.ne', ne_of_gt hc]

/-- Constant-rescaling volume scaling from density integrability alone. -/
theorem totalVolume_constSMul_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c)
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity g i)
        (coordinateLebesgueMeasure (C.coordinateDomain i))) :
    totalVolume (g.constSMul c hc) =
      Real.sqrt (c ^ n) * totalVolume g :=
  (ofBaseDensityIntegrable C g c hc hDensity).totalVolume_constSMul

/-- Constant-rescaling total-scalar scaling from density integrability
alone. -/
theorem totalScalar_constSMul_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c)
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity g i)
        (coordinateLebesgueMeasure (C.coordinateDomain i))) :
    totalScalar (g.constSMul c hc) =
      Real.sqrt (c ^ n) * c⁻¹ * totalScalar g :=
  (ofBaseDensityIntegrable C g c hc hDensity).totalScalar_constSMul

/-- Constant-rescaling mean-scalar scaling from density integrability
alone. -/
theorem meanScalar_constSMul_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (g : ClosedSmoothRiemannianMetric n M)
    (c : ℝ) (hc : 0 < c)
    (hDensity : ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity g i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : totalVolume g ≠ 0) :
    meanScalar (g.constSMul c hc) = c⁻¹ * meanScalar g :=
  (ofBaseDensityIntegrable C g c hc hDensity).meanScalar_constSMul hVolume

end FiniteAtlasConstSMulAreaData

/-- The mean scalar of a time-reparameterized positive constant rescaling is
the base-flow mean multiplied by `c(t)⁻¹`, provided both metrics carry the
restricted inverse-chart area formulas on the same finite cover. -/
theorem meanScalar_timeReparameterizedConstRescaling_eq_base
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (harea : ∀ t : ℝ,
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (t : ℝ) :
    meanScalar (timeReparameterizedConstRescaling gt τ c hc t) =
      (c t)⁻¹ * meanScalar (gt (τ t)) := by
  exact (harea t).meanScalar_constSMul (hVolume t)

/-- The implicit normalized-rescaling scale coefficient simplifies to the
mean scalar of the base unnormalized flow. -/
theorem normalizedRescaling_meanCoefficient_eq_base
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (harea : ∀ t : ℝ,
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (t : ℝ) :
    (2 / (n : ℝ)) *
        meanScalar (timeReparameterizedConstRescaling gt τ c hc t) * c t =
      (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
  rw [meanScalar_timeReparameterizedConstRescaling_eq_base
    C gt τ c hc harea hVolume t]
  calc
    (2 / (n : ℝ)) * ((c t)⁻¹ * meanScalar (gt (τ t))) * c t =
        (2 / (n : ℝ)) * meanScalar (gt (τ t)) * ((c t)⁻¹ * c t) := by
          ring
    _ = (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
      rw [inv_mul_cancel₀ (ne_of_gt (hc t)), mul_one]

/-- One-time normalized-flow rescaling theorem whose scale ODE is stated
directly using the base-flow mean scalar. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (harea : ∀ t : ℝ,
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    {t₀ : ℝ} {x : M}
    (hτ : HasDerivAt τ (c t₀)⁻¹ t₀)
    (hscaleBase : HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t₀))) t₀)
    (hflow : IsClosedRicciFlowSolutionAt gt (τ t₀) x)
    (htime : TimeDifferentiableAt gt (τ t₀) x) :
    IsClosedNormalizedRicciFlowSolutionAt
      (timeReparameterizedConstRescaling gt τ c hc) t₀ x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow
      gt τ c hc hτ
  · exact hscaleBase.congr_deriv
      (normalizedRescaling_meanCoefficient_eq_base
        C gt τ c hc harea hVolume t₀).symm
  · exact hflow
  · exact htime

/-- All-time normalized-flow rescaling theorem with the explicit base-mean
scale ODE. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_all_times_of_baseMeanScale
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (harea : ∀ t : ℝ,
      FiniteAtlasConstSMulAreaData C (gt (τ t)) (c t) (hc t))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (hτ : ∀ t : ℝ, HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t : ℝ, HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (hflow : ∀ s : ℝ, ∀ x : M, IsClosedRicciFlowSolutionAt gt s x)
    (htime : ∀ s : ℝ, ∀ x : M, TimeDifferentiableAt gt s x) :
    ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (timeReparameterizedConstRescaling gt τ c hc) t x := by
  intro t x
  exact
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale
      C gt τ c hc harea hVolume (hτ t) (hscaleBase t)
      (hflow (τ t) x) (htime (τ t) x)

/-! The following wrappers remove the now-proved area-formula inputs from
the theorem-facing API.  Only base inverse-chart density integrability is
needed; the rescaled integrability and both area formulas are constructed
internally. -/

/-- Time-dependent mean-scalar rescaling from base density integrability
alone. -/
theorem meanScalar_timeReparameterizedConstRescaling_eq_base_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (hDensity : ∀ t : ℝ, ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (t : ℝ) :
    meanScalar (timeReparameterizedConstRescaling gt τ c hc t) =
      (c t)⁻¹ * meanScalar (gt (τ t)) := by
  apply meanScalar_timeReparameterizedConstRescaling_eq_base
    C gt τ c hc
      (fun s ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
        C (gt (τ s)) (c s) (hc s) (hDensity s))
      hVolume t

/-- The normalized-rescaling mean coefficient from base density
integrability alone. -/
theorem normalizedRescaling_meanCoefficient_eq_base_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (hDensity : ∀ t : ℝ, ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (t : ℝ) :
    (2 / (n : ℝ)) *
        meanScalar (timeReparameterizedConstRescaling gt τ c hc t) * c t =
      (2 / (n : ℝ)) * meanScalar (gt (τ t)) := by
  apply normalizedRescaling_meanCoefficient_eq_base
    C gt τ c hc
      (fun s ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
        C (gt (τ s)) (c s) (hc s) (hDensity s))
      hVolume t

/-- One-time normalized-flow rescaling with the area-formula boundary
removed. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (hDensity : ∀ t : ℝ, ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    {t₀ : ℝ} {x : M}
    (hτ : HasDerivAt τ (c t₀)⁻¹ t₀)
    (hscaleBase : HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t₀))) t₀)
    (hflow : IsClosedRicciFlowSolutionAt gt (τ t₀) x)
    (htime : TimeDifferentiableAt gt (τ t₀) x) :
    IsClosedNormalizedRicciFlowSolutionAt
      (timeReparameterizedConstRescaling gt τ c hc) t₀ x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_of_ricciFlow_of_baseMeanScale
      C gt τ c hc
        (fun s ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
          C (gt (τ s)) (c s) (hc s) (hDensity s))
        hVolume hτ hscaleBase hflow htime

/-- All-time normalized-flow rescaling with only base density integrability
at the measure-theoretic seam. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_all_times_of_baseMeanScale_of_baseDensityIntegrable
    (C : FiniteExtendedChartCover (n := n) (M := M))
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (τ c : ℝ → ℝ) (hc : ∀ t : ℝ, 0 < c t)
    (hDensity : ∀ t : ℝ, ∀ i : Fin C.chartCount,
      Integrable (C.inverseChartDensity (gt (τ t)) i)
        (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hVolume : ∀ t : ℝ, totalVolume (gt (τ t)) ≠ 0)
    (hτ : ∀ t : ℝ, HasDerivAt τ (c t)⁻¹ t)
    (hscaleBase : ∀ t : ℝ, HasDerivAt c
      ((2 / (n : ℝ)) * meanScalar (gt (τ t))) t)
    (hflow : ∀ s : ℝ, ∀ x : M, IsClosedRicciFlowSolutionAt gt s x)
    (htime : ∀ s : ℝ, ∀ x : M, TimeDifferentiableAt gt s x) :
    ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt
        (timeReparameterizedConstRescaling gt τ c hc) t x := by
  apply
    isClosedNormalizedRicciFlowSolutionAt_timeReparameterizedConstRescaling_all_times_of_baseMeanScale
      C gt τ c hc
        (fun s ↦ FiniteAtlasConstSMulAreaData.ofBaseDensityIntegrable
          C (gt (τ s)) (c s) (hc s) (hDensity s))
        hVolume hτ hscaleBase hflow htime

end Poincare
