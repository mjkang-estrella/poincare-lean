import Poincare.Global.HausdorffScalarDensityDomination
import Poincare.Global.NormalizedFlowHausdorffSpatialMixedRegularity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Compactly supported coordinate-flux Stokes assembly

Mathlib does not yet provide an intrinsic divergence theorem for the
Hausdorff-defined Riemannian volume used by this repository.  It does provide
whole-space integration by parts for Frechet derivatives on finite-dimensional
real vector spaces.

This file combines that theorem with the existing finite Hausdorff chart
partition.  The remaining input is explicit coordinate geometry: on each
chart, the weighted pullback of the Laplacian is the Euclidean divergence of
a compactly supported `C¹` flux whose support lies in the chart domain.  From
these data we prove, rather than assume, both integrability of the intrinsic
Laplacian and vanishing of its integral.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section EuclideanDivergence

variable {n : ℕ}

local notation "E" => ClosedSmoothModel n

/-- Euclidean coordinate divergence, written componentwise so that Mathlib's
whole-space integration-by-parts theorem applies directly. -/
noncomputable def euclideanCoordinateDivergence
    (F : Fin n → E → ℝ) (x : E) : ℝ :=
  ∑ j : Fin n,
    fderiv ℝ (F j) x (EuclideanSpace.single j (1 : ℝ))

/-- A compactly supported `C¹` scalar field has integrable directional
derivative, and the whole-space integral of that derivative vanishes. -/
theorem fderiv_apply_integrable_and_integral_eq_zero_of_contDiff_one_of_hasCompactSupport
    (q : E → ℝ) (v : E)
    (hq : ContDiff ℝ 1 q) (hcompact : HasCompactSupport q) :
    Integrable (fun x : E ↦ fderiv ℝ q x v) ∧
      (∫ x : E, fderiv ℝ q x v) = 0 := by
  have hqInt : Integrable q :=
    hq.continuous.integrable_of_hasCompactSupport hcompact
  have hDerivContinuous : Continuous (fun x : E ↦ fderiv ℝ q x v) :=
    (hq.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDerivCompact : HasCompactSupport (fun x : E ↦ fderiv ℝ q x v) :=
    hcompact.fderiv_apply ℝ v
  have hDerivInt : Integrable (fun x : E ↦ fderiv ℝ q x v) :=
    hDerivContinuous.integrable_of_hasCompactSupport hDerivCompact
  refine ⟨hDerivInt, ?_⟩
  have hParts :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun _ : E ↦ (1 : ℝ)) (g := q) (v := v)
      (by simp)
      (by simpa using hDerivInt)
      (by simpa using hqInt)
      (fun _x _hx ↦ differentiableAt_const (1 : ℝ))
      (fun x _hx ↦ hq.differentiable one_ne_zero x)
  simpa using hParts

/-- A finite sum of compactly supported `C¹` coordinate flux derivatives is
integrable on Euclidean space. -/
theorem euclideanCoordinateDivergence_integrable
    (F : Fin n → E → ℝ)
    (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hcompact : ∀ j, HasCompactSupport (F j)) :
    Integrable (euclideanCoordinateDivergence F) := by
  unfold euclideanCoordinateDivergence
  exact integrable_finsetSum Finset.univ fun j _hj ↦
    (fderiv_apply_integrable_and_integral_eq_zero_of_contDiff_one_of_hasCompactSupport
      (F j) (EuclideanSpace.single j (1 : ℝ)) (hF j) (hcompact j)).1

/-- Whole-space Euclidean divergence integrates to zero for compactly
supported `C¹` coordinate fluxes. -/
theorem integral_euclideanCoordinateDivergence_eq_zero
    (F : Fin n → E → ℝ)
    (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hcompact : ∀ j, HasCompactSupport (F j)) :
    (∫ x : E, euclideanCoordinateDivergence F x) = 0 := by
  unfold euclideanCoordinateDivergence
  rw [integral_finsetSum Finset.univ fun j _hj ↦
      (fderiv_apply_integrable_and_integral_eq_zero_of_contDiff_one_of_hasCompactSupport
        (F j) (EuclideanSpace.single j (1 : ℝ)) (hF j) (hcompact j)).1]
  apply Finset.sum_eq_zero
  intro j _hj
  exact
    (fderiv_apply_integrable_and_integral_eq_zero_of_contDiff_one_of_hasCompactSupport
      (F j) (EuclideanSpace.single j (1 : ℝ)) (hF j) (hcompact j)).2

/-- If every component's topological support lies in `U`, its coordinate
divergence vanishes off `U`. -/
theorem euclideanCoordinateDivergence_eq_zero_of_not_mem
    (F : Fin n → E → ℝ) {U : Set E}
    (hsupport : ∀ j, tsupport (F j) ⊆ U)
    {x : E} (hx : x ∉ U) :
    euclideanCoordinateDivergence F x = 0 := by
  unfold euclideanCoordinateDivergence
  apply Finset.sum_eq_zero
  intro j _hj
  have hxj : x ∉ tsupport (F j) := fun hx' ↦ hx (hsupport j hx')
  rw [fderiv_of_notMem_tsupport ℝ hxj]
  simp

end EuclideanDivergence

section FiniteChartStokes

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

/-- Explicit local data that turn a finite Hausdorff chart decomposition into
Stokes for one scalar function at one time.

The fields contain no integral cancellation assertion.  Each flux component
is an actual compactly supported `C¹` Euclidean function, its support lies in
the corresponding coordinate domain, and its divergence is pointwise the
weighted pullback of the intrinsic Laplacian. -/
structure FiniteChartCompactlySupportedLaplacianFluxAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (t : ℝ) (f : M → ℝ) where
  laplacian_aestronglyMeasurable :
    AEStronglyMeasurable (fun x : M ↦ (gt t).laplacianAt f x)
      (volumeMeasure (gt t))
  fluxComponent : (i : Fin D.chartCount) → Fin n → E → ℝ
  fluxComponent_contDiff_one : ∀ i j,
    ContDiff ℝ 1 (fluxComponent i j)
  fluxComponent_hasCompactSupport : ∀ i j,
    HasCompactSupport (fluxComponent i j)
  fluxComponent_tsupport_subset_coordinateDomain : ∀ i j,
    tsupport (fluxComponent i j) ⊆ D.coordinateDomain i
  coordinateLaplacianDensity_eq_divergence : ∀ i,
    ∀ z : D.coordinateDomain i,
      (rawHausdorffLebesgueScale n : ℝ) * D.density t i z *
          (gt t).laplacianAt f (D.inverseChart i z) =
        euclideanCoordinateDivergence (fluxComponent i) z

/-- The weighted pulled-back Laplacian is integrable on every coordinate
domain, derived from compact support and `C¹` regularity of the flux. -/
theorem FiniteChartCompactlySupportedLaplacianFluxAt.coordinateLaplacianDensity_integrable
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s}
    {t : ℝ} {f : M → ℝ}
    (A : FiniteChartCompactlySupportedLaplacianFluxAt D t f)
    (i : Fin D.chartCount) :
    Integrable
      (fun z : D.coordinateDomain i ↦
        (rawHausdorffLebesgueScale n : ℝ) * D.density t i z *
          (gt t).laplacianAt f (D.inverseChart i z))
      (coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  have hDiv : Integrable (euclideanCoordinateDivergence (A.fluxComponent i)) :=
    euclideanCoordinateDivergence_integrable
      (A.fluxComponent i) (A.fluxComponent_contDiff_one i)
        (A.fluxComponent_hasCompactSupport i)
  have hDivOn : IntegrableOn
      (euclideanCoordinateDivergence (A.fluxComponent i))
      (D.coordinateDomain i) := hDiv.integrableOn
  have hSubtype : Integrable
      (fun z : D.coordinateDomain i ↦
        euclideanCoordinateDivergence (A.fluxComponent i) z)
      (coordinateLebesgueMeasure (D.coordinateDomain i)) := by
    simpa [coordinateLebesgueMeasure, Function.comp_def] using
      (integrableOn_iff_comap_subtypeVal
        (D.coordinateDomain_measurable i)).mp hDivOn
  apply hSubtype.congr
  exact Eventually.of_forall fun z ↦
    (A.coordinateLaplacianDensity_eq_divergence i z).symm

/-- The pulled-back Laplacian is integrable for the raw Hausdorff coordinate
density measure. -/
theorem FiniteChartCompactlySupportedLaplacianFluxAt.pulledBackLaplacian_integrable
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s}
    {t : ℝ} {f : M → ℝ}
    (A : FiniteChartCompactlySupportedLaplacianFluxAt D t f)
    (ht : t ∈ s) (i : Fin D.chartCount) :
    Integrable
      (fun z : D.coordinateDomain i ↦
        (gt t).laplacianAt f (D.inverseChart i z))
      (rawHausdorffCoordinateDensityMeasure
        (D.coordinateDomain i) (D.density t i)) := by
  let U := D.coordinateDomain i
  let μU := coordinateLebesgueMeasure U
  let c : ℝ := rawHausdorffLebesgueScale n
  let δ : U → ℝ := D.density t i
  let w : U → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (c * δ z)
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hwMeas : AEMeasurable w μU := by
    exact (((D.density_integrable t ht i).aestronglyMeasurable.const_mul c).aemeasurable).ennreal_ofReal
  have hwTop : ∀ᵐ z ∂μU, w z < (⊤ : ℝ≥0∞) :=
    Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top
  rw [rawHausdorffCoordinateDensityMeasure]
  refine (integrable_withDensity_iff_integrable_smul₀' hwMeas hwTop).2 ?_
  have hWeighted := A.coordinateLaplacianDensity_integrable i
  apply hWeighted.congr
  filter_upwards [D.density_nonneg t ht i] with z hz
  have hwReal : (w z).toReal = c * δ z := by
    exact ENNReal.toReal_ofReal (mul_nonneg hc hz)
  rw [hwReal]
  simp only [smul_eq_mul]
  rfl

/-- The explicit chart fluxes derive global intrinsic Laplacian integrability;
it is not a field of the package. -/
theorem FiniteChartCompactlySupportedLaplacianFluxAt.laplacian_integrable
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s}
    {t : ℝ} {f : M → ℝ}
    (A : FiniteChartCompactlySupportedLaplacianFluxAt D t f)
    (ht : t ∈ s) :
    Integrable (fun x : M ↦ (gt t).laplacianAt f x)
      (volumeMeasure (gt t)) := by
  rw [← integrableOn_univ, ← D.pieces_cover,
    integrableOn_finite_iUnion]
  intro i
  let ν := rawHausdorffCoordinateDensityMeasure
    (D.coordinateDomain i) (D.density t i)
  have hMeasMap : AEStronglyMeasurable
      (fun x : M ↦ (gt t).laplacianAt f x)
      (Measure.map (D.inverseChart i) ν) := by
    rw [D.chartMeasure t ht i]
    exact A.laplacian_aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hMap : Integrable (fun x : M ↦ (gt t).laplacianAt f x)
      (Measure.map (D.inverseChart i) ν) :=
    (integrable_map_measure hMeasMap
      (D.inverseChart_measurable i).aemeasurable).2
        (by simpa [ν, Function.comp_def] using
          A.pulledBackLaplacian_integrable ht i)
  rw [D.chartMeasure t ht i] at hMap
  exact hMap

/-- Compactly supported coordinate fluxes prove the primary intrinsic closed
Laplacian Stokes statement. -/
theorem FiniteChartCompactlySupportedLaplacianFluxAt.closedLaplacianStokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s}
    {t : ℝ} {f : M → ℝ}
    (A : FiniteChartCompactlySupportedLaplacianFluxAt D t f)
    (ht : t ∈ s) :
    ClosedLaplacianStokes (gt t) f := by
  have hLapInt := A.laplacian_integrable ht
  refine ⟨hLapInt, ?_⟩
  rw [integral_eq_sum_rawHausdorff_coordinateDensity D ht _ hLapInt]
  apply Finset.sum_eq_zero
  intro i _hi
  calc
    (∫ z : D.coordinateDomain i,
        (rawHausdorffLebesgueScale n : ℝ) * D.density t i z *
          (gt t).laplacianAt f (D.inverseChart i z)
        ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) =
        ∫ z : D.coordinateDomain i,
          euclideanCoordinateDivergence (A.fluxComponent i) z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
            apply integral_congr_ae
            exact Eventually.of_forall fun z ↦
              A.coordinateLaplacianDensity_eq_divergence i z
    _ = ∫ z in D.coordinateDomain i,
          euclideanCoordinateDivergence (A.fluxComponent i) z := by
            simpa [coordinateLebesgueMeasure] using
              integral_subtype_comap (D.coordinateDomain_measurable i)
                (euclideanCoordinateDivergence (A.fluxComponent i))
    _ = ∫ z : E, euclideanCoordinateDivergence (A.fluxComponent i) z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
        euclideanCoordinateDivergence_eq_zero_of_not_mem
          (A.fluxComponent i)
          (A.fluxComponent_tsupport_subset_coordinateDomain i) hz
    _ = 0 := integral_euclideanCoordinateDivergence_eq_zero
      (A.fluxComponent i) (A.fluxComponent_contDiff_one i)
        (A.fluxComponent_hasCompactSupport i)

end FiniteChartStokes

section GlobalStokes

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Explicit compactly supported coordinate fluxes at every time, relative to
an existing global Hausdorff volume-chart package. -/
structure GlobalFiniteHausdorffChartLaplacianFlux
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartDensityVariation gt)
    (f : ℝ → M → ℝ) where
  fluxAt : ∀ t : ℝ,
    FiniteChartCompactlySupportedLaplacianFluxAt
      (V.decomposition t) t (f t)

omit [SecondCountableTopology M] in
/-- The global explicit flux package supplies closed Laplacian Stokes at
every time. -/
theorem GlobalFiniteHausdorffChartLaplacianFlux.closedLaplacianStokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {V : GlobalFiniteHausdorffChartDensityVariation gt}
    {f : ℝ → M → ℝ}
    (A : GlobalFiniteHausdorffChartLaplacianFlux V f) (t : ℝ) :
    ClosedLaplacianStokes (gt t) (f t) :=
  (A.fluxAt t).closedLaplacianStokes
    (mem_of_mem_nhds (V.differentiation t).timeSet_mem)

end GlobalStokes

section DimensionThreeEndpoints

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The LSC Hausdorff/Lichnerowicz endpoint with all-time Stokes derived from
explicit compactly supported coordinate fluxes. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_compactCoordinateFlux_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorff.volumeVariation (fun t y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
      hFlow hHausdorff hLichnerowicz hFlux.closedLaplacianStokes
      hFiniteDissipation hCompact hc hScalarLower

/-- The closed mean-energy-range endpoint with Stokes derived from the same
explicit coordinate flux data. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_compactCoordinateFlux_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorff.volumeVariation (fun t y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff hLichnerowicz hFlux.closedLaplacianStokes
      hFiniteDissipation hRangeClosed hc hScalarLower

/-- Exponential dissipation version of the automatic-coordinate-Stokes
closed-range endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_compactCoordinateFlux_of_closed_meanEnergyRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorff.volumeVariation (fun t y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hRangeClosed : IsClosed (closedMetricMeanTracelessEnergyRange (M := M)))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_closed_meanEnergyRange
      hFlow hHausdorff hLichnerowicz hFlux.closedLaplacianStokes
      hDissipationMeasurable hrate hc hDecay hRangeClosed hScalarLower

end DimensionThreeEndpoints

end Poincare
