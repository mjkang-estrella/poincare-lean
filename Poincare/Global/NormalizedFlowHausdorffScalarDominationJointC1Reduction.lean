import Poincare.Global.HausdorffScalarVarianceContinuity
import Poincare.Global.NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint

/-!
# Scalar-density domination from intrinsic joint `C¹` control

The chart-frame total-scalar endpoint previously accepted a complete
`GlobalFiniteHausdorffChartFrameScalarDomination`.  This module lowers that
analytic bundle to an intrinsic regularity statement.

At one time, the existing density differentiation package is first
restricted to a compact two-sided interval inside its time neighborhood.
The already proved density mean-value estimate supplies an integrable
envelope for the moving densities themselves.  Joint continuity of scalar
curvature and of its actual time derivative then gives uniform bounds on the
compact space-time slab.  These data prove, rather than assume, integrability
of `density * scalar`, measurability of its product-rule derivative, and an
integrable product majorant.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- Restrict a finite Hausdorff chart decomposition to a smaller time set.
All charts, densities, and measure identities are retained literally; only
the membership hypotheses are narrowed. -/
def FiniteHausdorffChartDensityDecomposition.restrictTimeSet
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s s' : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (hsub : s' ⊆ s) :
    FiniteHausdorffChartDensityDecomposition gt s' where
  chartCount := D.chartCount
  coordinateDomain := D.coordinateDomain
  coordinateDomain_measurable := D.coordinateDomain_measurable
  inverseChart := D.inverseChart
  inverseChart_measurable := D.inverseChart_measurable
  manifoldPiece := D.manifoldPiece
  manifoldPiece_measurable := D.manifoldPiece_measurable
  pieces_pairwise := D.pieces_pairwise
  pieces_cover := D.pieces_cover
  density := D.density
  density_nonneg := fun t ht ↦ D.density_nonneg t (hsub ht)
  density_integrable := fun t ht ↦ D.density_integrable t (hsub ht)
  chartMeasure := fun t ht ↦ D.chartMeasure t (hsub ht)

/-- Restrict dominated density differentiation to the same smaller time
set.  The derivative and its integrable majorant are unchanged. -/
def FiniteChartDensityDominatedDifferentiationAt.restrictTimeSet
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s s' : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (hmem : s' ∈ 𝓝 t₀) (hsub : s' ⊆ s) :
    FiniteChartDensityDominatedDifferentiationAt
      (D.restrictTimeSet hsub) t₀ := by
  let D' := D.restrictTimeSet hsub
  exact {
    timeSet_mem := hmem
    densityDerivative := A.densityDerivative
    densityDerivative_aestronglyMeasurable_at := fun i ↦ by
      simpa [D'] using A.densityDerivative_aestronglyMeasurable_at i
    dominatingFunction := A.dominatingFunction
    dominatingFunction_integrable := fun i ↦ by
      simpa [D'] using A.dominatingFunction_integrable i
    densityDerivative_bound := fun i ↦ by
      filter_upwards [A.densityDerivative_bound i] with z hz
      intro t ht
      simpa [D'] using hz t (hsub ht)
    hasDerivAt_density := fun i ↦ by
      filter_upwards [A.hasDerivAt_density i] with z hz
      intro t ht
      simpa [D'] using hz t (hsub ht) }

/-- Intrinsic joint continuity of the actual time derivative of scalar
curvature.  This is a geometric `C¹` regularity statement on space-time,
not a chartwise domination package. -/
def ScalarTimeDerivativeJointContinuous
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) : Prop :=
  Continuous (fun p : ℝ × M ↦
    deriv (fun t ↦ (gt t).scalarAt p.2) p.1)

/-- Restricting a chart-frame density package preserves its intrinsic first
variation formula. -/
theorem FiniteHausdorffChartDensityDecomposition.hasIntrinsicDensityFirstVariationAt_restrictTimeSet
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s s' : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (hDensity : D.HasIntrinsicDensityFirstVariationAt t₀)
    (hsub : s' ⊆ s) :
    (D.restrictTimeSet hsub).HasIntrinsicDensityFirstVariationAt t₀ := by
  intro i z
  simpa [FiniteHausdorffChartDensityDecomposition.restrictTimeSet] using
    hDensity i z

/-- A compact local scalar and scalar-time-derivative bound, combined with
the already proved density envelope, constructs the complete analytic
scalar-density domination package on the restricted time set. -/
noncomputable def finiteChartScalarDensityDominationAt_of_local_joint_bounds
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s target : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (htarget_mem : target ∈ 𝓝 t₀) (htarget_subset : target ⊆ s)
    {S Q : ℝ} (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hScalarBound : ∀ t ∈ target, ∀ x : M,
      ‖(gt t).scalarAt x‖ ≤ S)
    (hScalarTimeDerivativeBound : ∀ t ∈ target, ∀ x : M,
      ‖deriv (fun r ↦ (gt r).scalarAt x) t‖ ≤ Q)
    (hScalarTimeDerivativeJoint : ScalarTimeDerivativeJointContinuous gt) :
    let L : FiniteChartDensityLocalDominationAt A target :=
      A.toLocalDensityDomination htarget_mem htarget_subset
    let hlocalSub : L.timeSet ⊆ s :=
      L.timeSet_subset.trans htarget_subset
    let D' := D.restrictTimeSet hlocalSub
    let A' := A.restrictTimeSet L.timeSet_mem hlocalSub
    FiniteChartScalarDensityDominationAt D' A' := by
  let L : FiniteChartDensityLocalDominationAt A target :=
    A.toLocalDensityDomination htarget_mem htarget_subset
  let hlocalSub : L.timeSet ⊆ s :=
    L.timeSet_subset.trans htarget_subset
  let D' := D.restrictTimeSet hlocalSub
  let A' := A.restrictTimeSet L.timeSet_mem hlocalSub
  let c : ℝ := rawHausdorffLebesgueScale n
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hScalarMeasurable : ∀ (t : ℝ) (i : Fin D'.chartCount),
      AEStronglyMeasurable
        (fun z : D'.coordinateDomain i ↦
          (gt t).scalarAt (D'.inverseChart i z))
        (coordinateLebesgueMeasure (D'.coordinateDomain i)) := by
    intro t i
    exact ((scalarAt_continuous (gt t)).measurable.comp
      (D'.inverseChart_measurable i)).aestronglyMeasurable
  have hDerivativeMeasurable : ∀ (t : ℝ) (i : Fin D'.chartCount),
      AEStronglyMeasurable
        (fun z : D'.coordinateDomain i ↦
          deriv (fun r ↦ (gt r).scalarAt (D'.inverseChart i z)) t)
        (coordinateLebesgueMeasure (D'.coordinateDomain i)) := by
    intro t i
    exact (hScalarTimeDerivativeJoint.measurable.comp
      (measurable_const.prodMk (D'.inverseChart_measurable i)))
        |>.aestronglyMeasurable
  refine {
    scalarDensity_integrable := ?_
    scalarDensityVariation_aestronglyMeasurable_at := ?_
    dominatingFunction := fun i z ↦
      c * (A'.dominatingFunction i z * S +
        L.dominatingFunction i z * Q)
    dominatingFunction_integrable := ?_
    scalarDensityVariation_bound := ?_ }
  · intro t ht i
    change Integrable (fun z : D'.coordinateDomain i ↦
        (rawHausdorffLebesgueScale n : ℝ) *
          (D'.density t i z * (gt t).scalarAt (D'.inverseChart i z)))
      (coordinateLebesgueMeasure (D'.coordinateDomain i))
    have htTarget : t ∈ target := L.timeSet_subset ht
    have hScalarAE : ∀ᵐ z
        ∂(coordinateLebesgueMeasure (D'.coordinateDomain i)),
        ‖(gt t).scalarAt (D'.inverseChart i z)‖ ≤ S :=
      Eventually.of_forall fun z ↦
        hScalarBound t htTarget (D'.inverseChart i z)
    have hProduct :=
      (D'.density_integrable t ht i).bdd_mul
        (hScalarMeasurable t i) hScalarAE
    have hScaled := hProduct.const_mul c
    simpa only [c, mul_comm, mul_left_comm, mul_assoc] using hScaled
  · intro i
    have ht₀ : t₀ ∈ L.timeSet := mem_of_mem_nhds L.timeSet_mem
    have hDensityMeasurable :=
      (D'.density_integrable t₀ ht₀ i).aestronglyMeasurable
    have hFirst :=
      (A'.densityDerivative_aestronglyMeasurable_at i).mul
        (hScalarMeasurable t₀ i)
    have hSecond := hDensityMeasurable.mul (hDerivativeMeasurable t₀ i)
    simpa only [coordinateScalarDensityVariationAt] using
      (hFirst.add hSecond).const_mul c
  · intro i
    exact (((A'.dominatingFunction_integrable i).mul_const S).add
      ((L.dominatingFunction_integrable i).mul_const Q)).const_mul c
  · intro i
    filter_upwards [A'.densityDerivative_bound i,
      L.density_bound i] with z hDensityDerivative hDensity
    intro t ht
    have htTarget : t ∈ target := L.timeSet_subset ht
    have hScalar := hScalarBound t htTarget (D'.inverseChart i z)
    have hDerivative :=
      hScalarTimeDerivativeBound t htTarget (D'.inverseChart i z)
    have hDensityDerivative' := hDensityDerivative t ht
    have hDensity' := hDensity t ht
    have hDerivativeMajorantNonneg :
        0 ≤ A'.dominatingFunction i z :=
      (norm_nonneg (A'.densityDerivative t i z)).trans
        hDensityDerivative'
    have hDensityMajorantNonneg :
        0 ≤ L.dominatingFunction i z :=
      (norm_nonneg (D'.density t i z)).trans hDensity'
    calc
      ‖coordinateScalarDensityVariationAt D' A' t i z‖ =
          c * ‖A'.densityDerivative t i z *
              (gt t).scalarAt (D'.inverseChart i z) +
            D'.density t i z *
              deriv (fun r ↦
                (gt r).scalarAt (D'.inverseChart i z)) t‖ := by
        dsimp only [coordinateScalarDensityVariationAt, c]
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ c *
          (‖A'.densityDerivative t i z *
              (gt t).scalarAt (D'.inverseChart i z)‖ +
            ‖D'.density t i z *
              deriv (fun r ↦
                (gt r).scalarAt (D'.inverseChart i z)) t‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hc
      _ = c *
          (‖A'.densityDerivative t i z‖ *
              ‖(gt t).scalarAt (D'.inverseChart i z)‖ +
            ‖D'.density t i z‖ *
              ‖deriv (fun r ↦
                (gt r).scalarAt (D'.inverseChart i z)) t‖) := by
        rw [norm_mul, norm_mul]
      _ ≤ c *
          (A'.dominatingFunction i z * S +
            L.dominatingFunction i z * Q) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply add_le_add
        · exact mul_le_mul hDensityDerivative' hScalar
            (norm_nonneg _) hDerivativeMajorantNonneg
        · exact mul_le_mul hDensity' hDerivative
            (norm_nonneg _) hDensityMajorantNonneg

/-- Joint `C³` metric entries and intrinsic joint continuity of the scalar
time derivative construct the moving total-scalar derivative at one time.
The proof uses a restricted finite-atlas density package, so no global
chartwise scalar-domination record is assumed. -/
theorem hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
    [Nonempty M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hScalarTimeDerivativeJoint : ScalarTimeDerivativeJointContinuous gt)
    (L : GlobalLichnerowiczAssemblyRegularity gt) (t₀ : ℝ)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hStokes : ClosedLaplacianStokes (gt t₀)
      (fun y ↦ (gt t₀).scalarAt y)) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t₀)) t₀ := by
  let scalarSlabTime : Set ℝ := Icc (t₀ - 1) (t₀ + 1)
  let target : Set ℝ := V.timeSet t₀ ∩ scalarSlabTime
  have hSlabMem : scalarSlabTime ∈ 𝓝 t₀ := by
    apply Icc_mem_nhds <;> dsimp only [scalarSlabTime] <;> linarith
  have htargetMem : target ∈ 𝓝 t₀ := by
    exact inter_mem (V.differentiation t₀).timeSet_mem hSlabMem
  have htargetSubset : target ⊆ V.timeSet t₀ := inter_subset_left
  let scalarSlab : Set (ℝ × M) :=
    scalarSlabTime ×ˢ (Set.univ : Set M)
  have hScalarSlabCompact : IsCompact scalarSlab := by
    dsimp only [scalarSlab, scalarSlabTime]
    exact isCompact_Icc.prod isCompact_univ
  have hScalarJoint : Continuous
      (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
    continuous_scalarAt_joint_of_metricEntriesJointContDiffAt_three hJoint
  obtain ⟨S₀, hS₀⟩ :=
    hScalarSlabCompact.exists_bound_of_continuousOn hScalarJoint.continuousOn
  obtain ⟨Q₀, hQ₀⟩ :=
    hScalarSlabCompact.exists_bound_of_continuousOn
      hScalarTimeDerivativeJoint.continuousOn
  let S : ℝ := |S₀|
  let Q : ℝ := |Q₀|
  have hS : 0 ≤ S := abs_nonneg S₀
  have hQ : 0 ≤ Q := abs_nonneg Q₀
  have hScalarBound : ∀ t ∈ target, ∀ x : M,
      ‖(gt t).scalarAt x‖ ≤ S := by
    intro t ht x
    exact (hS₀ (t, x) ⟨ht.2, Set.mem_univ x⟩).trans (le_abs_self S₀)
  have hDerivativeBound : ∀ t ∈ target, ∀ x : M,
      ‖deriv (fun r ↦ (gt r).scalarAt x) t‖ ≤ Q := by
    intro t ht x
    exact (hQ₀ (t, x) ⟨ht.2, Set.mem_univ x⟩).trans (le_abs_self Q₀)
  let D := V.decomposition t₀
  let A := V.differentiation t₀
  let densityLocal : FiniteChartDensityLocalDominationAt A target :=
    A.toLocalDensityDomination htargetMem htargetSubset
  let hlocalSub : densityLocal.timeSet ⊆ V.timeSet t₀ :=
    densityLocal.timeSet_subset.trans htargetSubset
  let D' := D.restrictTimeSet hlocalSub
  let A' := A.restrictTimeSet densityLocal.timeSet_mem hlocalSub
  let B : FiniteChartScalarDensityDominationAt D' A' :=
    finiteChartScalarDensityDominationAt_of_local_joint_bounds
      A htargetMem htargetSubset hS hQ hScalarBound hDerivativeBound
        hScalarTimeDerivativeJoint
  let scalarDifferentiation :
      FiniteChartScalarDensityDominatedDifferentiationAt D' A' :=
    B.toDominatedDifferentiation
      (fun _i _z s _hs ↦ L.hasDerivAt_scalar_deriv s _)
      (rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlowAt_of_lichnerowicz_of_stokes
        L t₀ hFlow hStokes)
  have hDensity : D'.HasIntrinsicDensityFirstVariationAt t₀ :=
    FiniteHausdorffChartDensityDecomposition.hasIntrinsicDensityFirstVariationAt_restrictTimeSet
      (V.intrinsicDensityFirstVariation t₀) hlocalSub
  exact hasDerivAt_totalScalar_energyNumerator_of_intrinsicChartDensity
    D' A' scalarDifferentiation hDensity hFlow (by norm_num)
    (fun x ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      hFlow (L.timeVariationEntries t₀) x)
    (fun x ↦ L.scalarVariation_stokes t₀ x) hStokes

end Poincare
