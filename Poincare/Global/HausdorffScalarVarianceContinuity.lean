import Poincare.Global.HausdorffChartFrameFirstVariation
import Poincare.Global.MetricFlowJointScalarContinuity

/-!
# Continuity of the moving scalar variance from finite charts

The normalized-flow endpoint needs time measurability of

`t ↦ ∫ (R(g(t)) - meanScalar(g(t)))² dμ_{g(t)}`.

This module pushes that regularity boundary through the existing finite
Hausdorff chart decomposition.  Joint `C³` metric entries give pointwise time
continuity of scalar curvature, the already-proved density derivative gives
continuity of each moving chart density, and continuity of the mean scalar
handles the centering term.  The sole new analytic datum is an integrable,
time-uniform bound for each finite coordinate variance density near the time
under consideration.  Dominated convergence and finite summation then prove
continuity of the intrinsic moving integral.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- The coordinate representative of the moving centered scalar-square
integral, including the raw-Hausdorff normalization and chart density. -/
noncomputable def coordinateScalarVarianceDensityAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    (t : ℝ) (i : Fin D.chartCount) (z : D.coordinateDomain i) : ℝ :=
  (rawHausdorffLebesgueScale n : ℝ) *
    (D.density t i z *
      ((gt t).scalarAt (D.inverseChart i z) - meanScalar (gt t)) ^ 2)

/-- The intrinsic scalar variance is the finite sum of its coordinate
variance densities. -/
theorem centeredScalarVarianceIntegral_eq_sum_coordinateScalarVarianceDensity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    (D : FiniteHausdorffChartDensityDecomposition gt s)
    {t : ℝ} (ht : t ∈ s) :
    (∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
      ∂(volumeMeasure (gt t))) =
      ∑ i : Fin D.chartCount,
        ∫ z : D.coordinateDomain i,
          coordinateScalarVarianceDensityAt D t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i)) := by
  simpa only [coordinateScalarVarianceDensityAt, mul_assoc] using
    integral_eq_sum_rawHausdorff_coordinateDensity D ht
      (fun x ↦ ((gt t).scalarAt x - meanScalar (gt t)) ^ 2)
      (centeredScalarSq_integrable (gt t))

/-- A local integrable majorant for the moving chart densities themselves.
The target neighborhood can be any neighborhood contained in the
decomposition time set. -/
structure FiniteChartDensityLocalDominationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (target : Set ℝ) where
  timeSet : Set ℝ
  timeSet_mem : timeSet ∈ 𝓝 t₀
  timeSet_subset : timeSet ⊆ target
  dominatingFunction :
    (i : Fin D.chartCount) → D.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  density_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ timeSet,
        ‖D.density t i z‖ ≤ dominatingFunction i z

/-- The derivative majorant already present in the chart-density package
produces an integrable majorant for the densities on a smaller closed time
interval.  This is the mean-value-theorem step needed before dominated
convergence can be applied to nonlinear curvature densities. -/
noncomputable def FiniteChartDensityDominatedDifferentiationAt.toLocalDensityDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s target : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (htarget_mem : target ∈ 𝓝 t₀) (htarget_subset : target ⊆ s) :
    FiniteChartDensityLocalDominationAt A target := by
  let hballExists := Metric.mem_nhds_iff.mp htarget_mem
  let ε : ℝ := Classical.choose hballExists
  have hεball := Classical.choose_spec hballExists
  have hε : 0 < ε := hεball.1
  have hball : Metric.ball t₀ ε ⊆ target := hεball.2
  let radius : ℝ := ε / 2
  let localTimeSet : Set ℝ := Icc (t₀ - radius) (t₀ + radius)
  have hradius : 0 < radius := by
    dsimp only [radius]
    linarith
  have hradius_lt : radius < ε := by
    dsimp only [radius]
    linarith
  have hlocal_mem : localTimeSet ∈ 𝓝 t₀ := by
    apply Icc_mem_nhds <;> dsimp only [localTimeSet] <;> linarith
  have hlocal_subset : localTimeSet ⊆ target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [localTimeSet] at ht
    constructor <;> linarith [ht.1, ht.2, hradius_lt]
  have hlocal_subset_s : localTimeSet ⊆ s :=
    hlocal_subset.trans htarget_subset
  have ht₀local : t₀ ∈ localTimeSet := by
    dsimp only [localTimeSet]
    constructor <;> linarith
  refine
    { timeSet := localTimeSet
      timeSet_mem := hlocal_mem
      timeSet_subset := hlocal_subset
      dominatingFunction := fun i z ↦
        ‖D.density t₀ i z‖ + radius * A.dominatingFunction i z
      dominatingFunction_integrable := ?_
      density_bound := ?_ }
  · intro i
    have ht₀s : t₀ ∈ s := hlocal_subset_s ht₀local
    exact
      (D.density_integrable t₀ ht₀s i).norm.add
        ((A.dominatingFunction_integrable i).const_mul radius)
  · intro i
    filter_upwards [A.hasDerivAt_density i,
      A.densityDerivative_bound i] with z hDerivative hDerivativeBound
    intro t ht
    have hGnonneg : 0 ≤ A.dominatingFunction i z :=
      (norm_nonneg (A.densityDerivative t₀ i z)).trans
        (hDerivativeBound t₀ (hlocal_subset_s ht₀local))
    have hMVT :
        ‖D.density t i z - D.density t₀ i z‖ ≤
          A.dominatingFunction i z * ‖t - t₀‖ :=
      (convex_Icc (t₀ - radius) (t₀ + radius)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun r ↦ D.density r i z)
        (f' := fun r ↦ A.densityDerivative r i z)
        (C := A.dominatingFunction i z)
        (fun r hr ↦
          (hDerivative r (hlocal_subset_s hr)).hasDerivWithinAt)
        (fun r hr ↦ hDerivativeBound r (hlocal_subset_s hr))
        ht₀local ht
    have hdist : ‖t - t₀‖ ≤ radius := by
      rw [Real.norm_eq_abs, abs_le]
      dsimp only [localTimeSet] at ht
      constructor <;> linarith [ht.1, ht.2]
    calc
      ‖D.density t i z‖ ≤
          ‖D.density t i z - D.density t₀ i z‖ +
            ‖D.density t₀ i z‖ :=
        norm_le_norm_sub_add (D.density t i z) (D.density t₀ i z)
      _ ≤ A.dominatingFunction i z * ‖t - t₀‖ +
            ‖D.density t₀ i z‖ :=
        add_le_add hMVT le_rfl
      _ ≤ A.dominatingFunction i z * radius +
            ‖D.density t₀ i z‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hdist hGnonneg) le_rfl
      _ = ‖D.density t₀ i z‖ +
            radius * A.dominatingFunction i z := by ring

/-- Local dominated-convergence data for the coordinate scalar-variance
densities.  The same time neighborhood as the chart-density differentiation
package is used, so the bound is uniform in time and may vary by chart. -/
structure FiniteChartScalarVarianceDensityDominationAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀) where
  timeSet : Set ℝ
  timeSet_mem : timeSet ∈ 𝓝 t₀
  timeSet_subset : timeSet ⊆ s
  dominatingFunction :
    (i : Fin D.chartCount) → D.coordinateDomain i → ℝ
  dominatingFunction_integrable : ∀ i,
    Integrable (dominatingFunction i)
      (coordinateLebesgueMeasure (D.coordinateDomain i))
  scalarVarianceDensity_bound : ∀ i,
    ∀ᵐ z ∂(coordinateLebesgueMeasure (D.coordinateDomain i)),
      ∀ t ∈ timeSet,
        ‖coordinateScalarVarianceDensityAt D t i z‖ ≤
          dominatingFunction i z

/-- A uniform local bound on the centered scalar curvature, together with the
existing density derivative package, constructs all coordinate
scalar-variance domination data. -/
noncomputable def FiniteChartScalarVarianceDensityDominationAt.of_centeredScalar_bound
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s target : Set ℝ}
    {D : FiniteHausdorffChartDensityDecomposition gt s} {t₀ : ℝ}
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (htarget_mem : target ∈ 𝓝 t₀) (htarget_subset : target ⊆ s)
    {K : ℝ} (hK : 0 ≤ K)
    (hCenteredScalarBound : ∀ t ∈ target, ∀ x : M,
      |(gt t).scalarAt x - meanScalar (gt t)| ≤ K) :
    FiniteChartScalarVarianceDensityDominationAt A := by
  let L : FiniteChartDensityLocalDominationAt A target :=
    A.toLocalDensityDomination htarget_mem htarget_subset
  let c : ℝ := rawHausdorffLebesgueScale n
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  refine
    { timeSet := L.timeSet
      timeSet_mem := L.timeSet_mem
      timeSet_subset := L.timeSet_subset.trans htarget_subset
      dominatingFunction := fun i z ↦
        c * L.dominatingFunction i z * K ^ 2
      dominatingFunction_integrable := ?_
      scalarVarianceDensity_bound := ?_ }
  · intro i
    exact ((L.dominatingFunction_integrable i).const_mul c).mul_const (K ^ 2)
  · intro i
    filter_upwards [L.density_bound i] with z hDensity
    intro t ht
    have htTarget : t ∈ target := L.timeSet_subset ht
    have hCentered :=
      hCenteredScalarBound t htTarget (D.inverseChart i z)
    have hCenteredSq :
        |(gt t).scalarAt (D.inverseChart i z) - meanScalar (gt t)| ^ 2 ≤
          K ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hK).2 hCentered
    have hDensityBound := hDensity t ht
    have hDominatingNonneg : 0 ≤ L.dominatingFunction i z :=
      (norm_nonneg (D.density t i z)).trans hDensityBound
    calc
      ‖coordinateScalarVarianceDensityAt D t i z‖ =
          c * ‖D.density t i z‖ *
            |(gt t).scalarAt (D.inverseChart i z) - meanScalar (gt t)| ^ 2 := by
        simp only [coordinateScalarVarianceDensityAt, norm_mul, norm_pow,
          Real.norm_eq_abs,
          abs_of_nonneg (by positivity :
            0 ≤ (rawHausdorffLebesgueScale n : ℝ))]
        ring
      _ ≤ c * L.dominatingFunction i z * K ^ 2 := by
        gcongr

/-- Forward-local uniform boundedness of the centered scalar curvature,
expressed relative to the time neighborhoods of a global chart-frame volume
package. -/
structure GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt) where
  exists_bound : ∀ t ∈ Ici (0 : ℝ),
    ∃ target : Set ℝ,
      target ∈ 𝓝 t ∧ target ⊆ V.timeSet t ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ s ∈ target, ∀ x : M,
          |(gt s).scalarAt x - meanScalar (gt s)| ≤ K

/-- All-point, all-time joint `C³` metric-entry regularity makes scalar
curvature continuous on the whole space-time product. -/
theorem continuous_scalarAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) := by
  rw [← continuousOn_univ]
  exact
    continuousOn_scalarAt_joint_of_metricEntriesJointContDiffAt_three
      (fun p _hp ↦ hJoint p.1 p.2)

/-- Joint scalar continuity and local continuity of the mean scalar
automatically produce the local centered-scalar bounds required by chartwise
dominated convergence.

For each forward time, scalar curvature is bounded on the compact slab
`[t - 1, t + 1] × M`.  Continuity of the mean at `t` bounds it on a
neighborhood of `t`; intersecting that neighborhood with the slab and the
chart-density time set gives the required common target. -/
noncomputable def
    GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound.of_jointMetricEntriesThree
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hMeanContinuous : ∀ t ∈ Ici (0 : ℝ),
      ContinuousAt (fun s ↦ meanScalar (gt s)) t) :
    GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound V := by
  refine { exists_bound := ?_ }
  intro t ht
  let scalarTimeSet : Set ℝ := Icc (t - 1) (t + 1)
  let meanTimeSet : Set ℝ :=
    (fun s ↦ meanScalar (gt s)) ⁻¹'
      Metric.ball (meanScalar (gt t)) 1
  let target : Set ℝ :=
    (V.timeSet t ∩ scalarTimeSet) ∩ meanTimeSet
  let scalarSlab : Set (ℝ × M) :=
    scalarTimeSet ×ˢ (Set.univ : Set M)
  have hScalarTimeSetMem : scalarTimeSet ∈ 𝓝 t := by
    apply Icc_mem_nhds <;> dsimp only [scalarTimeSet] <;> linarith
  have hMeanTimeSetMem : meanTimeSet ∈ 𝓝 t := by
    simpa only [meanTimeSet] using
      (hMeanContinuous t ht).preimage_mem_nhds
        (Metric.ball_mem_nhds (meanScalar (gt t)) (by norm_num))
  have hTargetMem : target ∈ 𝓝 t := by
    dsimp only [target]
    exact inter_mem
      (inter_mem (V.differentiation t).timeSet_mem hScalarTimeSetMem)
      hMeanTimeSetMem
  have hTargetSubset : target ⊆ V.timeSet t := by
    intro s hs
    exact hs.1.1
  have hScalarSlabCompact : IsCompact scalarSlab := by
    dsimp only [scalarSlab, scalarTimeSet]
    exact isCompact_Icc.prod isCompact_univ
  have hScalarJoint :
      Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
    continuous_scalarAt_joint_of_metricEntriesJointContDiffAt_three hJoint
  obtain ⟨B, hB⟩ :=
    hScalarSlabCompact.exists_bound_of_continuousOn hScalarJoint.continuousOn
  refine ⟨target, hTargetMem, hTargetSubset,
    |B| + (1 + |meanScalar (gt t)|), by positivity, ?_⟩
  intro s hs x
  have hsTarget := hs
  dsimp only [target] at hsTarget
  have hsScalarTime : s ∈ scalarTimeSet := hsTarget.1.2
  have hsMeanTime : s ∈ meanTimeSet := hsTarget.2
  have hScalarNormBound : ‖(gt s).scalarAt x‖ ≤ B := by
    exact hB (s, x)
      (show (s, x) ∈ scalarSlab by
        exact ⟨hsScalarTime, Set.mem_univ x⟩)
  have hScalarAbsBound : |(gt s).scalarAt x| ≤ |B| := by
    have hScalarAbsBound' : |(gt s).scalarAt x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hScalarNormBound
    exact hScalarAbsBound'.trans (le_abs_self B)
  have hMeanDistance :
      |meanScalar (gt s) - meanScalar (gt t)| < 1 := by
    dsimp only [meanTimeSet] at hsMeanTime
    simpa only [Metric.mem_ball, Real.dist_eq] using hsMeanTime
  have hMeanAbsBound :
      |meanScalar (gt s)| ≤ 1 + |meanScalar (gt t)| := by
    calc
      |meanScalar (gt s)| =
          |(meanScalar (gt s) - meanScalar (gt t)) +
            meanScalar (gt t)| := by rw [sub_add_cancel]
      _ ≤ |meanScalar (gt s) - meanScalar (gt t)| +
            |meanScalar (gt t)| := abs_add_le _ _
      _ ≤ 1 + |meanScalar (gt t)| :=
        add_le_add hMeanDistance.le (le_refl _)
  calc
    |(gt s).scalarAt x - meanScalar (gt s)| ≤
        |(gt s).scalarAt x| + |meanScalar (gt s)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le ((gt s).scalarAt x) (-meanScalar (gt s)))
    _ ≤ |B| + (1 + |meanScalar (gt t)|) :=
      add_le_add hScalarAbsBound hMeanAbsBound

/-- The centered-scalar local-bound package and the existing density
derivative data construct the chartwise variance domination consumed by the
continuity theorem. -/
noncomputable def GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound.toScalarVarianceDensityDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {V : GlobalFiniteHausdorffChartFrameDensityVariation gt}
    (H : GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound V)
    (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
    FiniteChartScalarVarianceDensityDominationAt (V.differentiation t) := by
  let hexists := H.exists_bound t ht
  let target : Set ℝ := Classical.choose hexists
  have htarget := Classical.choose_spec hexists
  let K : ℝ := Classical.choose htarget.2.2
  have hKBound := Classical.choose_spec htarget.2.2
  exact
    FiniteChartScalarVarianceDensityDominationAt.of_centeredScalar_bound
      (V.differentiation t) htarget.1 htarget.2.1 hKBound.1 hKBound.2

private theorem continuousAt_finset_sum_real
    {X ι : Type*} [TopologicalSpace X] {x : X}
    (S : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ S, ContinuousAt (f i) x) :
    ContinuousAt (fun y ↦ ∑ i ∈ S, f i y) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) x)
  | @insert a S ha ih =>
      have haContinuous : ContinuousAt (f a) x :=
        hf a (Finset.mem_insert_self a S)
      have hSContinuous : ContinuousAt (fun y ↦ ∑ i ∈ S, f i y) x :=
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using haContinuous.add hSContinuous

/-- Dominated convergence proves continuity of one coordinate
scalar-variance integral. -/
theorem continuousAt_chartScalarVarianceDensityIntegral_of_dominated
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarVarianceDensityDominationAt A)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hMeanContinuous : ContinuousAt (fun t ↦ meanScalar (gt t)) t₀)
    (i : Fin D.chartCount) :
    ContinuousAt
      (fun t ↦
        ∫ z : D.coordinateDomain i,
          coordinateScalarVarianceDensityAt D t i z
          ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
  let μᵢ := coordinateLebesgueMeasure (D.coordinateDomain i)
  have hMeasurable : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (coordinateScalarVarianceDensityAt D t i) μᵢ := by
    filter_upwards [B.timeSet_mem] with t ht
    have hts : t ∈ s := B.timeSet_subset ht
    have hScalarMeasurable : AEStronglyMeasurable
        (fun z : D.coordinateDomain i ↦
          (gt t).scalarAt (D.inverseChart i z)) μᵢ :=
      ((scalarAt_continuous (gt t)).measurable.comp
        (D.inverseChart_measurable i)).aestronglyMeasurable
    have hCenteredSqMeasurable : AEStronglyMeasurable
        (fun z : D.coordinateDomain i ↦
          ((gt t).scalarAt (D.inverseChart i z) - meanScalar (gt t)) ^ 2) μᵢ :=
      AEStronglyMeasurable.pow
        (hScalarMeasurable.sub aestronglyMeasurable_const) 2
    have hDensityMeasurable : AEStronglyMeasurable (D.density t i) μᵢ :=
      (D.density_integrable t hts i).aestronglyMeasurable
    simpa only [coordinateScalarVarianceDensityAt] using
      (hDensityMeasurable.mul hCenteredSqMeasurable).const_mul
        (rawHausdorffLebesgueScale n : ℝ)
  have hBound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ z ∂μᵢ,
      ‖coordinateScalarVarianceDensityAt D t i z‖ ≤
        B.dominatingFunction i z := by
    filter_upwards [B.timeSet_mem] with t ht
    exact (B.scalarVarianceDensity_bound i).mono fun z hz ↦ hz t ht
  have hPointwiseContinuous : ∀ᵐ z ∂μᵢ,
      ContinuousAt (fun t ↦ coordinateScalarVarianceDensityAt D t i z) t₀ := by
    filter_upwards [A.hasDerivAt_density i] with z hz
    have ht₀ : t₀ ∈ s := mem_of_mem_nhds A.timeSet_mem
    have hDensityContinuous : ContinuousAt (fun t ↦ D.density t i z) t₀ :=
      (hz t₀ ht₀).continuousAt
    have hScalarJoint :=
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
        (hJoint (D.inverseChart i z))
    have hTimePath : ContinuousAt
        (fun t : ℝ ↦ (t, D.inverseChart i z)) t₀ :=
      continuousAt_id.prodMk continuousAt_const
    have hScalarContinuous : ContinuousAt
        (fun t ↦ (gt t).scalarAt (D.inverseChart i z)) t₀ := by
      simpa using
        (ContinuousAt.comp'
          (f := fun t : ℝ ↦ (t, D.inverseChart i z))
          (g := fun p : ℝ × M ↦ (gt p.1).scalarAt p.2)
          (x := t₀) hScalarJoint hTimePath)
    simpa only [coordinateScalarVarianceDensityAt] using
      continuousAt_const.mul
        (hDensityContinuous.mul
          ((hScalarContinuous.sub hMeanContinuous).pow 2))
  exact continuousAt_of_dominated hMeasurable hBound
    (B.dominatingFunction_integrable i) hPointwiseContinuous

/-- The finite chart sum and the Hausdorff change-of-variables identity turn
the local dominated hypotheses into continuity of the intrinsic moving
scalar-variance integral at one time. -/
theorem continuousAt_centeredScalarVarianceIntegral_of_finiteChartFrameDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {s : Set ℝ}
    {t₀ : ℝ} (D : FiniteHausdorffChartDensityDecomposition gt s)
    (A : FiniteChartDensityDominatedDifferentiationAt D t₀)
    (B : FiniteChartScalarVarianceDensityDominationAt A)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hMeanContinuous : ContinuousAt (fun t ↦ meanScalar (gt t)) t₀) :
    ContinuousAt
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t))) t₀ := by
  have hCoordinateSum : ContinuousAt
      (fun t ↦
        ∑ i : Fin D.chartCount,
          ∫ z : D.coordinateDomain i,
            coordinateScalarVarianceDensityAt D t i z
            ∂(coordinateLebesgueMeasure (D.coordinateDomain i))) t₀ := by
    apply continuousAt_finset_sum_real Finset.univ
    intro i _hi
    exact continuousAt_chartScalarVarianceDensityIntegral_of_dominated
      D A B hJoint hMeanContinuous i
  apply hCoordinateSum.congr_of_eventuallyEq
  filter_upwards [A.timeSet_mem] with t ht
  exact
    (centeredScalarVarianceIntegral_eq_sum_coordinateScalarVarianceDensity
      D ht)

/-- Global forward-ray form of the finite-chart continuity bridge.  At each
time, the chart-frame volume package supplies its own local decomposition and
density differentiation data; only a matching local variance-density bound
has to be added. -/
theorem continuousOn_centeredScalarVarianceIntegral_of_globalFiniteHausdorffChartFrameDomination
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hMeanContinuous : ∀ t ∈ Ici (0 : ℝ),
      ContinuousAt (fun s ↦ meanScalar (gt s)) t)
    (hVarianceDomination : ∀ t ∈ Ici (0 : ℝ),
      FiniteChartScalarVarianceDensityDominationAt (V.differentiation t)) :
    ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0) := by
  intro t ht
  exact
    (continuousAt_centeredScalarVarianceIntegral_of_finiteChartFrameDomination
      (V.decomposition t) (V.differentiation t)
      (hVarianceDomination t ht) (hJoint t) (hMeanContinuous t ht)).continuousWithinAt

end Poincare
