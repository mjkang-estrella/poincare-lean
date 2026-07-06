import Poincare.Global.VolumeFiniteness

/-!
# Local inverse-chart comparison for volume finiteness

This file supplies the missing local Lipschitz comparison isolated by
`M5-vol-3_blocked.md`, then feeds it into the measure-theoretic reductions in
`Poincare.Global.VolumeFiniteness`.
-/

noncomputable section

open Set Filter MeasureTheory Manifold Bundle
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem extChartAt_symm_lipschitzOn_closedBall
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∃ r : ℝ, 0 < r ∧
      ∃ K : ℝ≥0,
        letI : MetricSpace M := g.toMetricSpace
        LipschitzOnWith K
          (fun y : ClosedSmoothModel n =>
            (extChartAt (closedSmoothModelWithCorners n) x).symm y)
          (Metric.closedBall
            ((extChartAt (closedSmoothModelWithCorners n) x) x) r) := by
  let I := closedSmoothModelWithCorners n
  letI : RiemannianBundle (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with
    ⟨C, C_pos, hC⟩
  let good : Set (ClosedSmoothModel n) :=
    {y | ‖mfderivWithin 𝓘(ℝ, ClosedSmoothModel n) I
        (extChartAt I x).symm (range I) y‖ₑ < C}
  have hCgood : good ∈ 𝓝[range I] (extChartAt I x x) := by
    change ∀ᶠ y in 𝓝[range I] (extChartAt I x x), y ∈ good
    simpa [good] using hC
  obtain ⟨R, R_pos, hR⟩ : ∃ R > 0,
      Metric.ball ((extChartAt I x) x) R ∩ range I ⊆
        (extChartAt I x).target ∩ good :=
    Metric.mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hCgood)
  refine ⟨R / 2, by positivity, C, ?_⟩
  letI : MetricSpace M := g.toMetricSpace
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  set γ := (extChartAt I x).symm ∘ η
  have hsmall {z : ClosedSmoothModel n}
      (hz : z ∈ Metric.closedBall ((extChartAt I x) x) (R / 2)) :
      z ∈ Metric.ball ((extChartAt I x) x) R ∩ range I := by
    refine ⟨?_, by simp [I]⟩
    have hzdist : dist z ((extChartAt I x) x) ≤ R / 2 := by
      simpa [Metric.mem_closedBall, dist_comm] using hz
    have : dist z ((extChartAt I x) x) < R := hzdist.trans_lt (by linarith)
    simpa [Metric.mem_ball, dist_comm] using this
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩ good) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact fun z hz => hR (hsmall ((convex_closedBall _ _).segment_subset hu hv hz))
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hγ_start : γ 0 = (extChartAt I x).symm u := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hγ_end : γ 1 = (extChartAt I x).symm v := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hdist_path :
      edist ((extChartAt I x).symm u) ((extChartAt I x).symm v) ≤
        pathELength I γ 0 1 := by
    rw [show edist ((extChartAt I x).symm u) ((extChartAt I x).symm v) =
        riemannianEDist I ((extChartAt I x).symm u) ((extChartAt I x).symm v) from
      IsRiemannianManifold.out _ _]
    exact riemannianEDist_le_pathELength
      ((contMDiffOn_extChartAt_symm x).comp η_smooth hη.1)
      hγ_start hγ_end zero_le_one
  apply hdist_path.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have hmfderiv : mfderiv[Icc 0 1] γ t =
      (mfderivWithin 𝓘(ℝ, ClosedSmoothModel n) I
        (extChartAt I x).symm (range I) (η t)) ∘L
        (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have hmfderiv_apply : mfderiv[Icc 0 1] γ t 1 =
      (mfderivWithin 𝓘(ℝ, ClosedSmoothModel n) I
        (extChartAt I x).symm (range I) (η t))
        (mfderiv[Icc 0 1] η t 1) := congr($hmfderiv 1)
  rw [hmfderiv_apply]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp [I, closedSmoothModelWithCorners, η]
    exact le_rfl

omit [MeasurableSpace M] [BorelSpace M] in
theorem exists_compact_lipschitz_extChartAt_symm_image_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∃ s : Set (ClosedSmoothModel n),
      IsCompact s ∧
      (extChartAt (closedSmoothModelWithCorners n) x).symm '' s ∈ 𝓝 x ∧
      ∃ K : ℝ≥0,
        letI : MetricSpace M := g.toMetricSpace
        LipschitzOnWith K
          (extChartAt (closedSmoothModelWithCorners n) x).symm s := by
  rcases extChartAt_symm_lipschitzOn_closedBall g x with ⟨r, r_pos, K, hLip⟩
  refine ⟨Metric.closedBall ((extChartAt (closedSmoothModelWithCorners n) x) x) r,
    isCompact_closedBall _ _, ?_, K, ?_⟩
  · have hpre :
        (extChartAt (closedSmoothModelWithCorners n) x) ⁻¹'
            Metric.ball ((extChartAt (closedSmoothModelWithCorners n) x) x) r ∈ 𝓝 x := by
      exact (continuousAt_extChartAt x).preimage_mem_nhds (Metric.ball_mem_nhds _ r_pos)
    filter_upwards [hpre, extChartAt_source_mem_nhds (I := closedSmoothModelWithCorners n) x]
      with y hy hys
    refine ⟨(extChartAt (closedSmoothModelWithCorners n) x) y, ?_, ?_⟩
    · exact Metric.ball_subset_closedBall hy
    · exact (extChartAt (closedSmoothModelWithCorners n) x).left_inv hys
  · letI : MetricSpace M := g.toMetricSpace
    simpa using hLip

theorem volumeMeasure_isFiniteMeasure
    (g : ClosedSmoothRiemannianMetric n M) :
    IsFiniteMeasure (volumeMeasure g) :=
  volumeMeasure_isFiniteMeasure_of_compact_lipschitz_chart_images g
    (exists_compact_lipschitz_extChartAt_symm_image_nhds g)

end Poincare
