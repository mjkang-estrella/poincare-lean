import Poincare.Global.HausdorffInverseChartFrozenMetricBridge

/-!
# Sharp local upper distance bound from the frozen inverse-chart metric

The local quadratic comparison gives an upper speed bound on every curve in
one coordinate neighborhood.  Here we apply it to the straight coordinate
segment between two nearby chart points.  A clamped version of the segment
is used only to obtain a globally subtype-valued coordinate curve; on
`[0, 1]` it agrees with the ordinary affine segment.

The resulting theorem is the Lipschitz half of the desired local
bi-Lipschitz comparison:

`riemannianEDist (symm z) (symm w) ≤ sqrt (1 + ε) * d_frozen z w`.

The lower half needs the imported chart-confined endpoint estimate together
with short-path confinement to handle the unrestricted path infimum.
-/

noncomputable section

open Bundle Filter Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The frozen speed integral of a constant coordinate velocity on the unit
interval is exactly its frozen linear e-norm. -/
theorem frozenInverseChartSpeedIntegral_const_zero_one
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) (v : E) :
    frozenInverseChartSpeedIntegral g x₀ z₀ (fun _t : ℝ ↦ v) 0 1 =
      let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
      let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
      let e := positiveDefiniteGramLinearEquiv G₀ hG₀
      ‖e v‖ₑ := by
  rw [frozenInverseChartSpeedIntegral]
  simp_rw [sqrt_inverseChartPullbackQuadraticForm_eq_norm_frozenLinearEquiv]
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
  simp only [ENNReal.ofReal_one, mul_one, ofReal_norm_eq_enorm]

/-- On one genuine coordinate ball, inverse-chart Riemannian distance is at
most `sqrt (1 + ε)` times the frozen linear distance. -/
theorem exists_inverseChart_riemannianEDist_le_frozenEDist
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r > 0, ∀ (z w : (extChartAt I x₀).target),
      dist z z₀ < r → dist w z₀ < r →
      Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (z : E))
          ((extChartAt I x₀).symm (w : E)) ≤
        ENNReal.ofReal (Real.sqrt (1 + ε)) *
          frozenInverseChartEDist g x₀ z₀ z w := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChartCurve_pathELength_relative_bounds
      g x₀ z₀ hε0 hε1 with ⟨rq, hrq, hcompare⟩
  rcases Metric.mem_nhds_iff.mp
      ((isOpen_extChartAt_target x₀).mem_nhds z₀.2) with
    ⟨rt, hrt, htarget⟩
  let r := min rq rt
  have hr : 0 < r := lt_min hrq hrt
  refine ⟨r, hr, ?_⟩
  intro z w hz hw
  have hzE : (z : E) ∈ Metric.ball (z₀ : E) r := by
    simpa only [Metric.mem_ball, Subtype.dist_eq] using hz
  have hwE : (w : E) ∈ Metric.ball (z₀ : E) r := by
    simpa only [Metric.mem_ball, Subtype.dist_eq] using hw
  let η := ContinuousAffineMap.lineMap (R := ℝ) (z : E) (w : E)
  have hηball : Icc (0 : ℝ) 1 ⊆
      ⇑η ⁻¹' Metric.ball (z₀ : E) r := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact (convex_ball (z₀ : E) r).segment_subset hzE hwE
  have hηtarget : ∀ t ∈ Icc (0 : ℝ) 1,
      η t ∈ (extChartAt I x₀).target := by
    intro t ht
    apply htarget
    have hball := Metric.mem_ball.mp (hηball ht)
    exact Metric.mem_ball.mpr
      (hball.trans_le (min_le_right rq rt))
  let p := projIcc (0 : ℝ) 1 zero_le_one
  let ηc : ℝ → E := fun t ↦ η (p t)
  have hηcTarget : ∀ t : ℝ, ηc t ∈ (extChartAt I x₀).target := by
    intro t
    exact hηtarget (p t) (p t).2
  let ζ : ℝ → (extChartAt I x₀).target :=
    fun t ↦ ⟨ηc t, hηcTarget t⟩
  let vel : ℝ → E := fun _t ↦ (w : E) - (z : E)
  have hζstay : ∀ t ∈ Ioo (0 : ℝ) 1, dist (ζ t) z₀ < rq := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hval : (ζ t : E) = η t := by
      simp only [ζ, ηc, p, projIcc_of_mem zero_le_one htcc]
    rw [Subtype.dist_eq, hval]
    exact (Metric.mem_ball.mp (hηball htcc)).trans_le (min_le_left rq rt)
  have hζder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ (ζ s : E)) (vel t) t := by
    intro t ht
    have heq : ηc =ᶠ[𝓝 t] η := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      simp only [ηc, p, projIcc_of_mem zero_le_one hs]
    have hline : HasDerivAt η ((w : E) - (z : E)) t := by
      simpa only [ContinuousAffineMap.coe_lineMap_eq, η] using
        (AffineMap.hasDerivAt_lineMap
          (a := (z : E)) (b := (w : E)) (x := t))
    exact hline.congr_of_eventuallyEq heq
  have hupper := (hcompare ζ vel 0 1 hζstay hζder).2
  let γ : ℝ → M := fun t ↦ (extChartAt I x₀).symm (η t)
  let γc : ℝ → M := fun t ↦ (extChartAt I x₀).symm (ζ t : E)
  have hηsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact (ContinuousAffineMap.contDiff η).contDiffOn
  have hγsmooth : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) := by
    exact (contMDiffOn_extChartAt_symm x₀).comp hηsmooth hηtarget
  have hdist :
      Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (z : E))
          ((extChartAt I x₀).symm (w : E)) ≤
        Manifold.pathELength I γ 0 1 := by
    apply Manifold.riemannianEDist_le_pathELength hγsmooth
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · exact zero_le_one
  have hlength : Manifold.pathELength I γ 0 1 =
      Manifold.pathELength I γc 0 1 := by
    apply Manifold.pathELength_congr
    intro t ht
    simp only [γ, γc, ζ, ηc, p, projIcc_of_mem zero_le_one ht]
  calc
    Manifold.riemannianEDist I
        ((extChartAt I x₀).symm (z : E))
        ((extChartAt I x₀).symm (w : E)) ≤
        Manifold.pathELength I γ 0 1 := hdist
    _ = Manifold.pathELength I γc 0 1 := hlength
    _ ≤ ENNReal.ofReal (Real.sqrt (1 + ε)) *
        frozenInverseChartSpeedIntegral g x₀ z₀ vel 0 1 := hupper
    _ = ENNReal.ofReal (Real.sqrt (1 + ε)) *
        frozenInverseChartEDist g x₀ z₀ z w := by
      rw [frozenInverseChartSpeedIntegral_const_zero_one]
      rfl

end Poincare
