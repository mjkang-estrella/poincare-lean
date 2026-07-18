import Poincare.Global.HausdorffInverseChartLocalFrozenHausdorffUpper
import Poincare.Global.AntilipschitzMathlib

/-!
# Local frozen-metric anti-Lipschitz and Hausdorff lower bounds

This file proves the lower half of the local frozen-metric comparison.

First, an arbitrary manifold path confined to the comparison chart ball is
clamped with `projIcc`, mapped through the extended chart, and bundled as a
globally target-valued coordinate curve.  The chart-confined frozen endpoint
estimate therefore applies to every such manifold path, not only to paths
presented initially in inverse-chart coordinates.

Second, Mathlib's intrinsic-distance neighborhood basis gives a positive exit
cost from that comparison neighborhood.  On a smaller target ball, both
endpoints and their frozen separation are so small that a hypothetical path
shorter than the desired lower bound cannot exit.  Thus every path satisfies
the lower bound, which promotes through the path infimum to an
`AntilipschitzWith` theorem.  Mathlib's Hausdorff API then gives the local
measure lower inequality.
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

private theorem ennreal_quarter_pos_frozen {δ : ℝ≥0} (hδ : 0 < δ) :
    (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 4 := by
  rw [← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]
  exact div_pos hδ (by norm_num : (0 : ℝ≥0) < 4)

private theorem ennreal_eighth_pos_frozen {δ : ℝ≥0} (hδ : 0 < δ) :
    (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 8 := by
  rw [← ENNReal.coe_ofNat 8,
    ← ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]
  exact div_pos hδ (by norm_num : (0 : ℝ≥0) < 8)

private theorem ennreal_quarter_add_quarter_lt_frozen
    {δ : ℝ≥0} (hδ : 0 < δ) :
    (δ : ℝ≥0∞) / 4 + (δ : ℝ≥0∞) / 4 < (δ : ℝ≥0∞) := by
  rw [← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
  exact NNReal.coe_lt_coe.mp (by
    have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    norm_num
    nlinarith)

private theorem ennreal_eighth_add_eighth_le_quarter_frozen
    (δ : ℝ≥0) :
    (δ : ℝ≥0∞) / 8 + (δ : ℝ≥0∞) / 8 ≤
      (δ : ℝ≥0∞) / 4 := by
  rw [← ENNReal.coe_ofNat 8, ← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
    ← ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
  apply le_of_eq
  apply NNReal.eq
  norm_num
  ring

private theorem ofReal_nnreal_div_eight_frozen (δ : ℝ≥0) :
    ENNReal.ofReal ((δ : ℝ) / 8) = (δ : ℝ≥0∞) / 8 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8)]
  rw [ENNReal.ofReal_coe_nnreal]
  norm_num

/-- Frozen linear distance is symmetric. -/
theorem frozenInverseChartEDist_comm
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ a b : (extChartAt I x₀).target) :
    frozenInverseChartEDist g x₀ z₀ a b =
      frozenInverseChartEDist g x₀ z₀ b a := by
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  change ‖e ((b : E) - (a : E))‖ₑ = ‖e ((a : E) - (b : E))‖ₑ
  rw [← neg_sub (a : E) (b : E), map_neg, enorm_neg]

/-- Frozen linear distance satisfies the triangle inequality, stated in the
unbundled form used by the path comparison modules. -/
theorem frozenInverseChartEDist_triangle
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ a b c : (extChartAt I x₀).target) :
    frozenInverseChartEDist g x₀ z₀ a c ≤
      frozenInverseChartEDist g x₀ z₀ a b +
        frozenInverseChartEDist g x₀ z₀ b c := by
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  simpa only [frozenInverseChartEDist, G₀, hG₀, e,
    ← edist_eq_enorm_sub, map_sub, add_comm] using
    (edist_triangle (e (c : E)) (e (b : E)) (e (a : E)))

/-- Every manifold path confined to the comparison chart ball satisfies the
sharp frozen-endpoint path-length lower bound.  The input path need not be
presented in coordinates. -/
theorem exists_chartConfined_pathELength_ge_frozenEndpoint
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r > 0, ∀ (a b : (extChartAt I x₀).target) {γ : ℝ → M},
      ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
      γ 0 = (extChartAt I x₀).symm (a : E) →
      γ 1 = (extChartAt I x₀).symm (b : E) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        γ t ∈ (extChartAt I x₀).source ∧
          dist ((extChartAt I x₀) (γ t)) (z₀ : E) < r) →
      ENNReal.ofReal (Real.sqrt (1 - ε)) *
          frozenInverseChartEDist g x₀ z₀ a b ≤
        Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChartCurve_pathELength_ge_frozenEndpoint
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hcoord⟩
  refine ⟨r, hr, ?_⟩
  intro a b γ hγ hγ0 hγ1 hstay
  let p := projIcc (0 : ℝ) 1 zero_le_one
  let γc : ℝ → M := fun t ↦ γ (p t)
  let f : Icc (0 : ℝ) 1 → M := fun t ↦ γ t
  have hf : ContMDiff (modelWithCornersEuclideanHalfSpace 1) I 1 f := by
    rw [← contMDiffOn_comp_projIcc_iff]
    apply hγ.congr
    intro t ht
    simp only [Function.comp_apply, f, projIcc_of_mem zero_le_one ht]
  have hγcSource : ∀ t : ℝ, γc t ∈ (extChartAt I x₀).source := by
    intro t
    exact (hstay (p t) (p t).2).1
  let zval : ℝ → E := fun t ↦ (extChartAt I x₀) (γc t)
  have hzvalTarget : ∀ t : ℝ, zval t ∈ (extChartAt I x₀).target := by
    intro t
    exact (extChartAt I x₀).map_source (hγcSource t)
  let z : ℝ → (extChartAt I x₀).target :=
    fun t ↦ ⟨zval t, hzvalTarget t⟩
  have hγcSmooth : ContMDiffOn 𝓘(ℝ) I 1 γc (Icc (0 : ℝ) 1) := by
    simpa only [γc, p, f, Function.comp_apply] using
      (contMDiffOn_comp_projIcc_iff.2 hf)
  have hγcChartSource : ∀ t ∈ Icc (0 : ℝ) 1,
      γc t ∈ (chartAt E x₀).source := by
    intro t ht
    simpa only [extChartAt_source] using hγcSource t
  have hzMDiff : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 zval (Icc (0 : ℝ) 1) := by
    exact contMDiffOn_extChartAt.comp (I' := I)
      (t := (chartAt E x₀).source) hγcSmooth hγcChartSource
  have hzcont : ContDiffOn ℝ 1 zval (Icc (0 : ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mp hzMDiff
  let vel : ℝ → E := fun t ↦ deriv zval t
  have hzder : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt zval (vel t) t := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    exact ((hzcont t htcc).contDiffAt (Icc_mem_nhds ht.1 ht.2))
      |>.differentiableAt one_ne_zero |>.hasDerivAt
  have hzstay : ∀ t ∈ Ioo (0 : ℝ) 1, dist (z t) z₀ < r := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hp : (p t : ℝ) = t := by
      simpa only [p] using
        congrArg Subtype.val (projIcc_of_mem zero_le_one htcc)
    rw [Subtype.dist_eq]
    simpa only [z, zval, γc, p, hp] using (hstay t htcc).2
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hz0 : z 0 = a := by
    apply Subtype.ext
    change (extChartAt I x₀) (γ (p 0)) = (a : E)
    have hp0 : (p 0 : ℝ) = 0 := by
      simpa only [p] using
        congrArg Subtype.val (projIcc_of_mem zero_le_one h0mem)
    rw [hp0, hγ0]
    exact (extChartAt I x₀).right_inv a.2
  have hz1 : z 1 = b := by
    apply Subtype.ext
    change (extChartAt I x₀) (γ (p 1)) = (b : E)
    have hp1 : (p 1 : ℝ) = 1 := by
      simpa only [p] using
        congrArg Subtype.val (projIcc_of_mem zero_le_one h1mem)
    rw [hp1, hγ1]
    exact (extChartAt I x₀).right_inv b.2
  have hlower := hcoord z vel zero_le_one hzstay hzcont hzder
  rw [hz0, hz1] at hlower
  apply hlower.trans_eq
  apply Manifold.pathELength_congr
  intro t ht
  change (extChartAt I x₀).symm ((extChartAt I x₀) (γ (p t))) = γ t
  have hpt : (p t : ℝ) = t := by
    simpa only [p] using
      congrArg Subtype.val (projIcc_of_mem zero_le_one ht)
  rw [hpt]
  exact (extChartAt I x₀).left_inv (hstay t ht).1

/-- On a sufficiently small target ball, every manifold path between two
inverse-chart points satisfies the sharp frozen-endpoint lower bound.  Paths
which remain in the comparison neighborhood are handled by
`exists_chartConfined_pathELength_ge_frozenEndpoint`; a path which exits would
have to pay a fixed positive intrinsic length, contradicting the fact that
the frozen endpoint bound has been made smaller than that exit cost. -/
theorem exists_inverseChart_pairwise_pathELength_ge_frozenEndpoint
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ ρ > 0, ∀ (a b : (extChartAt I x₀).target),
      dist a z₀ < ρ → dist b z₀ < ρ →
      ∀ {γ : ℝ → M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
        γ 0 = (extChartAt I x₀).symm (a : E) →
        γ 1 = (extChartAt I x₀).symm (b : E) →
        ENNReal.ofReal (Real.sqrt (1 - ε)) *
            frozenInverseChartEDist g x₀ z₀ a b ≤
          Manifold.pathELength I γ 0 1 := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  rcases exists_chartConfined_pathELength_ge_frozenEndpoint
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hconfined⟩
  let y₀ : M := (extChartAt I x₀).symm (z₀ : E)
  let good : Set M :=
    (extChartAt I x₀).source ∩
      (extChartAt I x₀) ⁻¹' Metric.ball (z₀ : E) r
  have hy₀source : y₀ ∈ (extChartAt I x₀).source := by
    exact (extChartAt I x₀).map_target z₀.2
  have hchart_y₀ : (extChartAt I x₀) y₀ = (z₀ : E) := by
    exact (extChartAt I x₀).right_inv z₀.2
  have hgood : good ∈ 𝓝 y₀ := by
    have hsource : (extChartAt I x₀).source ∈ 𝓝 y₀ :=
      (isOpen_extChartAt_source x₀).mem_nhds hy₀source
    have hball :
        (extChartAt I x₀) ⁻¹' Metric.ball (z₀ : E) r ∈ 𝓝 y₀ :=
      (continuousAt_extChartAt' hy₀source).preimage_mem_nhds (by
        simpa only [hchart_y₀] using
          (Metric.ball_mem_nhds (z₀ : E) hr))
    exact Filter.inter_mem hsource hball
  rcases setOf_riemannianEDist_lt_subset_nhds I hgood with
    ⟨δ, hδ, hδsub⟩
  have hδquarter : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 4 :=
    ennreal_quarter_pos_frozen hδ
  have hsmallM :
      {y : M | Manifold.riemannianEDist I y₀ y <
          (δ : ℝ≥0∞) / 4} ∈ 𝓝 y₀ :=
    eventually_riemannianEDist_lt I y₀ hδquarter
  have hψcont : ContinuousAt
      (fun z : (extChartAt I x₀).target ↦
        (extChartAt I x₀).symm (z : E)) z₀ :=
    (continuousAt_extChartAt_symm'' z₀.2).comp
      continuous_subtype_val.continuousAt
  have hsmallTarget :
      {z : (extChartAt I x₀).target |
        Manifold.riemannianEDist I y₀
            ((extChartAt I x₀).symm (z : E)) <
          (δ : ℝ≥0∞) / 4} ∈ 𝓝 z₀ :=
    hψcont.preimage_mem_nhds hsmallM
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  let c : ℝ := Real.sqrt (1 - ε)
  have hc : 0 < c := by
    dsimp [c]
    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hradialCont : Continuous
      (fun z : (extChartAt I x₀).target ↦
        c * ‖e ((z : E) - (z₀ : E))‖) := by
    have hsub : Continuous
        (fun z : (extChartAt I x₀).target ↦
          (z : E) - (z₀ : E)) :=
      continuous_subtype_val.sub continuous_const
    exact continuous_const.mul ((e.continuous.comp hsub).norm)
  have hradial :
      {z : (extChartAt I x₀).target |
        c * ‖e ((z : E) - (z₀ : E))‖ < (δ : ℝ) / 8} ∈ 𝓝 z₀ := by
    apply (isOpen_lt hradialCont continuous_const).mem_nhds
    change c * ‖e ((z₀ : E) - (z₀ : E))‖ < (δ : ℝ) / 8
    simp only [sub_self, map_zero, norm_zero, mul_zero]
    exact div_pos hδreal (by norm_num)
  have hcombined :
      Metric.ball z₀ r ∩
          ({z : (extChartAt I x₀).target |
            Manifold.riemannianEDist I y₀
                ((extChartAt I x₀).symm (z : E)) <
              (δ : ℝ≥0∞) / 4} ∩
            {z : (extChartAt I x₀).target |
              c * ‖e ((z : E) - (z₀ : E))‖ < (δ : ℝ) / 8}) ∈
        𝓝 z₀ :=
    Filter.inter_mem (Metric.ball_mem_nhds z₀ hr)
      (Filter.inter_mem hsmallTarget hradial)
  rcases Metric.mem_nhds_iff.mp hcombined with ⟨ρ, hρ, hρsub⟩
  refine ⟨ρ, hρ, ?_⟩
  intro a b ha hb γ hγ hγ0 hγ1
  have haPack := hρsub (Metric.mem_ball.mpr ha)
  have hbPack := hρsub (Metric.mem_ball.mpr hb)
  have haSmall :
      Manifold.riemannianEDist I y₀
          ((extChartAt I x₀).symm (a : E)) <
        (δ : ℝ≥0∞) / 4 := haPack.2.1
  have haRadial :
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ z₀ a <
        (δ : ℝ≥0∞) / 8 := by
    calc
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ z₀ a =
          ENNReal.ofReal c * ‖e ((a : E) - (z₀ : E))‖ₑ := by
        rfl
      _ = ENNReal.ofReal c *
          ENNReal.ofReal ‖e ((a : E) - (z₀ : E))‖ := by
        rw [ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal
          (c * ‖e ((a : E) - (z₀ : E))‖) := by
        rw [ENNReal.ofReal_mul hc.le]
      _ < ENNReal.ofReal ((δ : ℝ) / 8) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (div_pos hδreal (by norm_num))]
        exact haPack.2.2
      _ = (δ : ℝ≥0∞) / 8 := ofReal_nnreal_div_eight_frozen δ
  have hbRadial :
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ z₀ b <
        (δ : ℝ≥0∞) / 8 := by
    calc
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ z₀ b =
          ENNReal.ofReal c * ‖e ((b : E) - (z₀ : E))‖ₑ := by
        rfl
      _ = ENNReal.ofReal c *
          ENNReal.ofReal ‖e ((b : E) - (z₀ : E))‖ := by
        rw [ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal
          (c * ‖e ((b : E) - (z₀ : E))‖) := by
        rw [ENNReal.ofReal_mul hc.le]
      _ < ENNReal.ofReal ((δ : ℝ) / 8) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (div_pos hδreal (by norm_num))]
        exact hbPack.2.2
      _ = (δ : ℝ≥0∞) / 8 := ofReal_nnreal_div_eight_frozen δ
  have hLquarter :
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ a b ≤
        (δ : ℝ≥0∞) / 4 := by
    calc
      ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ a b ≤
          ENNReal.ofReal c *
            (frozenInverseChartEDist g x₀ z₀ a z₀ +
              frozenInverseChartEDist g x₀ z₀ z₀ b) :=
        mul_le_mul_left' (frozenInverseChartEDist_triangle g x₀ z₀ a z₀ b) _
      _ = ENNReal.ofReal c *
              frozenInverseChartEDist g x₀ z₀ z₀ a +
            ENNReal.ofReal c *
              frozenInverseChartEDist g x₀ z₀ z₀ b := by
        rw [mul_add, frozenInverseChartEDist_comm g x₀ z₀ a z₀]
      _ ≤ (δ : ℝ≥0∞) / 8 + (δ : ℝ≥0∞) / 8 :=
        add_le_add haRadial.le hbRadial.le
      _ ≤ (δ : ℝ≥0∞) / 4 :=
        ennreal_eighth_add_eighth_le_quarter_frozen δ
  change ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ a b ≤
    Manifold.pathELength I γ 0 1
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ good
  · exact hconfined a b hγ hγ0 hγ1 (by
      intro t ht
      have htgood := hstay t ht
      exact ⟨htgood.1, Metric.mem_ball.mp htgood.2⟩)
  · push Not at hstay
    rcases hstay with ⟨t, ht, htout⟩
    by_contra hnot
    have hlenLtL :
        Manifold.pathELength I γ 0 1 <
          ENNReal.ofReal c * frozenInverseChartEDist g x₀ z₀ a b :=
      lt_of_not_ge hnot
    have hlenLtQuarter :
        Manifold.pathELength I γ 0 1 < (δ : ℝ≥0∞) / 4 :=
      hlenLtL.trans_le hLquarter
    have hγseg : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) t) :=
      hγ.mono (Icc_subset_Icc le_rfl ht.2)
    have hprefixDist :
        Manifold.riemannianEDist I (γ 0) (γ t) ≤
          Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength hγseg rfl rfl ht.1
    have hprefixLength :
        Manifold.pathELength I γ 0 t ≤
          Manifold.pathELength I γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    have hprefixLt :
        Manifold.riemannianEDist I (γ 0) (γ t) <
          (δ : ℝ≥0∞) / 4 :=
      hprefixDist.trans_lt (hprefixLength.trans_lt hlenLtQuarter)
    have hy₀γ0 :
        Manifold.riemannianEDist I y₀ (γ 0) <
          (δ : ℝ≥0∞) / 4 := by
      simpa only [hγ0] using haSmall
    have hy₀γt :
        Manifold.riemannianEDist I y₀ (γ t) < (δ : ℝ≥0∞) := by
      calc
        Manifold.riemannianEDist I y₀ (γ t) ≤
            Manifold.riemannianEDist I y₀ (γ 0) +
              Manifold.riemannianEDist I (γ 0) (γ t) :=
          Manifold.riemannianEDist_triangle
        _ < (δ : ℝ≥0∞) / 4 + (δ : ℝ≥0∞) / 4 :=
          ENNReal.add_lt_add hy₀γ0 hprefixLt
        _ < (δ : ℝ≥0∞) :=
          ennreal_quarter_add_quarter_lt_frozen hδ
    exact htout (hδsub hy₀γt)

/-- On a sufficiently small target ball, the actual Riemannian extended
distance dominates `sqrt (1 - ε)` times the frozen extended distance.  This
is the metric-infimum form of the preceding all-path estimate. -/
theorem exists_inverseChart_frozenEDist_le_riemannianEDist
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r > 0, ∀ (z w : (extChartAt I x₀).target),
      dist z z₀ < r → dist w z₀ < r →
      ENNReal.ofReal (Real.sqrt (1 - ε)) *
          frozenInverseChartEDist g x₀ z₀ z w ≤
        Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (z : E))
          ((extChartAt I x₀).symm (w : E)) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChart_pairwise_pathELength_ge_frozenEndpoint
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hpaths⟩
  refine ⟨r, hr, ?_⟩
  intro z w hz hw
  let G₀ := inverseChartPullbackGramMatrix g x₀ z₀
  let hG₀ := inverseChartPullbackGramMatrix_posDef g x₀ z₀
  let e := positiveDefiniteGramLinearEquiv G₀ hG₀
  have hraw :=
    GeodesicTransport.ofReal_le_riemannianEDist_of_forall_pathELength_lower
      (g := g)
      (x := (extChartAt I x₀).symm (z : E))
      (y := (extChartAt I x₀).symm (w : E))
      (L := Real.sqrt (1 - ε) * ‖e ((w : E) - (z : E))‖)
      (by
        intro γ hγ hγ0 hγ1
        calc
          ENNReal.ofReal
              (Real.sqrt (1 - ε) * ‖e ((w : E) - (z : E))‖) =
              ENNReal.ofReal (Real.sqrt (1 - ε)) *
                frozenInverseChartEDist g x₀ z₀ z w := by
            rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
            simp only [frozenInverseChartEDist, G₀, hG₀, e,
              ofReal_norm_eq_enorm]
          _ ≤ Manifold.pathELength I γ 0 1 :=
            hpaths z w hz hw hγ hγ0 hγ1)
  calc
    ENNReal.ofReal (Real.sqrt (1 - ε)) *
        frozenInverseChartEDist g x₀ z₀ z w =
        ENNReal.ofReal
          (Real.sqrt (1 - ε) * ‖e ((w : E) - (z : E))‖) := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      simp only [frozenInverseChartEDist, G₀, hG₀, e,
        ofReal_norm_eq_enorm]
    _ ≤ Manifold.riemannianEDist I
          ((extChartAt I x₀).symm (z : E))
          ((extChartAt I x₀).symm (w : E)) := hraw

/-- On a sufficiently small target ball, the genuine inverse chart is
anti-Lipschitz from the frozen Gram-factor metric to the induced Riemannian
metric.  The constant is the reciprocal of `sqrt (1 - ε)`.  Consequently,
every subset of the ball satisfies the corresponding Hausdorff-measure lower
inequality. -/
theorem exists_inverseChart_frozen_antilipschitzWith_and_hausdorff_lower
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z₀ : (extChartAt I x₀).target) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ r > 0,
      let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
      let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
      let hφ :=
        frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
      let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
      let frozenEMetric : EMetricSpace U :=
        @MetricSpace.toEMetricSpace U frozenMetric
      let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
      let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
      let K : ℝ≥0 := C⁻¹
      letI : EMetricSpace U := frozenEMetric
      letI : PseudoEMetricSpace U := frozenEMetric.toPseudoEMetricSpace
      letI : MetricSpace M := g.toMetricSpace
      @AntilipschitzWith U M frozenEMetric.toPseudoEMetricSpace
          g.toEMetricSpace.toPseudoEMetricSpace K ψ ∧
        ∀ s : Set U,
          μH[(n : ℝ)] s ≤
            (K : ℝ≥0∞) ^ (n : ℝ) * μH[(n : ℝ)] (ψ '' s) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_inverseChart_frozenEDist_le_riemannianEDist
      g x₀ z₀ hε0 hε1 with ⟨r, hr, hlowerDistance⟩
  refine ⟨r, hr, ?_⟩
  let U : Set (extChartAt I x₀).target := Metric.ball z₀ r
  let φ := frozenInverseChartLinearParametrizationAt g x₀ z₀ U
  let hφ :=
    frozenInverseChartLinearParametrizationAt_isEmbedding g x₀ z₀ U
  let frozenMetric : MetricSpace U := hφ.comapMetricSpace φ
  let frozenEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U frozenMetric
  let ψ := inverseChartParametrizationOn (n := n) (M := M) x₀ U
  let C : ℝ≥0 := ⟨Real.sqrt (1 - ε), Real.sqrt_nonneg _⟩
  let K : ℝ≥0 := C⁻¹
  have hCpos : 0 < C := by
    change 0 < Real.sqrt (1 - ε)
    exact Real.sqrt_pos.2 (sub_pos.2 hε1)
  have hcoef :
      ENNReal.ofReal (Real.sqrt (1 - ε)) = (C : ℝ≥0∞) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg _)]
    apply ENNReal.coe_inj.mpr
    apply Subtype.ext
    rfl
  letI : EMetricSpace U := frozenEMetric
  letI : PseudoEMetricSpace U := frozenEMetric.toPseudoEMetricSpace
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  haveI : IsRiemannianManifold I M := g.toIsRiemannianManifold
  have hφiso : Isometry φ := by
    intro z w
    rfl
  have hanti : @AntilipschitzWith U M frozenEMetric.toPseudoEMetricSpace
      g.toEMetricSpace.toPseudoEMetricSpace K ψ := by
    intro z w
    have hfrozen :
        frozenInverseChartEDist g x₀ z₀ z.1 w.1 =
          @edist U frozenEMetric.toEDist z w := by
      rw [show frozenInverseChartEDist g x₀ z₀ z.1 w.1 =
          edist (φ w) (φ z) by
        simp only [frozenInverseChartEDist, φ,
          frozenInverseChartLinearParametrizationAt,
          edist_eq_enorm_sub, map_sub]]
      rw [edist_comm, hφiso.edist_eq]
    have htarget :
        edist (ψ z) (ψ w) =
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (z.1 : E))
            ((extChartAt I x₀).symm (w.1 : E)) := by
      exact GeodesicTransport.induced_edist_eq_riemannianEDist
        (g := g) (ψ z) (ψ w)
    have hriem :
        ENNReal.ofReal (Real.sqrt (1 - ε)) *
            frozenInverseChartEDist g x₀ z₀ z.1 w.1 ≤
          Manifold.riemannianEDist I
            ((extChartAt I x₀).symm (z.1 : E))
            ((extChartAt I x₀).symm (w.1 : E)) := by
      exact hlowerDistance z.1 w.1 z.2 w.2
    have hlower :
        (C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w ≤
          edist (ψ z) (ψ w) := by
      calc
        (C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w =
            ENNReal.ofReal (Real.sqrt (1 - ε)) *
              frozenInverseChartEDist g x₀ z₀ z.1 w.1 := by
          rw [hcoef, hfrozen]
        _ ≤ Manifold.riemannianEDist I
              ((extChartAt I x₀).symm (z.1 : E))
              ((extChartAt I x₀).symm (w.1 : E)) := hriem
        _ = edist (ψ z) (ψ w) := htarget.symm
    have hCzero : (C : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hCpos.ne'
    have hKcoe : (K : ℝ≥0∞) = (C : ℝ≥0∞)⁻¹ := by
      exact ENNReal.coe_inv hCpos.ne'
    calc
      @edist U frozenEMetric.toEDist z w = (C : ℝ≥0∞)⁻¹ *
          ((C : ℝ≥0∞) * @edist U frozenEMetric.toEDist z w) := by
        exact (ENNReal.inv_mul_cancel_left hCzero ENNReal.coe_ne_top).symm
      _ ≤ (C : ℝ≥0∞)⁻¹ * edist (ψ z) (ψ w) :=
        mul_le_mul_left' hlower _
      _ = (K : ℝ≥0∞) * edist (ψ z) (ψ w) := by
        rw [hKcoe]
  refine ⟨hanti, ?_⟩
  intro s
  exact hanti.le_hausdorffMeasure_image (d := (n : ℝ)) (by positivity) s

end Poincare
