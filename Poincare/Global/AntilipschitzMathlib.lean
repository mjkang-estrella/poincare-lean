import Poincare.Global.AntilipschitzClose
import Poincare.Global.ExponentialFrechet

/-!
# Anti-Lipschitz lower comparison from Mathlib's Riemannian topology proof

This module mines the public lower-comparison lemmas from
`Mathlib.Geometry.Manifold.Riemannian.Basic`.  The key exported ingredient is
`setOf_riemannianEDist_lt_subset_nhds`: every topological neighborhood of an
anchor contains a sufficiently small `riemannianEDist` ball.  Since the metric
induced by a `ClosedSmoothRiemannianMetric` is definitionally Mathlib's
`riemannianEDist`, this gives a reusable positive exit cost from chart
neighborhoods.
-/

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal RealInnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/--
Mathlib lower comparison specialized to an extended-chart source ball: for a
positive chart radius, there is a positive Riemannian extended-distance radius
such that the small `riemannianEDist` ball is contained in the chart source and
in the prescribed chart ball.
-/
theorem exists_riemannianEDist_ball_subset_extChartAt_source_ball
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) {R : ℝ} (hR : 0 < R) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ c : ℝ≥0, 0 < c ∧
      {y : M | Manifold.riemannianEDist I x₀ y < (c : ℝ≥0∞)} ⊆
        (extChartAt I x₀).source ∩
          (extChartAt I x₀) ⁻¹'
            Metric.ball ((extChartAt I x₀) x₀) R := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  have hpre :
      (extChartAt I x₀) ⁻¹'
          Metric.ball ((extChartAt I x₀) x₀) R ∈ 𝓝 x₀ :=
    (continuousAt_extChartAt x₀).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hR)
  have hs :
      (extChartAt I x₀).source ∩
          (extChartAt I x₀) ⁻¹'
            Metric.ball ((extChartAt I x₀) x₀) R ∈ 𝓝 x₀ :=
    Filter.inter_mem (extChartAt_source_mem_nhds x₀) hpre
  simpa using setOf_riemannianEDist_lt_subset_nhds I hs

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/--
Positive exit cost from a source chart ball, obtained directly from Mathlib's
lower-comparison lemma and `riemannianEDist_le_pathELength`.
-/
theorem chart_source_ball_exit_pathELength_lower_bound_mathlib
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {R : ℝ} (hR : 0 < R) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ {γ : ℝ → M} {a b : ℝ} {y : M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b) →
        γ a = x₀ →
        γ b = y →
        a ≤ b →
        y ∉ (extChartAt I x₀).source ∩
          (extChartAt I x₀) ⁻¹'
            Metric.ball ((extChartAt I x₀) x₀) R →
        (c : ℝ≥0∞) ≤ Manifold.pathELength I γ a b := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rcases exists_riemannianEDist_ball_subset_extChartAt_source_ball
      (g := g) (x₀ := x₀) hR with
    ⟨c, hc_pos, hc_subset⟩
  refine ⟨c, hc_pos, ?_⟩
  intro γ a b y hγ hγa hγb hab hy_out
  have hc_le_riem : (c : ℝ≥0∞) ≤ Manifold.riemannianEDist I x₀ y := by
    by_contra hnot
    exact hy_out (hc_subset (lt_of_not_ge hnot))
  exact hc_le_riem.trans
    (Manifold.riemannianEDist_le_pathELength hγ hγa hγb hab)

private theorem ennreal_quarter_pos {δ : ℝ≥0} (hδ : 0 < δ) :
    (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 4 := by
  rw [← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_zero, ENNReal.coe_lt_coe]
  exact div_pos hδ (by norm_num : (0 : ℝ≥0) < 4)

private theorem ennreal_quarter_add_quarter_lt {δ : ℝ≥0} (hδ : 0 < δ) :
    (δ : ℝ≥0∞) / 4 + (δ : ℝ≥0∞) / 4 < (δ : ℝ≥0∞) := by
  rw [← ENNReal.coe_ofNat 4,
    ← ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0)]
  rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
  exact NNReal.coe_lt_coe.mp (by
    have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    norm_num
    nlinarith)

private theorem ofReal_nnreal_div_four (δ : ℝ≥0) :
    ENNReal.ofReal ((δ : ℝ) / 4) = (δ : ℝ≥0∞) / 4 := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
  rw [ENNReal.ofReal_coe_nnreal]
  norm_num

private theorem exists_large_chart_constant
    {C : ℝ≥0} {r : ℝ} {δ : ℝ≥0} :
    ∃ K : ℝ≥0, 0 < K ∧ (C : ℝ) ≤ K ∧ 8 * r / (δ : ℝ) ≤ K := by
  let Kreal : ℝ := max (C : ℝ) (8 * r / (δ : ℝ)) + 1
  have hKreal_nonneg : 0 ≤ Kreal := by
    dsimp [Kreal]
    have hCnonneg : 0 ≤ (C : ℝ) := by positivity
    have hmax : 0 ≤ max (C : ℝ) (8 * r / (δ : ℝ)) :=
      le_max_of_le_left hCnonneg
    exact add_nonneg hmax zero_le_one
  let K : ℝ≥0 := ⟨Kreal, hKreal_nonneg⟩
  refine ⟨K, ?_, ?_, ?_⟩
  · change (0 : ℝ) < Kreal
    dsimp [Kreal]
    have hCnonneg : 0 ≤ (C : ℝ) := by positivity
    have hmax : 0 ≤ max (C : ℝ) (8 * r / (δ : ℝ)) :=
      le_max_of_le_left hCnonneg
    exact add_pos_of_nonneg_of_pos hmax zero_lt_one
  · change (C : ℝ) ≤ Kreal
    dsimp [Kreal]
    exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  · change 8 * r / (δ : ℝ) ≤ Kreal
    dsimp [Kreal]
    exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)

private theorem inv_mul_dist_le_quarter_of_large
    {K dist r : ℝ} {δ : ℝ≥0} (hKpos : 0 < K) (hδ : 0 < δ)
    (hdist : dist ≤ 2 * r) (hKge : 8 * r / (δ : ℝ) ≤ K) :
    K⁻¹ * dist ≤ (δ : ℝ) / 4 := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hmul : 2 * r ≤ K * ((δ : ℝ) / 4) := by
    have hbase : 2 * r = (8 * r / (δ : ℝ)) * ((δ : ℝ) / 4) := by
      field_simp [ne_of_gt hδR]
      ring
    rw [hbase]
    exact mul_le_mul_of_nonneg_right hKge (by positivity)
  calc
    K⁻¹ * dist ≤ K⁻¹ * (2 * r) := by
      exact mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr hKpos.le)
    _ ≤ K⁻¹ * (K * ((δ : ℝ) / 4)) := by
      exact mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hKpos.le)
    _ = (δ : ℝ) / 4 := by
      field_simp [ne_of_gt hKpos]

omit [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/--
Uniform pairwise path-length lower bound on a small chart ball.

This is the non-inductive reroute through Mathlib's lower comparison: a path
that remains inside the controlled chart ball is handled by the forward-chart
derivative estimate from `AntilipschitzBallFinal`; a path that ever leaves that
ball would give a point outside a neighborhood whose `riemannianEDist` from the
anchor is bounded below by `setOf_riemannianEDist_lt_subset_nhds`.
-/
theorem exists_chart_ball_pairwise_pathELength_lower_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r : ℝ, 0 < r ∧
      ∃ K : ℝ≥0, 0 < K ∧
        ∀ (u v :
            {y : E //
              y ∈ Metric.ball ((extChartAt I x₀) x₀) r})
          {γ : ℝ → M},
          ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) 1) →
          γ 0 = (extChartAt I x₀).symm (u : E) →
          γ 1 = (extChartAt I x₀).symm (v : E) →
          ENNReal.ofReal
              (((K : ℝ)⁻¹) * dist (u : E) (v : E)) ≤
            Manifold.pathELength I γ 0 1 := by
  classical
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle E
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  rcases eventually_enorm_mfderiv_extChartAt_lt I x₀ with
    ⟨C, hCpos, hCevent⟩
  let good : Set M :=
    (extChartAt I x₀).source ∩
      {y : M | ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y‖ₑ < (C : ℝ≥0∞)}
  have hgood_mem : good ∈ 𝓝 x₀ := by
    have hsource_mem : (extChartAt I x₀).source ∈ 𝓝 x₀ :=
      extChartAt_source_mem_nhds x₀
    filter_upwards [hsource_mem, hCevent] with y hsrc hder
    exact ⟨hsrc, hder⟩
  have hgood_chart :
      (extChartAt I x₀).symm ⁻¹' good ∈ 𝓝 ((extChartAt I x₀) x₀) :=
    extChartAt_preimage_mem_nhds hgood_mem
  rcases Metric.mem_nhds_iff.mp hgood_chart with ⟨R, hR, hRsub⟩
  rcases exists_riemannianEDist_ball_subset_extChartAt_source_ball
      (g := g) (x₀ := x₀) hR with
    ⟨δ, hδpos, hδsubset⟩
  have hδquarter_pos : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) / 4 :=
    ennreal_quarter_pos hδpos
  have hsmallM :
      {y : M | Manifold.riemannianEDist I x₀ y < (δ : ℝ≥0∞) / 4} ∈ 𝓝 x₀ :=
    eventually_riemannianEDist_lt I x₀ hδquarter_pos
  haveI : (closedSmoothModelWithCorners n).Boundaryless := by infer_instance
  have hsmallChart :
      (extChartAt I x₀).target ∩
        (Metric.ball ((extChartAt I x₀) x₀) R ∩
          (extChartAt I x₀).symm ⁻¹'
            {y : M | Manifold.riemannianEDist I x₀ y < (δ : ℝ≥0∞) / 4})
          ∈ 𝓝 ((extChartAt I x₀) x₀) := by
    exact Filter.inter_mem (extChartAt_target_mem_nhds x₀)
      (Filter.inter_mem (Metric.ball_mem_nhds _ hR)
        (extChartAt_preimage_mem_nhds hsmallM))
  rcases Metric.mem_nhds_iff.mp hsmallChart with ⟨r, hr, hrsub⟩
  rcases exists_large_chart_constant (C := C) (r := r) (δ := δ) with
    ⟨K, hKpos, hC_le_K, hK_margin⟩
  refine ⟨r, hr, K, hKpos, ?_⟩
  intro u v γ hγ hγ0 hγ1
  have hu_pack := hrsub u.2
  have hv_pack := hrsub v.2
  have hu_target : (u : E) ∈ (extChartAt I x₀).target := hu_pack.1
  have hv_target : (v : E) ∈ (extChartAt I x₀).target := hv_pack.1
  have hu_small :
      Manifold.riemannianEDist I x₀ ((extChartAt I x₀).symm (u : E)) <
        (δ : ℝ≥0∞) / 4 := hu_pack.2.2
  have hdist_le : dist (u : E) (v : E) ≤ 2 * r :=
    dist_le_two_mul_radius_of_mem_ball u.2 v.2
  have hKposℝ : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hL_quarter :
      ENNReal.ofReal (((K : ℝ)⁻¹) * dist (u : E) (v : E)) ≤
        (δ : ℝ≥0∞) / 4 := by
    have hreal :
        ((K : ℝ)⁻¹) * dist (u : E) (v : E) ≤ (δ : ℝ) / 4 :=
      inv_mul_dist_le_quarter_of_large
        (K := (K : ℝ)) (dist := dist (u : E) (v : E))
        (r := r) (δ := δ) hKposℝ hδpos hdist_le hK_margin
    calc
      ENNReal.ofReal (((K : ℝ)⁻¹) * dist (u : E) (v : E)) ≤
          ENNReal.ofReal ((δ : ℝ) / 4) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = (δ : ℝ≥0∞) / 4 := ofReal_nnreal_div_four δ
  by_cases hstay :
      ∀ t ∈ Icc (0 : ℝ) 1,
        γ t ∈ (extChartAt I x₀).source ∩
          (extChartAt I x₀) ⁻¹'
            Metric.ball ((extChartAt I x₀) x₀) R
  · have hsrc : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt I x₀).source := by
      intro t ht
      exact (hstay t ht).1
    have hCbound :
        ∀ t ∈ Icc (0 : ℝ) 1,
          ‖mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t)‖ₑ ≤ C := by
      intro t ht
      have hsymm_good : (extChartAt I x₀).symm ((extChartAt I x₀) (γ t)) ∈ good :=
        hRsub (hstay t ht).2
      have hγ_good : γ t ∈ good := by
        have hsrc_chart : γ t ∈ (chartAt E x₀).source := by
          simpa [extChartAt_source] using hsrc t ht
        have hleft_chart :
            (chartAt E x₀).symm ((chartAt E x₀) (γ t)) = γ t :=
          (chartAt E x₀).left_inv hsrc_chart
        simpa [good, extChartAt_source, hleft_chart] using hsymm_good
      exact hγ_good.2.le
    have hC_lower :
        ENNReal.ofReal (((C : ℝ)⁻¹) * dist (u : E) (v : E)) ≤
          Manifold.pathELength I γ 0 1 := by
      have hraw :=
        ofReal_inv_mul_dist_extChartAt_endpoints_le_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
          (g := g) (x₀ := x₀) (C := C) hCpos hγ hsrc hCbound
      have hCposℝ : 0 < (C : ℝ) := by exact_mod_cast hCpos
      have hchart0 : (extChartAt I x₀) (γ 0) = (u : E) := by
        rw [hγ0]
        exact (extChartAt I x₀).right_inv hu_target
      have hchart1 : (extChartAt I x₀) (γ 1) = (v : E) := by
        rw [hγ1]
        exact (extChartAt I x₀).right_inv hv_target
      have hchart0' : (chartAt E x₀) (γ 0) = (u : E) := by
        change (extChartAt I x₀) (γ 0) = (u : E)
        exact hchart0
      have hchart1' : (chartAt E x₀) (γ 1) = (v : E) := by
        change (extChartAt I x₀) (γ 1) = (v : E)
        exact hchart1
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hCposℝ.le)]
      simpa [hchart0', hchart1'] using hraw
    have hK_le_C_inv :
        ((K : ℝ)⁻¹) * dist (u : E) (v : E) ≤
          ((C : ℝ)⁻¹) * dist (u : E) (v : E) := by
      have hCposℝ : 0 < (C : ℝ) := by exact_mod_cast hCpos
      have hinv : (K : ℝ)⁻¹ ≤ (C : ℝ)⁻¹ :=
        inv_anti₀ hCposℝ hC_le_K
      exact mul_le_mul_of_nonneg_right hinv dist_nonneg
    exact (ENNReal.ofReal_le_ofReal hK_le_C_inv).trans hC_lower
  · push Not at hstay
    rcases hstay with ⟨t, ht, htout⟩
    by_contra hnot
    have hlen_lt_L :
        Manifold.pathELength I γ 0 1 <
          ENNReal.ofReal (((K : ℝ)⁻¹) * dist (u : E) (v : E)) :=
      lt_of_not_ge hnot
    have hlen_lt_quarter :
        Manifold.pathELength I γ 0 1 < (δ : ℝ≥0∞) / 4 :=
      hlen_lt_L.trans_le hL_quarter
    have hγ_seg : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc (0 : ℝ) t) :=
      hγ.mono (Icc_subset_Icc le_rfl ht.2)
    have hriem_seg :
        Manifold.riemannianEDist I (γ 0) (γ t) ≤
          Manifold.pathELength I γ 0 t :=
      Manifold.riemannianEDist_le_pathELength hγ_seg rfl rfl ht.1
    have hseg_le_total :
        Manifold.pathELength I γ 0 t ≤ Manifold.pathELength I γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    have hriem_seg_lt_quarter :
        Manifold.riemannianEDist I (γ 0) (γ t) < (δ : ℝ≥0∞) / 4 :=
      hriem_seg.trans_lt (hseg_le_total.trans_lt hlen_lt_quarter)
    have hxγ0_lt_quarter :
        Manifold.riemannianEDist I x₀ (γ 0) < (δ : ℝ≥0∞) / 4 := by
      simpa [hγ0] using hu_small
    have hq_lt_delta :
        Manifold.riemannianEDist I x₀ (γ t) < (δ : ℝ≥0∞) := by
      calc
        Manifold.riemannianEDist I x₀ (γ t) ≤
            Manifold.riemannianEDist I x₀ (γ 0) +
              Manifold.riemannianEDist I (γ 0) (γ t) :=
          Manifold.riemannianEDist_triangle
        _ < (δ : ℝ≥0∞) / 4 + (δ : ℝ≥0∞) / 4 :=
          ENNReal.add_lt_add hxγ0_lt_quarter hriem_seg_lt_quarter
        _ < (δ : ℝ≥0∞) :=
          ennreal_quarter_add_quarter_lt hδpos
    have hq_ge_delta : (δ : ℝ≥0∞) ≤ Manifold.riemannianEDist I x₀ (γ t) := by
      by_contra hlt_not
      exact htout (hδsubset (lt_of_not_ge hlt_not))
    exact not_lt_of_ge hq_ge_delta hq_lt_delta

omit [MeasurableSpace M] [BorelSpace M] in
/--
Unconditional local anti-Lipschitz ball for the inverse extended chart,
assembled from the Mathlib-rerouted pairwise path-length lower bound.
-/
theorem exists_extChartAt_symm_antilipschitz_ball
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ r : ℝ, 0 < r ∧
      ∃ K : ℝ≥0,
        letI : MetricSpace M := g.toMetricSpace
        AntilipschitzWith K
          (fun y :
              {y : E //
                y ∈ Metric.ball ((extChartAt I x₀) x₀) r} =>
            (extChartAt I x₀).symm (y : E)) := by
  rcases exists_chart_ball_pairwise_pathELength_lower_bound (g := g) (x₀ := x₀) with
    ⟨r, hr, K, hKpos, hpaths⟩
  refine ⟨r, hr, K, ?_⟩
  exact antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower
    (g := g) (x₀ := x₀) hKpos hpaths

omit [MeasurableSpace M] [BorelSpace M] in
/-- Mathlib-rerouted proof of the local chart anti-Lipschitz lower-bound predicate. -/
theorem localChartAntilipschitzLowerBound_mathlib
    (g : ClosedSmoothRiemannianMetric n M) :
    LocalChartAntilipschitzLowerBound (n := n) (M := M) g := by
  intro x
  exact exists_extChartAt_symm_antilipschitz_ball (g := g) x

/-- Nonzero total Riemannian volume, using the Mathlib-rerouted anti-Lipschitz ball. -/
theorem volumeMeasure_univ_ne_zero_mathlib
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) :
    volumeMeasure g Set.univ ≠ 0 :=
  volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound
    (g := g) (localChartAntilipschitzLowerBound_mathlib (g := g))

omit [MeasurableSpace M] [BorelSpace M] in
/--
Local lower bound for the fixed-time exponential map, in the requested
`dist x₀ (expAt g x₀ v) ≥ c * ‖v‖` shape.
-/
theorem exists_expAt_dist_lower_bound_ball
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ v : E, ‖v‖ < ρ →
        letI : MetricSpace M := g.toMetricSpace
        c * ‖v‖ ≤ dist x₀ (expAt g x₀ v) := by
  rcases exists_chart_ball_pairwise_pathELength_lower_bound (g := g) (x₀ := x₀) with
    ⟨r, hr, K, hKpos, hpaths⟩
  letI : MetricSpace M := g.toMetricSpace
  have hAnti :
      AntilipschitzWith K
        (fun y :
            {y : E //
              y ∈ Metric.ball ((extChartAt I x₀) x₀) r} =>
          (extChartAt I x₀).symm (y : E)) :=
    antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower
      (g := g) (x₀ := x₀) hKpos hpaths
  let z₀ : E := (extChartAt I x₀) x₀
  have hrem_event :
      ∀ᶠ v : E in 𝓝 (0 : E),
        ‖(extChartAt I x₀) (expAt g x₀ v) - (z₀ + v)‖ ≤
          (1 / 2 : ℝ) * ‖v‖ := by
    simpa [z₀] using
      (Asymptotics.isLittleO_iff.mp
        (expAt_chart_remainder_isLittleO_zero (g := g) (x₀ := x₀))
        (by norm_num : (0 : ℝ) < 1 / 2))
  have hchart_ball_event :
      {v : E | (extChartAt I x₀) (expAt g x₀ v) ∈ Metric.ball z₀ r} ∈
        𝓝 (0 : E) := by
    have hball :
        Metric.ball z₀ r ∈
          𝓝 ((extChartAt I x₀) (expAt g x₀ (0 : E))) := by
      simpa [z₀, expAt_zero] using Metric.ball_mem_nhds z₀ hr
    simpa [z₀] using
      (expAt_chart_continuousAt_zero (g := g) (x₀ := x₀)).preimage_mem_nhds
        hball
  have hsrc_event :
      {v : E | expAt g x₀ v ∈ (extChartAt I x₀).source} ∈ 𝓝 (0 : E) := by
    rcases expAt_mem_source_of_norm_lt (g := g) (x₀ := x₀) with
      ⟨ρ₀, hρ₀, hsrc⟩
    filter_upwards [Metric.ball_mem_nhds (0 : E) hρ₀] with v hv
    exact hsrc v (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
  have hgood_event :
      {v : E | expAt g x₀ v ∈ (extChartAt I x₀).source} ∩
        ({v : E | (extChartAt I x₀) (expAt g x₀ v) ∈ Metric.ball z₀ r} ∩
          {v : E |
            ‖(extChartAt I x₀) (expAt g x₀ v) - (z₀ + v)‖ ≤
              (1 / 2 : ℝ) * ‖v‖}) ∈ 𝓝 (0 : E) :=
    Filter.inter_mem hsrc_event (Filter.inter_mem hchart_ball_event hrem_event)
  rcases Metric.mem_nhds_iff.mp hgood_event with ⟨ρ, hρ, hρsub⟩
  let c : ℝ := ((K : ℝ)⁻¹) / 2
  have hKposℝ : 0 < (K : ℝ) := by exact_mod_cast hKpos
  refine ⟨ρ, hρ, c, ?_, ?_⟩
  · dsimp [c]
    positivity
  intro v hv
  have hpack := hρsub (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
  have hvsrc : expAt g x₀ v ∈ (extChartAt I x₀).source := hpack.1
  have hzball : (extChartAt I x₀) (expAt g x₀ v) ∈ Metric.ball z₀ r :=
    hpack.2.1
  have hrem :
      ‖(extChartAt I x₀) (expAt g x₀ v) - (z₀ + v)‖ ≤
          (1 / 2 : ℝ) * ‖v‖ :=
    hpack.2.2
  let u₀ : {y : E // y ∈ Metric.ball z₀ r} :=
    ⟨z₀, Metric.mem_ball_self hr⟩
  let u : {y : E // y ∈ Metric.ball z₀ r} :=
    ⟨(extChartAt I x₀) (expAt g x₀ v), hzball⟩
  have hanti_le := hAnti.le_mul_dist u₀ u
  have hsymm₀ : (extChartAt I x₀).symm z₀ = x₀ := by
    dsimp [z₀]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hsymm :
      (extChartAt I x₀).symm ((extChartAt I x₀) (expAt g x₀ v)) =
        expAt g x₀ v :=
    (extChartAt I x₀).left_inv hvsrc
  have hchart_le_metric :
      dist z₀ ((extChartAt I x₀) (expAt g x₀ v)) ≤
        (K : ℝ) * dist x₀ (expAt g x₀ v) := by
    have hsymm₀' : (chartAt E x₀).symm z₀ = x₀ := by
      change (extChartAt I x₀).symm z₀ = x₀
      exact hsymm₀
    have hsymm' :
        (chartAt E x₀).symm ((chartAt E x₀) (expAt g x₀ v)) =
          expAt g x₀ v := by
      change (extChartAt I x₀).symm
          ((extChartAt I x₀) (expAt g x₀ v)) = expAt g x₀ v
      exact hsymm
    simpa [u₀, u, Subtype.dist_eq, hsymm₀', hsymm'] using hanti_le
  have hhalf_norm_le_chart :
      (1 / 2 : ℝ) * ‖v‖ ≤
        dist z₀ ((extChartAt I x₀) (expAt g x₀ v)) := by
    let z : E := (extChartAt I x₀) (expAt g x₀ v)
    have hdecomp : v = (z - z₀) - (z - (z₀ + v)) := by
      abel
    have hnorm :
        ‖v‖ ≤ ‖z - z₀‖ + ‖z - (z₀ + v)‖ := by
      have hnorm0 :
          ‖(z - z₀) - (z - (z₀ + v))‖ ≤
            ‖z - z₀‖ + ‖z - (z₀ + v)‖ :=
        norm_sub_le _ _
      simpa [← hdecomp] using hnorm0
    have hnorm' :
        ‖v‖ ≤ dist z₀ z + (1 / 2 : ℝ) * ‖v‖ := by
      calc
        ‖v‖ ≤ ‖z - z₀‖ + ‖z - (z₀ + v)‖ := hnorm
        _ = dist z₀ z + ‖z - (z₀ + v)‖ := by
          rw [dist_comm, dist_eq_norm]
        _ ≤ dist z₀ z + (1 / 2 : ℝ) * ‖v‖ :=
          add_le_add le_rfl (by simpa [z] using hrem)
    suffices (1 / 2 : ℝ) * ‖v‖ ≤ dist z₀ z by
      simpa [z] using this
    linarith
  have hhalf_le_metric :
      (1 / 2 : ℝ) * ‖v‖ ≤ (K : ℝ) * dist x₀ (expAt g x₀ v) :=
    hhalf_norm_le_chart.trans hchart_le_metric
  calc
    c * ‖v‖ = (K : ℝ)⁻¹ * ((1 / 2 : ℝ) * ‖v‖) := by
      dsimp [c]
      ring
    _ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * dist x₀ (expAt g x₀ v)) := by
      exact mul_le_mul_of_nonneg_left hhalf_le_metric (inv_nonneg.mpr hKposℝ.le)
    _ = dist x₀ (expAt g x₀ v) := by
      field_simp [ne_of_gt hKposℝ]

end GeodesicTransport
end Poincare
