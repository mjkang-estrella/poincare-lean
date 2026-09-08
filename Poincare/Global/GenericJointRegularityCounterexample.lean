import Poincare.Global.CartanSourceExponentialFamily
import Poincare.Global.ChartTransitionGeodesicMap

/-!
# Generic joint regularity is atlas-dependent: a checked counterexample

`CartanSourceExponential.GenericJointRegularity g` asks, among other clauses,
that the joint source locus of the generic exponential family be open.  That
family is built from the preferred charts `chartAt E x` of the ambient
`ChartedSpace` instance.  A `ChartedSpace` instance may choose, at every point
other than one fixed point `x₀`, a chart whose source excludes `x₀`; the
resulting atlas is still smooth.  For such an instance the joint source locus
is not a neighborhood of the diagonal, so the predicate fails for every
metric.  The construction below realizes this on `ClosedSmoothModel 3` itself
with the constant Euclidean metric.

This is the M5-glob-71 worker's refutation (harness/reports/M5-glob-71_blocked.md),
re-checked and recorded as a module so that the build keeps it true.  Together
with `FixedChartSuccessorDataPersistence.lean` and
`SuccessorEqualityRadiusPersistence.lean`, it shows that the successor-data
and successor-equality obligations H1 and H2 must be formulated for a
controlled chart selection rather than for the arbitrary preferred charts.
-/

open Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ExponentialChartJointRegularity
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
open CartanSourceExponential

theorem preferred_chart_source_mem_nhds_of_joint
    (g : ClosedSmoothRiemannianMetric 3 M) (h : GenericJointRegularity g) (x : M) :
    {y : M | x ∈ (chartAt E y).source} ∈ 𝓝 x := by
  have hdiag : (x, x) ∈ (genericFamily g).sourceLocus :=
    (genericFamily g).anchor_mem_source x
  have hn := h.isOpen_sourceLocus.mem_nhds hdiag
  have hc : Continuous (fun y : M => (y, x)) := continuous_id.prodMk continuous_const
  have hp := hc.continuousAt.preimage_mem_nhds hn
  apply Filter.mem_of_superset hp
  intro y hy
  change x ∈ (chartAt E y).source ∩ _ at hy
  exact hy.1

theorem not_joint_of_excluded_preferred_chart_source
    (g : ClosedSmoothRiemannianMetric 3 M) {x : M}
    (hx : ¬ IsOpen ({x} : Set M))
    (hexclude : ∀ y : M, y ≠ x → x ∉ (chartAt E y).source) :
    ¬ GenericJointRegularity g := by
  intro h
  have hn := preferred_chart_source_mem_nhds_of_joint g h x
  have hs : ({x} : Set M) ∈ 𝓝 x := by
    apply Filter.mem_of_superset hn
    intro y hy
    by_contra hne
    exact hexclude y hne hy
  apply hx
  rw [isOpen_iff_mem_nhds]
  intro y hy
  simpa only [Set.mem_singleton_iff.mp hy] using hs
end Poincare.ExponentialChartJointRegularity

noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.ExponentialChartJointRegularity.Counterexample
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

def puncturedChart (x : E) : OpenPartialHomeomorph E E :=
  (OpenPartialHomeomorph.refl E).restrOpen
    (if x = 0 then Set.univ else {0}ᶜ)
    (by split <;> simp)

@[reducible] def puncturedChartedSpace : ChartedSpace E E where
  atlas := Set.range puncturedChart
  chartAt := puncturedChart
  mem_chart_source x := by
    simp only [puncturedChart, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_univ, true_and]
    split <;> simp_all
  chart_mem_atlas x := ⟨x, rfl⟩

local instance : ChartedSpace E E := puncturedChartedSpace

local instance punctured_isManifold : IsManifold I ∞ E := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  change ContDiffOn ℝ ∞ (fun z : E => z) _
  exact contDiffOn_id

theorem not_genericJointRegularity (g : ClosedSmoothRiemannianMetric 3 E) :
    ¬ CartanSourceExponential.GenericJointRegularity g := by
  apply not_joint_of_excluded_preferred_chart_source g (not_isOpen_singleton (0 : E))
  intro y hy
  change 0 ∉ (puncturedChart y).source
  simp [puncturedChart, hy]

open Bundle Bornology
def flatInner : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
set_option backward.isDefEq.respectTransparency false in
def flatMetric : ClosedSmoothRiemannianMetric 3 E where
  inner _ := flatInner
  symm _ v w := @real_inner_comm E _ _ w v
  pos _ v hv := (@real_inner_self_pos E _ _ v).2 hv
  isVonNBounded _ := by
    change IsVonNBounded ℝ {v : E | inner ℝ v v < 1}
    have hball : Metric.ball (0 : E) 1 = {v : E | inner ℝ v v < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_setOf_eq]
      conv_lhs => rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← hball]
    exact NormedSpace.isVonNBounded_ball ℝ E 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have hconst : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun _ : E => flatInner) x := contMDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
    have hsymm : (trivializationAt E (TangentSpace I) x).symmL ℝ y =
        ContinuousLinearMap.id ℝ E := by
      rw [TangentBundle.symmL_trivializationAt_eq_core hy,
        tangentBundleCore_coordChange_achart]
      simp only [extChartAt_coe, extChartAt_coe_symm]
      change fderivWithin ℝ (id : E → E) (Set.range (id : E → E)) y = _
      rw [Set.range_id]
      exact fderivWithin_id uniqueDiffWithinAt_univ
    rw [hom_trivializationAt_apply]
    ext v w
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
      hsymm]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem]
    · rw [hom_trivializationAt_apply]
      simp [ContinuousLinearMap.inCoordinates, hsymm]
      rfl
    · simpa using hy

theorem flatMetric_not_genericJointRegularity :
    ¬ CartanSourceExponential.GenericJointRegularity flatMetric :=
  not_genericJointRegularity flatMetric

theorem not_forall_genericJointRegularity :
    ¬ (∀ g : ClosedSmoothRiemannianMetric 3 E,
      CartanSourceExponential.GenericJointRegularity g) := by
  intro h
  exact flatMetric_not_genericJointRegularity (h flatMetric)

end Poincare.ExponentialChartJointRegularity.Counterexample
