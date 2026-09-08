import Poincare.Global.DifferentialSuccessorEqualityStabilityReduction

/-!
# A preferred-chart obstruction to successor equality radius persistence

The equality-radius contract compares total Cartan maps, including outside
their open partial-homeomorphism sources. Since a successor map factors
through its preferred source chart, that equality forces injectivity of the
preferred chart on any part of the equality ball where the predecessor is
injective. Constant curvature supplies actual successor data near a fixed
anchor. Consequently even one admissible positive radius forces all nearby
preferred charts to be injective on a common neighborhood.

No curvature-only persistence theorem is asserted here. The final theorem
excludes it whenever preferred-chart collisions accumulate at an anchor.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace SuccessorEqualityRadiusPersistence

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]

open CartanChain DifferentialInducedSuccessor
open DifferentialSuccessorEqualityStabilityReduction

omit [T2Space M] in
/-- The total successor map cannot distinguish two points identified by its
preferred source chart, even when those points are outside its source. -/
theorem successor_germ_eq_of_chartAt_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {s : ChainState g} {z a b : M}
    (d : Data s z) (hab : chartAt E z a = chartAt E z b) :
    d.successor.germ a = d.successor.germ b := by
  change CartanMap.cartanMap g z (s.map z) d.alignment a =
    CartanMap.cartanMap g z (s.map z) d.alignment b
  simp only [CartanMap.cartanMap_apply, hab]

omit [T2Space M] in
/-- Equality with an injective predecessor forces injectivity of the total
preferred chart on the part of the equality set in the predecessor source. -/
theorem injOn_chartAt_of_eqOn_successor
    {g : ClosedSmoothRiemannianMetric 3 M} {s : ChainState g} {z : M}
    (d : Data s z) {U : Set M}
    (heq : EqOn s.germ d.successor.germ U) :
    InjOn (chartAt E z) (s.germ.source ∩ U) := by
  intro a ha b hb hab
  apply s.germ.injOn ha.1 hb.1
  exact (heq ha.2).trans
    ((successor_germ_eq_of_chartAt_eq d hab).trans (heq hb.2).symm)

variable [CompactSpace M] [ConnectedSpace M]

/-- One positive equality radius at fixed source and target anchors already
requires a neighborhood on which every nearby preferred source chart is
injective. Neither the target anchor nor its alignment moves in this proof. -/
theorem exists_open_nhds_injOn_chartAt_of_constantCurvature_of_admissible
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) {radius : ℝ} (hradius : 0 < radius)
    (hadmissible : ActualSuccessorEqualityRadiusAdmissible g x p radius) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V, InjOn (chartAt E z) V := by
  letI : MetricSpace M := g.toMetricSpace
  let L : CartanMap.TangentAlignment g x p :=
    Classical.choice (CartanMap.tangentAlignment_nonempty (g := g) (x₀ := x) (p₀ := p))
  let s : ChainState g := ⟨x, p, L⟩
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with ⟨epsilon, hepsilon, hdata⟩
  let small : ℝ := min epsilon (radius / 2)
  have hsmall : 0 < small := lt_min hepsilon (half_pos hradius)
  let V : Set M := s.germ.source ∩ ball x small
  have hxSource : x ∈ s.germ.source := CartanMap.anchor_mem_source g x p L
  refine ⟨V, s.germ.open_source.inter isOpen_ball, ⟨hxSource, mem_ball_self hsmall⟩, ?_⟩
  intro z hz
  have hzx : dist z x < small := hz.2
  obtain ⟨d⟩ := hdata L z (hzx.trans_le (min_le_left _ _))
  have hzxRadius : dist z x < radius :=
    (hzx.trans_le (min_le_right _ _)).trans (half_lt_self hradius)
  have heq : EqOn s.germ d.successor.germ (ball z radius) :=
    hadmissible L z d hzxRadius
  apply (injOn_chartAt_of_eqOn_successor d heq).mono
  intro a ha
  refine ⟨ha.1, ?_⟩
  have hax : dist a x < radius / 2 := ha.2.trans_le (min_le_right _ _)
  have hxz : dist x z < radius / 2 := by
    rw [dist_comm]
    exact hzx.trans_le (min_le_right _ _)
  change dist a z < radius
  exact (dist_triangle a x z).trans_lt (by linarith)

/-- A concrete obstruction involving only the chosen total chart maps.
Every neighborhood contains a nearby chart identifying two distinct points
of that same neighborhood. The points need not lie in that chart's source. -/
def PreferredChartCollisionAccumulation (x : M) : Prop :=
  ∀ V : Set M, V ∈ 𝓝 x →
    ∃ z ∈ V, ∃ a ∈ V, ∃ b ∈ V, a ≠ b ∧ chartAt E z a = chartAt E z b

/-- Constant total extensions outside balls shrinking toward a nonisolated
anchor produce the precise collision obstruction. The condition concerns
only off-ball chart values, with no assumptions on Cartan-map extensions. -/
theorem preferredChartCollisionAccumulation_of_shrinking_constant_extensions
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M)
    (hacc : AccPt x (𝓟 (univ : Set M)))
    (hconstant :
      letI : MetricSpace M := g.toMetricSpace
      ∀ z : M, z ≠ x → ∀ a b : M,
        dist z x / 2 ≤ dist a z → dist z x / 2 ≤ dist b z →
          chartAt E z a = chartAt E z b) :
    PreferredChartCollisionAccumulation x := by
  letI : MetricSpace M := g.toMetricSpace
  intro V hV
  have hnear := accPt_iff_nhds.mp hacc
  rcases hnear V hV with ⟨z, hz, hzx⟩
  have hdist : 0 < dist z x := dist_pos.mpr hzx
  have hsmall : 0 < dist z x / 4 := div_pos hdist (by norm_num)
  rcases hnear (V ∩ ball x (dist z x / 4))
      (inter_mem hV (ball_mem_nhds x hsmall)) with ⟨b, hb, hbx⟩
  refine ⟨z, hz.1, x, mem_of_mem_nhds hV, b, hb.1.1, hbx.symm, ?_⟩
  apply hconstant z hzx
  · rw [dist_comm x z]
    exact half_le_self hdist.le
  · have hbsmall : dist b x < dist z x / 4 := hb.1.2
    have htriangle := dist_triangle z b x
    rw [dist_comm z b] at htriangle
    linarith

/-- Accumulating preferred-chart collisions rule out a positive common
output radius even with predecessor source and target anchors fixed. -/
theorem not_admissible_of_constantCurvature_of_preferredChartCollisionAccumulation
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3)
    (hcollision : PreferredChartCollisionAccumulation x)
    {radius : ℝ} (hradius : 0 < radius) :
    ¬ ActualSuccessorEqualityRadiusAdmissible g x p radius := by
  intro hadmissible
  rcases exists_open_nhds_injOn_chartAt_of_constantCurvature_of_admissible
      g hcurv x p hradius hadmissible with ⟨V, hV, hx, hinj⟩
  rcases hcollision V (hV.mem_nhds hx) with ⟨z, hz, a, ha, b, hb, hne, heq⟩
  exact hne (hinj z hz ha hb heq)

/-- The frozen persistence conclusion is incompatible with accumulating
collisions of the total preferred charts. The contradiction already occurs
at the center of the purported neighborhood of anchor pairs. -/
theorem not_actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature_of_preferredChartCollisionAccumulation
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (hcollision : PreferredChartCollisionAccumulation x) :
    ¬ ActualSuccessorEqualityRadiusLocalPersistence g := by
  intro hpersistence
  let p : RoundSphere3 := Classical.choice inferInstance
  rcases hpersistence (x, p) with ⟨radius, hradius, hlocal⟩
  exact not_admissible_of_constantCurvature_of_preferredChartCollisionAccumulation
    g hcurv x p hcollision hradius hlocal.self_of_nhds

end SuccessorEqualityRadiusPersistence
end Poincare
