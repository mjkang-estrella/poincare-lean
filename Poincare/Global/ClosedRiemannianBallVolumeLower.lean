import Poincare.Global.NormalizedFlowEnergyConcentration
import Poincare.Global.VolumeMeasureOpenPositivity

/-!
# Uniform positive volume of fixed-metric balls

For one closed Riemannian manifold, compactness and full support of Riemannian
volume give a positive lower bound for all balls of any fixed positive radius.
The proof uses a finite metric-ball cover: every arbitrary ball contains one
member of a finite family of smaller balls, and the minimum of their positive
volumes is positive.

The same argument, followed by a second finite minimum, proves the qualitative
noncollapse contract for every finite family of closed metrics.  No curvature
comparison theorem is needed.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Bundle MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- For a single closed Riemannian metric and any fixed positive radius, all
metric balls have volume bounded below by one positive real constant. -/
theorem exists_pos_uniform_closedRiemannianBall_volume_lower
    (g : ClosedSmoothRiemannianMetric n M)
    (r : ℝ) (hr : 0 < r) :
    ∃ v : ℝ, 0 < v ∧ ∀ x : M,
      v ≤ (volumeMeasure g).real (closedRiemannianBall g x r) := by
  letI : MetricSpace M := g.toMetricSpace
  let smallRadius : ℝ := r / 3
  have hsmallRadius : 0 < smallRadius := div_pos hr (by norm_num)
  classical
  obtain ⟨centers, hcover⟩ :=
    isCompact_univ.elim_finite_subcover
      (fun x : M ↦ Metric.ball x smallRadius)
      (fun _x ↦ Metric.isOpen_ball)
      (fun x _hx ↦ Set.mem_iUnion.mpr
        ⟨x, Metric.mem_ball_self hsmallRadius⟩)
  have hcenters : centers.Nonempty := by
    let x : M := Classical.choice inferInstance
    obtain ⟨a, ha, _hxa⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ x))
    exact ⟨a, ha⟩
  let volumeAt : M → ℝ := fun a ↦
    (volumeMeasure g).real (Metric.ball a smallRadius)
  let v : ℝ := centers.inf' hcenters volumeAt
  letI : IsFiniteMeasure (volumeMeasure g) := volumeMeasure_isFiniteMeasure g
  have hvolumeAt : ∀ a ∈ centers, 0 < volumeAt a := by
    intro a _ha
    have hne : volumeMeasure g (Metric.ball a smallRadius) ≠ 0 :=
      volumeMeasure_ne_zero_of_isOpen_nonempty g Metric.isOpen_ball
        ⟨a, Metric.mem_ball_self hsmallRadius⟩
    have htop : volumeMeasure g (Metric.ball a smallRadius) ≠ (⊤ : ℝ≥0∞) :=
      measure_ne_top (volumeMeasure g) _
    exact ENNReal.toReal_pos hne htop
  have hv : 0 < v := by
    dsimp only [v]
    rw [Finset.lt_inf'_iff]
    exact hvolumeAt
  refine ⟨v, hv, ?_⟩
  intro x
  obtain ⟨a, ha, hxa⟩ :=
    Set.mem_iUnion₂.mp (hcover (Set.mem_univ x))
  have hsubset : Metric.ball a smallRadius ⊆ Metric.ball x r := by
    intro y hya
    rw [Metric.mem_ball] at hya hxa ⊢
    have hax : dist a x < smallRadius := by simpa [dist_comm] using hxa
    calc
      dist y x ≤ dist y a + dist a x := dist_triangle _ _ _
      _ < smallRadius + smallRadius := add_lt_add hya hax
      _ < r := by
        dsimp only [smallRadius]
        linarith
  have hvCenter : v ≤ volumeAt a := by
    exact Finset.inf'_le volumeAt ha
  have hmeasure : volumeAt a ≤
      (volumeMeasure g).real (Metric.ball x r) := by
    exact measureReal_mono hsubset
  simpa only [closedRiemannianBall, volumeAt] using hvCenter.trans hmeasure

/-- A constant metric family satisfies the qualitative uniform ball-volume
lower bound used by the concentration theorem. -/
theorem uniformClosedRiemannianBallVolumeLower_const
    {ι : Type*} (g : ClosedSmoothRiemannianMetric n M) :
    UniformClosedRiemannianBallVolumeLower (fun _ : ι ↦ g) := by
  intro r hr
  rcases exists_pos_uniform_closedRiemannianBall_volume_lower g r hr with
    ⟨v, hv, hball⟩
  exact ⟨v, hv, fun _i x ↦ hball x⟩

/-- Every nonempty finite family of closed metrics satisfies one common
qualitative ball-volume lower bound at each fixed positive radius. -/
theorem uniformClosedRiemannianBallVolumeLower_of_finite
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → ClosedSmoothRiemannianMetric n M) :
    UniformClosedRiemannianBallVolumeLower g := by
  classical
  intro r hr
  have hmetric : ∀ i : ι,
      ∃ v : ℝ, 0 < v ∧ ∀ x : M,
        v ≤ (volumeMeasure (g i)).real
          (closedRiemannianBall (g i) x r) :=
    fun i ↦ exists_pos_uniform_closedRiemannianBall_volume_lower (g i) r hr
  choose volumeLower hvolumeLower hball using hmetric
  have huniv : (Finset.univ : Finset ι).Nonempty :=
    Finset.univ_nonempty
  let v : ℝ := Finset.univ.inf' huniv volumeLower
  have hv : 0 < v := by
    dsimp only [v]
    rw [Finset.lt_inf'_iff]
    intro i _hi
    exact hvolumeLower i
  refine ⟨v, hv, ?_⟩
  intro i x
  exact (Finset.inf'_le volumeLower (Finset.mem_univ i)).trans (hball i x)

/-- Uniform upper comparison of each family distance by a fixed reference
distance.  This is the ball-inclusion half of a uniform bilipschitz bound. -/
def UniformClosedRiemannianDistanceUpperComparison
    {ι : Type*} (gref : ClosedSmoothRiemannianMetric n M)
    (g : ι → ClosedSmoothRiemannianMetric n M) (C : ℝ) : Prop :=
  0 < C ∧ ∀ i x y,
    closedRiemannianDistance (g i) y x ≤
      C * closedRiemannianDistance gref y x

/-- Uniform lower comparison of the family volume measures by one fixed
reference Riemannian volume. -/
def UniformClosedRiemannianVolumeMeasureLowerComparison
    {ι : Type*} (gref : ClosedSmoothRiemannianMetric n M)
    (g : ι → ClosedSmoothRiemannianMetric n M) (c : ℝ) : Prop :=
  0 < c ∧ ∀ i (A : Set M), MeasurableSet A →
    c * (volumeMeasure gref).real A ≤ (volumeMeasure (g i)).real A

/-- Uniform distance and volume-measure comparison with one reference metric
imply the qualitative ball noncollapse used by concentration. -/
theorem uniformClosedRiemannianBallVolumeLower_of_referenceComparison
    {ι : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : ι → ClosedSmoothRiemannianMetric n M)
    {C c : ℝ}
    (hdist : UniformClosedRiemannianDistanceUpperComparison gref g C)
    (hvolume : UniformClosedRiemannianVolumeMeasureLowerComparison gref g c) :
    UniformClosedRiemannianBallVolumeLower g := by
  intro r hr
  let refRadius : ℝ := r / C
  have hrefRadius : 0 < refRadius := div_pos hr hdist.1
  rcases
      exists_pos_uniform_closedRiemannianBall_volume_lower
        gref refRadius hrefRadius with
    ⟨vref, hvref, hrefBall⟩
  refine ⟨c * vref, mul_pos hvolume.1 hvref, ?_⟩
  intro i x
  have hsubset :
      closedRiemannianBall gref x refRadius ⊆
        closedRiemannianBall (g i) x r := by
    intro y hy
    rw [mem_closedRiemannianBall_iff] at hy ⊢
    calc
      closedRiemannianDistance (g i) y x ≤
          C * closedRiemannianDistance gref y x := hdist.2 i x y
      _ < C * refRadius := mul_lt_mul_of_pos_left hy hdist.1
      _ = r := by
        dsimp only [refRadius]
        exact mul_div_cancel₀ r (ne_of_gt hdist.1)
  have hrefMeasurable :
      MeasurableSet (closedRiemannianBall gref x refRadius) :=
    closedRiemannianBall_measurableSet gref x refRadius
  letI : IsFiniteMeasure (volumeMeasure (g i)) :=
    volumeMeasure_isFiniteMeasure (g i)
  calc
    c * vref ≤
        c * (volumeMeasure gref).real
          (closedRiemannianBall gref x refRadius) :=
      mul_le_mul_of_nonneg_left (hrefBall x) hvolume.1.le
    _ ≤ (volumeMeasure (g i)).real
          (closedRiemannianBall gref x refRadius) :=
      hvolume.2 i _ hrefMeasurable
    _ ≤ (volumeMeasure (g i)).real
          (closedRiemannianBall (g i) x r) :=
      measureReal_mono hsubset

/--
Pointwise reference comparisons over a compact parameter space become uniform
when their positive distance and volume factors vary continuously.

This is the compact-family form needed for a normalized-flow orbit closure:
it asks for the ordinary comparison estimates at each parameter, while the
extreme-value theorem supplies the single upper distance factor and single
positive lower volume factor consumed by
`uniformClosedRiemannianBallVolumeLower_of_referenceComparison`.
-/
theorem uniformClosedRiemannianBallVolumeLower_of_compact_referenceComparison
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : K → ClosedSmoothRiemannianMetric n M)
    (distanceFactor volumeFactor : K → ℝ)
    (hDistanceContinuous : Continuous distanceFactor)
    (hVolumeContinuous : Continuous volumeFactor)
    (hDistancePos : ∀ k, 0 < distanceFactor k)
    (hVolumePos : ∀ k, 0 < volumeFactor k)
    (hDistance : ∀ k x y,
      closedRiemannianDistance (g k) y x ≤
        distanceFactor k * closedRiemannianDistance gref y x)
    (hVolume : ∀ k (A : Set M), MeasurableSet A →
      volumeFactor k * (volumeMeasure gref).real A ≤
        (volumeMeasure (g k)).real A) :
    UniformClosedRiemannianBallVolumeLower g := by
  obtain ⟨kMax, _hkMax, hkMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMaxOn
      Set.univ_nonempty hDistanceContinuous.continuousOn
  obtain ⟨kMin, _hkMin, hkMin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMinOn
      Set.univ_nonempty hVolumeContinuous.continuousOn
  have hUniformDistance :
      UniformClosedRiemannianDistanceUpperComparison
        gref g (distanceFactor kMax) := by
    refine ⟨hDistancePos kMax, ?_⟩
    intro k x y
    have hrefNonneg : 0 ≤ closedRiemannianDistance gref y x := by
      letI : MetricSpace M := gref.toMetricSpace
      exact dist_nonneg
    exact (hDistance k x y).trans <|
      mul_le_mul_of_nonneg_right (hkMax (Set.mem_univ k)) hrefNonneg
  have hUniformVolume :
      UniformClosedRiemannianVolumeMeasureLowerComparison
        gref g (volumeFactor kMin) := by
    refine ⟨hVolumePos kMin, ?_⟩
    intro k A hA
    have hrefNonneg : 0 ≤ (volumeMeasure gref).real A :=
      measureReal_nonneg
    exact
      (mul_le_mul_of_nonneg_right (hkMin (Set.mem_univ k)) hrefNonneg).trans
        (hVolume k A hA)
  exact
    uniformClosedRiemannianBallVolumeLower_of_referenceComparison
      gref g hUniformDistance hUniformVolume

/-- Uniform qualitative noncollapse is preserved by an arbitrary reindexing
of a metric family. -/
theorem UniformClosedRiemannianBallVolumeLower.comp
    {K ι : Type*} {g : K → ClosedSmoothRiemannianMetric n M}
    (h : UniformClosedRiemannianBallVolumeLower g) (parameter : ι → K) :
    UniformClosedRiemannianBallVolumeLower (fun i ↦ g (parameter i)) := by
  intro r hr
  rcases h r hr with ⟨v, hv, hball⟩
  exact ⟨v, hv, fun i x ↦ hball (parameter i) x⟩

/--
A metric family realized through a compact parameter space inherits uniform
ball noncollapse from continuous pointwise reference-comparison factors on
the ambient compact family.

The index type `ι` is unrestricted.  In particular, it can be `ℝ` for a
normalized flow or `ℕ` for a sampled sequence; compactness is required only
of the parameter space containing its metric orbit.
-/
theorem uniformClosedRiemannianBallVolumeLower_of_compact_parameterization
    {K ι : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gref : ClosedSmoothRiemannianMetric n M)
    (metric : K → ClosedSmoothRiemannianMetric n M)
    (parameter : ι → K)
    (g : ι → ClosedSmoothRiemannianMetric n M)
    (hRealize : ∀ i, metric (parameter i) = g i)
    (distanceFactor volumeFactor : K → ℝ)
    (hDistanceContinuous : Continuous distanceFactor)
    (hVolumeContinuous : Continuous volumeFactor)
    (hDistancePos : ∀ k, 0 < distanceFactor k)
    (hVolumePos : ∀ k, 0 < volumeFactor k)
    (hDistance : ∀ k x y,
      closedRiemannianDistance (metric k) y x ≤
        distanceFactor k * closedRiemannianDistance gref y x)
    (hVolume : ∀ k (A : Set M), MeasurableSet A →
      volumeFactor k * (volumeMeasure gref).real A ≤
        (volumeMeasure (metric k)).real A) :
    UniformClosedRiemannianBallVolumeLower g := by
  have hCompactFamily :
      UniformClosedRiemannianBallVolumeLower metric :=
    uniformClosedRiemannianBallVolumeLower_of_compact_referenceComparison
      gref metric distanceFactor volumeFactor hDistanceContinuous
      hVolumeContinuous hDistancePos hVolumePos hDistance hVolume
  have hParameterized := hCompactFamily.comp parameter
  intro r hr
  rcases hParameterized r hr with ⟨v, hv, hball⟩
  refine ⟨v, hv, ?_⟩
  intro i x
  simpa only [hRealize i] using hball i x

/--
For a sequence of metrics, uniform noncollapse of one tail extends across the
whole sequence.  The omitted prefix is finite and therefore has its own
positive minimum ball volume at every fixed radius.
-/
theorem uniformClosedRiemannianBallVolumeLower_nat_of_tail
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (N : ℕ)
    (hTail : UniformClosedRiemannianBallVolumeLower
      (fun i : {j : ℕ // N ≤ j} ↦ g i)) :
    UniformClosedRiemannianBallVolumeLower g := by
  intro r hr
  rcases hTail r hr with ⟨vTail, hvTail, htailBall⟩
  have hPrefix : UniformClosedRiemannianBallVolumeLower
      (fun i : Fin (N + 1) ↦ g i) :=
    uniformClosedRiemannianBallVolumeLower_of_finite
      (fun i : Fin (N + 1) ↦ g i)
  rcases hPrefix r hr with ⟨vPrefix, hvPrefix, hprefixBall⟩
  refine ⟨min vPrefix vTail, lt_min hvPrefix hvTail, ?_⟩
  intro i x
  by_cases hi : N ≤ i
  · exact (min_le_right vPrefix vTail).trans
      (htailBall ⟨i, hi⟩ x)
  · have hiN : i < N := Nat.lt_of_not_ge hi
    let j : Fin (N + 1) := ⟨i, hiN.trans_le (Nat.le_add_right N 1)⟩
    exact (min_le_left vPrefix vTail).trans (hprefixBall j x)

/--
Eventual uniform comparison with one reference metric supplies uniform ball
noncollapse for an entire metric sequence.  Only the tail must satisfy the
comparison; compactness of the manifold handles the finite prefix.
-/
theorem uniformClosedRiemannianBallVolumeLower_nat_of_eventual_referenceComparison
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (N : ℕ) {C c : ℝ}
    (hC : 0 < C) (hc : 0 < c)
    (hDistance : ∀ i, N ≤ i → ∀ x y,
      closedRiemannianDistance (g i) y x ≤
        C * closedRiemannianDistance gref y x)
    (hVolume : ∀ i, N ≤ i → ∀ (A : Set M), MeasurableSet A →
      c * (volumeMeasure gref).real A ≤
        (volumeMeasure (g i)).real A) :
    UniformClosedRiemannianBallVolumeLower g := by
  let tail : {i : ℕ // N ≤ i} → ClosedSmoothRiemannianMetric n M :=
    fun i ↦ g i
  have hTailDistance :
      UniformClosedRiemannianDistanceUpperComparison gref tail C := by
    exact ⟨hC, fun i x y ↦ hDistance i i.property x y⟩
  have hTailVolume :
      UniformClosedRiemannianVolumeMeasureLowerComparison gref tail c := by
    exact ⟨hc, fun i A hA ↦ hVolume i i.property A hA⟩
  have hTail : UniformClosedRiemannianBallVolumeLower tail :=
    uniformClosedRiemannianBallVolumeLower_of_referenceComparison
      gref tail hTailDistance hTailVolume
  exact uniformClosedRiemannianBallVolumeLower_nat_of_tail g N hTail

end Poincare
