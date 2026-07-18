import Poincare.Global.ClosedRiemannianBallVolumeLower
import Poincare.Global.NormalizedFlowEnergyConcentrationLipschitzBridge

/-!
# Riemannian distance comparison from tangent-norm comparison

The ball-volume compactness bridge is naturally stated using a distance
comparison with a reference metric.  This module derives that comparison from
the more local geometric input: a pointwise upper comparison of tangent
norms.  The proof integrates the norm estimate along every smooth path and
then uses the defining infimum of Riemannian distance.
-/

noncomputable section

open Bundle FiberBundle Manifold MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M] [Nonempty M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The extended norm of a tangent vector for one supplied metric, exposed
without installing its Riemannian-bundle instance globally. -/
def closedRiemannianTangentEnorm
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x) : ℝ≥0∞ :=
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  ‖v‖ₑ

/-- The ordinary tangent norm for one supplied metric. -/
def closedRiemannianTangentNorm
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x) : ℝ :=
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  ‖v‖

theorem closedRiemannianTangentNorm_nonneg
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x) :
    0 ≤ closedRiemannianTangentNorm g x v := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  exact norm_nonneg v

theorem closedRiemannianTangentEnorm_eq_ofReal_norm
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x) :
    closedRiemannianTangentEnorm g x v =
      ENNReal.ofReal (closedRiemannianTangentNorm g x v) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  exact (ofReal_norm_eq_enorm v).symm

theorem closedRiemannianTangentNorm_sq
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (v : TM x) :
    closedRiemannianTangentNorm g x v ^ 2 = g.inner x v v := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  rw [← ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
  exact (real_inner_self_eq_norm_sq v).symm

/-- The Riemannian extended distance belonging to one supplied metric. -/
def closedRiemannianEDistance
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) : ℝ≥0∞ :=
  letI : EMetricSpace M := g.toEMetricSpace
  edist x y

/-- The exposed extended distance is the infimum of the exposed path
derivative integrals. -/
theorem closedRiemannianEDistance_eq_iInf_pathDerivativeIntegral
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    closedRiemannianEDistance g x y =
      ⨅ (gamma : Path x y)
        (_ : ContMDiff (𝓡∂ 1) I 1 gamma),
          closedRiemannianPathDerivativeIntegral g gamma := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  letI : IsContinuousRiemannianBundle (ClosedSmoothModel n)
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toIsContinuousRiemannianBundle
  letI : EMetricSpace M := g.toEMetricSpace
  change edist x y =
    ⨅ (gamma : Path x y)
      (_ : ContMDiff (𝓡∂ 1) I 1 gamma),
        ∫⁻ t, ‖mfderiv (𝓡∂ 1) I gamma t 1‖ₑ
  rw [show edist x y = riemannianEDist I x y by rfl]
  rw [riemannianEDist]

/-- Extended and ordinary distance wrappers agree through `ofReal`. -/
theorem closedRiemannianEDistance_eq_ofReal_distance
    (g : ClosedSmoothRiemannianMetric n M) (x y : M) :
    closedRiemannianEDistance g x y =
      ENNReal.ofReal (closedRiemannianDistance g x y) := by
  letI : EMetricSpace M := g.toEMetricSpace
  letI : MetricSpace M := g.toMetricSpace
  change edist x y = ENNReal.ofReal (dist x y)
  rw [← edist_dist]

/-- Pointwise tangent norm comparison with one fixed reference metric. -/
def UniformClosedRiemannianTangentEnormUpperComparison
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) (C : ℝ) : Prop :=
  0 < C ∧ ∀ i x (v : TM x),
    closedRiemannianTangentEnorm (g i) x v ≤
      ENNReal.ofReal C * closedRiemannianTangentEnorm gref x v

/-- Pointwise quadratic-form domination by one reference metric.  The square
on `C` is chosen so that `C` is the resulting tangent-norm and path-length
factor. -/
def UniformClosedRiemannianMetricUpperComparison
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) (C : ℝ) : Prop :=
  0 < C ∧ ∀ i x (v : TM x),
    (g i).inner x v v ≤ C ^ 2 * gref.inner x v v

/-- Quadratic-form domination gives the exposed extended tangent-norm
comparison. -/
theorem uniformClosedRiemannianTangentEnormUpperComparison_of_metric
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C : ℝ}
    (h : UniformClosedRiemannianMetricUpperComparison gref g C) :
    UniformClosedRiemannianTangentEnormUpperComparison gref g C := by
  refine ⟨h.1, ?_⟩
  intro i x v
  have hsq : closedRiemannianTangentNorm (g i) x v ^ 2 ≤
      (C * closedRiemannianTangentNorm gref x v) ^ 2 := by
    rw [closedRiemannianTangentNorm_sq]
    calc
      (g i).inner x v v ≤ C ^ 2 * gref.inner x v v := h.2 i x v
      _ = (C * closedRiemannianTangentNorm gref x v) ^ 2 := by
        rw [← closedRiemannianTangentNorm_sq]
        ring
  have hnorm : closedRiemannianTangentNorm (g i) x v ≤
      C * closedRiemannianTangentNorm gref x v :=
    (sq_le_sq₀
      (closedRiemannianTangentNorm_nonneg (g i) x v)
      (mul_nonneg h.1.le
        (closedRiemannianTangentNorm_nonneg gref x v))).1 hsq
  rw [closedRiemannianTangentEnorm_eq_ofReal_norm,
    closedRiemannianTangentEnorm_eq_ofReal_norm,
    ← ENNReal.ofReal_mul h.1.le]
  exact ENNReal.ofReal_le_ofReal hnorm

/-- The corresponding comparison for every smooth path length. -/
def UniformClosedRiemannianPathLengthUpperComparison
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) (C : ℝ) : Prop :=
  0 < C ∧ ∀ i x y (gamma : Path x y),
    closedRiemannianPathDerivativeIntegral (g i) gamma ≤
      ENNReal.ofReal C *
        closedRiemannianPathDerivativeIntegral gref gamma

/-- Pointwise tangent norm comparison integrates to path-length comparison. -/
theorem uniformClosedRiemannianPathLengthUpperComparison_of_tangentEnorm
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C : ℝ}
    (h : UniformClosedRiemannianTangentEnormUpperComparison gref g C) :
    UniformClosedRiemannianPathLengthUpperComparison gref g C := by
  refine ⟨h.1, ?_⟩
  intro i x y gamma
  change
    (∫⁻ t, closedRiemannianTangentEnorm (g i) (gamma t)
      (mfderiv (𝓡∂ 1) I gamma t 1)) ≤
      ENNReal.ofReal C *
        ∫⁻ t, closedRiemannianTangentEnorm gref (gamma t)
          (mfderiv (𝓡∂ 1) I gamma t 1)
  calc
    (∫⁻ t, closedRiemannianTangentEnorm (g i) (gamma t)
        (mfderiv (𝓡∂ 1) I gamma t 1)) ≤
        ∫⁻ t, ENNReal.ofReal C *
          closedRiemannianTangentEnorm gref (gamma t)
            (mfderiv (𝓡∂ 1) I gamma t 1) :=
      lintegral_mono (fun t ↦ h.2 i (gamma t)
        (mfderiv (𝓡∂ 1) I gamma t 1))
    _ = ENNReal.ofReal C *
        ∫⁻ t, closedRiemannianTangentEnorm gref (gamma t)
          (mfderiv (𝓡∂ 1) I gamma t 1) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- A uniform path-length comparison passes to the infimum defining
Riemannian distance. -/
theorem uniformClosedRiemannianDistanceUpperComparison_of_pathLength
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C : ℝ}
    (h : UniformClosedRiemannianPathLengthUpperComparison gref g C) :
    UniformClosedRiemannianDistanceUpperComparison gref g C := by
  refine ⟨h.1, ?_⟩
  intro i x y
  have hCne : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 h.1).ne'
  have hCtop : ENNReal.ofReal C ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hEDistance :
      closedRiemannianEDistance (g i) y x ≤
        ENNReal.ofReal C * closedRiemannianEDistance gref y x := by
    rw [closedRiemannianEDistance_eq_iInf_pathDerivativeIntegral,
      closedRiemannianEDistance_eq_iInf_pathDerivativeIntegral,
      ENNReal.mul_iInf_of_ne hCne hCtop]
    refine le_iInf (fun gamma ↦ ?_)
    rw [ENNReal.mul_iInf_of_ne hCne hCtop]
    refine le_iInf (fun hgamma ↦ ?_)
    exact
      (iInf_le_of_le gamma
        (iInf_le_of_le hgamma (le_refl _))).trans
          (h.2 i y x gamma)
  have hrefNonneg : 0 ≤ closedRiemannianDistance gref y x := by
    letI : MetricSpace M := gref.toMetricSpace
    exact dist_nonneg
  rw [closedRiemannianEDistance_eq_ofReal_distance,
    closedRiemannianEDistance_eq_ofReal_distance,
    ← ENNReal.ofReal_mul h.1.le] at hEDistance
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg h.1.le hrefNonneg)).1 hEDistance

/-- Pointwise tangent norm comparison directly supplies ordinary distance
comparison. -/
theorem uniformClosedRiemannianDistanceUpperComparison_of_tangentEnorm
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C : ℝ}
    (h : UniformClosedRiemannianTangentEnormUpperComparison gref g C) :
    UniformClosedRiemannianDistanceUpperComparison gref g C :=
  uniformClosedRiemannianDistanceUpperComparison_of_pathLength gref g
    (uniformClosedRiemannianPathLengthUpperComparison_of_tangentEnorm
      gref g h)

/-- Pointwise quadratic-form domination directly supplies ordinary distance
comparison. -/
theorem uniformClosedRiemannianDistanceUpperComparison_of_metric
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C : ℝ}
    (h : UniformClosedRiemannianMetricUpperComparison gref g C) :
    UniformClosedRiemannianDistanceUpperComparison gref g C :=
  uniformClosedRiemannianDistanceUpperComparison_of_tangentEnorm gref g
    (uniformClosedRiemannianTangentEnormUpperComparison_of_metric gref g h)

/-- Tangent norm comparison and reference-volume comparison imply uniform
qualitative ball noncollapse. -/
theorem uniformClosedRiemannianBallVolumeLower_of_tangentEnorm_volumeReferenceComparison
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C c : ℝ}
    (hTangent :
      UniformClosedRiemannianTangentEnormUpperComparison gref g C)
    (hVolume :
      UniformClosedRiemannianVolumeMeasureLowerComparison gref g c) :
    UniformClosedRiemannianBallVolumeLower g :=
  uniformClosedRiemannianBallVolumeLower_of_referenceComparison
    gref g
      (uniformClosedRiemannianDistanceUpperComparison_of_tangentEnorm
        gref g hTangent)
      hVolume

/-- Quadratic-form domination and reference-volume comparison imply uniform
qualitative ball noncollapse. -/
theorem uniformClosedRiemannianBallVolumeLower_of_metric_volumeReferenceComparison
    {iota : Type*}
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : iota → ClosedSmoothRiemannianMetric n M) {C c : ℝ}
    (hMetric : UniformClosedRiemannianMetricUpperComparison gref g C)
    (hVolume :
      UniformClosedRiemannianVolumeMeasureLowerComparison gref g c) :
    UniformClosedRiemannianBallVolumeLower g :=
  uniformClosedRiemannianBallVolumeLower_of_referenceComparison
    gref g
      (uniformClosedRiemannianDistanceUpperComparison_of_metric
        gref g hMetric)
      hVolume

/--
Continuous positive pointwise quadratic-form and volume factors on a compact
metric parameter space become uniform.  Consequently, tensor-level reference
comparison on the compact family implies uniform ball noncollapse without a
preselected global comparison constant.
-/
theorem uniformClosedRiemannianBallVolumeLower_of_compact_metric_volumeReferenceComparison
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (gref : ClosedSmoothRiemannianMetric n M)
    (g : K → ClosedSmoothRiemannianMetric n M)
    (metricFactor volumeFactor : K → ℝ)
    (hMetricFactorContinuous : Continuous metricFactor)
    (hVolumeFactorContinuous : Continuous volumeFactor)
    (hMetricFactorPos : ∀ k, 0 < metricFactor k)
    (hVolumeFactorPos : ∀ k, 0 < volumeFactor k)
    (hMetric : ∀ k x (v : TM x),
      (g k).inner x v v ≤
        (metricFactor k) ^ 2 * gref.inner x v v)
    (hVolume : ∀ k (A : Set M), MeasurableSet A →
      volumeFactor k * (volumeMeasure gref).real A ≤
        (volumeMeasure (g k)).real A) :
    UniformClosedRiemannianBallVolumeLower g := by
  obtain ⟨kMax, _hkMax, hkMax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMaxOn
      Set.univ_nonempty hMetricFactorContinuous.continuousOn
  obtain ⟨kMin, _hkMin, hkMin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set K)).exists_isMinOn
      Set.univ_nonempty hVolumeFactorContinuous.continuousOn
  have hUniformMetric :
      UniformClosedRiemannianMetricUpperComparison
        gref g (metricFactor kMax) := by
    refine ⟨hMetricFactorPos kMax, ?_⟩
    intro k x v
    have hfactorSq : (metricFactor k) ^ 2 ≤
        (metricFactor kMax) ^ 2 :=
      (sq_le_sq₀ (hMetricFactorPos k).le
        (hMetricFactorPos kMax).le).2
          (hkMax (Set.mem_univ k))
    exact (hMetric k x v).trans <|
      mul_le_mul_of_nonneg_right hfactorSq (gref.inner_nonneg x v)
  have hUniformVolume :
      UniformClosedRiemannianVolumeMeasureLowerComparison
        gref g (volumeFactor kMin) := by
    refine ⟨hVolumeFactorPos kMin, ?_⟩
    intro k A hA
    exact
      (mul_le_mul_of_nonneg_right (hkMin (Set.mem_univ k))
        measureReal_nonneg).trans (hVolume k A hA)
  exact
    uniformClosedRiemannianBallVolumeLower_of_metric_volumeReferenceComparison
      gref g hUniformMetric hUniformVolume

end Poincare
