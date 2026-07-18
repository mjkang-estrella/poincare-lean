import Poincare.Global.NormalizedFlowEnergyConcentration

/-!
# Path-integral source of the normalized-flow Lipschitz hypothesis

The concentration theorem in `NormalizedFlowEnergyConcentration` asks for a
uniform Lipschitz bound measured in each time slice's own Riemannian distance.
This file reduces that hypothesis to the corresponding first-order estimate
along every smooth path.

The path premise is deliberately stated using the integral that defines
Mathlib's Riemannian distance.  It is therefore the exact remaining interface
for turning a uniform bound on the spatial derivative of a scalar field into a
global Lipschitz estimate.  In particular, a future contraction of a Shi bound
to the gradient of squared traceless Ricci curvature only has to establish this
path-integral premise; the distance infimum and the concentration argument are
then automatic.
-/

noncomputable section

open Bundle FiberBundle Filter Manifold MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section PathIntegralLipschitz

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/--
The Riemannian speed integral of a unit-interval path, with the tangent norm
installed from the supplied metric.

This is the integrand occurring definitionally in Mathlib's
`riemannianEDist`.
-/
def closedRiemannianPathDerivativeIntegral
    (g : ClosedSmoothRiemannianMetric n M) {x y : M} (gamma : Path x y) : ℝ≥0∞ :=
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    g.toRiemannianBundle
  ∫⁻ t, ‖mfderiv (𝓡∂ 1) (closedSmoothModelWithCorners n) gamma t 1‖ₑ

/--
A uniform first-order path-integral estimate for scalar fields on a family of
Riemannian metrics.

The estimate says that the endpoint oscillation is at most `L` times the
integral of Riemannian speed along every `C¹` path.  This is the coordinate-free
integrated form of the pointwise gradient bound `|df|_g ≤ L`.
-/
def UniformClosedRiemannianPathIntegralGradientBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) (L : ℝ) : Prop :=
  0 < L ∧ ∀ i x y (gamma : Path x y),
    ContMDiff (𝓡∂ 1) (closedSmoothModelWithCorners n) 1 gamma →
    ENNReal.ofReal |f i y - f i x| ≤
      ENNReal.ofReal L *
        closedRiemannianPathDerivativeIntegral (g i) gamma

/--
A uniform pointwise bound on the manifold derivative of a scalar field, with
the source tangent norm taken from each metric in the family.

This is the usual intrinsic hypothesis `|df|_g ≤ L`.  The explicit `C¹`
field records the regularity needed by the fundamental theorem of calculus.
-/
def UniformClosedRiemannianMFDerivBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) (L : ℝ) : Prop :=
  0 < L ∧
    (∀ i, ContMDiff (closedSmoothModelWithCorners n) 𝓘(ℝ) 1 (f i)) ∧
    ∀ i x (v : TangentSpace (closedSmoothModelWithCorners n) x),
      letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
        (g i).toRiemannianBundle
      ‖mfderiv (closedSmoothModelWithCorners n) 𝓘(ℝ) (f i) x v‖ₑ ≤
        ENNReal.ofReal L * ‖v‖ₑ

/--
An intrinsic uniform `|df|_g ≤ L` bound integrates along every smooth path.

This is the analytic bridge between a pointwise spatial first-derivative
estimate and `UniformClosedRiemannianPathIntegralGradientBound`.
-/
theorem uniformClosedRiemannianPathIntegralGradientBound_of_mfderivBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) {L : ℝ}
    (h : UniformClosedRiemannianMFDerivBound g f L) :
    UniformClosedRiemannianPathIntegralGradientBound g f L := by
  refine ⟨h.1, ?_⟩
  intro i x y gamma hgamma
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    (g i).toRiemannianBundle
  let curve : ℝ → M := gamma ∘ Set.projIcc 0 1 zero_le_one
  let F : ℝ → ℝ := f i ∘ curve
  have hcurve :
      ContMDiffOn 𝓘(ℝ) (closedSmoothModelWithCorners n) 1 curve (Icc 0 1) := by
    exact contMDiffOn_comp_projIcc_iff.2 hgamma
  have hFManifold : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) 1 F (Icc 0 1) := by
    exact (h.2.1 i).comp_contMDiffOn hcurve
  have hF : ContDiffOn ℝ 1 F (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp hFManifold
  have hPointwise : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖derivWithin F (Icc 0 1) t‖ₑ ≤
        ENNReal.ofReal L *
          ‖mfderivWithin 𝓘(ℝ) (closedSmoothModelWithCorners n)
            curve (Icc 0 1) t 1‖ₑ := by
    intro t ht
    have hOuter : MDifferentiableWithinAt
        (closedSmoothModelWithCorners n) 𝓘(ℝ) (f i) Set.univ (curve t) :=
      ((h.2.1 i).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
    have hInner : MDifferentiableWithinAt 𝓘(ℝ)
        (closedSmoothModelWithCorners n) curve (Icc 0 1) t :=
      hcurve.mdifferentiableOn one_ne_zero t ht
    have hUnique : UniqueMDiffWithinAt 𝓘(ℝ) (Icc 0 1) t :=
      (uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt
    have hChain := mfderivWithin_comp
      (I := 𝓘(ℝ)) (I' := closedSmoothModelWithCorners n) (I'' := 𝓘(ℝ))
      (f := curve) (g := f i) (s := Icc 0 1) (u := Set.univ) (x := t)
      hOuter hInner (by simp) hUnique
    have hDeriv :
        mfderivWithin 𝓘(ℝ) 𝓘(ℝ) F (Icc 0 1) t 1 =
          derivWithin F (Icc 0 1) t := by
      simp only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin]
      rfl
    rw [← hDeriv, hChain, mfderivWithin_univ]
    simpa only [ContinuousLinearMap.comp_apply, enorm_tangentSpace_vectorSpace] using
      h.2.2 i (curve t)
        (mfderivWithin 𝓘(ℝ) (closedSmoothModelWithCorners n)
          curve (Icc 0 1) t 1)
  have hEndpoint :
      ENNReal.ofReal |f i y - f i x| ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin F (Icc 0 1) t‖ₑ := by
    have hFTC :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF zero_le_one
    have hcurveZero : curve 0 = x := by
      have hproj : Set.projIcc 0 1 zero_le_one 0 = (0 : unitInterval) := by
        apply Subtype.ext
        simp
      simpa only [curve, Function.comp_apply, hproj] using gamma.source
    have hcurveOne : curve 1 = y := by
      have hproj : Set.projIcc 0 1 zero_le_one 1 = (1 : unitInterval) := by
        apply Subtype.ext
        simp
      simpa only [curve, Function.comp_apply, hproj] using gamma.target
    rw [← hcurveOne, ← hcurveZero]
    simpa only [F, Function.comp_apply, Real.enorm_eq_ofReal_abs] using hFTC
  calc
    ENNReal.ofReal |f i y - f i x|
        ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin F (Icc 0 1) t‖ₑ := hEndpoint
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal L *
            ‖mfderivWithin 𝓘(ℝ) (closedSmoothModelWithCorners n)
              curve (Icc 0 1) t 1‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hPointwise
    _ = ENNReal.ofReal L *
          Manifold.pathELength (closedSmoothModelWithCorners n) curve 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
    _ = ENNReal.ofReal L *
          closedRiemannianPathDerivativeIntegral (g i) gamma := by
      rw [closedRiemannianPathDerivativeIntegral,
        ← Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc]

/--
The path-integral gradient estimate supplies the global Lipschitz estimate in
the Riemannian distance induced by each metric.

The proof uses the defining infimum of `riemannianEDist`; no minimizing
geodesic or compactness theorem is needed.
-/
theorem uniformClosedRiemannianLipschitzBound_of_pathIntegralGradientBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) {L : ℝ}
    (h : UniformClosedRiemannianPathIntegralGradientBound g f L) :
    UniformClosedRiemannianLipschitzBound g f L := by
  refine ⟨h.1, ?_⟩
  intro i x y
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
    (g i).toRiemannianBundle
  letI : MetricSpace M := (g i).toMetricSpace
  have hL0 : ENNReal.ofReal L ≠ 0 := (ENNReal.ofReal_pos.2 h.1).ne'
  have hLtop : ENNReal.ofReal L ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hEDist :
      ENNReal.ofReal |f i y - f i x| ≤
        ENNReal.ofReal L *
          riemannianEDist (closedSmoothModelWithCorners n) x y := by
    rw [riemannianEDist, ENNReal.mul_iInf_of_ne hL0 hLtop]
    refine le_iInf (fun gamma ↦ ?_)
    rw [ENNReal.mul_iInf_of_ne hL0 hLtop]
    refine le_iInf (fun hgamma ↦ ?_)
    simpa only [closedRiemannianPathDerivativeIntegral] using
      h.2 i x y gamma hgamma
  have hDistance :
      riemannianEDist (closedSmoothModelWithCorners n) x y =
        ENNReal.ofReal (dist x y) := by
    rw [← edist_dist]
    rfl
  rw [hDistance, ← ENNReal.ofReal_mul h.1.le] at hEDist
  have hReal : |f i y - f i x| ≤ L * dist x y :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1.le dist_nonneg)).1 hEDist
  simpa only [closedRiemannianDistance, dist_comm] using hReal

/-- A uniform intrinsic manifold-derivative bound directly supplies the
Riemannian Lipschitz contract used by concentration. -/
theorem uniformClosedRiemannianLipschitzBound_of_mfderivBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    (f : ι → M → ℝ) {L : ℝ}
    (h : UniformClosedRiemannianMFDerivBound g f L) :
    UniformClosedRiemannianLipschitzBound g f L :=
  uniformClosedRiemannianLipschitzBound_of_pathIntegralGradientBound g f
    (uniformClosedRiemannianPathIntegralGradientBound_of_mfderivBound g f h)

end PathIntegralLipschitz

section CenteredScalarSquareLipschitz

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/-- A uniform bound on the centered scalar and a spatial Lipschitz bound on
scalar curvature give a Lipschitz bound for the squared centered scalar.

The mean scalar is a spatial constant on each metric slice: it cancels from
the difference of centered scalar values.  Thus no spatial derivative of the
mean scalar is introduced.  The estimate is the elementary identity
`|u² - v²| = |u - v| |u + v|` with `|u|, |v| ≤ C`. -/
theorem uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarLipschitz
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    {C G : ℝ} (hC : 0 < C)
    (hCentered : ∀ i x,
      |(g i).scalarAt x - meanScalar (g i)| ≤ C)
    (hScalar : UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ (g i).scalarAt x) G) :
    UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ ((g i).scalarAt x - meanScalar (g i)) ^ 2)
      (2 * C * G) := by
  refine ⟨mul_pos (mul_pos (by norm_num) hC) hScalar.1, ?_⟩
  intro i x y
  have hFactor :
      ((g i).scalarAt y - meanScalar (g i)) ^ 2 -
          ((g i).scalarAt x - meanScalar (g i)) ^ 2 =
        ((g i).scalarAt y - (g i).scalarAt x) *
          (((g i).scalarAt y - meanScalar (g i)) +
            ((g i).scalarAt x - meanScalar (g i))) := by
    ring
  have hSum :
      |((g i).scalarAt y - meanScalar (g i)) +
          ((g i).scalarAt x - meanScalar (g i))| ≤ 2 * C := by
    calc
      |((g i).scalarAt y - meanScalar (g i)) +
          ((g i).scalarAt x - meanScalar (g i))|
          ≤ |(g i).scalarAt y - meanScalar (g i)| +
              |(g i).scalarAt x - meanScalar (g i)| := abs_add_le _ _
      _ ≤ C + C := add_le_add (hCentered i y) (hCentered i x)
      _ = 2 * C := by ring
  have hScalarDifference := hScalar.2 i x y
  have hScalarRhsNonneg :
      0 ≤ G * closedRiemannianDistance (g i) y x :=
    (abs_nonneg ((g i).scalarAt y - (g i).scalarAt x)).trans
      hScalarDifference
  rw [hFactor, abs_mul]
  calc
    |(g i).scalarAt y - (g i).scalarAt x| *
          |((g i).scalarAt y - meanScalar (g i)) +
            ((g i).scalarAt x - meanScalar (g i))|
        ≤ (G * closedRiemannianDistance (g i) y x) * (2 * C) :=
      mul_le_mul hScalarDifference hSum (abs_nonneg _) hScalarRhsNonneg
    _ = (2 * C * G) * closedRiemannianDistance (g i) y x := by ring

/-- Intrinsic uniform `|dR| ≤ G` control and a centered-scalar bound
derive the exact scalar-variance Lipschitz contract used by concentration.

This premise is genuinely scalar.  The repository's existing bound on
`|∇ Ric°|` alone does not control the trace derivative `dR`. -/
theorem uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarMFDerivBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric n M)
    {C G : ℝ} (hC : 0 < C)
    (hCentered : ∀ i x,
      |(g i).scalarAt x - meanScalar (g i)| ≤ C)
    (hScalarGradient : UniformClosedRiemannianMFDerivBound g
      (fun i x ↦ (g i).scalarAt x) G) :
    UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ ((g i).scalarAt x - meanScalar (g i)) ^ 2)
      (2 * C * G) :=
  uniformClosedRiemannianLipschitzBound_centeredScalarSq_of_centeredBound_of_scalarLipschitz
    g hC hCentered
      (uniformClosedRiemannianLipschitzBound_of_mfderivBound g
        (fun i x ↦ (g i).scalarAt x) hScalarGradient)

end CenteredScalarSquareLipschitz

section TracelessRicciConcentration

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

/--
Path-integrated control of the spatial derivative of squared traceless Ricci
curvature is sufficient for the compactness-free `L¹`-to-`L∞` concentration
endpoint.
-/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_pathIntegralGradientBound
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L : ℝ}
    (hGradient : UniformClosedRiemannianPathIntegralGradientBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
    g hn
      (uniformClosedRiemannianLipschitzBound_of_pathIntegralGradientBound
        g (fun i x ↦ (g i).tracelessRicciNormSqAt x) hGradient)
      hNoncollapse hEnergyZero

/-- Pointwise intrinsic first-derivative form of the compactness-free
traceless-Ricci concentration endpoint. -/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_mfderivBound
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L : ℝ}
    (hGradient : UniformClosedRiemannianMFDerivBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero
    g hn
      (uniformClosedRiemannianLipschitzBound_of_mfderivBound
        g (fun i x ↦ (g i).tracelessRicciNormSqAt x) hGradient)
      hNoncollapse hEnergyZero

/-- Cubic-noncollapse form of the path-integral concentration endpoint. -/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_pathIntegralGradientBound_of_cubicNoncollapse
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L kappa r0 : ℝ}
    (hGradient : UniformClosedRiemannianPathIntegralGradientBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianCubicNoncollapse g kappa r0)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_cubicNoncollapse
    g hn
      (uniformClosedRiemannianLipschitzBound_of_pathIntegralGradientBound
        g (fun i x ↦ (g i).tracelessRicciNormSqAt x) hGradient)
      hNoncollapse hEnergyZero

/-- Cubic-noncollapse form with a pointwise intrinsic first-derivative bound. -/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_mfderivBound_of_cubicNoncollapse
    (g : ℕ → ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    {L kappa r0 : ℝ}
    (hGradient : UniformClosedRiemannianMFDerivBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) L)
    (hNoncollapse : UniformClosedRiemannianCubicNoncollapse g kappa r0)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_cubicNoncollapse
    g hn
      (uniformClosedRiemannianLipschitzBound_of_mfderivBound
        g (fun i x ↦ (g i).tracelessRicciNormSqAt x) hGradient)
      hNoncollapse hEnergyZero

end TracelessRicciConcentration

section NormalizedFlowConcentration

variable {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Finite absolute normalized-flow dissipation plus an intrinsic uniform spatial
first-derivative bound produces an escaping sequence with uniformly vanishing
squared traceless Ricci curvature.
-/
theorem exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_mfderivBound
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L : ℝ}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse : UniformClosedRiemannianBallVolumeLower gt) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ i in atTop, ∀ x : M,
          (gt (sample i)).tracelessRicciNormSqAt x < epsilon) :=
  exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation
      (uniformClosedRiemannianLipschitzBound_of_mfderivBound gt
        (fun t x ↦ (gt t).tracelessRicciNormSqAt x) hUniformGradient)
      hUniformNoncollapse

/-- Cubic-noncollapse form of the intrinsic first-derivative normalized-flow
concentration endpoint. -/
theorem exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_mfderivBound_of_cubicNoncollapse
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {L kappa r0 : ℝ}
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hUniformGradient : UniformClosedRiemannianMFDerivBound gt
      (fun t x ↦ (gt t).tracelessRicciNormSqAt x) L)
    (hUniformNoncollapse :
      UniformClosedRiemannianCubicNoncollapse gt kappa r0) :
    ∃ sample : ℕ → ℝ,
      Tendsto sample atTop atTop ∧
      Tendsto
        (fun i ↦ ∫ x, (gt (sample i)).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample i)))) atTop (nhds 0) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ i in atTop, ∀ x : M,
          (gt (sample i)).tracelessRicciNormSqAt x < epsilon) :=
  exists_normalizedFlow_tracelessRicciNormSqAt_eventually_uniformly_small_of_finiteAbsoluteDissipation_of_cubicNoncollapse
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation
      (uniformClosedRiemannianLipschitzBound_of_mfderivBound gt
        (fun t x ↦ (gt t).tracelessRicciNormSqAt x) hUniformGradient)
      hUniformNoncollapse

end NormalizedFlowConcentration

end Poincare
