import Poincare.Global.AntilipschitzMathlib
import Poincare.Global.NormalizedFlowVolumeVariation

/-!
# Full support of the Riemannian Hausdorff volume

The repository defines Riemannian volume as the Hausdorff measure of the
metric induced by a closed smooth Riemannian metric.  The existing local
anti-Lipschitz chart theorem proves nonzero total volume.  Here the same
argument is localized inside an arbitrary nonempty open set, giving the
`IsOpenPosMeasure` instance needed to turn vanishing curvature energies into
pointwise identities.
-/

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal MeasureTheory

namespace Poincare

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- Every nonempty open set has nonzero Riemannian Hausdorff volume. -/
theorem volumeMeasure_ne_zero_of_isOpen_nonempty
    (g : ClosedSmoothRiemannianMetric n M)
    {U : Set M} (hU : IsOpen U) (hUne : U.Nonempty) :
    volumeMeasure g U ≠ 0 := by
  letI : MetricSpace M := g.toMetricSpace
  rcases hUne with ⟨x, hxU⟩
  rcases GeodesicTransport.exists_extChartAt_symm_antilipschitz_ball
      (g := g) x with
    ⟨r₀, hr₀, K, hAnti₀⟩
  have hpre :
      (extChartAt I x).symm ⁻¹' U ∈ 𝓝 ((extChartAt I x) x) :=
    extChartAt_preimage_mem_nhds (hU.mem_nhds hxU)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨rU, hrU, hrUsub⟩
  let r : ℝ := min r₀ rU
  have hr : 0 < r := lt_min hr₀ hrU
  let c : E := (extChartAt I x) x
  let s₀ : Set E := Metric.ball c r₀
  let s : Set E := Metric.ball c r
  have hs_sub : s ⊆ s₀ := by
    exact Metric.ball_subset_ball (min_le_left r₀ rU)
  let inclusion : s → s₀ := fun z ↦ ⟨z, hs_sub z.2⟩
  have hInclusion : AntilipschitzWith 1 inclusion := by
    apply AntilipschitzWith.of_le_mul_dist
    intro z w
    simp [inclusion, Subtype.dist_eq]
  let f₀ : s₀ → M := fun z ↦ (extChartAt I x).symm (z : E)
  let f : s → M := fun z ↦ (extChartAt I x).symm (z : E)
  have hAnti : AntilipschitzWith K f := by
    have hcomp := hAnti₀.comp hInclusion
    simpa [f, f₀, inclusion, Function.comp_def, s₀, c] using hcomp
  have hs_pos :
      0 < (μH[(n : ℝ)] : Measure E) s := by
    simpa [s] using closedSmoothModel_hausdorffMeasure_ball_pos c hr
  have hsub_image :
      ((fun z : s ↦ (z : E)) '' (Set.univ : Set s)) = s := by
    ext z
    constructor
    · rintro ⟨w, _hw, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, by simp, rfl⟩
  have hsub_measure :
      (μH[(n : ℝ)] : Measure E) s =
        (μH[(n : ℝ)] : Measure s) Set.univ := by
    simpa [hsub_image] using
      (isometry_subtype_coe.hausdorffMeasure_image
        (f := fun z : s ↦ (z : E))
        (d := (n : ℝ)) (Or.inl (by positivity)) (Set.univ : Set s))
  have hsub_pos :
      0 < (μH[(n : ℝ)] : Measure s) Set.univ := by
    simpa [hsub_measure] using hs_pos
  have hle :
      (μH[(n : ℝ)] : Measure s) Set.univ ≤
        (K : ℝ≥0∞) ^ (n : ℝ) *
          (volumeMeasure g) (f '' (Set.univ : Set s)) := by
    simpa [volumeMeasure] using
      hAnti.le_hausdorffMeasure_image (d := (n : ℝ))
        (by positivity) (Set.univ : Set s)
  have himage_ne :
      (volumeMeasure g) (f '' (Set.univ : Set s)) ≠ 0 := by
    intro himage
    have hzero :
        (μH[(n : ℝ)] : Measure s) Set.univ ≤ 0 := by
      calc
        (μH[(n : ℝ)] : Measure s) Set.univ ≤
            (K : ℝ≥0∞) ^ (n : ℝ) *
              (volumeMeasure g) (f '' (Set.univ : Set s)) := hle
        _ = 0 := by rw [himage, mul_zero]
    exact hsub_pos.not_ge hzero
  have himage_sub : f '' (Set.univ : Set s) ⊆ U := by
    rintro _y ⟨z, _hz, rfl⟩
    apply hrUsub
    exact Metric.ball_subset_ball (min_le_right r₀ rU) z.2
  intro hUzero
  exact himage_ne (measure_mono_null himage_sub hUzero)

/-- The Riemannian Hausdorff volume has full topological support. -/
instance volumeMeasure_isOpenPosMeasure
    (g : ClosedSmoothRiemannianMetric n M) :
    (volumeMeasure g).IsOpenPosMeasure where
  open_pos U hU hUne :=
    volumeMeasure_ne_zero_of_isOpen_nonempty g hU hUne

/-- For a continuous integrable nonnegative function, zero Riemannian-volume
integral is equivalent to pointwise vanishing. -/
theorem integral_volumeMeasure_eq_zero_iff_of_continuous_nonneg
    (g : ClosedSmoothRiemannianMetric n M)
    {f : M → ℝ} (hfcont : Continuous f)
    (hfint : Integrable f (volumeMeasure g))
    (hfnonneg : 0 ≤ f) :
    (∫ x, f x ∂(volumeMeasure g)) = 0 ↔ ∀ x, f x = 0 := by
  constructor
  · intro hzero x
    by_contra hx
    have hpos : 0 < ∫ y, f y ∂(volumeMeasure g) :=
      integral_pos_of_integrable_nonneg_nonzero
        hfcont hfint hfnonneg hx
    exact hpos.ne' hzero
  · intro hzero
    simp only [hzero, integral_zero]

/-- Vanishing total traceless-Ricci energy forces the Einstein identity at
every point, provided the smooth curvature energy is supplied in the standard
continuous/integrable form. -/
theorem integral_tracelessRicciNormSqAt_eq_zero_iff_forall_ricciEndoAt_eq
    (g : ClosedSmoothRiemannianMetric n M)
    (hn : 0 < (n : ℝ))
    (hcont : Continuous (fun x : M ↦ g.tracelessRicciNormSqAt x))
    (hint : Integrable (fun x : M ↦ g.tracelessRicciNormSqAt x)
      (volumeMeasure g)) :
    (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) = 0 ↔
      ∀ x : M, g.ricciEndoAt x =
        (g.scalarAt x / (n : ℝ)) • LinearMap.id := by
  rw [integral_volumeMeasure_eq_zero_iff_of_continuous_nonneg
    g hcont hint]
  · constructor
    · intro hzero x
      exact
        (g.tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id
          x hn).1 (hzero x)
    · intro hEin x
      exact
        (g.tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id
          x hn).2 (hEin x)
  · exact fun x ↦ g.tracelessRicciNormSqAt_nonneg x hn

/-- A positive mean scalar curvature is attained positively somewhere.  This
uses only nonzero finite Riemannian volume and the definition of the mean. -/
theorem exists_scalarAt_pos_of_meanScalar_pos
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M)
    (hmean : 0 < meanScalar g) :
    ∃ x : M, 0 < g.scalarAt x := by
  by_contra hpos
  push Not at hpos
  have htotal : totalScalar g ≤ 0 := by
    exact integral_nonpos hpos
  have hvolne : volumeMeasure g Set.univ ≠ 0 :=
    GeodesicTransport.volumeMeasure_univ_ne_zero_mathlib g
  letI : IsFiniteMeasure (volumeMeasure g) :=
    volumeMeasure_isFiniteMeasure g
  have hvoltop : volumeMeasure g Set.univ ≠ (⊤ : ℝ≥0∞) :=
    measure_ne_top (volumeMeasure g) Set.univ
  have hvolreal : 0 < (volumeMeasure g Set.univ).toReal :=
    ENNReal.toReal_pos hvolne hvoltop
  have hmean_nonpos : meanScalar g ≤ 0 := by
    unfold meanScalar
    exact div_nonpos_of_nonpos_of_nonneg htotal hvolreal.le
  exact (not_le_of_gt hmean) hmean_nonpos

section DimensionThree

variable {N : Type u}
variable [TopologicalSpace N] [T2Space N] [CompactSpace N] [ConnectedSpace N]
variable [MeasurableSpace N] [BorelSpace N]
variable [SecondCountableTopology N] [SimplyConnectedSpace N]
variable [ChartedSpace (ClosedSmoothModel 3) N]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ N]

/-- Zero traceless-Ricci energy and positive mean scalar curvature already
form the reduced Hamilton limit payload.  Thus an energy-decay compactness
argument may target one scalar integral instead of pointwise pinching. -/
theorem hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy
    [Nonempty N]
    (g : ClosedSmoothRiemannianMetric 3 N)
    (hcont : Continuous (fun x : N ↦ g.tracelessRicciNormSqAt x))
    (hint : Integrable (fun x : N ↦ g.tracelessRicciNormSqAt x)
      (volumeMeasure g))
    (henergy :
      (∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g)) = 0)
    (hmean : 0 < meanScalar g) :
    HamiltonConvergencePinchedLimit3Core N := by
  have hzero : ∀ x : N, g.tracelessRicciNormSqAt x = 0 :=
    (integral_volumeMeasure_eq_zero_iff_of_continuous_nonneg
      g hcont hint (fun x ↦
        g.tracelessRicciNormSqAt_nonneg x (by norm_num))).1 henergy
  exact ⟨g, hzero, exists_scalarAt_pos_of_meanScalar_pos g hmean⟩

end DimensionThree

end Poincare
