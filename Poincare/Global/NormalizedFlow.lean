import Poincare.Global.ScalarIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Normalized closed Ricci flow

This module adds the volume-normalized Ricci-flow right-hand side for closed
smooth Riemannian metrics.  The flow predicate keeps the same section-tested
shape as `IsClosedRicciFlowSolutionAt`, while the pointwise RHS is exposed as a
separate bilinear expression.
-/

noncomputable section

open Bundle FiberBundle MeasureTheory
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

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
local notation "TM" => (TangentSpace I : M → Type _)

/-- The pointwise right-hand side of the normalized closed Ricci flow. -/
def normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) : ℝ :=
  -2 * g.ricciAt x u w +
    (2 / (n : ℝ)) * meanScalar g * g.inner x u w

/-- The normalized Ricci-flow right-hand side is symmetric. -/
theorem normalizedRicciFlowRHSAt_symm
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) :
    normalizedRicciFlowRHSAt g x u w =
      normalizedRicciFlowRHSAt g x w u := by
  unfold normalizedRicciFlowRHSAt
  rw [g.ricciAt_symm x u w, g.inner_symm x u w]

/--
Pointwise comparison with the unnormalized Ricci-flow right-hand side.
The normalized equation differs by the mean-scalar multiple of the metric.
-/
theorem normalizedRicciFlowRHSAt_sub_neg_two_ricciAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TM x) :
    normalizedRicciFlowRHSAt g x u w - (-2 * g.ricciAt x u w) =
      (2 / (n : ℝ)) * meanScalar g * g.inner x u w := by
  unfold normalizedRicciFlowRHSAt
  ring

/--
For a `C²` test field, the section-tested normalized RHS agrees with the
pointwise bilinear RHS at the field value.
-/
theorem normalizedRicciFlow_traceRHS_eq_normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    {Z : ∀ y : M, TM y} (hZ : ClosedC2TangentField (n := n) (M := M) Z)
    (hreg : CovariantDerivative.DerivRegularAt g.leviCivita Z x)
    (w : TM x) :
    -2 * CovariantDerivative.ricciTraceAt g.leviCivita hreg w +
        (2 / (n : ℝ)) * meanScalar g * g.inner x (Z x) w =
      normalizedRicciFlowRHSAt g x (Z x) w := by
  have htrace₀ :=
    CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
      (cov := g.leviCivita) (Z := Z) (x := x) (hZ x) hreg w
  have htrace :
      CovariantDerivative.ricciTraceAt g.leviCivita hreg w =
        g.ricciAt x (Z x) w := by
    calc
      CovariantDerivative.ricciTraceAt g.leviCivita hreg w =
          g.ricciAt x w (Z x) := by
            simpa [ClosedSmoothRiemannianMetric.ricciAt] using htrace₀
      _ = g.ricciAt x (Z x) w := g.ricciAt_symm x w (Z x)
  simp [normalizedRicciFlowRHSAt, htrace]

/--
The pointwise normalized Ricci-flow solution condition for a time-family of
closed smooth Riemannian metrics.  This mirrors the section-tested shape of
`IsClosedRicciFlowSolutionAt`, with the additional mean-scalar metric term.
-/
structure IsClosedNormalizedRicciFlowSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop where
  leviCivita : ∀ t : ℝ,
    CovariantDerivative.IsLeviCivitaAt
      (fun y ↦ (gt t).inner y) (gt t).leviCivita x
  flow : ∀ {Z : ∀ y : M, TM y}, ClosedC2TangentField (n := n) (M := M) Z →
    ∀ (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
      (w : TM x),
      deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
        -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
          (2 / (n : ℝ)) * meanScalar (gt t₀) *
            (gt t₀).inner x (Z x) w

/-- Expose the normalized-flow equation through `timeDerivAt`. -/
theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    {Z : ∀ y : M, TM y} (hZ : ClosedC2TangentField (n := n) (M := M) Z)
    (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
    (w : TM x) :
    timeDerivAt gt t₀ x (Z x) w =
      -2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w +
        (2 / (n : ℝ)) * meanScalar (gt t₀) *
          (gt t₀).inner x (Z x) w := by
  simpa [timeDerivAt] using hflow.flow hZ hreg w

/--
Section-tested comparison with the unnormalized Ricci-flow equation.  The
difference is exactly the mean-scalar metric multiple.
-/
theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_sub_ricciFlowRHS
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    {Z : ∀ y : M, TM y} (hZ : ClosedC2TangentField (n := n) (M := M) Z)
    (hreg : CovariantDerivative.DerivRegularAt (gt t₀).leviCivita Z x)
    (w : TM x) :
    timeDerivAt gt t₀ x (Z x) w -
        (-2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w) =
      (2 / (n : ℝ)) * meanScalar (gt t₀) *
        (gt t₀).inner x (Z x) w := by
  rw [isClosedNormalizedRicciFlowSolutionAt_timeDerivAt
    (gt := gt) (t₀ := t₀) (x := x) hflow hZ hreg w]
  ring

/-- If the mean scalar term vanishes, the normalized clause reduces to Ricci flow. -/
theorem isClosedRicciFlowSolutionAt_of_isClosedNormalizedRicciFlowSolutionAt_of_meanScalar_eq_zero
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
    (hmean : meanScalar (gt t₀) = 0) :
    IsClosedRicciFlowSolutionAt gt t₀ x := by
  refine ⟨hflow.leviCivita, ?_⟩
  intro Z hZ hreg w
  simpa [hmean] using hflow.flow hZ hreg w

/--
The concrete local lower-bound statement still missing from the volume
positivity route: in a chart around each point, the inverse chart has an
anti-Lipschitz lower comparison to the Riemannian path metric on some
positive Euclidean ball scale.
-/
def LocalChartAntilipschitzLowerBound
    (g : ClosedSmoothRiemannianMetric n M) : Prop :=
  ∀ x : M, ∃ r : ℝ, 0 < r ∧
    ∃ K : ℝ≥0,
      letI : MetricSpace M := g.toMetricSpace
      AntilipschitzWith K
        (fun y :
            {y : ClosedSmoothModel n //
              y ∈ Metric.ball
                ((extChartAt (closedSmoothModelWithCorners n) x) x) r} =>
          (extChartAt (closedSmoothModelWithCorners n) x).symm
            (y : ClosedSmoothModel n))

/-- Euclidean model balls have positive `n`-dimensional Hausdorff measure. -/
theorem closedSmoothModel_hausdorffMeasure_ball_pos
    (x : ClosedSmoothModel n) {r : ℝ} (hr : 0 < r) :
    0 < (μH[(n : ℝ)] : MeasureTheory.Measure (ClosedSmoothModel n))
      (Metric.ball x r) := by
  have hdim :
      (Module.finrank ℝ (ClosedSmoothModel n) : ℝ) = n := by
    simp [ClosedSmoothModel, finrank_euclideanSpace]
  simpa [hdim] using
    (Metric.isOpen_ball.measure_pos
      (μ := (μH[(Module.finrank ℝ (ClosedSmoothModel n) : ℝ)] :
        MeasureTheory.Measure (ClosedSmoothModel n)))
      (Metric.nonempty_ball.2 hr))

/--
Volume positivity from the isolated local anti-Lipschitz chart lower bound.
This is the strict partial downstream of the missing geometric comparison.
-/
theorem volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M)
    (hlower : LocalChartAntilipschitzLowerBound (n := n) (M := M) g) :
    volumeMeasure g Set.univ ≠ 0 := by
  letI : MetricSpace M := g.toMetricSpace
  obtain ⟨x⟩ : Nonempty M := inferInstance
  rcases hlower x with ⟨r, hr, K, hAnti⟩
  let c : ClosedSmoothModel n := (extChartAt (closedSmoothModelWithCorners n) x) x
  let s : Set (ClosedSmoothModel n) := Metric.ball c r
  have hs_pos : 0 < (μH[(n : ℝ)] : MeasureTheory.Measure (ClosedSmoothModel n)) s :=
    closedSmoothModel_hausdorffMeasure_ball_pos c hr
  have hsub_image :
      ((fun y : s => (y : ClosedSmoothModel n)) '' (Set.univ : Set s)) = s := by
    ext y
    constructor
    · rintro ⟨z, _hz, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, by simp, rfl⟩
  have hsub_measure :
      (μH[(n : ℝ)] : MeasureTheory.Measure (ClosedSmoothModel n)) s =
        (μH[(n : ℝ)] : MeasureTheory.Measure s) Set.univ := by
    simpa [hsub_image] using
      (isometry_subtype_coe.hausdorffMeasure_image
        (f := fun y : s => (y : ClosedSmoothModel n))
        (d := (n : ℝ)) (Or.inl (by positivity)) (Set.univ : Set s))
  have hsub_pos : 0 < (μH[(n : ℝ)] : MeasureTheory.Measure s) Set.univ := by
    simpa [hsub_measure] using hs_pos
  let f : s → M := fun y =>
    (extChartAt (closedSmoothModelWithCorners n) x).symm
      (y : ClosedSmoothModel n)
  have hle :
      (μH[(n : ℝ)] : MeasureTheory.Measure s) Set.univ ≤
        (K : ℝ≥0∞) ^ (n : ℝ) *
          (volumeMeasure g) (f '' (Set.univ : Set s)) := by
    simpa [volumeMeasure] using
      hAnti.le_hausdorffMeasure_image (d := (n : ℝ)) (by positivity)
        (Set.univ : Set s)
  have himage_ne_zero :
      (volumeMeasure g) (f '' (Set.univ : Set s)) ≠ 0 := by
    intro hzero
    have hle_zero :
        (μH[(n : ℝ)] : MeasureTheory.Measure s) Set.univ ≤
          (K : ℝ≥0∞) ^ (n : ℝ) * 0 := by
      rw [← hzero]
      exact hle
    have : (μH[(n : ℝ)] : MeasureTheory.Measure s) Set.univ ≤ 0 := by
      simpa using hle_zero
    exact hsub_pos.not_ge this
  exact fun huniv =>
    himage_ne_zero (measure_mono_null (Set.subset_univ _) huniv)

/--
An everywhere-Einstein closed metric is stationary for the normalized flow,
provided the dimension and total volume denominators are nonzero.
-/
theorem isClosedNormalizedRicciFlowSolutionAt_const_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hn : (n : ℝ) ≠ 0)
    (hEin : ∀ y : M, g.IsEinsteinAt lam y)
    (hvol : volumeMeasure g Set.univ ≠ 0)
    (t₀ : ℝ) (x : M) :
    IsClosedNormalizedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ x := by
  refine ⟨?_, ?_⟩
  · intro _t
    exact ⟨g.leviCivita_metricCompatibleAt x, g.leviCivita_torsionFreeAt x⟩
  · intro Z hZ hreg w
    have htrace₀ :=
      CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
        (cov := g.leviCivita) (Z := Z) (x := x) (hZ x) hreg w
    have htrace :
        CovariantDerivative.ricciTraceAt g.leviCivita hreg w =
          g.ricciAt x (Z x) w := by
      calc
        CovariantDerivative.ricciTraceAt g.leviCivita hreg w =
            g.ricciAt x w (Z x) := by
              simpa [ClosedSmoothRiemannianMetric.ricciAt] using htrace₀
        _ = g.ricciAt x (Z x) w := g.ricciAt_symm x w (Z x)
    have hRic : g.ricciAt x (Z x) w = lam * g.inner x (Z x) w :=
      (g.isEinsteinAt_iff lam x).1 (hEin x) (Z x) w
    have hmean : meanScalar g = n * lam :=
      meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero (g := g) hEin hvol
    rw [deriv_const, htrace, hRic, hmean]
    have hcoef :
        -2 * lam + (2 / (n : ℝ)) * (n * lam) = 0 := by
      field_simp [hn]
      ring
    calc
      0 = (-2 * lam + (2 / (n : ℝ)) * (n * lam)) *
          g.inner x (Z x) w := by rw [hcoef, zero_mul]
      _ = -2 * (lam * g.inner x (Z x) w) +
          (2 / (n : ℝ)) * (n * lam) * g.inner x (Z x) w := by
            ring

end Poincare
