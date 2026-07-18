import Poincare.Global.HausdorffInverseChartGlobalEpsilonSqueeze
import Poincare.Global.HausdorffMeasureScalarLimitSqueeze

/-!
# The inverse-chart Hausdorff area formula

The fixed-epsilon comparison on the whole inverse-chart target has four
scalar coefficients.  Along any positive sequence `ε → 0`, all four
coefficients converge to one.  Closedness of the order on `ℝ≥0∞` then
turns the two global inequalities into exact equality of measures, without
any local-finiteness assumption.
-/

noncomputable section

set_option maxHeartbeats 800000

open Bundle Filter MeasureTheory Metric Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal
  RealInnerProductSpace

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
variable [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n)
  ((⊤ : ℕ∞) : WithTop ℕ∞) M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- The Hausdorff measure of the Riemannian pullback metric on a genuine
inverse-chart target is exactly the raw Euclidean Hausdorff measure weighted
by `sqrt |det G|`. -/
theorem inverseChartPullbackHausdorffAreaFormula
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    InverseChartPullbackHausdorffAreaFormula g x₀ := by
  rw [InverseChartPullbackHausdorffAreaFormula,
    PullbackMetricHausdorffDensityFormula]
  let U : Set E := (extChartAt I x₀).target
  let ψ : U → M :=
    inverseExtendedChartParametrization (n := n) (M := M) x₀
  letI : MetricSpace M := g.toMetricSpace
  let hψ : Topology.IsEmbedding ψ :=
    inverseExtendedChartParametrization_isEmbedding
      (n := n) (M := M) x₀
  let pullbackMetric : MetricSpace U := hψ.comapMetricSpace ψ
  let pullbackEMetric : EMetricSpace U :=
    @MetricSpace.toEMetricSpace U pullbackMetric
  let μ : Measure U := rawHausdorffCoordinateDensityMeasure U
    (inverseChartPullbackVolumeDensity g x₀)
  let ν : Measure U := (μH[(n : ℝ)] : Measure U)
  letI : EMetricSpace U := pullbackEMetric
  letI : PseudoEMetricSpace U := pullbackEMetric.toPseudoEMetricSpace
  change ν = μ

  let ε : ℕ → ℝ := fun k ↦ 1 / (((k + 2 : ℕ) : ℝ))
  let C : ℕ → ℝ≥0 := fun k ↦
    ⟨Real.sqrt (1 - ε k), Real.sqrt_nonneg _⟩
  let K : ℕ → ℝ≥0 := fun k ↦ (C k)⁻¹
  let L : ℕ → ℝ≥0 := fun k ↦
    ⟨Real.sqrt (1 + ε k), Real.sqrt_nonneg _⟩
  let a : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal (1 - ε k)
  let b : ℕ → ℝ≥0∞ := fun k ↦
    (L k : ℝ≥0∞) ^ (n : ℝ)
  let c : ℕ → ℝ≥0∞ := fun _ ↦ 1
  let d : ℕ → ℝ≥0∞ := fun k ↦
    ENNReal.ofReal (1 + ε k) * (K k : ℝ≥0∞) ^ (n : ℝ)

  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp only [ε]
    positivity
  have hεlt (k : ℕ) : ε k < 1 := by
    dsimp only [ε]
    rw [div_lt_one (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))]
    exact_mod_cast (by omega : 1 < k + 2)
  have hε : Tendsto ε atTop (nhds 0) := by
    have h :=
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 2)
    simpa only [ε, Function.comp_apply] using h

  have hCReal :
      Tendsto (fun k ↦ Real.sqrt (1 - ε k)) atTop (nhds 1) := by
    simpa only [sub_zero, Real.sqrt_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).sqrt
  have hC : Tendsto C atTop (nhds 1) := by
    apply NNReal.tendsto_coe.mp
    simpa only [C, NNReal.coe_mk, NNReal.coe_one] using hCReal
  have hK : Tendsto K atTop (nhds 1) := by
    simpa only [K, inv_one] using hC.inv₀ one_ne_zero
  have hLENN : Tendsto (fun k ↦ (L k : ℝ≥0∞)) atTop (nhds 1) := by
    have hLReal :
        Tendsto (fun k ↦ Real.sqrt (1 + ε k)) atTop (nhds 1) := by
      simpa only [add_zero, Real.sqrt_one] using
        ((tendsto_const_nhds (x := (1 : ℝ))).add hε).sqrt
    have hL : Tendsto L atTop (nhds 1) := by
      apply NNReal.tendsto_coe.mp
      simpa only [L, NNReal.coe_mk, NNReal.coe_one] using hLReal
    simpa only [ENNReal.coe_one] using
      (ENNReal.continuous_coe.tendsto (1 : ℝ≥0)).comp hL
  have hKENN : Tendsto (fun k ↦ (K k : ℝ≥0∞)) atTop (nhds 1) := by
    simpa only [ENNReal.coe_one] using
      (ENNReal.continuous_coe.tendsto (1 : ℝ≥0)).comp hK

  have ha : Tendsto a atTop (nhds 1) := by
    simpa only [a, sub_zero, ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := (1 : ℝ))).sub hε)
  have hb : Tendsto b atTop (nhds 1) := by
    simpa only [b, ENNReal.one_rpow] using
      hLENN.ennrpow_const (n : ℝ)
  have hc : Tendsto c atTop (nhds 1) := by
    exact tendsto_const_nhds
  have hdLeft :
      Tendsto (fun k ↦ ENNReal.ofReal (1 + ε k)) atTop (nhds 1) := by
    simpa only [add_zero, ENNReal.ofReal_one] using
      ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := (1 : ℝ))).add hε)
  have hdRight :
      Tendsto (fun k ↦ (K k : ℝ≥0∞) ^ (n : ℝ)) atTop (nhds 1) := by
    simpa only [ENNReal.one_rpow] using
      hKENN.ennrpow_const (n : ℝ)
  have hd : Tendsto d atTop (nhds 1) := by
    simpa only [d, one_mul] using
      ENNReal.Tendsto.mul hdLeft (Or.inl one_ne_zero) hdRight
        (Or.inl one_ne_zero)

  apply measure_eq_of_two_sided_smul_squeeze_tendsto_one
      ν μ a b c d ha hb hc hd
  · intro k
    have hk := (inverseChart_global_measure_squeeze
      g x₀ (hεpos k) (hεlt k)).1
    simpa only [a, b, C, K, L, ε, μ, ν, U, ψ, hψ, pullbackMetric,
      pullbackEMetric] using hk
  · intro k
    have hk := (inverseChart_global_measure_squeeze
      g x₀ (hεpos k) (hεlt k)).2
    simpa only [c, d, C, K, L, ε, μ, ν, U, ψ, hψ, pullbackMetric,
      pullbackEMetric, one_smul] using hk

/-- The exact inverse-chart area formula supplies the unconditional local
Hausdorff chart-density equality for a fixed Riemannian metric. -/
theorem inverseChart_hausdorffChartDensityEquality
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    HausdorffChartDensityEquality g (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀))
      (inverseChartPullbackVolumeDensity g x₀) :=
  inverseChart_hausdorffChartDensityEquality_of_areaFormula
    g x₀ (inverseChartPullbackHausdorffAreaFormula g x₀)

/-- Along a metric path, the honest inverse-chart frame density gives an
unconditional Hausdorff chart-density equality at every time. -/
theorem inverseChart_hausdorffChartDensityEquality_chartFrame_auto
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x₀ : M) :
    HausdorffChartDensityEquality (gt t) (extChartAt I x₀).target
      (inverseExtendedChartParametrization (n := n) (M := M) x₀)
      (Set.range
        (inverseExtendedChartParametrization (n := n) (M := M) x₀))
      (fun z ↦ ClosedSmoothRiemannianMetric.inverseChartVolumeDensityAt
        gt x₀ z.2 t) :=
  inverseChart_hausdorffChartDensityEquality_chartFrame gt t x₀
    (inverseChartPullbackHausdorffAreaFormula (gt t) x₀)

end Poincare
