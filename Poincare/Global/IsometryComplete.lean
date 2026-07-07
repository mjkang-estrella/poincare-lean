import Poincare.Global.EnrichedCascade
import Poincare.Global.OneSidedPayload
import Poincare.Global.SolutionsFeed

/-!
# Enriched Cartan isometry assembly

This module instantiates the one-sided orthogonality and transverse-transverse
solution feeds from the enriched cascade packages.  The point is to consume the
same hosted `α` exported by `EnrichedCascade.BaseCurvePackage` and
`EnrichedCascade.LinearizedFamilyPackage`, so the old base-curve mismatch is no
longer an assembly boundary.
-/

noncomputable section

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace IsometryComplete

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/-- Local public version of the chart-geodesic metric differentiability fact. -/
theorem chartGeodesicMetric_differentiableAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (z : E3) :
    DifferentiableAt ℝ (chartGeodesicMetric g x₀) z := by
  have htwo_le_top : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) = ((2 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have htwo_add_one_le_top : (2 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    rw [show (2 : ℕ∞ω) + 1 = ((3 : ℕ∞) : ℕ∞ω) from rfl,
      show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  have hg2 :
      ContMDiff I3 ((I3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) 2
        (fun y : M =>
          (⟨y, g.inner y⟩ :
            TotalSpace (E3 →L[ℝ] E3 →L[ℝ] ℝ)
              (fun y : M =>
                TangentSpace I3 y →L[ℝ] TangentSpace I3 y →L[ℝ] ℝ))) := by
    simpa using g.contMDiff_inner.of_le htwo_le_top
  have hcont : ContDiff ℝ 2 (chartGeodesicMetric g x₀) := by
    simpa [chartGeodesicMetric] using
      (CovariantDerivative.contDiff_blendedChartMetric
        (cutoff (n := 3) x₀) (backgroundMetric (n := 3)) g.inner x₀
        htwo_add_one_le_top (cutoff_contDiff (n := 3) x₀)
        (cutoff_tsupport (n := 3) x₀) hg2)
  exact (hcont.differentiable (by norm_num)).differentiableAt

omit [T2Space M] in
/--
The enriched source packages supply the one-sided endpoint orthogonality input
for every source-anchor-orthogonal linearized direction.
-/
theorem source_orthogonal_of_enriched_packages
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} {aPkg : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ) :
    ∀ w : E3,
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        ∀ τ ∈ Icc (0 : ℝ) T,
          CovariantDerivative.chartMetric g.inner x₀
            (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1
            (Ψ w τ).1
            (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 = 0 := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  rcases hbase with
    ⟨hα0, _hbaseFull, hbase0T, _hbaseAt, _hmem, _htargetFull,
      _htarget0T, _hcutFull, hχ0T, _hspeedBase, _hendpoint⟩
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hlin with ⟨hΨ0, _hΨFull, hΨ0T, _hΨAt, hflow, hspeedConst⟩
  intro w hw
  have hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀)
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1 := by
    intro τ _hτ
    exact chartGeodesicMetric_differentiableAt g x₀
      (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1
  have hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric g x₀) (extChartAt I3 x₀ x₀) :=
    chartGeodesicMetric_differentiableAt g x₀ (extChartAt I3 x₀ x₀)
  have horthScaled :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • w) = 0 := by
    simp [hw]
  have hcut0T : ∀ τ ∈ Icc (0 : ℝ) T,
      cutoff (n := 3) x₀ (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1 = 1 := by
    intro τ hτ
    exact (hχ0T τ hτ).self_of_nhds
  exact
    OrthogonalityFeed.source_transverse_horth_on_Icc_of_oneSided_payload
      (g := g) (x₀ := x₀) (α := α)
      (v := T⁻¹ • v) (w := T⁻¹ • w) (Ψ := Ψ w)
      (T := T) hT hbase0T (hΨ0T w) (hflow w)
      (hspeedConst w) hGd_base hGd_initial hα0 (hΨ0 w)
      horthScaled hcut0T

/--
The enriched target packages supply the one-sided endpoint orthogonality input
for every target-anchor-orthogonal linearized direction.
-/
theorem target_orthogonal_of_enriched_packages
    (p₀ : RoundSphere3)
    {T ε : ℝ} {aPkg : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase :
      EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T ε aPkg α v)
    (hlin :
      EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T ε α v Ψ) :
    ∀ w : E3,
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        ∀ τ ∈ Icc (0 : ℝ) T,
          CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
            (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1
            (Ψ w τ).1
            (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).2 = 0 := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  rcases hbase with
    ⟨hα0, _hbaseFull, hbase0T, _hbaseAt, _hmem, _htargetFull,
      _htarget0T, _hcutFull, hχ0T, _hspeedBase, _hendpoint⟩
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hlin with ⟨hΨ0, _hΨFull, hΨ0T, _hΨAt, hflow, hspeedConst⟩
  intro w hw
  have hGd_base : ∀ τ ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1 := by
    intro τ _hτ
    exact chartGeodesicMetric_differentiableAt roundSphereMetric3 p₀
      (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1
  have hGd_initial :
      DifferentiableAt ℝ (chartGeodesicMetric roundSphereMetric3 p₀)
        (extChartAt I3 p₀ p₀) :=
    chartGeodesicMetric_differentiableAt roundSphereMetric3 p₀
      (extChartAt I3 p₀ p₀)
  have horthScaled :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • w) = 0 := by
    simp [hw]
  have hcut0T : ∀ τ ∈ Icc (0 : ℝ) T,
      cutoff (n := 3) p₀ (α (extChartAt I3 p₀ p₀, T⁻¹ • v) τ).1 = 1 := by
    intro τ hτ
    exact (hχ0T τ hτ).self_of_nhds
  exact
    OrthogonalityFeed.target_transverse_horth_on_Icc_of_oneSided_payload
      (p₀ := p₀) (α := α)
      (v := T⁻¹ • v) (w := T⁻¹ • w) (Ψ := Ψ w)
      (T := T) hT hbase0T (hΨ0T w) (hflow w)
      (hspeedConst w) hGd_base hGd_initial hα0 (hΨ0 w)
      horthScaled hcut0T

/--
Source transverse-transverse endpoint block from the enriched same-`α` packages,
assuming only the remaining norm-system PL and closed-ball facts required by
`SolutionsFeed`.
-/
theorem source_transverseTransverse_of_enriched_solutions_feed
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hplNorm : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      IsPicardLindelof
        (fun _ : ℝ => fun x : Triple => Aop x)
        (tmin := 0) (tmax := T)
        ⟨(0 : ℝ), by exact ⟨le_rfl, le_of_lt hT⟩⟩
        ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hmemNorm : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      (JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) s,
        JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) s,
        JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) s) ∈
        closedBall ((0 : ℝ), (0 : ℝ),
          chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) radius)
    (hpinnedmem : ∀ w : E3, ∀ s ∈ Icc (0 : ℝ) T,
      (JacobiNormSystem.speedPinnedA speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedB speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s,
        JacobiNormSystem.speedPinnedC speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) s) ∈
          closedBall ((0 : ℝ), (0 : ℝ),
            chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
              (T⁻¹ • w) (T⁻¹ • w)) radius)
    (ha0 : ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0)
    (hb0 : ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0)
    (hc0 : ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a)
          (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
  have horth :=
    source_orthogonal_of_enriched_packages
      (g := g) (x₀ := x₀) (T := T) (ε := ε) (aPkg := aPkg)
      (α := α) (Ψ := Ψ) (v := v) hT hbase hlin
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  rcases hbase with
    ⟨_hα0, _hbaseFull, _hbase0T, hbaseAt, _hmem, _htargetFull,
      htarget0T, _hcutFull, hχ0T, hspeedBase, hendpoint⟩
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hlin with ⟨_hΨ0, _hΨFull, _hΨ0T, hΨAt, _hflow, _hspeedConst⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_of_lt hT⟩
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨le_of_lt hT, le_rfl⟩
  have hspeed : ∀ s ∈ Icc (0 : ℝ) T,
      CovariantDerivative.chartMetric g.inner x₀
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).2
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).2 = speed ^ 2 := by
    intro s hs
    exact (hspeedBase s hs).trans hanchorSpeed
  have hGd : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentiableAt ℝ (chartGeodesicMetric g x₀)
        (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1 := by
    intro s _hs
    exact chartGeodesicMetric_differentiableAt g x₀
      (α (extChartAt I3 x₀ x₀, T⁻¹ • v) s).1
  exact
    SolutionsFeed.source_transverseTransverse_of_solutions_feed
      (g := g) hcurv (x₀ := x₀)
      (γ := α (extChartAt I3 x₀ x₀, T⁻¹ • v)) (Ψ := Ψ)
      (v := v) (T := T) (tmin := 0) (tmax := T) (speed := speed)
      hspeed_ne hzero hΨadd hΨsmul hTmem hendpoint Aop hRpos hplNorm
      hAop hbaseAt hΨAt htarget0T hχ0T hspeed horth hGd hmemNorm
      hpinnedmem ha0 hb0 hc0

end IsometryComplete
end Poincare
