import Poincare.Global.MetricAdaptedBufferedAtlas
import Poincare.Global.MetricInverseCoefficientRegularity
import Poincare.Global.FiniteLocalSolverBounds

/-!
# Local parametrices constructed from the actual metric

The local solver chooses its tolerances before the atlas and buffers are
constructed. Its actual operators then share finite bounds and a positive
interval. The residual identity and estimates retain the forcing support
condition needed by subsequent global tensor operator assembly.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.MetricAdaptedLocalParametrix
/-- Construct genuine chart-local solvers and a common positive interval from the actual metric. -/
theorem exists_metric_adapted_local_parametrix :
∀ {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M], ∀ [IsManifold (modelWithCornersSelf ℝ (Poincare.ClosedSmoothModel 3)) ((⊤ : ENat) : WithTop ENat) M], ∀ (g0 : Poincare.ClosedSmoothRiemannianMetric 3 M) (α : ℝ), 0 < α → α < 1 →
 ∃ A : Poincare.FiniteAtlasParabolicTensorSpace.AtlasData M,
 ∃ ψ ξ : Fin A.cover.chartCount → (Poincare.ClosedSmoothModel 3) → ℝ,
 (∀ i, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (ψ i) ∧ HasCompactSupport (ψ i) ∧
   (∀ z ∈ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i, Filter.Eventually (fun y ↦ ψ i y = 1) (nhds z)) ∧
   (∀ z, ψ i z ∈ Set.Icc 0 1) ∧
   ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (ξ i) ∧ HasCompactSupport (ξ i) ∧
   (∀ z, ξ i z ∈ Set.Icc 0 1) ∧ (∀ z ∈ tsupport (ψ i), ξ i z = 1) ∧
   tsupport (ξ i) ⊆ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i).target ∧
   (∀ z ∈ tsupport (ξ i), Filter.Eventually (fun y ↦ Poincare.GeodesicTransport.cutoff (n := 3) (A.cover.anchor i) y = 1) (nhds z))) ∧
 ∃ Cψ CP τ : ℝ, 0 ≤ Cψ ∧ 0 ≤ CP ∧ 0 < τ ∧ τ ≤ 1 ∧
 ∀ T ∈ Set.Ioc 0 τ,
   ∃ P : Fin A.cover.chartCount → (Poincare.ParabolicHolder.Y (E := (Poincare.ClosedSmoothModel 3)) α T ℝ) →L[ℝ] (Poincare.ParabolicSolutionGraph.Graph (E := (Poincare.ClosedSmoothModel 3)) α T),
   ∃ R : Fin A.cover.chartCount → (Poincare.ParabolicHolder.Y (E := (Poincare.ClosedSmoothModel 3)) α T ℝ) →L[ℝ] (Poincare.ParabolicHolder.Y (E := (Poincare.ClosedSmoothModel 3)) α T ℝ),
   ∀ i, (∀ f p, p.2 ∉ tsupport (ψ i) → (P i f).u p = 0) ∧
     ∀ f : (Poincare.ParabolicHolder.Y (E := (Poincare.ClosedSmoothModel 3)) α T ℝ), (∀ p, p.2 ∉ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i → f p = 0) →
       (∀ p, R i f p = Poincare.BufferedFrozenParabolicSolver.chartValue
         (fun z ↦ @Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv
           (Poincare.inverseChartPullbackGramMatrixField g0 (A.cover.anchor i) z))
         (P i f) p - f p) ∧
       ‖R i f‖ ≤ Cψ * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ ∧
       ‖P i f‖ ≤ CP * ‖f‖ := by
  intro M _ _ _ _ _ g0 α hα hα1
  classical
  have hsolver (p : M) :=
    BufferedFrozenParabolicSolver.exists_single_chart_parametrix hα hα1
      (isOpen_extChartAt_target p)
      (fun z => (inverseChartPullbackGramMatrixField g0 p z)⁻¹)
      (extChartAt (closedSmoothModelWithCorners 3) p p)
      (MetricInverseCoefficientRegularity.inverse_metric_entry_contDiffOn g0 p)
      (MetricInverseCoefficientRegularity.inverse_metric_field_posDef g0 p _
        (mem_extChartAt_target p))
  choose ε hε hsolve using hsolver
  obtain ⟨A, ψ, ξ, hbuffer⟩ :=
    MetricAdaptedBufferedAtlas.exists_metric_adapted_buffered_atlas g0 ε hε
  have hlocal (i : Fin A.cover.chartCount) := by
    rcases hbuffer i with
      ⟨hψ, hψc, hψone, _hψrange, hξ, hξc, hξrange, hξψ, hξU, _hcut, hosc⟩
    exact hsolve (A.cover.anchor i)
      (FiniteAtlasParabolicTensorSpace.coordSupport A i) (ψ i) (ξ i)
      hψ hψc hξ hξc hξU hξrange hξψ
      (fun z hz => Filter.EventuallyEq.eq_of_nhds (hψone z hz)) hosc
  choose C D τ hC hD hτ hoperators using hlocal
  obtain ⟨C₀, D₀, δ, hC₀, hD₀, hδ, hδ1, hcommon⟩ :=
    FiniteLocalSolverBounds.exists_common_bounds_and_lifespan A.cover.chartCount C D τ hC hD hτ
  refine ⟨A, ψ, ξ, ?_, C₀, D₀, δ, hC₀, hD₀, hδ, hδ1, ?_⟩
  · intro i
    rcases hbuffer i with
      ⟨hψ, hψc, hψone, hψrange, hξ, hξc, hξrange, hξψ, hξU, hcut, _hosc⟩
    exact ⟨hψ, hψc, hψone, hψrange, hξ, hξc, hξrange, hξψ, hξU, hcut⟩
  · intro T hT
    have hiT (i : Fin A.cover.chartCount) : T ∈ Ioc 0 (τ i) :=
      ⟨hT.1, hT.2.trans (hcommon i).2.2⟩
    choose P R hsupport hest using fun i => hoperators i T (hiT i)
    refine ⟨P, R, ?_⟩
    intro i
    refine ⟨hsupport i, ?_⟩
    intro f hf
    obtain ⟨hidentity, hR, hP⟩ := hest i f hf
    refine ⟨hidentity, hR.trans ?_, hP.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcommon i).1
          (add_nonneg (Real.rpow_nonneg hT.1.le _) (Real.rpow_nonneg hT.1.le _)))
        (norm_nonneg f)
    · exact mul_le_mul_of_nonneg_right (hcommon i).2.1 (norm_nonneg f)

end Poincare.MetricAdaptedLocalParametrix
