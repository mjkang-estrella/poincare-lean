import Poincare.Global.GlobalParametrixAssemblyRange
import Poincare.Global.GlobalParametrixAssemblyBound
import Poincare.Global.MetricAdaptedLocalParametrix
import Poincare.Global.BufferedChartTransitionExtensions
import Poincare.Global.BufferedTensorGraphTransportOperator

/-!
Construct the global parametrix from actual metric-adapted local solvers and
buffered tensor transport. Its next consumer is the full DeTurck L/P/R
identity on the Hamilton existence route.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Manifold ContDiff Topology

universe u
namespace Poincare.MetricAdaptedGlobalParametrix
open FiniteAtlasParabolicTensorSpace GlobalParametrixAssembly

/-- Construct the actual globally compatible bounded solver from the metric. -/
theorem exists_metric_adapted_global_parametrix :
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
 ∃ θ : Fin A.cover.chartCount → Fin A.cover.chartCount → Poincare.ClosedSmoothModel 3 → ℝ,
 ∃ F : Fin A.cover.chartCount → Fin A.cover.chartCount → Poincare.ClosedSmoothModel 3 → Poincare.ClosedSmoothModel 3,
 (∀ i j,
 ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (θ i j) ∧ HasCompactSupport (θ i j) ∧
 (∀ z, θ i j z ∈ Set.Icc 0 1) ∧
 tsupport (θ i j) ⊆ ((Poincare.FiniteAtlasParabolicTensorSpace.chart A i).symm.trans (Poincare.FiniteAtlasParabolicTensorSpace.chart A j)).source ∧
 (∀ z ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i) '' (tsupport (A.partition i) ∩ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j).symm '' tsupport (ξ j)),
  Filter.Eventually (fun y => θ i j y = 1) (nhds z)) ∧
 ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (F i j) ∧ HasCompactSupport (F i j) ∧
 (∀ z ∈ tsupport (θ i j), Filter.Eventually (fun y => F i j y = Poincare.FiniteAtlasParabolicTensorSpace.change A i j y) (nhds z)) ∧
 ∃ L : NNReal, LipschitzWith L (F i j)) ∧
 ∃ Cψ CP Cglobal τ : ℝ,
 ∃ CB : Fin A.cover.chartCount → Fin A.cover.chartCount → Fin 3 → Fin 3 → ℝ,
 0 ≤ Cψ ∧ 0 ≤ CP ∧ 0 < τ ∧ τ ≤ 1 ∧ (∀ i j c d, 0 ≤ CB i j c d) ∧
 Cglobal = CP * (∑ i : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
   ∑ c : Fin 3, ∑ d : Fin 3, CB i j c d) ∧
 ∀ T ∈ Set.Ioc 0 τ,
 ∃ S : Fin A.cover.chartCount → (Poincare.FiniteAtlasParabolicTensorSpace.Scalar α T) →L[ℝ] (Poincare.FiniteAtlasParabolicTensorSpace.Jet α T),
 ∃ R : Fin A.cover.chartCount → (Poincare.FiniteAtlasParabolicTensorSpace.Scalar α T) →L[ℝ] (Poincare.FiniteAtlasParabolicTensorSpace.Scalar α T),
 ∃ B : Poincare.GlobalParametrixAssembly.Transports A α T,
 ∃ Pglobal : (Poincare.FiniteAtlasParabolicTensorSpace.Y_M A α T) →L[ℝ] (Poincare.FiniteAtlasParabolicTensorSpace.X_M A α T),
 (∀ i, (∀ f p, p.2 ∉ tsupport (ψ i) → (S i f).u p = 0) ∧
     ∀ f : (Poincare.ParabolicHolder.Y (E := (Poincare.ClosedSmoothModel 3)) α T ℝ), (∀ p, p.2 ∉ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i → f p = 0) →
       (∀ p, R i f p = Poincare.BufferedFrozenParabolicSolver.chartValue
         (fun z ↦ @Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv
           (Poincare.inverseChartPullbackGramMatrixField g0 (A.cover.anchor i) z))
         (S i f) p - f p) ∧
       ‖R i f‖ ≤ Cψ * (T ^ ((1-α)/2) + T ^ (1-α/2)) * ‖f‖ ∧
       ‖S i f‖ ≤ CP * ‖f‖) ∧
 (∀ i j c d, ‖B i j c d‖ ≤ CB i j c d ∧ (∀ w p, (B i j c d w).u p = ∑ a : Fin 3, ∑ b : Fin 3,
 Poincare.BufferedTensorGraphTransport.weight A i (θ i j) (ξ j) (F i j) a b c d p.2 *
 (w (a,b)).u (p.1,F i j p.2)) ∧ (∀ (w : Poincare.GlobalParametrixAssembly.SourceGraphs α T) t z,
z ∉ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i → (B i j c d w).u (t,z) = 0) ∧ (∀ (w : Poincare.GlobalParametrixAssembly.SourceGraphs α T) t (x : M),
x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i).source →
(B i j c d w).u (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A i x) =
A.partition i x * (@ite ℝ (x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j).source) (Classical.propDecidable _)
 (∑ a : Fin 3, ∑ b : Fin 3,
   ξ j (Poincare.FiniteAtlasParabolicTensorSpace.chart A j x) * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x a c * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x b d *
   (w (a,b)).u (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A j x)) 0))) ∧
 ‖Pglobal‖ ≤ Cglobal ∧
 (∀ (f : Poincare.FiniteAtlasParabolicTensorSpace.Y_M A α T) i c d, (Pglobal f).val (i,c,d) =
   ∑ j : Fin A.cover.chartCount, B i j c d (fun ab => S j (f.val (j,ab.1,ab.2)))) ∧
 (∀ (f : Poincare.FiniteAtlasParabolicTensorSpace.Y_M A α T) i c d t (x : M), x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i).source →
((Pglobal f).val (i,c,d)).u (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A i x) =
Poincare.FiniteAtlasBufferedTensorValue.value A ξ (fun j a b z => (S j (f.val (j,a,b))).u (t,z)) i c d x) := by
  intro M _ _ _ _ _ g0 α hα hα1
  classical
  obtain ⟨A, ψ, ξ, hbuffer, Cψ, CP, τ, hCψ, hCP, hτ, hτ1, hlocal⟩ :=
    MetricAdaptedLocalParametrix.exists_metric_adapted_local_parametrix g0 α hα hα1
  have hpartition (i : Fin A.cover.chartCount) (z : ClosedSmoothModel 3)
      (hz : z ∈ coordSupport A i) :
      ∀ᶠ y in 𝓝 z, GeodesicTransport.cutoff (n := 3) (A.cover.anchor i) y = 1 := by
    have hψz : ψ i z = 1 := Filter.EventuallyEq.eq_of_nhds ((hbuffer i).2.2.1 z hz)
    have hzψ : z ∈ tsupport (ψ i) := subset_tsupport _ (by simp [Function.mem_support, hψz])
    have hξz : ξ i z = 1 := (hbuffer i).2.2.2.2.2.2.2.1 z hzψ
    have hzξ : z ∈ tsupport (ξ i) := subset_tsupport _ (by simp [Function.mem_support, hξz])
    exact (hbuffer i).2.2.2.2.2.2.2.2.2 z hzξ
  obtain ⟨θ, F, hgate⟩ :=
    BufferedChartTransitionExtensions.exists_gated_chart_extensions A ξ
      (fun i => (hbuffer i).2.2.2.2.2.1)
      (fun i => (hbuffer i).2.2.2.2.2.2.2.2.1)
      (fun i => (hbuffer i).2.2.2.2.2.2.2.2.2) hpartition
  have hgateSource (i j : Fin A.cover.chartCount) :
      tsupport (θ i j) ⊆ ((chart A i).symm.trans (chart A j)).source :=
    fun z hz => ((hgate i j).2.2.2.1 hz).1.1
  have htransport (i j : Fin A.cover.chartCount) (c d : Fin 3) :=
    BufferedTensorGraphTransport.exists_destination_entry_transport M A i j
      (θ i j) (ξ j) (F i j) c d (hgate i j).1 (hgate i j).2.1
      (hbuffer j).2.2.2.2.1 (hgate i j).2.2.2.2.2.1
      (hgate i j).2.2.2.2.2.2.1 (hgateSource i j)
      (hgate i j).2.2.2.2.2.2.2.1
      (fun z hz => Filter.EventuallyEq.eq_of_nhds ((hgate i j).2.2.2.2.1 z hz))
      α hα hα1
  choose CB hCB hBfamily using htransport
  let Cglobal : ℝ := CP *
    (∑ i : Fin A.cover.chartCount, ∑ j : Fin A.cover.chartCount,
      ∑ c : Fin 3, ∑ d : Fin 3, CB i j c d)
  refine ⟨A, ψ, ξ, hbuffer, θ, F, ?_, Cψ, CP, Cglobal, τ, CB,
    hCψ, hCP, hτ, hτ1, hCB, rfl, ?_⟩
  · intro i j
    exact ⟨(hgate i j).1, (hgate i j).2.1, (hgate i j).2.2.1, hgateSource i j,
      (hgate i j).2.2.2.2.1, (hgate i j).2.2.2.2.2.1,
      (hgate i j).2.2.2.2.2.2.1, (hgate i j).2.2.2.2.2.2.2.1,
      (hgate i j).2.2.2.2.2.2.2.2⟩
  · intro T hT
    obtain ⟨S, R, hS⟩ := hlocal T hT
    have hT1 : T ∈ Ioc (0 : ℝ) 1 := ⟨hT.1, hT.2.trans hτ1⟩
    choose B hBN hBraw hBsupport hBchart using
      fun i j c d => hBfamily i j c d T hT1
    have hrange := ambient_mem_and_chart_value M A α T S B ξ hBsupport hBchart
    let Pglobal : Y_M A α T →L[ℝ] X_M A α T :=
      (ambient A α T S B).codRestrict (tensorSubmodule A (evalX α T)) hrange.1
    refine ⟨S, R, B, Pglobal, hS, ?_, ?_, ?_, ?_⟩
    · intro i j c d
      exact ⟨hBN i j c d, hBraw i j c d, hBsupport i j c d, hBchart i j c d⟩
    · change ‖(ambient A α T S B).codRestrict
        (tensorSubmodule A (evalX α T)) hrange.1‖ ≤ Cglobal
      change ‖ambient A α T S B‖ ≤ Cglobal
      exact ambient_norm_le M A α T S B CP CB hCP hCB hBN
        (fun j f hf => (hS j).2 f hf |>.2.2)
    · intro f i c d
      change ((∑ j : Fin A.cover.chartCount,
        (B i j c d).comp (localGraphs A α T S j)) f) = _
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
      rfl
    · exact hrange.2

end Poincare.MetricAdaptedGlobalParametrix
