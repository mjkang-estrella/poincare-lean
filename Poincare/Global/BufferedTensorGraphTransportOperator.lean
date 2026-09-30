import Poincare.Global.BufferedTensorGraphTransportWeights
import Poincare.Global.BufferedTensorGraphTransportValues
import Poincare.Global.ParabolicSpatialGraphPullback
import Poincare.Global.BufferedFrozenParabolicSolver

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedTensorGraphTransport
open FiniteAtlasParabolicTensorSpace ParabolicSolutionGraph
universe u

/-- Actual gated tensor transport retains the genuine derivative graph and a
uniform bound before the positive time interval is selected. -/
theorem exists_destination_entry_transport :
∀ (M : Type u) [TopologicalSpace M]
[ChartedSpace (Poincare.ClosedSmoothModel 3) M]
[IsManifold (Poincare.closedSmoothModelWithCorners 3) ((⊤ : ENat) : WithTop ENat) M]
(A : Poincare.FiniteAtlasParabolicTensorSpace.AtlasData M)
(i j : Fin A.cover.chartCount) (θ ξ : Poincare.ClosedSmoothModel 3 → ℝ)
(F : Poincare.ClosedSmoothModel 3 → Poincare.ClosedSmoothModel 3) (c d : Fin 3),
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) θ → HasCompactSupport θ →
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ →
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F → HasCompactSupport F →
tsupport θ ⊆ ((Poincare.FiniteAtlasParabolicTensorSpace.chart A i).symm.trans (Poincare.FiniteAtlasParabolicTensorSpace.chart A j)).source →
(∀ z ∈ tsupport θ, ∀ᶠ y in nhds z, F y = Poincare.FiniteAtlasParabolicTensorSpace.change A i j y) →
(∀ z ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i) ''
 (tsupport (A.partition i) ∩ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j).symm '' tsupport ξ), θ z = 1) →
∀ α : ℝ, 0 < α → α < 1 →
∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Set.Ioc (0 : ℝ) 1,
∃ B : ((Fin 3 × Fin 3) → (Poincare.ParabolicSolutionGraph.Graph (E := Poincare.ClosedSmoothModel 3) α T)) →L[ℝ] (Poincare.ParabolicSolutionGraph.Graph (E := Poincare.ClosedSmoothModel 3) α T), ‖B‖ ≤ C ∧
(∀ w p, (B w).u p = ∑ a : Fin 3, ∑ b : Fin 3,
 Poincare.BufferedTensorGraphTransport.weight A i θ ξ F a b c d p.2 *
 (w (a,b)).u (p.1, F p.2)) ∧
(∀ w t z, z ∉ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i →
 (B w).u (t,z) = 0) ∧
(∀ w t (x : M), x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i).source →
 (B w).u (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A i x) =
 A.partition i x * (@ite ℝ (x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j).source) (Classical.propDecidable _)
   (∑ a : Fin 3, ∑ b : Fin 3,
     ξ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j x) * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x a c * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x b d *
     (w (a,b)).u (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A j x)) 0)) := by
  classical
  intro M _ _ _ A i j θ ξ F c d hθ hcθ hξ hF hcF hθsource hagree hone α hα hα1
  have hθtarget : tsupport θ ⊆ (chart A i).target := fun z hz => (hθsource hz).1
  have hw (a b : Fin 3) :=
    contDiff_hasCompactSupport_weight M A i θ ξ F a b c d hθ hcθ hθtarget hξ hF
  have hd (a b : Fin 3) :=
    BufferedFrozenParabolicSolver.exists_uniform_cutoff_bound
      (hw a b).1 (hw a b).2 hα hα1
  choose D hD hbound using hd
  obtain ⟨CF, hCF, hQ⟩ :=
    ParabolicSpatialGraphPullback.exists_spatial_Graph_pullback F hF hcF α hα hα1
  let bound : ℝ := (∑ a : Fin 3, ∑ b : Fin 3, D a b) * CF
  have hbound0 : 0 ≤ bound := by
    exact mul_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hD a b) hCF
  refine ⟨bound, hbound0, ?_⟩
  intro T hT
  obtain ⟨Q, hQN, hQvalue⟩ := hQ T hT
  have hcut (a b : Fin 3) :
      ∃ C : Graph (E := ClosedSmoothModel 3) α T →L[ℝ]
        Graph (E := ClosedSmoothModel 3) α T,
        ∀ G p, (C G).u p = weight A i θ ξ F a b c d p.2 * G.u p := by
    obtain ⟨C, hv, _⟩ := ParabolicCutoffCommutator.exists_cutoff_operator
      (hw a b).1 (hw a b).2 hα hα1
    exact ⟨C, hv⟩
  choose C hC using hcut
  let B : ((Fin 3 × Fin 3) → Graph (E := ClosedSmoothModel 3) α T) →L[ℝ]
      Graph (E := ClosedSmoothModel 3) α T :=
    ∑ a : Fin 3, ∑ b : Fin 3,
      ((C a b).comp Q).comp (ContinuousLinearMap.proj (a,b))
  have hBN : ‖B‖ ≤ bound := by
    apply ContinuousLinearMap.opNorm_le_bound B hbound0
    intro w
    have hpart (a b : Fin 3) : ‖C a b (Q (w (a,b)))‖ ≤ D a b * CF * ‖w‖ := by
      calc
        _ ≤ ‖C a b‖ * ‖Q (w (a,b))‖ := (C a b).le_opNorm _
        _ ≤ D a b * (CF * ‖w‖) := by
          apply mul_le_mul (hbound a b T hT.1 (C a b) (hC a b))
            ((Q.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hQN
              (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left
                (norm_le_pi_norm w (a,b)) hCF)))
            (norm_nonneg _) (hD a b)
        _ = _ := by ring
    calc
      ‖B w‖ = ‖∑ a : Fin 3, ∑ b : Fin 3, C a b (Q (w (a,b)))‖ := by
        simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply]
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖C a b (Q (w (a,b)))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, D a b * CF * ‖w‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpart a b
      _ = bound * ‖w‖ := by simp only [bound, Finset.sum_mul, mul_assoc]
  have hraw (w : (Fin 3 × Fin 3) → Graph (E := ClosedSmoothModel 3) α T)
      (p : ℝ × ClosedSmoothModel 3) :
      (B w).u p = ∑ a : Fin 3, ∑ b : Fin 3,
        weight A i θ ξ F a b c d p.2 * (w (a,b)).u (p.1,F p.2) := by
    change evalX α T p (B w) = _
    simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change (C a b (Q (w (a,b)))).u p = _
    rw [hC a b, (hQvalue (w (a,b)) p).1]
  refine ⟨B, hBN, hraw, ?_, ?_⟩
  · intro w t z hz
    rw [hraw]
    simp only [weight_zero_off_coordSupport A i θ ξ F _ _ c d hθtarget z hz,
      zero_mul, Finset.sum_const_zero]
  · intro w t x hx
    rw [hraw]
    have hchart (a b : Fin 3) := weight_pullback_chart A i θ ξ F a b c d j
      hθsource hagree hone (fun z => (w (a,b)).u (t,z)) x hx
    simp_rw [hchart]
    by_cases hj : x ∈ (chart A j).source
    · simp only [if_pos hj, Finset.mul_sum]
    · simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Poincare.BufferedTensorGraphTransport
