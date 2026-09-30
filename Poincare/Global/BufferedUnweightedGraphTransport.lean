import Poincare.Global.BufferedUnweightedGraphTransportDefinitions
import Poincare.Global.ParabolicSpatialGraphPullback
import Poincare.Global.BufferedFrozenParabolicSolver

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedUnweightedGraphTransport
open FiniteAtlasParabolicTensorSpace ParabolicSolutionGraph

/-- Compactness of the gate controls the actual coefficient, including both
ordered differential slots and the source and destination buffers. -/
private theorem contDiff_hasCompactSupport_weight
    (θ ψ ξ : ClosedSmoothModel 3 → ℝ)
    (F : ClosedSmoothModel 3 → ClosedSmoothModel 3) (a b c d : Fin 3)
    (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ)
    (hψ : ContDiff ℝ ∞ ψ) (hξ : ContDiff ℝ ∞ ξ)
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (weight θ ψ ξ F a b c d) ∧
      HasCompactSupport (weight θ ψ ξ F a b c d) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hentry (r s : Fin 3) : ContDiff ℝ ∞
      (fun z ↦ (fderiv ℝ F z ((EuclideanSpace.basisFun (Fin 3) ℝ) s)) r) :=
    (EuclideanSpace.proj r).contDiff.comp
      (hDF.clm_apply (contDiff_const (c := EuclideanSpace.basisFun (Fin 3) ℝ s)))
  exact ⟨hθ.mul (((hψ.mul (hξ.comp hF)).mul (hentry a c)).mul (hentry b d)),
    hcθ.mul_right⟩

/-- The actual unweighted reconstruction row is bounded in the original
derivative graph norm, uniformly before the positive time interval is chosen. -/
theorem exists_entry_transport :
∀ (θ ψ ξ : Poincare.ClosedSmoothModel 3 → ℝ)
(F : Poincare.ClosedSmoothModel 3 → Poincare.ClosedSmoothModel 3) (c d : Fin 3),
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) θ → HasCompactSupport θ →
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ψ →
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ξ →
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F → HasCompactSupport F →
∀ α : ℝ, 0 < α → α < 1 →
∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Set.Ioc (0 : ℝ) 1,
∃ B : ((Fin 3 × Fin 3) → (Poincare.ParabolicSolutionGraph.Graph
  (E := Poincare.ClosedSmoothModel 3) α T)) →L[ℝ]
  (Poincare.ParabolicSolutionGraph.Graph (E := Poincare.ClosedSmoothModel 3) α T),
‖B‖ ≤ C ∧
(∀ w p, (B w).u p = ∑ a : Fin 3, ∑ b : Fin 3,
 Poincare.BufferedUnweightedGraphTransport.weight θ ψ ξ F a b c d p.2 *
 (w (a,b)).u (p.1,F p.2)) ∧
∀ w t z, z ∉ tsupport ψ → (B w).u (t,z) = 0 := by
  classical
  intro θ ψ ξ F c d hθ hcθ hψ hξ hF hcF α hα hα1
  have hw (a b : Fin 3) :=
    contDiff_hasCompactSupport_weight θ ψ ξ F a b c d hθ hcθ hψ hξ hF
  have hd (a b : Fin 3) :=
    BufferedFrozenParabolicSolver.exists_uniform_cutoff_bound
      (hw a b).1 (hw a b).2 hα hα1
  choose D hD hbound using hd
  obtain ⟨CF, hCF, hQ⟩ :=
    ParabolicSpatialGraphPullback.exists_spatial_Graph_pullback F hF hcF α hα hα1
  let bound : ℝ := (∑ a : Fin 3, ∑ b : Fin 3, D a b) * CF
  have hbound0 : 0 ≤ bound :=
    mul_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hD a b) hCF
  refine ⟨bound, hbound0, ?_⟩
  intro T hT
  obtain ⟨Q, hQN, hQvalue⟩ := hQ T hT
  have hcut (a b : Fin 3) :
      ∃ C : Graph (E := ClosedSmoothModel 3) α T →L[ℝ]
        Graph (E := ClosedSmoothModel 3) α T,
        ∀ G p, (C G).u p = weight θ ψ ξ F a b c d p.2 * G.u p := by
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
        weight θ ψ ξ F a b c d p.2 * (w (a,b)).u (p.1,F p.2) := by
    change evalX α T p (B w) = _
    simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    change (C a b (Q (w (a,b)))).u p = _
    rw [hC a b, (hQvalue (w (a,b)) p).1]
  refine ⟨B, hBN, hraw, ?_⟩
  intro w t z hz
  have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
  rw [hraw]
  simp only [weight, hψz, zero_mul, mul_zero, Finset.sum_const_zero]

end Poincare.BufferedUnweightedGraphTransport
