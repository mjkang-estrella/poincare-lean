import Poincare.Global.BufferedTensorGraphTransportWeights
import Poincare.Global.BufferedTensorGraphTransportValues
import Poincare.Global.ParabolicSpatialHolderPullback
import Poincare.Global.ParabolicCutoffCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.BufferedTensorGraphTransport
open FiniteAtlasParabolicTensorSpace
universe u

/-- The actual weighted sum acts on the nine original scalar carriers. -/
private def valueRowLinearMap {α T : ℝ}
    (f : Fin 3 → Fin 3 → Scalar α T)
    (P : Scalar α T →L[ℝ] Scalar α T) :
    ((Fin 3 × Fin 3) → Scalar α T) →ₗ[ℝ] Scalar α T where
  toFun w := ∑ a : Fin 3, ∑ b : Fin 3, f a b * P (w (a,b))
  map_add' w v := by
    apply ParabolicHolder.ext
    intro p hp
    simp only [ParabolicHolderMultiplier.sum_apply, ParabolicHolder.mul_apply,
      map_add, Pi.add_apply, ParabolicHolder.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' r w := by
    apply ParabolicHolder.ext
    intro p hp
    simp only [ParabolicHolderMultiplier.sum_apply, ParabolicHolder.mul_apply,
      map_smul, Pi.smul_apply, ParabolicHolder.smul_apply, RingHom.id_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring

/-- Compact coefficients and spatial substitution give one bound for all time horizons. -/
theorem exists_destination_Y_entry_transport :
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
∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ,
∃ Q : ((Fin 3 × Fin 3) → (Poincare.FiniteAtlasParabolicTensorSpace.Scalar α T)) →L[ℝ] (Poincare.FiniteAtlasParabolicTensorSpace.Scalar α T), ‖Q‖ ≤ C ∧
(∀ w p, (Q w) p = ∑ a : Fin 3, ∑ b : Fin 3,
 Poincare.BufferedTensorGraphTransport.weight A i θ ξ F a b c d p.2 *
 (w (a,b)) (p.1, F p.2)) ∧
(∀ w t z, z ∉ Poincare.FiniteAtlasParabolicTensorSpace.coordSupport A i →
 (Q w) (t,z) = 0) ∧
(∀ w t (x : M), x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A i).source →
 (Q w) (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A i x) =
 A.partition i x * (@ite ℝ (x ∈ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j).source) (Classical.propDecidable _)
   (∑ a : Fin 3, ∑ b : Fin 3,
     ξ (Poincare.FiniteAtlasParabolicTensorSpace.chart A j x) * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x a c * Poincare.FiniteAtlasParabolicTensorSpace.jac A i j x b d *
     (w (a,b)) (t,Poincare.FiniteAtlasParabolicTensorSpace.chart A j x)) 0)) := by
  classical
  intro M _ _ _ A i j θ ξ F c d hθ hcθ hξ hF hcF hθsource hagree hone α hα hα1
  have hθtarget : tsupport θ ⊆ (chart A i).target := fun z hz => (hθsource hz).1
  have hw (a b : Fin 3) :=
    contDiff_hasCompactSupport_weight M A i θ ξ F a b c d hθ hcθ hθtarget hξ hF
  have hcarrier (a b : Fin 3) :=
    ParabolicCutoffCommutator.exists_cutoff_carrier (hw a b).1 (hw a b).2 hα hα1
  choose K hK hfamily using hcarrier
  obtain ⟨CF, hCF, hP⟩ :=
    ParabolicSpatialHolderPullback.exists_spatial_Y_pullback (V := ℝ) F hF hcF α hα.le
  let bound : ℝ := (∑ a : Fin 3, ∑ b : Fin 3, K a b) * CF
  have hbound0 : 0 ≤ bound :=
    mul_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK a b) hCF
  refine ⟨bound, hbound0, ?_⟩
  intro T
  obtain ⟨P, hPN, hPvalue⟩ := hP T
  choose f hf hfnorm using fun a b => hfamily a b T
  let L := valueRowLinearMap f P
  have hLN (w : (Fin 3 × Fin 3) → Scalar α T) : ‖L w‖ ≤ bound * ‖w‖ := by
    have hpart (a b : Fin 3) : ‖f a b * P (w (a,b))‖ ≤ K a b * CF * ‖w‖ := by
      calc
        _ ≤ ‖f a b‖ * ‖P (w (a,b))‖ := ParabolicHolder.norm_mul_le _ _
        _ ≤ K a b * (CF * ‖w‖) := by
          apply mul_le_mul (hfnorm a b)
            ((P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hPN
              (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left
                (norm_le_pi_norm w (a,b)) hCF)))
            (norm_nonneg _) (hK a b)
        _ = _ := by ring
    change ‖∑ a : Fin 3, ∑ b : Fin 3, f a b * P (w (a,b))‖ ≤ _
    calc
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖f a b * P (w (a,b))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, K a b * CF * ‖w‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpart a b
      _ = bound * ‖w‖ := by simp only [bound, Finset.sum_mul, mul_assoc]
  let Q := L.mkContinuous bound hLN
  have hraw (w : (Fin 3 × Fin 3) → Scalar α T) (p : ℝ × ClosedSmoothModel 3) :
      Q w p = ∑ a : Fin 3, ∑ b : Fin 3,
        weight A i θ ξ F a b c d p.2 * (w (a,b)) (p.1,F p.2) := by
    change (∑ a : Fin 3, ∑ b : Fin 3, f a b * P (w (a,b))) p = _
    simp only [ParabolicHolderMultiplier.sum_apply, ParabolicHolder.mul_apply, hPvalue]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hp : p ∈ ParabolicHolder.cylinder T
    · rw [hf a b p hp]
    · have hpF : (p.1, F p.2) ∉ ParabolicHolder.cylinder T :=
        fun h => hp ⟨h.1, mem_univ _⟩
      rw [ParabolicHolder.zero_off (w (a,b)) hpF]
      simp only [mul_zero]
  refine ⟨Q, L.mkContinuous_norm_le hbound0 hLN, hraw, ?_, ?_⟩
  · intro w t z hz
    rw [hraw]
    simp only [weight_zero_off_coordSupport A i θ ξ F _ _ c d hθtarget z hz,
      zero_mul, Finset.sum_const_zero]
  · intro w t x hx
    rw [hraw]
    have hchart (a b : Fin 3) := weight_pullback_chart A i θ ξ F a b c d j
      hθsource hagree hone (fun z => (w (a,b)) (t,z)) x hx
    simp_rw [hchart]
    by_cases hj : x ∈ (chart A j).source
    · simp only [if_pos hj, Finset.mul_sum]
    · simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Poincare.BufferedTensorGraphTransport
