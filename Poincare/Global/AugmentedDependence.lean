import Poincare.Global.AugmentedC1
import Poincare.Global.GeodesicDependence

/-!
# Gronwall dependence for augmented chart geodesic flows

This module exports the augmented analogue of the first-order Lipschitz
dependence step: any common augmented solution family staying in one closed
tube has fixed-time endpoints Lipschitz in the augmented initial data.
-/

noncomputable section

open Bundle Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Gronwall dependence on augmented initial data for any supplied common
chart-Christoffel augmented flow.

The compact-tube Lipschitz constant for
`augmentedGeodesicFlowField (chartChristoffelField g x₀)` is obtained from
`AugmentedC1`; the remaining hypotheses are the honest ODE and tube data for
the supplied solution family.
-/
theorem exists_chartChristoffel_augmentedFlow_lipschitzOn_of_ODE
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {S : Set ((E × E) × (E × E))}
    {β : ((E × E) × (E × E)) → ℝ → ((E × E) × (E × E))}
    {T a : ℝ} {p : (E × E) × (E × E)} {t : ℝ}
    (hβ0 : ∀ z ∈ S, β z 0 = z)
    (hβder : ∀ z ∈ S, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (β z)
        (augmentedGeodesicFlowField (chartChristoffelField g x₀) (β z τ))
        (Icc (0 : ℝ) T) τ)
    (hβmem : ∀ z ∈ S, ∀ τ ∈ Icc (0 : ℝ) T,
      β z τ ∈ closedBall p a)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ K : ℝ≥0,
      LipschitzOnWith
        ⟨Real.exp ((K : ℝ) * T), (Real.exp_pos _).le⟩
        (fun z : (E × E) × (E × E) => β z t) S := by
  let X := (E × E) × (E × E)
  let F : X → X :=
    augmentedGeodesicFlowField (chartChristoffelField g x₀)
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall
        (g := g) (x₀ := x₀) (p := p) (a := a) with
    ⟨_haug, K, hLip⟩
  use K
  apply LipschitzOnWith.of_dist_le_mul
  intro z₁ hz₁ z₂ hz₂
  have hcont₁ : ContinuousOn (β z₁) (Icc (0 : ℝ) T) := by
    exact HasDerivWithinAt.continuousOn
      (f' := fun τ => F (β z₁ τ))
      (by
        intro τ hτ
        simpa [F] using hβder z₁ hz₁ τ hτ)
  have hcont₂ : ContinuousOn (β z₂) (Icc (0 : ℝ) T) := by
    exact HasDerivWithinAt.continuousOn
      (f' := fun τ => F (β z₂ τ))
      (by
        intro τ hτ
        simpa [F] using hβder z₂ hz₂ τ hτ)
  have hdist :
      dist (β z₁ t) (β z₂ t) ≤
        dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) := by
    exact
      dist_le_of_trajectories_ODE_of_mem
        (v := fun _ : ℝ => F)
        (s := fun _ : ℝ => closedBall p (a + 1))
        (K := K) (a := 0) (b := T)
        (by
          intro _ _
          simpa [F] using hLip)
        hcont₁
        (by
          intro τ hτ
          have hτIcc : τ ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hτ
          exact (hβder z₁ hz₁ τ hτIcc).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩))
        (by
          intro τ hτ
          exact closedBall_subset_closedBall (by linarith)
            (hβmem z₁ hz₁ τ (Ico_subset_Icc_self hτ)))
        hcont₂
        (by
          intro τ hτ
          have hτIcc : τ ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hτ
          exact (hβder z₂ hz₂ τ hτIcc).mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2⟩))
        (by
          intro τ hτ
          exact closedBall_subset_closedBall (by linarith)
            (hβmem z₂ hz₂ τ (Ico_subset_Icc_self hτ)))
        (by
          rw [hβ0 z₁ hz₁, hβ0 z₂ hz₂])
        t ht
  have hKt : (K : ℝ) * t ≤ (K : ℝ) * T :=
    mul_le_mul_of_nonneg_left ht.2 K.2
  have hexp : Real.exp ((K : ℝ) * t) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.mpr hKt
  calc
    dist (β z₁ t) (β z₂ t)
        ≤ Real.exp ((K : ℝ) * t) * dist z₁ z₂ := by
          simpa [sub_zero, mul_comm] using hdist
    _ ≤ Real.exp ((K : ℝ) * T) * dist z₁ z₂ := by
          exact mul_le_mul_of_nonneg_right hexp dist_nonneg

end GeodesicTransport
end Poincare
