import Poincare.Global.CenteredMembership
import Poincare.Global.IndexedSelection

/-!
# Selector assembly boundary

This module assembles the centered all-direction hosted third-variation
package into the two concrete consumers that are currently exposed:

* the local-eventual endpoint derivative theorem for a fixed hosted base;
* the cross-point Gronwall transfer for two centered endpoint CLM packages.

The final neighborhood-indexed source/target producer is not asserted here.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace SelectorAssembly

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
The centered all-direction hosted third-variation package supplies the
endpoint CLM data required by the local-eventual doubly-augmented endpoint
derivative theorem, for any hosted time inside the selected centered interval.
-/
theorem exists_centered_hosted_endpoint_hasFDerivAt
    [FiniteDimensional ℝ (A × A)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (fun τ : ℝ => (β y.1 τ, Ξ y.1 y.2 τ))) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ Ω : A × A → ℝ → A × A,
      (∀ η : A × A, Ω η 0 = η) ∧
        (∀ η : A × A, ∀ τ ∈ Icc (-ε) ε,
          HasDerivWithinAt (Ω η)
            (fderiv ℝ
              (fun y' : A × A =>
                let F : A → A :=
                  augmentedGeodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                (F y'.1, (fderiv ℝ F y'.1) y'.2))
              (β y.1 τ, Ξ y.1 y.2 τ) (Ω η τ))
            (Icc (-ε) ε) τ) ∧
          ∀ {T a : ℝ} {p : A × A},
            0 < T →
            T ∈ Icc (-ε) ε →
            β y.1 0 = y.1 →
            (∀ τ ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (β y.1)
                (augmentedGeodesicFlowField
                  (GeodesicTransport.chartChristoffelField g x₀)
                  (β y.1 τ))
                (Icc (0 : ℝ) T) τ) →
            Ξ y.1 y.2 0 = y.2 →
            (∀ τ ∈ Icc (0 : ℝ) T,
              HasDerivWithinAt (Ξ y.1 y.2)
                (secondVariationFlowFieldAlong
                  (GeodesicTransport.chartChristoffelField g x₀)
                  (β y.1) τ (Ξ y.1 y.2 τ))
                (Icc (0 : ℝ) T) τ) →
            (∀ τ ∈ Icc (0 : ℝ) T,
              (β y.1 τ, Ξ y.1 y.2 τ) ∈ closedBall p a) →
            (∀ᶠ h in 𝓝 (0 : A × A),
              β (y + h).1 0 = (y + h).1 ∧
                Ξ (y + h).1 (y + h).2 0 = (y + h).2 ∧
                  (∀ τ ∈ Icc (0 : ℝ) T,
                    HasDerivWithinAt (β (y + h).1)
                      (augmentedGeodesicFlowField
                        (GeodesicTransport.chartChristoffelField g x₀)
                        (β (y + h).1 τ))
                      (Icc (0 : ℝ) T) τ) ∧
                    (∀ τ ∈ Icc (0 : ℝ) T,
                      HasDerivWithinAt (Ξ (y + h).1 (y + h).2)
                        (secondVariationFlowFieldAlong
                          (GeodesicTransport.chartChristoffelField g x₀)
                          (β (y + h).1) τ (Ξ (y + h).1 (y + h).2 τ))
                        (Icc (0 : ℝ) T) τ) ∧
                      ∀ τ ∈ Icc (0 : ℝ) T,
                        (β (y + h).1 τ, Ξ (y + h).1 (y + h).2 τ) ∈
                          closedBall p a) →
            ∃ D : (A × A) →L[ℝ] (A × A),
              HasFDerivAt
                (fun y' : A × A => (β y'.1 T, Ξ y'.1 y'.2 T)) D y := by
  rcases
      CenteredMembership.exists_rescaled_hosted_thirdVariation_centered_membership_clm_package
        (g := g) (x₀ := x₀) (ζ := fun τ : ℝ => (β y.1 τ, Ξ y.1 y.2 τ))
        hpaired with
    ⟨ε, hε, Ω, hΩ0, hΩder, _hΩadd, _hΩsmul, _centeredRadius,
      _hcenteredRadius_nonneg, _hΩmem_centered, _hΩadd_mem_centered,
      _hΩsmul_mem_centered, hCLM⟩
  have hrest :
      ∀ {T a : ℝ} {p : A × A},
        0 < T →
        T ∈ Icc (-ε) ε →
        β y.1 0 = y.1 →
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (β y.1)
            (augmentedGeodesicFlowField
              (GeodesicTransport.chartChristoffelField g x₀)
              (β y.1 τ))
            (Icc (0 : ℝ) T) τ) →
        Ξ y.1 y.2 0 = y.2 →
        (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (Ξ y.1 y.2)
            (secondVariationFlowFieldAlong
              (GeodesicTransport.chartChristoffelField g x₀)
              (β y.1) τ (Ξ y.1 y.2 τ))
            (Icc (0 : ℝ) T) τ) →
        (∀ τ ∈ Icc (0 : ℝ) T,
          (β y.1 τ, Ξ y.1 y.2 τ) ∈ closedBall p a) →
        (∀ᶠ h in 𝓝 (0 : A × A),
          β (y + h).1 0 = (y + h).1 ∧
            Ξ (y + h).1 (y + h).2 0 = (y + h).2 ∧
              (∀ τ ∈ Icc (0 : ℝ) T,
                HasDerivWithinAt (β (y + h).1)
                  (augmentedGeodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                    (β (y + h).1 τ))
                  (Icc (0 : ℝ) T) τ) ∧
                (∀ τ ∈ Icc (0 : ℝ) T,
                  HasDerivWithinAt (Ξ (y + h).1 (y + h).2)
                    (secondVariationFlowFieldAlong
                      (GeodesicTransport.chartChristoffelField g x₀)
                      (β (y + h).1) τ (Ξ (y + h).1 (y + h).2 τ))
                    (Icc (0 : ℝ) T) τ) ∧
                  ∀ τ ∈ Icc (0 : ℝ) T,
                    (β (y + h).1 τ, Ξ (y + h).1 (y + h).2 τ) ∈
                      closedBall p a) →
        ∃ D : (A × A) →L[ℝ] (A × A),
          HasFDerivAt
            (fun y' : A × A => (β y'.1 T, Ξ y'.1 y'.2 T)) D y := by
    intro T a p hT_pos hTε hbaseβ0 hbaseβder hbaseΞ0 hbaseΞder hbase_mem hpert
    rcases hCLM T hTε with ⟨pkg⟩
    let D : (A × A) →L[ℝ] (A × A) := pkg.1
    have hsub : ∀ τ ∈ Icc (0 : ℝ) T, τ ∈ Icc (-ε) ε := by
      intro τ hτ
      constructor
      · linarith [hε, hτ.1]
      · exact hτ.2.trans hTε.2
    have hΩD : ∀ᶠ h in 𝓝 (0 : A × A),
        Ω h 0 = h ∧
          (∀ τ ∈ Icc (0 : ℝ) T,
            HasDerivWithinAt (Ω h)
              (fderiv ℝ
                (fun y' : A × A =>
                  let F : A → A :=
                    augmentedGeodesicFlowField
                      (GeodesicTransport.chartChristoffelField g x₀)
                  (F y'.1, (fderiv ℝ F y'.1) y'.2))
                (β y.1 τ, Ξ y.1 y.2 τ) (Ω h τ))
              (Icc (0 : ℝ) T) τ) ∧
          Ω h T = D h := by
      filter_upwards [pkg.2.2] with h hh
      exact ⟨hh.1, by
        intro τ hτ
        exact (hΩder h τ (hsub τ hτ)).mono
          (Icc_subset_Icc (by linarith [hε]) hTε.2),
        by simpa [D] using hh.2⟩
    have ht : T ∈ Icc (0 : ℝ) T := ⟨hT_pos.le, le_rfl⟩
    have hD_deriv :
        HasFDerivAt
          (fun y' : A × A => (β y'.1 T, Ξ y'.1 y'.2 T)) D y :=
      GeodesicTransport.chartChristoffel_doublyAugmented_endpoint_hasFDerivAt_of_thirdVariation_eventually
        (g := g) (x₀ := x₀) (β := β) (Ξ := Ξ) (y := y) (Ω := Ω)
        (D := D) (T := T) (a := a) (p := p) (t := T)
        hT_pos hbaseβ0 hbaseβder hbaseΞ0 hbaseΞder hbase_mem hpert hΩD ht
    exact ⟨D, hD_deriv⟩
  exact ⟨ε, hε, Ω, hΩ0, hΩder, hrest⟩

omit [T2Space M] in
/--
Two centered all-direction hosted third-variation packages supply the endpoint
CLMs and endpoint equalities needed by the selector-level cross-point
Gronwall transfer.
-/
theorem exists_centered_endpoint_gronwall_bound
    [FiniteDimensional ℝ (A × A)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ₁ ζ₂ : ℝ → A × A} (hζ₁ : Continuous ζ₁) (hζ₂ : Continuous ζ₂) :
    ∃ (ε₁ : ℝ), 0 < ε₁ ∧ ∃ Ω₁ : A × A → ℝ → A × A,
      (∀ η : A × A, Ω₁ η 0 = η) ∧
        (∀ η : A × A, ∀ τ ∈ Icc (-ε₁) ε₁,
          HasDerivWithinAt (Ω₁ η)
            (fderiv ℝ
              (fun y' : A × A =>
                let F : A → A :=
                  augmentedGeodesicFlowField
                    (GeodesicTransport.chartChristoffelField g x₀)
                (F y'.1, (fderiv ℝ F y'.1) y'.2))
              (ζ₁ τ) (Ω₁ η τ))
            (Icc (-ε₁) ε₁) τ) ∧
          ∃ (ε₂ : ℝ), 0 < ε₂ ∧ ∃ Ω₂ : A × A → ℝ → A × A,
            (∀ η : A × A, Ω₂ η 0 = η) ∧
              (∀ η : A × A, ∀ τ ∈ Icc (-ε₂) ε₂,
                HasDerivWithinAt (Ω₂ η)
                  (fderiv ℝ
                    (fun y' : A × A =>
                      let F : A → A :=
                        augmentedGeodesicFlowField
                          (GeodesicTransport.chartChristoffelField g x₀)
                      (F y'.1, (fderiv ℝ F y'.1) y'.2))
                    (ζ₂ τ) (Ω₂ η τ))
                  (Icc (-ε₂) ε₂) τ) ∧
                ∀ {T a δnorm : ℝ} {p : A × A} {t : ℝ},
                  0 ≤ T →
                  T ∈ Icc (-ε₁) ε₁ →
                  T ∈ Icc (-ε₂) ε₂ →
                  0 ≤ δnorm →
                  (∀ τ ∈ Ico (0 : ℝ) T, ζ₁ τ ∈ closedBall p (a + 1)) →
                  (∀ τ ∈ Ico (0 : ℝ) T, ζ₂ τ ∈ closedBall p (a + 1)) →
                  (∀ τ ∈ Ico (0 : ℝ) T, ‖ζ₂ τ - ζ₁ τ‖ ≤ δnorm) →
                  t ∈ Icc (0 : ℝ) T →
                  ∃ D₁ D₂ : (A × A) →L[ℝ] (A × A),
                    (∀ h : A × A, D₁ h = Ω₁ h t) ∧
                      (∀ h : A × A, D₂ h = Ω₂ h t) ∧
                        ∃ C : ℝ, 0 ≤ C ∧ ‖D₂ - D₁‖ ≤ C * δnorm := by
  rcases
      CenteredMembership.exists_rescaled_hosted_thirdVariation_centered_membership_clm_package
        (g := g) (x₀ := x₀) (ζ := ζ₁) hζ₁ with
    ⟨ε₁, hε₁, Ω₁, hΩ₁0, hΩ₁der, _hΩ₁add, _hΩ₁smul,
      _centeredRadius₁, _hcenteredRadius₁_nonneg, _hΩ₁mem_centered,
      _hΩ₁add_mem_centered, _hΩ₁smul_mem_centered, hCLM₁⟩
  rcases
      CenteredMembership.exists_rescaled_hosted_thirdVariation_centered_membership_clm_package
        (g := g) (x₀ := x₀) (ζ := ζ₂) hζ₂ with
    ⟨ε₂, hε₂, Ω₂, hΩ₂0, hΩ₂der, _hΩ₂add, _hΩ₂smul,
      _centeredRadius₂, _hcenteredRadius₂_nonneg, _hΩ₂mem_centered,
      _hΩ₂add_mem_centered, _hΩ₂smul_mem_centered, hCLM₂⟩
  have hrest :
      ∀ {T a δnorm : ℝ} {p : A × A} {t : ℝ},
        0 ≤ T →
        T ∈ Icc (-ε₁) ε₁ →
        T ∈ Icc (-ε₂) ε₂ →
        0 ≤ δnorm →
        (∀ τ ∈ Ico (0 : ℝ) T, ζ₁ τ ∈ closedBall p (a + 1)) →
        (∀ τ ∈ Ico (0 : ℝ) T, ζ₂ τ ∈ closedBall p (a + 1)) →
        (∀ τ ∈ Ico (0 : ℝ) T, ‖ζ₂ τ - ζ₁ τ‖ ≤ δnorm) →
        t ∈ Icc (0 : ℝ) T →
        ∃ D₁ D₂ : (A × A) →L[ℝ] (A × A),
          (∀ h : A × A, D₁ h = Ω₁ h t) ∧
            (∀ h : A × A, D₂ h = Ω₂ h t) ∧
              ∃ C : ℝ, 0 ≤ C ∧ ‖D₂ - D₁‖ ≤ C * δnorm := by
    intro T a δnorm p t hT_nonneg hTε₁ hTε₂ hδ hζ₁mem hζ₂mem hζdist ht
    have htε₁ : t ∈ Icc (-ε₁) ε₁ := by
      constructor
      · linarith [hε₁, ht.1]
      · exact ht.2.trans hTε₁.2
    have htε₂ : t ∈ Icc (-ε₂) ε₂ := by
      constructor
      · linarith [hε₂, ht.1]
      · exact ht.2.trans hTε₂.2
    rcases hCLM₁ t htε₁ with ⟨pkg₁⟩
    rcases hCLM₂ t htε₂ with ⟨pkg₂⟩
    let D₁ : (A × A) →L[ℝ] (A × A) := pkg₁.1
    let D₂ : (A × A) →L[ℝ] (A × A) := pkg₂.1
    have hD₁ : ∀ h : A × A, D₁ h = Ω₁ h t := by
      intro h
      simpa [D₁] using pkg₁.2.1 h
    have hD₂ : ∀ h : A × A, D₂ h = Ω₂ h t := by
      intro h
      simpa [D₂] using pkg₂.2.1 h
    have hsub₁ : ∀ τ ∈ Icc (0 : ℝ) T, τ ∈ Icc (-ε₁) ε₁ := by
      intro τ hτ
      constructor
      · linarith [hε₁, hτ.1]
      · exact hτ.2.trans hTε₁.2
    have hsub₂ : ∀ τ ∈ Icc (0 : ℝ) T, τ ∈ Icc (-ε₂) ε₂ := by
      intro τ hτ
      constructor
      · linarith [hε₂, hτ.1]
      · exact hτ.2.trans hTε₂.2
    have hbound :
        ∃ C : ℝ, 0 ≤ C ∧ ‖D₂ - D₁‖ ≤ C * δnorm :=
      TheSelector.selected_endpoint_gronwall_bound
        (g := g) (x₀ := x₀) (ζ₁ := ζ₁) (ζ₂ := ζ₂) (Ω₁ := Ω₁)
        (Ω₂ := Ω₂) (D₁ := D₁) (D₂ := D₂) (T := T) (a := a)
        (δnorm := δnorm) (p := p) (t := t)
        hT_nonneg hδ hζ₁mem hζ₂mem hζdist hΩ₁0 hΩ₂0
        (by
          intro h τ hτ
          exact (hΩ₁der h τ (hsub₁ τ hτ)).mono
            (Icc_subset_Icc (by linarith [hε₁]) hTε₁.2))
        (by
          intro h τ hτ
          exact (hΩ₂der h τ (hsub₂ τ hτ)).mono
            (Icc_subset_Icc (by linarith [hε₂]) hTε₂.2))
        hD₁ hD₂ ht
    exact ⟨D₁, D₂, hD₁, hD₂, hbound⟩
  exact
    ⟨ε₁, hε₁, Ω₁, hΩ₁0, hΩ₁der, ε₂, hε₂, Ω₂, hΩ₂0, hΩ₂der, hrest⟩

end SelectorAssembly
end Poincare
