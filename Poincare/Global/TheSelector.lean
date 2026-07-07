import Poincare.Global.HostedCLM

/-!
# Third-variation selector boundary

This module records the noncomputable selectors that are available from the
current hosted third-variation exports.  It deliberately stays at selector
level: no downstream Cartan/F-transition consumer is imported or invoked.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace TheSelector

universe u v

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "A" => (E × E) × (E × E)

/--
The hosted doubly-augmented base used by `OmegaGronwall`.

In the full source/target selector, the inputs `β`, `Ξ`, and `y` are produced
pointwise from the hosted base and linearized flow exported by
`UniformFlowExport`, together with the second-variation ODE data discharged by
`SecondDischarge`.
-/
def hostedDoublyAugmentedBase
    (β : A → ℝ → A) (Ξ : A → A → ℝ → A) (y : A × A) :
    ℝ → A × A :=
  fun τ => (β y.1 τ, Ξ y.1 y.2 τ)

/-- Indexed spelling of `hostedDoublyAugmentedBase`, i.e. `q ↦ ζ_q`. -/
def selectedZeta
    {Q : Type v} (β : A → ℝ → A) (Ξ : A → A → ℝ → A)
    (y : Q → A × A) (q : Q) : ℝ → A × A :=
  hostedDoublyAugmentedBase β Ξ (y q)

@[simp]
theorem selectedZeta_apply
    {Q : Type v} (β : A → ℝ → A) (Ξ : A → A → ℝ → A)
    (y : Q → A × A) (q : Q) (τ : ℝ) :
    selectedZeta β Ξ y q τ = (β (y q).1 τ, Ξ (y q).1 (y q).2 τ) :=
  rfl

/-- The exact package chosen from `OmegaGronwall` for one paired base. -/
def OmegaPackage
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (_hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) : Type _ :=
  { p : ℝ × ℝ≥0 × ℝ≥0 × (A × A → ℝ → A × A) //
      0 < p.1 ∧
        0 < (p.2.2.1 : ℝ) ∧
          ∀ h : A × A, h ∈ closedBall (0 : A × A) p.2.2.1 →
            p.2.2.2 h 0 = h ∧
              (∀ t ∈ Icc (-p.1) p.1,
                HasDerivWithinAt (p.2.2.2 h)
                  (fderiv ℝ
                    (fun y' : A × A =>
                      let F : A → A :=
                        augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
                      (F y'.1, (fderiv ℝ F y'.1) y'.2))
                    (hostedDoublyAugmentedBase β Ξ y t) (p.2.2.2 h t))
                  (Icc (-p.1) p.1) t) ∧
              ∀ t ∈ Icc (-p.1) p.1,
                p.2.2.2 h t ∈ closedBall (0 : A × A) p.2.1 }

omit [T2Space M] in
theorem exists_omegaPackage
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    Nonempty (OmegaPackage (g := g) x₀ hpaired) := by
  rcases
      GeodesicTransport.exists_hosted_thirdVariation_solution_family_on_paired_base
        (g := g) (x₀ := x₀) (β := β) (Ξ := Ξ) (y := y) hpaired with
    ⟨ε, hε, a, r, hr, Ω, hΩ⟩
  exact ⟨⟨(ε, a, r, Ω), hε, hr, hΩ⟩⟩

/-- The selected `OmegaGronwall` package for the paired base. -/
def selectedOmegaPackage
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    OmegaPackage (g := g) x₀ hpaired :=
  Classical.choice (exists_omegaPackage (g := g) (x₀ := x₀) hpaired)

/-- The selected local third-variation time radius. -/
def selectedOmegaEpsilon
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) : ℝ :=
  (selectedOmegaPackage (g := g) x₀ hpaired).1.1

/-- The selected closed-ball bound for the third-variation family. -/
def selectedOmegaBound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) : ℝ≥0 :=
  (selectedOmegaPackage (g := g) x₀ hpaired).1.2.1

/-- The selected perturbation radius for the third-variation family. -/
def selectedOmegaRadius
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) : ℝ≥0 :=
  (selectedOmegaPackage (g := g) x₀ hpaired).1.2.2.1

/-- The selected hosted third-variation family `Ω`. -/
def selectedOmega
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    A × A → ℝ → A × A :=
  (selectedOmegaPackage (g := g) x₀ hpaired).1.2.2.2

/-- Indexed spelling of the selected hosted third-variation family, `q ↦ Ω_q`. -/
def selectedOmegaAt
    {Q : Type v} (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (β : A → ℝ → A) (Ξ : A → A → ℝ → A) (y : Q → A × A)
    (hpaired : ∀ q : Q, Continuous (selectedZeta β Ξ y q)) (q : Q) :
    A × A → ℝ → A × A :=
  selectedOmega (g := g) x₀ (β := β) (Ξ := Ξ) (y := y q) (hpaired q)

omit [T2Space M] in
theorem selectedOmegaEpsilon_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    0 < selectedOmegaEpsilon (g := g) x₀ hpaired :=
  (selectedOmegaPackage (g := g) x₀ hpaired).2.1

omit [T2Space M] in
theorem selectedOmegaRadius_pos
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    0 < (selectedOmegaRadius (g := g) x₀ hpaired : ℝ) :=
  (selectedOmegaPackage (g := g) x₀ hpaired).2.2.1

omit [T2Space M] in
theorem selectedOmega_spec
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {β : A → ℝ → A} {Ξ : A → A → ℝ → A} {y : A × A}
    (hpaired : Continuous (hostedDoublyAugmentedBase β Ξ y)) :
    ∀ h : A × A,
      h ∈ closedBall (0 : A × A) (selectedOmegaRadius (g := g) x₀ hpaired) →
        selectedOmega (g := g) x₀ hpaired h 0 = h ∧
          (∀ t ∈ Icc (-(selectedOmegaEpsilon (g := g) x₀ hpaired))
              (selectedOmegaEpsilon (g := g) x₀ hpaired),
            HasDerivWithinAt (selectedOmega (g := g) x₀ hpaired h)
              (fderiv ℝ
                (fun y' : A × A =>
                  let F : A → A :=
                    augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
                  (F y'.1, (fderiv ℝ F y'.1) y'.2))
                (hostedDoublyAugmentedBase β Ξ y t)
                (selectedOmega (g := g) x₀ hpaired h t))
              (Icc (-(selectedOmegaEpsilon (g := g) x₀ hpaired))
                (selectedOmegaEpsilon (g := g) x₀ hpaired)) t) ∧
          ∀ t ∈ Icc (-(selectedOmegaEpsilon (g := g) x₀ hpaired))
              (selectedOmegaEpsilon (g := g) x₀ hpaired),
            selectedOmega (g := g) x₀ hpaired h t ∈
              closedBall (0 : A × A) (selectedOmegaBound (g := g) x₀ hpaired) :=
  (selectedOmegaPackage (g := g) x₀ hpaired).2.2.2

/-- The exact endpoint-CLM package produced by `HostedCLM`. -/
def HostedCLMPackage
    {Ω : A × A → ℝ → A × A} {T : ℝ} : Type _ :=
  { D : (A × A) →L[ℝ] (A × A) //
      (∀ η : A × A, D η = Ω η T) ∧
        ∀ᶠ h in 𝓝 (0 : A × A),
          Ω h 0 = h ∧ Ω h T = D h }

omit [T2Space M] in
theorem exists_hostedCLMPackage
    [FiniteDimensional ℝ (A × A)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → A × A} {Ω : A × A → ℝ → A × A}
    {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax) {a r L K : ℝ≥0}
    (hpl : ∀ η : A × A,
      IsPicardLindelof
        (fun t ξ =>
          fderiv ℝ
            (fun y' : A × A =>
              let F : A → A :=
                augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
              (F y'.1, (fderiv ℝ F y'.1) y'.2))
            (ζ t) ξ)
        (tmin := tmin) (tmax := tmax)
        ⟨(0 : ℝ), hzero⟩ η a r L K)
    (hΩ0 : ∀ η : A × A, Ω η 0 = η)
    (hΩder : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ω η)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ t) (Ω η t))
        (Icc tmin tmax) t)
    (hΩmem : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t ∈ closedBall η a)
    (hadd_mem : ∀ η η' : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t + Ω η' t ∈ closedBall (η + η') a)
    (hsmul_mem : ∀ (c : ℝ) (η : A × A), ∀ t ∈ Icc tmin tmax,
      c • Ω η t ∈ closedBall (c • η) a) :
    Nonempty (HostedCLMPackage (Ω := Ω) (T := T)) := by
  rcases
      GeodesicTransport.chartChristoffel_hostedThirdVariation_endpoint_clm_of_linearODE_uniqueOn_Icc
        (g := g) (x₀ := x₀) (ζ := ζ) (Ω := Ω) hzero hT hpl hΩ0
        hΩder hΩmem hadd_mem hsmul_mem with
    ⟨D, hD, hD_eventually⟩
  have hD_eventually' :
      ∀ᶠ h in 𝓝 (0 : A × A), Ω h 0 = h ∧ Ω h T = D h := by
    filter_upwards [hD_eventually] with h hh
    exact ⟨hh.1, hh.2.2⟩
  exact ⟨⟨D, hD, hD_eventually'⟩⟩

/-- The selected endpoint CLM `D` from the `HostedCLM` construction. -/
def selectedHostedCLM
    [FiniteDimensional ℝ (A × A)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → A × A} {Ω : A × A → ℝ → A × A}
    {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax) {a r L K : ℝ≥0}
    (hpl : ∀ η : A × A,
      IsPicardLindelof
        (fun t ξ =>
          fderiv ℝ
            (fun y' : A × A =>
              let F : A → A :=
                augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
              (F y'.1, (fderiv ℝ F y'.1) y'.2))
            (ζ t) ξ)
        (tmin := tmin) (tmax := tmax)
        ⟨(0 : ℝ), hzero⟩ η a r L K)
    (hΩ0 : ∀ η : A × A, Ω η 0 = η)
    (hΩder : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ω η)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ t) (Ω η t))
        (Icc tmin tmax) t)
    (hΩmem : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t ∈ closedBall η a)
    (hadd_mem : ∀ η η' : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t + Ω η' t ∈ closedBall (η + η') a)
    (hsmul_mem : ∀ (c : ℝ) (η : A × A), ∀ t ∈ Icc tmin tmax,
      c • Ω η t ∈ closedBall (c • η) a) :
    (A × A) →L[ℝ] (A × A) :=
  (Classical.choice
    (exists_hostedCLMPackage (g := g) (x₀ := x₀) (ζ := ζ) (Ω := Ω)
      hzero hT hpl hΩ0 hΩder hΩmem hadd_mem hsmul_mem)).1

omit [T2Space M] in
theorem selectedHostedCLM_endpoint_eq
    [FiniteDimensional ℝ (A × A)]
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → A × A} {Ω : A × A → ℝ → A × A}
    {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    (hT : T ∈ Icc tmin tmax) {a r L K : ℝ≥0}
    (hpl : ∀ η : A × A,
      IsPicardLindelof
        (fun t ξ =>
          fderiv ℝ
            (fun y' : A × A =>
              let F : A → A :=
                augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
              (F y'.1, (fderiv ℝ F y'.1) y'.2))
            (ζ t) ξ)
        (tmin := tmin) (tmax := tmax)
        ⟨(0 : ℝ), hzero⟩ η a r L K)
    (hΩ0 : ∀ η : A × A, Ω η 0 = η)
    (hΩder : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt (Ω η)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ t) (Ω η t))
        (Icc tmin tmax) t)
    (hΩmem : ∀ η : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t ∈ closedBall η a)
    (hadd_mem : ∀ η η' : A × A, ∀ t ∈ Icc tmin tmax,
      Ω η t + Ω η' t ∈ closedBall (η + η') a)
    (hsmul_mem : ∀ (c : ℝ) (η : A × A), ∀ t ∈ Icc tmin tmax,
      c • Ω η t ∈ closedBall (c • η) a) :
    ∀ η : A × A,
      selectedHostedCLM (g := g) (x₀ := x₀) (ζ := ζ) (Ω := Ω)
          hzero hT hpl hΩ0 hΩder hΩmem hadd_mem hsmul_mem η =
        Ω η T :=
  (Classical.choice
    (exists_hostedCLMPackage (g := g) (x₀ := x₀) (ζ := ζ) (Ω := Ω)
      hzero hT hpl hΩ0 hΩder hΩmem hadd_mem hsmul_mem)).2.1

omit [T2Space M] in
/--
Cross-point Gronwall transfer once the selected endpoint CLMs have the exact
endpoint equalities required by `OmegaGronwall`.
-/
theorem selected_endpoint_gronwall_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ₁ ζ₂ : ℝ → A × A}
    {Ω₁ Ω₂ : A × A → ℝ → A × A}
    {D₁ D₂ : (A × A) →L[ℝ] (A × A)}
    {T a δnorm : ℝ} {p : A × A} {t : ℝ}
    (hT : 0 ≤ T) (hδ : 0 ≤ δnorm)
    (hζ₁mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₁ τ ∈ closedBall p (a + 1))
    (hζ₂mem : ∀ τ ∈ Ico (0 : ℝ) T, ζ₂ τ ∈ closedBall p (a + 1))
    (hζdist : ∀ τ ∈ Ico (0 : ℝ) T, ‖ζ₂ τ - ζ₁ τ‖ ≤ δnorm)
    (hΩ₁0 : ∀ h : A × A, Ω₁ h 0 = h)
    (hΩ₂0 : ∀ h : A × A, Ω₂ h 0 = h)
    (hΩ₁der : ∀ h : A × A, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₁ h)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ₁ τ) (Ω₁ h τ))
        (Icc (0 : ℝ) T) τ)
    (hΩ₂der : ∀ h : A × A, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (Ω₂ h)
        (fderiv ℝ
          (fun y' : A × A =>
            let F : A → A :=
              augmentedGeodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
            (F y'.1, (fderiv ℝ F y'.1) y'.2))
          (ζ₂ τ) (Ω₂ h τ))
        (Icc (0 : ℝ) T) τ)
    (hD₁ : ∀ h : A × A, D₁ h = Ω₁ h t)
    (hD₂ : ∀ h : A × A, D₂ h = Ω₂ h t)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ C : ℝ, 0 ≤ C ∧ ‖D₂ - D₁‖ ≤ C * δnorm := by
  exact
    GeodesicTransport.chartChristoffel_thirdVariation_endpoint_gronwall_bound
      (g := g) (x₀ := x₀) (ζ₁ := ζ₁) (ζ₂ := ζ₂) (Ω₁ := Ω₁)
      (Ω₂ := Ω₂) (D₁ := D₁) (D₂ := D₂) (T := T) (a := a)
      (δnorm := δnorm) (p := p) (t := t) hT hδ hζ₁mem hζ₂mem
      hζdist hΩ₁0 hΩ₂0 hΩ₁der hΩ₂der
      (fun h => (hD₁ h).symm) (fun h => (hD₂ h).symm) ht

end TheSelector
end Poincare
