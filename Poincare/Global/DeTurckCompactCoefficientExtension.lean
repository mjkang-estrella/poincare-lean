import Poincare.Global.DeTurckCompactCoefficientDefinitions
import Poincare.Global.BufferedFrozenParabolicSolver

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 100
open Set Filter
open scoped Manifold ContDiff Topology BigOperators
universe u
namespace Poincare.DeTurckCompactCoefficients
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Poincare.DeTurckPrincipalSecondJet.Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E) := ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := (Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E →L[ℝ] Poincare.DeTurckPrincipalSecondJet.E)) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Jet2 := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.E) (F := Poincare.DeTurckPrincipalSecondJet.Jet1) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedAddCommGroup
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.normedSpace
local instance : NormedAddCommGroup Poincare.DeTurckJetLinearization.Variables := Prod.normedAddCommGroup
local instance : NormedSpace ℝ Poincare.DeTurckJetLinearization.Variables := Prod.normedSpace
local instance : AddCommMonoid (Poincare.DeTurckPrincipalSecondJet.Bilin × Poincare.DeTurckPrincipalSecondJet.Jet1) := Prod.instAddCommMonoid
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Bilin →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Bilin) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)
local instance : NormedAddCommGroup (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedAddCommGroup
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (Poincare.DeTurckPrincipalSecondJet.Jet1 →L[ℝ] Poincare.DeTurckPrincipalSecondJet.Bilin) := ContinuousLinearMap.toNormedSpace
 (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Poincare.DeTurckPrincipalSecondJet.Jet1) (F := Poincare.DeTurckPrincipalSecondJet.Bilin) (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

/-- Buffer the actual lower coefficients and construct uniformly bounded scalar carriers. -/
theorem exists_actual_compact_carriers :
∀ (M : Type u) [TopologicalSpace M] [T2Space M]
[ChartedSpace Poincare.DeTurckPrincipalSecondJet.E M]
[IsManifold (Poincare.closedSmoothModelWithCorners 3) ((⊤ : ENat) : WithTop ENat) M]
(g0 bg : Poincare.ClosedSmoothRiemannianMetric 3 M) (anchor : M)
(ξ : Poincare.DeTurckPrincipalSecondJet.E → ℝ) (α : ℝ), HasCompactSupport ξ → tsupport ξ ⊆ Poincare.DeTurckCompactCoefficients.zone anchor →
0 < α → α < 1 →
∃ η : Poincare.DeTurckPrincipalSecondJet.E → ℝ,
ContDiff ℝ ((⊤ : ENat) : WithTop ENat) η ∧ HasCompactSupport η ∧
tsupport η ⊆ Poincare.DeTurckCompactCoefficients.zone anchor ∧
(∀ z ∈ tsupport ξ, Filter.Eventually (fun y => η y = 1) (nhds z)) ∧
(∀ z, η z ∈ Set.Icc 0 1) ∧
(∀ a b c d : Fin 3,
 ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => η z * Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d z) ∧
 HasCompactSupport (fun z => η z * Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d z) ∧
 (∀ z ∈ tsupport ξ, Filter.Eventually (fun y => η y * Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d y = Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d y) (nhds z))) ∧
(∀ p a b c d : Fin 3,
 ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => η z * Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d z) ∧
 HasCompactSupport (fun z => η z * Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d z) ∧
 (∀ z ∈ tsupport ξ, Filter.Eventually (fun y => η y * Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d y = Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d y) (nhds z))) ∧
∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ T : ℝ,
 ∃ c0 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Poincare.ParabolicHolder.Y (E := Poincare.DeTurckPrincipalSecondJet.E) α T ℝ),
 ∃ c1 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → (Poincare.ParabolicHolder.Y (E := Poincare.DeTurckPrincipalSecondJet.E) α T ℝ),
 (∀ a b c d : Fin 3, ∀ q ∈ Poincare.ParabolicHolder.cylinder T, c0 a b c d q = η q.2 * Poincare.DeTurckCompactCoefficients.raw0 g0 bg anchor a b c d q.2) ∧
 (∀ p a b c d : Fin 3, ∀ q ∈ Poincare.ParabolicHolder.cylinder T, c1 p a b c d q = η q.2 * Poincare.DeTurckCompactCoefficients.raw1 g0 bg anchor p a b c d q.2) ∧
 ∀ c d : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3, ‖c0 a b c d‖) ≤ C0 ∧
 (∑ a : Fin 3, ∑ b : Fin 3, ∑ p : Fin 3, ‖c1 p a b c d‖) ≤ C1 := by
  intro M _ _ _ _ g0 bg anchor ξ α hcξ hξU hα hα1
  classical
  have hactual := DeTurckActualSpatialCoefficients.actual_spatial_coefficients M g0 bg anchor
  have hU : IsOpen (zone anchor) := hactual.1
  have hfield0 : ContDiffOn ℝ ∞ (field0 g0 bg anchor) (zone anchor) :=
    hactual.2.2.2.1
  have hfield1 : ContDiffOn ℝ ∞ (field1 g0 bg anchor) (zone anchor) :=
    hactual.2.2.2.2.1
  obtain ⟨η, hη, hcη, hηU, hηξ, hη01⟩ :=
    BufferedFrozenParabolicSolver.exists_buffered_cutoff hcξ hU hξU
  have hraw0 (a b c d : Fin 3) :
      ContDiffOn ℝ ∞ (raw0 g0 bg anchor a b c d) (zone anchor) := by
    exact (DeTurckInverseEntryDerivative.entryCLM c d).contDiff.comp_contDiffOn
      (hfield0.clm_apply contDiffOn_const)
  have hraw1 (p a b c d : Fin 3) :
      ContDiffOn ℝ ∞ (raw1 g0 bg anchor p a b c d) (zone anchor) := by
    exact (DeTurckInverseEntryDerivative.entryCLM c d).contDiff.comp_contDiffOn
      (hfield1.clm_apply contDiffOn_const)
  have h0 (a b c d : Fin 3) :
      ContDiff ℝ ∞ (fun z => η z * raw0 g0 bg anchor a b c d z) :=
    ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul hU hη hηU (hraw0 a b c d)
  have h1 (p a b c d : Fin 3) :
      ContDiff ℝ ∞ (fun z => η z * raw1 g0 bg anchor p a b c d z) :=
    ClosedLaplacianStokesGlobalCoefficients.contDiff_cutoff_mul hU hη hηU (hraw1 p a b c d)
  have hex0 (a b c d : Fin 3) :=
    ParabolicCutoffCommutator.exists_cutoff_carrier (h0 a b c d)
      hcη.mul_right hα hα1
  have hex1 (p a b c d : Fin 3) :=
    ParabolicCutoffCommutator.exists_cutoff_carrier (h1 p a b c d)
      hcη.mul_right hα hα1
  choose K0 hK0 c0 hc0 using hex0
  choose K1 hK1 c1 hc1 using hex1
  let row0 (c d : Fin 3) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, K0 a b c d
  let row1 (c d : Fin 3) : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, ∑ p : Fin 3, K1 p a b c d
  have hrow0 (c d : Fin 3) : 0 ≤ row0 c d :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hK0 a b c d))
  have hrow1 (c d : Fin 3) : 0 ≤ row1 c d :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ =>
      Finset.sum_nonneg (fun p _ => hK1 p a b c d)))
  refine ⟨η, hη, hcη, hηU, hηξ, hη01, ?_, ?_,
    ∑ c : Fin 3, ∑ d : Fin 3, row0 c d,
    ∑ c : Fin 3, ∑ d : Fin 3, row1 c d,
    Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => hrow0 c d)),
    Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => hrow1 c d)), ?_⟩
  · intro a b c d
    refine ⟨h0 a b c d, hcη.mul_right, ?_⟩
    intro z hz
    filter_upwards [hηξ z hz] with y hy
    simp only [hy, one_mul]
  · intro p a b c d
    refine ⟨h1 p a b c d, hcη.mul_right, ?_⟩
    intro z hz
    filter_upwards [hηξ z hz] with y hy
    simp only [hy, one_mul]
  · intro T
    refine ⟨fun a b c d => c0 a b c d T,
      fun p a b c d => c1 p a b c d T,
      fun a b c d q hq => (hc0 a b c d T).1 q hq,
      fun p a b c d q hq => (hc1 p a b c d T).1 q hq, ?_⟩
    intro c d
    constructor
    · apply (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum
        (fun b _ => (hc0 a b c d T).2))).trans
      exact (Finset.single_le_sum (fun d _ => hrow0 c d) (Finset.mem_univ d)).trans
        (Finset.single_le_sum (fun c _ => Finset.sum_nonneg (fun d _ => hrow0 c d))
          (Finset.mem_univ c))
    · apply (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum
        (fun b _ => Finset.sum_le_sum (fun p _ => (hc1 p a b c d T).2)))).trans
      exact (Finset.single_le_sum (fun d _ => hrow1 c d) (Finset.mem_univ d)).trans
        (Finset.single_le_sum (fun c _ => Finset.sum_nonneg (fun d _ => hrow1 c d))
          (Finset.mem_univ c))

end Poincare.DeTurckCompactCoefficients
