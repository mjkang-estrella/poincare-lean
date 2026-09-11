import Poincare.Global.ClosedLaplacianStokesProducer
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Calculus.LineDeriv.Basic

noncomputable section
open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology ENNReal NNReal
set_option autoImplicit false
universe u
namespace Poincare.ClosedLaplacianStokesGlobalCoefficients

variable {n : ℕ}
local notation "E" => ClosedSmoothModel n

/-- Multiplication by a smooth cutoff extends a chartwise smooth scalar globally. -/
theorem contDiff_cutoff_mul {U : Set E} {χ F : E → ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ) (hχU : tsupport χ ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z ↦ χ z * F z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul ((hF z hz).contDiffAt (hU.mem_nhds hz))
  · have hzero := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (hχU h))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

/-- A compact subset of an open coordinate domain has a smooth cutoff equal to one nearby. -/
theorem exists_cutoff_of_isCompact {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, ∀ᶠ y in 𝓝 z, χ y = 1) ∧ (∀ z, χ z ∈ Icc 0 1) := by
  obtain ⟨χ, hzero, hone, hbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
      hU.isClosed_compl hK.isClosed
      (disjoint_compl_left_iff_subset.mpr hKU) (n := ⊤)
  refine ⟨χ, χ.contMDiff.contDiff, ?_, ?_, hbounds⟩
  · intro z hz
    by_contra hzU
    have hloc : (fun y ↦ χ y) =ᶠ[𝓝 z] 0 :=
      hzero.filter_mono (nhds_le_nhdsSet hzU)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hz
  · intro z hz
    exact hone.filter_mono (nhds_le_nhdsSet hz)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) ∞ M]
local notation "I" => closedSmoothModelWithCorners n

/-- The genuine weight and inverse metric extend smoothly with local agreement on a compact set. -/
theorem exists_global_coefficients_on_compact
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (extChartAt I p).target) :
    ∃ (w : E → ℝ) (a : E → Fin n → Fin n → ℝ),
      ContDiff ℝ ∞ w ∧ (∀ i j, ContDiff ℝ ∞ (fun z ↦ a z i j)) ∧
      (∀ z ∈ K, w =ᶠ[𝓝 z] (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y))) ∧
      (∀ z ∈ K, a =ᶠ[𝓝 z] (fun y ↦ ((inverseChartPullbackGramMatrixField g p y)⁻¹ :
        Matrix (Fin n) (Fin n) ℝ))) ∧
      (∀ z : (extChartAt I p).target, (z : E) ∈ K →
        w z = (rawHausdorffLebesgueScale n : ℝ) * inverseChartPullbackVolumeDensity g p z) := by
  obtain ⟨χ, hχ, hχU, hone, _⟩ := exists_cutoff_of_isCompact hK
    (isOpen_extChartAt_target p) hKU
  let W := fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
    VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)
  let A := fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹
  refine ⟨fun y ↦ χ y * W y, fun y i j ↦ χ y * A y i j, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartWeight_regular g p).1
  · intro i j
    exact contDiff_cutoff_mul (isOpen_extChartAt_target p) hχ hχU
      (ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j)
  · intro z hz
    filter_upwards [hone z hz] with y hy
    simp only [hy, one_mul, W]
  · intro z hz
    filter_upwards [hone z hz] with y hy
    funext i j
    change χ y * A y i j = A y i j
    rw [hy, one_mul]
  · intro z hz
    change χ z * W z = _
    rw [(hone z hz).self_of_nhds, one_mul]
    exact (ClosedLaplacianStokesProducer.chartWeight_regular g p).2 z

/-- A finite chart cover shrinks to open regions with compact coordinate closures. -/
theorem exists_shrunk_chart_cover
    (C : FiniteExtendedChartCover (n := n) (M := M)) :
    ∃ V : Fin C.chartCount → Set M,
      (⋃ i, V i) = univ ∧ (∀ i, IsOpen (V i)) ∧
      (∀ i, closure (V i) ⊆ (extChartAt I (C.anchor i)).source) ∧
      (∀ i, IsCompact ((extChartAt I (C.anchor i)) '' closure (V i))) ∧
      (∀ i, (extChartAt I (C.anchor i)) '' closure (V i) ⊆
        (extChartAt I (C.anchor i)).target) ∧
      ∃ ρ : SmoothPartitionOfUnity (Fin C.chartCount) I M univ, ρ.IsSubordinate V := by
  obtain ⟨V, hcover, hopen, hclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i ↦ isOpen_extChartAt_source (C.anchor i))
    (fun _ ↦ Set.toFinite _) C.sources_cover
  refine ⟨V, hcover, hopen, hclosure, ?_, ?_, ?_⟩
  · intro i
    exact isClosed_closure.isCompact.image_of_continuousOn
      ((continuousOn_extChartAt (C.anchor i)).mono (hclosure i))
  · intro i
    exact image_subset_iff.mpr (fun x hx ↦ (extChartAt I (C.anchor i)).map_source
      (hclosure i hx))
  · apply SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ V hopen
    rw [hcover]

/-- Jacobi's density formula in any spatial coordinate direction. -/
theorem fderiv_chartWeight
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) :
    fderiv ℝ (fun y ↦ (rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p y)) z v =
      (1 / 2 : ℝ) * ((rawHausdorffLebesgueScale n : ℝ) *
        VolumeDensity.chartVolumeDensity (inverseChartPullbackGramMatrixField g p z)) *
        ∑ i, ∑ j, (inverseChartPullbackGramMatrixField g p z)⁻¹ i j *
          fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y j i) z v := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (i j : Fin n) : DifferentiableAt ℝ (fun y ↦ G y i j) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p i j z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hline := VolumeDensity.hasDerivAt_chartVolumeDensity_of_det_ne_zero
    (G := fun t : ℝ ↦ G (z + t • v))
    (G' := fun i j ↦ fderiv ℝ (fun y ↦ G y i j) z v)
    (fun i j ↦ (hG i j).hasFDerivAt.hasLineDerivAt v)
    (by simpa only [zero_smul, add_zero] using hdet)
  have hweight := (((ClosedLaplacianStokesProducer.chartWeight_regular g p).1 z hz).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have heq := ((hline.const_mul (rawHausdorffLebesgueScale n : ℝ)).unique
    (hweight.hasFDerivAt.hasLineDerivAt v)).symm
  simpa only [zero_smul, add_zero, mul_assoc, mul_left_comm] using heq

/-- Differentiating the inverse identity gives the full inverse-matrix derivative. -/
theorem deriv_matrix_inv_entry {A : ℝ → Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun s ↦ A s i j) t)
    (hdet : (A t).det ≠ 0) (i j : Fin n) :
    deriv (fun s ↦ (A s)⁻¹ i j) t =
      -(∑ k, ∑ l, (A t)⁻¹ i k * deriv (fun s ↦ A s k l) t * (A t)⁻¹ l j) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := (A t)⁻¹
  let D : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ A s k l) t
  let Q : Matrix (Fin n) (Fin n) ℝ := fun k l ↦ deriv (fun s ↦ (A s)⁻¹ k l) t
  have hB (k l : Fin n) : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹ k l) t :=
    differentiableAt_matrix_inv_entry_of_entries hA hdet k l
  have hlocal : ∀ᶠ s in 𝓝 t, (A s).det ≠ 0 :=
    (differentiableAt_matrix_det_of_entries hA).continuousAt.eventually_ne hdet
  have hprod : Q * A t + B * D = 0 := by
    ext k l
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun m _ ↦ (hB k m).hasDerivAt.mul (hA m l).hasDerivAt)
    have heq : (fun s ↦ ∑ m, (A s)⁻¹ k m * A s m l) =ᶠ[𝓝 t]
        (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℝ) k l) := by
      filter_upwards [hlocal] with s hs
      exact congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T k l)
        (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
    have hzero := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const t _)
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      ← Finset.sum_add_distrib, Q, B, D] using hzero
  have hab : A t * B = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  have hq : Q = -(B * D * B) := by
    have hh := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T * B) hprod
    dsimp only at hh
    rw [add_mul, Matrix.mul_assoc, hab, mul_one, zero_mul] at hh
    exact eq_neg_of_add_eq_zero_left hh
  have hentry := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ T i j) hq
  simp only [Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul, Q, B, D] at hentry
  rw [Finset.sum_comm] at hentry
  exact hentry

/-- The inverse Gram entries have the usual spatial derivative. -/
theorem fderiv_chartInverseMetric
    (g : ClosedSmoothRiemannianMetric n M) (p : M) {z : E}
    (hz : z ∈ (extChartAt I p).target) (v : E) (i j : Fin n) :
    fderiv ℝ (fun y ↦ (inverseChartPullbackGramMatrixField g p y)⁻¹ i j) z v =
      -(∑ k, ∑ l, (inverseChartPullbackGramMatrixField g p z)⁻¹ i k *
        fderiv ℝ (fun y ↦ inverseChartPullbackGramMatrixField g p y k l) z v *
        (inverseChartPullbackGramMatrixField g p z)⁻¹ l j) := by
  let G := inverseChartPullbackGramMatrixField g p
  have hG (k l : Fin n) : DifferentiableAt ℝ (fun y ↦ G y k l) z :=
    ((contDiffOn_inverseChartPullbackGramMatrixField_entry g p k l z hz).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hdet : (G z).det ≠ 0 := by
    dsimp [G]
    rw [← inverseChartPullbackGramMatrix_eq_field g p ⟨z, hz⟩]
    exact (inverseChartPullbackGramMatrix_posDef g p ⟨z, hz⟩).det_pos.ne'
  have hInv := (((ClosedLaplacianStokesProducer.chartInverseMetric_contDiffOn g p i j) z hz).contDiffAt ((isOpen_extChartAt_target p).mem_nhds hz)).differentiableAt (by simp)
  have hd := deriv_matrix_inv_entry (A := fun s : ℝ ↦ G (z + s • v)) (t := 0)
    (fun k l ↦ ((hG k l).hasFDerivAt.hasLineDerivAt v).differentiableAt)
    (by simpa only [zero_smul, add_zero] using hdet) i j
  rw [(hInv.hasFDerivAt.hasLineDerivAt v).deriv] at hd
  simp only [zero_smul, add_zero] at hd
  simpa only [((hG _ _).hasFDerivAt.hasLineDerivAt v).deriv] using hd

end Poincare.ClosedLaplacianStokesGlobalCoefficients
