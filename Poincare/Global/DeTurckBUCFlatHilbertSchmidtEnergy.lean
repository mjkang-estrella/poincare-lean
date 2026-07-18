import Poincare.Global.DeTurckBUCQuasilinearDifferenceEnergy
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Flat chart Hilbert--Schmidt energy for DeTurck differences

The common-chart coefficient split exposes the ordinary Euclidean Laplacian
of every scalar metric entry.  This file packages the finitely many entries
in the standard orthonormal basis into a Euclidean space.  Its squared norm is
the chart Hilbert--Schmidt energy.  A direct product-Laplacian calculation
then proves the exact flat Bochner identity and its principal inequality.

The last section isolates chart-connection corrections as lower-order entry
vectors and proves the compact-track operator bound that turns every
continuous linear lower-order action into a uniform reaction coefficient.
-/

noncomputable section

open Filter Function Set InnerProductSpace
open scoped Topology InnerProductSpace Laplacian Manifold ContDiff NNReal
  BigOperators

namespace Poincare

section FlatScalarBochner

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Iterated differentiation along an affine line is the ambient iterated
Fréchet derivative evaluated repeatedly on the line direction. -/
theorem iteratedDeriv_affineLine_eq_iteratedFDeriv
    {m : ℕ} (f : E → ℝ) (hf : ContDiff ℝ m f) (x e : E) :
    iteratedDeriv m (fun s : ℝ ↦ f (x + s • e)) 0 =
      iteratedFDeriv ℝ m f x (fun _ ↦ e) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ e
  let fshift : E → ℝ := fun z ↦ f (x + z)
  have hfshift : ContDiff ℝ m fshift := by
    exact hf.comp (contDiff_const.add contDiff_id)
  have hcomp := L.iteratedFDeriv_comp_right hfshift 0 (i := m) le_rfl
  have happ := congrArg (fun A ↦ A (fun _ : Fin m ↦ (1 : ℝ))) hcomp
  change iteratedFDeriv ℝ m (fshift ∘ L) 0 (fun _ ↦ 1) = _ at happ
  dsimp only [fshift] at happ
  simp only [L, ContinuousLinearMap.toSpanSingleton_apply, zero_smul] at happ
  rw [iteratedFDeriv_comp_add_left m x 0] at happ
  simpa only [iteratedDeriv, L, Function.comp_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, add_zero]
    using happ

omit [FiniteDimensional ℝ E] in
/-- Directional second derivative of a square. -/
theorem iteratedFDeriv_sq_apply_two
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x e : E) :
    iteratedFDeriv ℝ 2 (fun y ↦ f y ^ 2) x ![e, e] =
      2 * f x * iteratedFDeriv ℝ 2 f x ![e, e] +
        2 * (fderiv ℝ f x e) ^ 2 := by
  let line : ℝ → ℝ := fun s ↦ f (x + s • e)
  have hline : ContDiff ℝ 2 line := by
    exact hf.comp (contDiff_const.add
      (contDiff_id.smul contDiff_const))
  have hmul := iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
    hline.contDiffAt hline.contDiffAt
  have hmul' :
      iteratedDeriv 2 (fun s ↦ line s ^ 2) 0 =
        2 * line 0 * iteratedDeriv 2 line 0 +
          2 * (iteratedDeriv 1 line 0) ^ 2 := by
    rw [show (fun s ↦ line s ^ 2) = line * line by
      funext s
      simp only [Pi.mul_apply, pow_two]]
    rw [hmul]
    norm_num [Finset.sum_range_succ]
    ring
  have hsq := iteratedDeriv_affineLine_eq_iteratedFDeriv
    (fun y ↦ f y ^ 2) (hf.pow 2) x e
  have htwo := iteratedDeriv_affineLine_eq_iteratedFDeriv f hf x e
  have hone := iteratedDeriv_affineLine_eq_iteratedFDeriv (m := 1) f
    (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)) x e
  rw [hsq, htwo, hone] at hmul'
  have hvec : (fun _ : Fin 2 ↦ e) = ![e, e] := by
    funext i
    fin_cases i <;> rfl
  simpa only [hvec, line, zero_smul, add_zero, iteratedFDeriv_one_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons] using hmul'

/-- Exact Euclidean product-Laplacian identity for a scalar square. -/
theorem flat_laplacian_sq
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    (Δ fun y ↦ f y ^ 2) x =
      2 * f x * (Δ f) x +
        2 * ∑ k : Fin (Module.finrank ℝ E),
          (fderiv ℝ f x ((stdOrthonormalBasis ℝ E) k)) ^ 2 := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_sq_apply_two f hf x]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]

/-- Flat scalar principal Bochner inequality. -/
theorem two_mul_value_mul_flat_laplacian_le_flat_laplacian_sq
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    2 * f x * (Δ f) x ≤ (Δ fun y ↦ f y ^ 2) x := by
  rw [flat_laplacian_sq f hf x]
  have hnonneg : 0 ≤
      2 * ∑ k : Fin (Module.finrank ℝ E),
        (fderiv ℝ f x ((stdOrthonormalBasis ℝ E) k)) ^ 2 := by
    positivity
  linarith

end FlatScalarBochner

section ChartHilbertSchmidtEnergy

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Ordered pairs indexing all matrix entries in the standard orthonormal
basis of the coordinate model. -/
abbrev CoordinateTensorEntryIndex (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)

/-- The finitely many entries of a continuous coordinate bilinear form,
equipped with their Euclidean `L²` norm. -/
def coordinateTensorEntryVector (H : E →L[ℝ] E →L[ℝ] ℝ) :
    EuclideanSpace ℝ (CoordinateTensorEntryIndex E) :=
  WithLp.toLp 2 fun p ↦
    H ((stdOrthonormalBasis ℝ E) p.1)
      ((stdOrthonormalBasis ℝ E) p.2)

@[simp] theorem coordinateTensorEntryVector_apply
    (H : E →L[ℝ] E →L[ℝ] ℝ) (p : CoordinateTensorEntryIndex E) :
    coordinateTensorEntryVector H p =
      H ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2) :=
  rfl

/-- Squared chart Hilbert--Schmidt energy. -/
def coordinateTensorHilbertSchmidtEnergy
    (H : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ‖coordinateTensorEntryVector H‖ ^ 2

theorem coordinateTensorHilbertSchmidtEnergy_eq_sum_sq
    (H : E →L[ℝ] E →L[ℝ] ℝ) :
    coordinateTensorHilbertSchmidtEnergy H =
      ∑ p : CoordinateTensorEntryIndex E,
        (H ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2)) ^ 2 := by
  rw [coordinateTensorHilbertSchmidtEnergy,
    EuclideanSpace.real_norm_sq_eq]
  simp only [coordinateTensorEntryVector_apply]

/-- Hilbert--Schmidt pairing of two coordinate bilinear forms. -/
def coordinateTensorHilbertSchmidtPairing
    (H R : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ⟪coordinateTensorEntryVector H, coordinateTensorEntryVector R⟫_ℝ

theorem coordinateTensorHilbertSchmidtPairing_eq_sum
    (H R : E →L[ℝ] E →L[ℝ] ℝ) :
    coordinateTensorHilbertSchmidtPairing H R =
      ∑ p : CoordinateTensorEntryIndex E,
        H ((stdOrthonormalBasis ℝ E) p.1)
            ((stdOrthonormalBasis ℝ E) p.2) *
          R ((stdOrthonormalBasis ℝ E) p.1)
            ((stdOrthonormalBasis ℝ E) p.2) := by
  simp only [coordinateTensorHilbertSchmidtPairing, PiLp.inner_apply,
    coordinateTensorEntryVector_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The vector of flat componentwise Laplacians. -/
def coordinateTensorFlatLaplacianEntryVector
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    EuclideanSpace ℝ (CoordinateTensorEntryIndex E) :=
  WithLp.toLp 2 fun p ↦
    (Δ fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
      ((stdOrthonormalBasis ℝ E) p.2)) x

/-- Exact flat Bochner identity for the finite chart Hilbert--Schmidt energy. -/
theorem flat_laplacian_coordinateTensorHilbertSchmidtEnergy
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ p : CoordinateTensorEntryIndex E, ContDiff ℝ 2
      (fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2)) )
    (x : E) :
    (Δ fun y ↦ coordinateTensorHilbertSchmidtEnergy (H y)) x =
      2 * ⟪coordinateTensorEntryVector (H x),
          coordinateTensorFlatLaplacianEntryVector H x⟫_ℝ +
        2 * ∑ p : CoordinateTensorEntryIndex E,
          ∑ k : Fin (Module.finrank ℝ E),
            (fderiv ℝ
              (fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
                ((stdOrthonormalBasis ℝ E) p.2)) x
              ((stdOrthonormalBasis ℝ E) k)) ^ 2 := by
  rw [show (fun y ↦ coordinateTensorHilbertSchmidtEnergy (H y)) =
      (fun y ↦ ∑ p : CoordinateTensorEntryIndex E,
        (H y ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2)) ^ 2) by
    funext y
    exact coordinateTensorHilbertSchmidtEnergy_eq_sum_sq (H y)]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_fun_sum_apply
    (n := 2) (x := x) (u := Finset.univ)
    (fun p _ ↦ (hH p).contDiffAt.pow 2)]
  simp only [ContinuousMultilinearMap.sum_apply]
  conv_lhs => rw [Finset.sum_comm]
  have hlap (p : CoordinateTensorEntryIndex E) :
      (∑ i : Fin (Module.finrank ℝ E),
        iteratedFDeriv ℝ 2
          (fun y ↦ (H y ((stdOrthonormalBasis ℝ E) p.1)
            ((stdOrthonormalBasis ℝ E) p.2)) ^ 2) x
          ![(stdOrthonormalBasis ℝ E) i,
            (stdOrthonormalBasis ℝ E) i]) =
        (Δ fun y ↦ (H y ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2)) ^ 2) x := by
    exact (congrFun
      (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
        (fun y ↦ (H y ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2)) ^ 2)) x).symm
  simp_rw [hlap]
  simp_rw [flat_laplacian_sq _ (hH _) x]
  rw [coordinateTensorFlatLaplacianEntryVector,
    PiLp.inner_apply]
  simp only [coordinateTensorEntryVector_apply,
    RCLike.inner_apply, conj_trivial, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hprincipal :
      (∑ p : CoordinateTensorEntryIndex E,
        2 * H x ((stdOrthonormalBasis ℝ E) p.1)
            ((stdOrthonormalBasis ℝ E) p.2) *
          (Δ fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
            ((stdOrthonormalBasis ℝ E) p.2)) x) =
        2 * (∑ p : CoordinateTensorEntryIndex E,
          (Δ fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
              ((stdOrthonormalBasis ℝ E) p.2)) x *
            H x ((stdOrthonormalBasis ℝ E) p.1)
              ((stdOrthonormalBasis ℝ E) p.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hprincipal]

/-- Principal flat Bochner inequality for the complete finite entry energy. -/
theorem two_mul_coordinateTensor_flatPrincipalPairing_le_laplacian_energy
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hH : ∀ p : CoordinateTensorEntryIndex E, ContDiff ℝ 2
      (fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2)))
    (x : E) :
    2 * ⟪coordinateTensorEntryVector (H x),
        coordinateTensorFlatLaplacianEntryVector H x⟫_ℝ ≤
      (Δ fun y ↦ coordinateTensorHilbertSchmidtEnergy (H y)) x := by
  rw [flat_laplacian_coordinateTensorHilbertSchmidtEnergy H hH x]
  have hnonneg : 0 ≤
      2 * ∑ p : CoordinateTensorEntryIndex E,
        ∑ k : Fin (Module.finrank ℝ E),
          (fderiv ℝ
            (fun y ↦ H y ((stdOrthonormalBasis ℝ E) p.1)
              ((stdOrthonormalBasis ℝ E) p.2)) x
            ((stdOrthonormalBasis ℝ E) k)) ^ 2 := by
    positivity
  linarith

end ChartHilbertSchmidtEnergy

section EnergyRateAndLowerOrder

universe u v

variable {E : Type u} {M : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => CoordinateTensorEntryIndex E
local notation "H²" => EuclideanSpace ℝ P

/-- Componentwise differentiability assembles into differentiability of the
finite entry vector. -/
theorem coordinateTensorEntryVector_hasDerivAt
    (H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (R : E →L[ℝ] E →L[ℝ] ℝ) (t : ℝ)
    (hR : ∀ p : P, HasDerivAt
      (fun s ↦ H s ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2))
      (R ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2)) t) :
    HasDerivAt (fun s ↦ coordinateTensorEntryVector (H s))
      (coordinateTensorEntryVector R) t := by
  have hfun : HasDerivAt
      (fun s ↦ fun p : P ↦
        H s ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2))
      (fun p : P ↦
        R ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2)) t :=
    hasDerivAt_pi.mpr hR
  have h :=
    (EuclideanSpace.equiv P ℝ).symm.hasFDerivAt.comp_hasDerivAt t hfun
  simpa only [coordinateTensorEntryVector,
    ContinuousLinearEquiv.coe_coe, EuclideanSpace.equiv,
    PiLp.continuousLinearEquiv_symm_apply] using h

/-- The time derivative of the squared finite-entry energy is twice the
Hilbert--Schmidt pairing with the entry rate. -/
theorem coordinateTensorHilbertSchmidtEnergy_hasDerivAt
    (H : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (R : E →L[ℝ] E →L[ℝ] ℝ) (t : ℝ)
    (hR : ∀ p : P, HasDerivAt
      (fun s ↦ H s ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2))
      (R ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2)) t) :
    HasDerivAt (fun s ↦ coordinateTensorHilbertSchmidtEnergy (H s))
      (2 * coordinateTensorHilbertSchmidtPairing (H t) R) t := by
  have h := (coordinateTensorEntryVector_hasDerivAt H R t hR).norm_sq
  simpa only [coordinateTensorHilbertSchmidtEnergy,
    coordinateTensorHilbertSchmidtPairing] using h

/-- The exact entry-vector correction when a flat chart principal vector is
replaced by an intrinsic principal vector. -/
def chartConnectionCorrectionEntryVector
    (flatPrincipal intrinsicPrincipal : H²) : H² :=
  flatPrincipal - intrinsicPrincipal

/-- Absorb the chart-connection correction into the lower-order vector. -/
def chartConnectionCorrectedLowerEntryVector
    (lower flatPrincipal intrinsicPrincipal : H²) : H² :=
  lower + chartConnectionCorrectionEntryVector flatPrincipal intrinsicPrincipal

theorem flatPrincipal_add_lower_eq_intrinsicPrincipal_add_connectionCorrectedLower
    (lower flatPrincipal intrinsicPrincipal : H²) :
    flatPrincipal + lower =
      intrinsicPrincipal +
        chartConnectionCorrectedLowerEntryVector
          lower flatPrincipal intrinsicPrincipal := by
  simp only [chartConnectionCorrectedLowerEntryVector,
    chartConnectionCorrectionEntryVector]
  abel

/-- A linear lower-order entry action bounded in operator norm contributes at
most a uniform multiple of the Hilbert--Schmidt energy. -/
theorem two_mul_inner_linearLower_le_reaction_energy
    (A : H² →L[ℝ] H²) (h : H²) {B : ℝ} (hA : ‖A‖ ≤ B) :
    2 * ⟪h, A h⟫_ℝ ≤ 2 * B * ‖h‖ ^ 2 := by
  calc
    2 * ⟪h, A h⟫_ℝ ≤ 2 * (‖h‖ * ‖A h‖) := by
      exact mul_le_mul_of_nonneg_left (real_inner_le_norm h (A h)) (by norm_num)
    _ ≤ 2 * (‖h‖ * (B * ‖h‖)) := by
      gcongr
      exact A.le_of_opNorm_le hA h
    _ = 2 * B * ‖h‖ ^ 2 := by ring

variable [TopologicalSpace M] [CompactSpace M]

/-- Compactness produces one operator-norm bound for all analytic and
chart-connection lower-order actions on the closed spacetime track. -/
theorem exists_uniform_chartConnectionCorrectedLowerOperator_bound
    (T : ℝ) (A : ℝ → M → H² →L[ℝ] H²)
    (hA : ContinuousOn (Function.uncurry A)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M,
        ‖A t x‖ ≤ B :=
  exists_nonnegative_uniform_norm_bound_on_compact_parabolic_track T A hA

/-- Compact-track uniform lower-order energy estimate. -/
theorem exists_uniform_chartConnectionCorrectedLower_energy_bound
    (T : ℝ) (A : ℝ → M → H² →L[ℝ] H²)
    (hA : ContinuousOn (Function.uncurry A)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : M, ∀ h : H²,
        2 * ⟪h, A t x h⟫_ℝ ≤ 2 * B * ‖h‖ ^ 2 := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_uniform_chartConnectionCorrectedLowerOperator_bound T A hA
  exact ⟨B, hB0, fun t ht x h ↦
    two_mul_inner_linearLower_le_reaction_energy (A t x) h (hB t ht x)⟩

end EnergyRateAndLowerOrder

end Poincare
