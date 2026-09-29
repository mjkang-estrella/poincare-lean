import Poincare.Global.ScalarEvolution

/-!
# The doubled Ricci-gradient completed square

The nonnegative square `|c ∇Ric - dR ⊗ Ric|²` bounds the mixed contraction
for every real coefficient `c`.  Taking `c = 2 R` gives the coefficient
needed by the scalar-gradient quotient estimate, without curvature signs
or flow assumptions.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare.HamiltonScalarGradientMixedBound

/-- Absorb a weighted tensor pairing into the two squares, with no sign
restriction on the coefficient or tensor entries. -/
lemma weighted_square_absorption
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (c : ℝ) (A B W : α → β → γ → ℝ)
    (hW : ∀ a i j, 0 ≤ W a i j) :
    2 * c * (∑ a, ∑ i, ∑ j, A a i j * B a i j * W a i j) ≤
      c ^ 2 * (∑ a, ∑ i, ∑ j, (A a i j) ^ 2 * W a i j) +
        (∑ a, ∑ i, ∑ j, (B a i j) ^ 2 * W a i j) := by
  classical
  have hnonneg :
      0 ≤ ∑ a, ∑ i, ∑ j, (c * A a i j - B a i j) ^ 2 * W a i j := by
    refine Finset.sum_nonneg fun a _ ↦ ?_
    refine Finset.sum_nonneg fun i _ ↦ ?_
    refine Finset.sum_nonneg fun j _ ↦ ?_
    exact mul_nonneg (sq_nonneg _) (hW a i j)
  have hexpand :
      (∑ a, ∑ i, ∑ j, (c * A a i j - B a i j) ^ 2 * W a i j) =
        c ^ 2 * (∑ a, ∑ i, ∑ j, (A a i j) ^ 2 * W a i j) -
          2 * c * (∑ a, ∑ i, ∑ j, A a i j * B a i j * W a i j) +
            (∑ a, ∑ i, ∑ j, (B a i j) ^ 2 * W a i j) := by
    simp_rw [sub_sq, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring_nf
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    ring_nf
  rw [hexpand] at hnonneg
  linarith

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- Intrinsic absorption from the actual metric-orthogonal tensor square
`|c ∇Ric - dR ⊗ Ric|²`. -/
theorem ricci_gradient_absorption
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (c : ℝ) (x : M) :
    2 * c * g.pinchingMixedGradientPairingAt x ≤
      c ^ 2 * covRicciNormSqAt g x +
        g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let A :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦ covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)
  let B :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦
      extDerivFun (fun y : M ↦ g.scalarAt y) x (b a) * g.ricciAt x (b i) (b j)
  let W :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦
      (g.metricBilinAt x (b a) (b a) * g.metricBilinAt x (b i) (b i) *
        g.metricBilinAt x (b j) (b j))⁻¹
  have hW : ∀ a i j, 0 ≤ W a i j := by
    intro a i j
    exact inv_nonneg.mpr (le_of_lt (mul_pos
      (mul_pos (g.metricBilinAt_pos x (b.ne_zero a))
        (g.metricBilinAt_pos x (b.ne_zero i)))
      (g.metricBilinAt_pos x (b.ne_zero j))))
  rw [← g.pinchingScalarRicciGradientProductAt_eq_scalarGradNormSqAt_mul_ricciNormSqAt x]
  simpa [ClosedSmoothRiemannianMetric.pinchingMixedGradientPairingAt,
    covRicciNormSqAt, ClosedSmoothRiemannianMetric.pinchingScalarRicciGradientProductAt,
    b, A, B, W, div_eq_mul_inv] using weighted_square_absorption c A B W hW

/-- The doubled completed square controls the literal mixed scalar-gradient
inner product, using metric compatibility to differentiate the Ricci norm. -/
theorem mixed_gradient_square_completion
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    2 * g.scalarAt x * g.inner x
        (g.gradientAt (fun y ↦ g.scalarAt y) x)
        (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) ≤
      4 * g.scalarAt x ^ 2 * covRicciNormSqAt g x +
        g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
  have hinner :
      g.inner x (g.gradientAt (fun y ↦ g.scalarAt y) x)
          (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) =
        2 * g.pinchingMixedGradientPairingAt x := by
    rw [g.inner_symm, g.inner_gradientAt,
      extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt,
      ← g.pinchingMixedGradientPairingAt_eq_covRicciRicciPairingAt_gradientAt_scalarAt]
  calc
    2 * g.scalarAt x * g.inner x
        (g.gradientAt (fun y ↦ g.scalarAt y) x)
        (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) =
        2 * (2 * g.scalarAt x) * g.pinchingMixedGradientPairingAt x := by
          rw [hinner]
          ring
    _ ≤ (2 * g.scalarAt x) ^ 2 * covRicciNormSqAt g x +
        g.scalarGradNormSqAt x * g.ricciNormSqAt x :=
          ricci_gradient_absorption g (2 * g.scalarAt x) x
    _ = 4 * g.scalarAt x ^ 2 * covRicciNormSqAt g x +
        g.scalarGradNormSqAt x * g.ricciNormSqAt x := by ring

end Poincare.HamiltonScalarGradientMixedBound
