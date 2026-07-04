import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm
import Poincare.Global.RicciFlow
import Poincare.Global.ScalarVariation
import Poincare.MaximumPrinciple

/-!
# Closed-manifold scalar evolution statement

This module records the closed-manifold Hamilton scalar evolution equation in
terms of the current global vocabulary:
`scalarAt`, `laplacianAt`, `ricciNormSqAt`, and
`IsClosedRicciFlowSolutionAt`.

The full closed-manifold proof is intentionally not supplied here.  The
single-chart analogues already live in `ModelLaplacian.lean`; this file adds
the statement layer and a static Ricci-flat sanity instance.
-/

noncomputable section

open Bundle FiberBundle
open Set
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
Hamilton's scalar evolution equation at a point of a time-family of closed
smooth Riemannian metrics.

The implicit regularity instance is exactly the one required by the existing
`scalarAt` and `ricciNormSqAt` wrappers for each time-slice.
-/
def SatisfiesHamiltonScalarEvolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  HasDerivAt (fun t ↦ (gt t).scalarAt x)
    ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
      2 * (gt t₀).ricciNormSqAt x) t₀

/-- Unfold the closed Hamilton scalar evolution statement. -/
@[simp] theorem satisfiesHamiltonScalarEvolutionAt_iff
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x ↔
      HasDerivAt (fun t ↦ (gt t).scalarAt x)
        ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
          2 * (gt t₀).ricciNormSqAt x) t₀ :=
  Iff.rfl

/--
Scalar-square parabolic form following from Hamilton's scalar evolution:
`∂ₜ(R²) = Δ(R²) - 2 |∇R|² + 4 R |Ric|²`.
-/
theorem hasDerivAt_scalarAt_sq_of_satisfiesHamiltonScalarEvolutionAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hHam : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hScalar₂ :
      ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun z : M ↦ (gt t₀).scalarAt z) y) :
    HasDerivAt (fun t ↦ (gt t).scalarAt x ^ 2)
      ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
        - 2 * (gt t₀).scalarGradNormSqAt x
        + 4 * (gt t₀).scalarAt x * (gt t₀).ricciNormSqAt x) t₀ := by
  have hsq_lap :=
    (gt t₀).laplacianAt_sq
      (f := fun y : M ↦ (gt t₀).scalarAt y) (x := x) hScalar₂
  have hprod :
      HasDerivAt
        (fun t ↦ (gt t).scalarAt x * (gt t).scalarAt x)
        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
            + 2 * (gt t₀).ricciNormSqAt x) * (gt t₀).scalarAt x
          + (gt t₀).scalarAt x *
            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x)) t₀ := by
    simpa [SatisfiesHamiltonScalarEvolutionAt] using hHam.mul hHam
  have htarget :
      (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y ^ 2) x
          - 2 * (gt t₀).scalarGradNormSqAt x
          + 4 * (gt t₀).scalarAt x * (gt t₀).ricciNormSqAt x =
        (((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
            + 2 * (gt t₀).ricciNormSqAt x) * (gt t₀).scalarAt x
          + (gt t₀).scalarAt x *
            ((gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
              + 2 * (gt t₀).ricciNormSqAt x)) := by
    rw [hsq_lap]
    simp [ClosedSmoothRiemannianMetric.scalarGradNormSqAt]
    ring
  rw [htarget]
  simpa [pow_two] using hprod

/-- Algebra for the derivative of `N / R^2`. -/
private lemma quotient_derivative_sq_algebra
    {R N N' R' : ℝ} (hR : R ≠ 0) :
    (N' * R ^ 2 - N * (2 * R ^ (2 - 1) * R')) / (R ^ 2) ^ 2 =
      N' / R ^ 2 - 2 * N * R' / R ^ 3 := by
  norm_num
  field_simp [hR]

/-- Algebra identifying the reaction quotient with the normalized remainder. -/
private lemma pinching_reaction_remainder_algebra
    {R N M S : ℝ} (hR : R ≠ 0) :
    M / R ^ 2 - 2 * N * S / R ^ 3 =
      (2 / R ^ 4) * ((1 / 2 : ℝ) * R ^ 2 * M - R * N * S) := by
  field_simp [hR]

private lemma finset_sum_completed_square
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (R : ℝ) (A B W : α → β → γ → ℝ) :
  (∑ a, ∑ i, ∑ j, ((R * A a i j - B a i j) ^ 2 * W a i j)) =
      R ^ 2 * (∑ a, ∑ i, ∑ j, (A a i j) ^ 2 * W a i j)
        - 2 * R * (∑ a, ∑ i, ∑ j, A a i j * B a i j * W a i j)
        + (∑ a, ∑ i, ∑ j, (B a i j) ^ 2 * W a i j) := by
  simp_rw [sub_sq, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring_nf
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf

private lemma finset_sum_mul_sum₂
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : α → ℝ) (B : β → γ → ℝ) :
    (∑ a, A a) * (∑ i, ∑ j, B i j) =
      ∑ a, ∑ i, ∑ j, A a * B i j := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]

private lemma finset_sum_comm_three
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ i, ∑ j, ∑ a, F a i j) =
      ∑ a, ∑ i, ∑ j, F a i j := by
  calc
    (∑ i, ∑ j, ∑ a, F a i j) =
        ∑ i, ∑ a, ∑ j, F a i j := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, F a i j := by
          rw [Finset.sum_comm]

private lemma finset_sum_pairing_linearize
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (D : α → ℝ) (C : α → β → γ → ℝ) (W : β → γ → ℝ) :
    (∑ i, ∑ j, (∑ a, D a * C a i j) * W i j) =
      ∑ a, ∑ i, ∑ j, D a * C a i j * W i j := by
  calc
    (∑ i, ∑ j, (∑ a, D a * C a i j) * W i j) =
        ∑ i, ∑ j, ∑ a, (D a * C a i j) * W i j := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_mul]
    _ = ∑ a, ∑ i, ∑ j, D a * C a i j * W i j :=
        finset_sum_comm_three (fun a i j ↦ D a * C a i j * W i j)

/--
The spatial completed-square identity needed to assemble Hamilton's corrected
pinching quotient evolution.  This is intentionally named as a separate
obligation: it is the gradient algebra, not the reaction sign.
-/
def PinchingQuotientCompletedSquareIdentityAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Prop :=
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let A : ℝ := covRicciNormSqAt g x
  R ≠ 0 →
    g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / R ^ 2
      - 2 * N * g.laplacianAt (fun y : M ↦ g.scalarAt y) x / R ^ 3
      - 2 * A / R ^ 2 =
    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
      + g.pinchingQuotientGradientDrift3At x
      + g.pinchingGradientDampingAt x

namespace ClosedSmoothRiemannianMetric

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/--
Mixed contraction `⟨∇Ric, ∇R ⊗ Ric⟩` in the same metric-orthogonal frame used
by `pinchingGradientSquareAt`.
-/
noncomputable def pinchingMixedGradientPairingAt (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  ∑ a : Fin (Module.finrank ℝ (TM x)), ∑ i : Fin (Module.finrank ℝ (TM x)),
    ∑ j : Fin (Module.finrank ℝ (TM x)),
      (covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j) *
          (extDerivFun (fun y : M ↦ g.scalarAt y) x (b a) *
            g.ricciAt x (b i) (b j))) /
        (g.metricBilinAt x (b a) (b a) *
          g.metricBilinAt x (b i) (b i) *
          g.metricBilinAt x (b j) (b j))

/--
The raw norm of `∇R ⊗ Ric`, written in the same orthogonal-frame contraction
as `pinchingGradientSquareAt`.
-/
noncomputable def pinchingScalarRicciGradientProductAt (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  ∑ a : Fin (Module.finrank ℝ (TM x)), ∑ i : Fin (Module.finrank ℝ (TM x)),
    ∑ j : Fin (Module.finrank ℝ (TM x)),
      (extDerivFun (fun y : M ↦ g.scalarAt y) x (b a) *
          g.ricciAt x (b i) (b j)) ^ 2 /
        (g.metricBilinAt x (b a) (b a) *
          g.metricBilinAt x (b i) (b i) *
          g.metricBilinAt x (b j) (b j))

set_option maxHeartbeats 5000000 in
/--
In a metric-orthogonal frame, the Ricci pairing of a symmetric `(0,2)` field is
the double diagonal-inverse contraction.
-/
theorem metricVariationRicciPairingAt_eq_orthogonalBasis_sum_of_symm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ∀ y : M, TM y → TM y → ℝ) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (b : Module.Basis ι ℝ (TM x))
    (hOrtho : (g.metricBilinAt x).IsOrthoᵢ b)
    (B : LinearMap.BilinForm ℝ (TM x))
    (hB : ∀ p q : TM x, B p q = h x p q)
    (hSymm : ∀ p q : TM x, h x p q = h x q p) :
    metricVariationRicciPairingAt g h x =
      (let diag : ι → ℝ := fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, ∑ j,
        (diag i)⁻¹ * (diag j)⁻¹ *
          h x (b i) (b j) * g.ricciAt x (b i) (b j)) := by
  classical
  let diag : ι → ℝ := fun k ↦ g.metricBilinAt x (b k) (b k)
  let sharp : ι → TM x := fun i ↦ metricDualVectorAt g x (b.coord i)
  have hdual : ∀ i, sharp i = (diag i)⁻¹ • b i := by
    intro i
    simpa [sharp, diag] using
      metricDualVectorAt_orthogonalBasis_coord_eq
        (g := g) (x := x) (b := b) hOrtho i
  have hRicExpand : ∀ i,
      g.ricciEndoAt x (b i) =
        ∑ j, ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) • b j := by
    intro i
    calc
      g.ricciEndoAt x (b i) =
          ∑ j, b.coord j (g.ricciEndoAt x (b i)) • b j :=
            (b.sum_repr (g.ricciEndoAt x (b i))).symm
      _ = ∑ j, ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) • b j := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            have hcoord :
                b.coord j (g.ricciEndoAt x (b i)) =
                  (diag j)⁻¹ * g.ricciAt x (b i) (b j) := by
              calc
                b.coord j (g.ricciEndoAt x (b i)) =
                    g.inner x (g.ricciEndoAt x (b i)) (sharp j) := by
                      simpa [sharp] using
                        coord_eq_inner_metricDualVectorAt_of_basis
                          (g := g) (x := x) (b := b) j
                          (g.ricciEndoAt x (b i))
                _ = g.inner x (g.ricciEndoAt x (b i))
                    ((diag j)⁻¹ • b j) := by rw [hdual j]
                _ = (diag j)⁻¹ * g.ricciAt x (b i) (b j) := by
                      rw [← g.inner_ricciEndoAt]
                      simp [smul_eq_mul]
            rw [hcoord]
  have hTrace :
      metricVariationRicciPairingAt g h x =
        metricRicciPairingTraceInBasisAt g x B b :=
    metricVariationRicciPairingAt_eq_metricRicciPairingTraceInBasisAt
      (g := g) (h := h) (x := x) (B := B) hB hSymm b
  calc
    metricVariationRicciPairingAt g h x =
        metricRicciPairingTraceInBasisAt g x B b := hTrace
    _ = ∑ i, B (g.ricciEndoAt x (b i)) (sharp i) := by
          rfl
    _ = ∑ i, B (∑ j,
            ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) • b j)
          ((diag i)⁻¹ • b i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hRicExpand i, hdual i]
    _ = ∑ i, ∑ j,
          (diag i)⁻¹ * (diag j)⁻¹ *
            h x (b i) (b j) * g.ricciAt x (b i) (b j) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          calc
            B (∑ j, ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) • b j)
                ((diag i)⁻¹ • b i) =
                (diag i)⁻¹ *
                  B (∑ j,
                    ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) • b j)
                    (b i) := by
                  simp [smul_eq_mul]
            _ = (diag i)⁻¹ *
                (∑ j, ((diag j)⁻¹ * g.ricciAt x (b i) (b j)) *
                  B (b j) (b i)) := by
                  rw [map_sum]
                  simp [smul_eq_mul]
            _ = ∑ j,
                (diag i)⁻¹ * (diag j)⁻¹ *
                  h x (b i) (b j) * g.ricciAt x (b i) (b j) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun j _ ↦ ?_
                  rw [hB (b j) (b i), hSymm (b j) (b i)]
                  ring
    _ =
        (let diag : ι → ℝ := fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i, ∑ j,
          (diag i)⁻¹ * (diag j)⁻¹ *
            h x (b i) (b j) * g.ricciAt x (b i) (b j)) := by
        simp [diag]

/-- Orthogonal-frame expansion of `⟨∇_v Ric,Ric⟩`. -/
theorem covRicciRicciPairingAt_eq_metricOrthogonalBasis_sum
    (x : M) (v : TM x) :
    covRicciRicciPairingAt g x v =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, ∑ j,
        (diag i)⁻¹ * (diag j)⁻¹ *
          covTensor2DerivAt g (ricciVariationField g) x v (b i) (b j) *
          g.ricciAt x (b i) (b j)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  let H : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦
      covTensor2DerivAt g (ricciVariationField g) y (extend E v y) p q
  let B : LinearMap.BilinForm ℝ (TM x) :=
    LinearMap.mk₂ ℝ
      (fun p q ↦ covTensor2DerivAt g (ricciVariationField g) x v p q)
      (fun p p' q ↦
        covTensor2DerivAt_add_left
          (g := g) (h := ricciVariationField g) (x := x)
          (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
            (g := g) (x := x))
          (tensor2AddLeft_ricciVariationField g) v p p' q)
      (fun c p q ↦ by
        simpa [smul_eq_mul] using
          covTensor2DerivAt_smul_left
            (g := g) (h := ricciVariationField g) (x := x)
            (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
              (g := g) (x := x))
            (tensor2SMulLeft_ricciVariationField g) c v p q)
      (fun p q q' ↦
        covTensor2DerivAt_add_right
          (g := g) (h := ricciVariationField g) (x := x)
          (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
            (g := g) (x := x))
          (tensor2AddRight_ricciVariationField g) v p q q')
      (fun c p q ↦ by
        simpa [smul_eq_mul] using
          covTensor2DerivAt_smul_right
            (g := g) (h := ricciVariationField g) (x := x)
            (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
              (g := g) (x := x))
            (tensor2SMulRight_ricciVariationField g) c v p q)
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    simpa [b, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hB : ∀ p q : TM x, B p q = H x p q := by
    intro p q
    simp [B, H]
  have hSymm : ∀ p q : TM x, H x p q = H x q p := by
    intro p q
    simp [H, covTensor2DerivAt_ricciVariationField_symm]
  calc
    covRicciRicciPairingAt g x v =
        metricVariationRicciPairingAt g H x := by
          simpa [H] using
            covRicciRicciPairingAt_eq_metricVariationRicciPairingAt_covTensor2DerivAt
              (g := g) (x := x) (v := v)
    _ =
        (let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
          fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i, ∑ j,
          (diag i)⁻¹ * (diag j)⁻¹ *
            H x (b i) (b j) * g.ricciAt x (b i) (b j)) :=
          metricVariationRicciPairingAt_eq_orthogonalBasis_sum_of_symm
            (g := g) (h := H) (x := x) (b := b) hOrtho
            (B := B) hB hSymm
    _ =
        (let b := metricOrthogonalBasisAt g x
        let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
          fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i, ∑ j,
          (diag i)⁻¹ * (diag j)⁻¹ *
            covTensor2DerivAt g (ricciVariationField g) x v (b i) (b j) *
            g.ricciAt x (b i) (b j)) := by
        simp [b, H]

/-- The metric gradient in an orthogonal frame. -/
theorem gradientAt_eq_metricOrthogonalBasis_sum (f : M → ℝ) (x : M) :
    g.gradientAt f x =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, ((diag i)⁻¹ * extDerivFun f x (b i)) • b i) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    simpa [b, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hcoord : ∀ i,
      b.coord i (g.gradientAt f x) =
        (diag i)⁻¹ * extDerivFun f x (b i) := by
    intro i
    calc
      b.coord i (g.gradientAt f x) =
          g.inner x (g.gradientAt f x)
            (metricDualVectorAt g x (b.coord i)) := by
            rw [coord_eq_inner_metricDualVectorAt_of_basis
              (g := g) (x := x) (b := b)]
      _ = g.inner x (g.gradientAt f x) ((diag i)⁻¹ • b i) := by
            rw [metricDualVectorAt_orthogonalBasis_coord_eq
              (g := g) (x := x) (b := b) hOrtho i]
      _ = (diag i)⁻¹ * extDerivFun f x (b i) := by
            simp [smul_eq_mul, g.inner_gradientAt]
  calc
    g.gradientAt f x = ∑ i, b.coord i (g.gradientAt f x) • b i :=
      (b.sum_repr (g.gradientAt f x)).symm
    _ = ∑ i, ((diag i)⁻¹ * extDerivFun f x (b i)) • b i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcoord i]
    _ =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, ((diag i)⁻¹ * extDerivFun f x (b i)) • b i) := by
      simp [b, diag]

/-- Orthogonal-frame expansion of the scalar-gradient norm. -/
theorem scalarGradNormSqAt_eq_metricOrthogonalBasis_sum (x : M) :
    g.scalarGradNormSqAt x =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, (extDerivFun (fun y : M ↦ g.scalarAt y) x (b i)) ^ 2 / diag i) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let f : M → ℝ := fun y ↦ g.scalarAt y
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  have hgrad := g.gradientAt_eq_metricOrthogonalBasis_sum f x
  unfold scalarGradNormSqAt
  calc
    g.inner x (g.gradientAt f x) (g.gradientAt f x) =
        g.inner x
          ((let b := metricOrthogonalBasisAt g x
            let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
              fun k ↦ g.metricBilinAt x (b k) (b k)
            ∑ i, ((diag i)⁻¹ * extDerivFun f x (b i)) • b i))
          (g.gradientAt f x) := by
          rw [hgrad]
    _ =
        ∑ i,
          ((diag i)⁻¹ * extDerivFun f x (b i)) *
            g.inner x (b i) (g.gradientAt f x) := by
          simp [b, diag]
    _ = ∑ i, (extDerivFun f x (b i)) ^ 2 / diag i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [g.inner_symm x (b i) (g.gradientAt f x),
            g.inner_gradientAt]
          field_simp
    _ =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, (extDerivFun (fun y : M ↦ g.scalarAt y) x (b i)) ^ 2 / diag i) := by
      simp [f, b, diag]

set_option maxHeartbeats 20000000 in
/-- Orthogonal-frame expansion of the Ricci norm. -/
theorem ricciNormSqAt_eq_metricOrthogonalBasis_sum (x : M) :
    g.ricciNormSqAt x =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i, ∑ j, (g.ricciAt x (b i) (b j)) ^ 2 / (diag i * diag j)) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  let RicB : LinearMap.BilinForm ℝ (TM x) :=
    LinearMap.mk₂ ℝ (fun p q ↦ g.ricciAt x p q)
      (fun p p' q ↦ g.ricciAt_add_left x p p' q)
      (fun c p q ↦ by
        simpa [smul_eq_mul] using g.ricciAt_smul_left x c p q)
      (fun p q q' ↦ g.ricciAt_add_right x p q q')
      (fun c p q ↦ by
        simpa [smul_eq_mul] using g.ricciAt_smul_right x c p q)
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    simpa [b, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hB : ∀ p q : TM x,
      RicB p q = ricciVariationField g x p q := by
    intro p q
    simp [RicB, ricciVariationField]
  have hSymm : ∀ p q : TM x,
      ricciVariationField g x p q = ricciVariationField g x q p := by
    intro p q
    exact g.ricciAt_symm x p q
  calc
    g.ricciNormSqAt x =
        metricVariationRicciPairingAt g (ricciVariationField g) x := by
          exact (metricVariationRicciPairingAt_ricci g x).symm
    _ =
        (let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
          fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i, ∑ j,
          (diag i)⁻¹ * (diag j)⁻¹ *
            ricciVariationField g x (b i) (b j) *
            g.ricciAt x (b i) (b j)) :=
          metricVariationRicciPairingAt_eq_orthogonalBasis_sum_of_symm
            (g := g) (h := ricciVariationField g) (x := x) (b := b)
            hOrtho
            (B := RicB)
            hB hSymm
    _ =
        (let b := metricOrthogonalBasisAt g x
        let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
          fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i, ∑ j, (g.ricciAt x (b i) (b j)) ^ 2 / (diag i * diag j)) := by
        simp [b, ricciVariationField, div_eq_mul_inv, pow_two,
          mul_comm, mul_left_comm, mul_assoc]

set_option maxHeartbeats 20000000 in
/-- The mixed completed-square contraction is the covariant Ricci/Ricci pairing
evaluated on the scalar-gradient direction. -/
theorem pinchingMixedGradientPairingAt_eq_covRicciRicciPairingAt_gradientAt_scalarAt
    (x : M) :
    g.pinchingMixedGradientPairingAt x =
      covRicciRicciPairingAt g x
        (g.gradientAt (fun y : M ↦ g.scalarAt y) x) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let f : M → ℝ := fun y ↦ g.scalarAt y
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  have hgrad := g.gradientAt_eq_metricOrthogonalBasis_sum f x
  have hpair :=
    g.covRicciRicciPairingAt_eq_metricOrthogonalBasis_sum x
      (g.gradientAt f x)
  have hCovSum : ∀ i j,
      covTensor2DerivAt g (ricciVariationField g) x
          (∑ a, ((diag a)⁻¹ * extDerivFun f x (b a)) • b a)
          (b i) (b j) =
        ∑ a, ((diag a)⁻¹ * extDerivFun f x (b a)) *
          covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j) := by
    intro i j
    set L : TM x →ₗ[ℝ] ℝ :=
      IsLinearMap.mk' (fun v ↦
          covTensor2DerivAt g (ricciVariationField g) x v (b i) (b j))
        ⟨fun v₁ v₂ ↦
            covTensor2DerivAt_add_deriv
              (g := g) (h := ricciVariationField g) (x := x)
              (tensor2AddLeft_ricciVariationField g)
              (tensor2AddRight_ricciVariationField g) v₁ v₂ (b i) (b j),
          fun c v ↦ by
            simpa [smul_eq_mul] using
              covTensor2DerivAt_smul_deriv
                (g := g) (h := ricciVariationField g) (x := x)
                (tensor2SMulLeft_ricciVariationField g)
                (tensor2SMulRight_ricciVariationField g) c v (b i) (b j)⟩ with hL
    change L (∑ a, ((diag a)⁻¹ * extDerivFun f x (b a)) • b a) =
      ∑ a, ((diag a)⁻¹ * extDerivFun f x (b a)) * L (b a)
    have hmap := map_sum L
      (fun a ↦ ((diag a)⁻¹ * extDerivFun f x (b a)) • b a) Finset.univ
    simpa [smul_eq_mul] using hmap
  let D : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a ↦ (diag a)⁻¹ * extDerivFun f x (b a)
  let C :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦ covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)
  let W :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun i j ↦ (diag i)⁻¹ * (diag j)⁻¹ * g.ricciAt x (b i) (b j)
  have hRhs :
      covRicciRicciPairingAt g x (g.gradientAt f x) =
        ∑ i, ∑ j, (∑ a, D a * C a i j) * W i j := by
    rw [hpair, hgrad]
    change
      (∑ i, ∑ j,
        (diag i)⁻¹ * (diag j)⁻¹ *
          covTensor2DerivAt g (ricciVariationField g) x
            (∑ a, ((diag a)⁻¹ * extDerivFun f x (b a)) • b a)
            (b i) (b j) *
          g.ricciAt x (b i) (b j)) =
        ∑ i, ∑ j, (∑ a, D a * C a i j) * W i j
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hCovSum i j]
    dsimp [D, C, W]
    ring
  rw [hRhs]
  rw [finset_sum_pairing_linearize (D := D) (C := C) (W := W)]
  dsimp [pinchingMixedGradientPairingAt, D, C, W]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change
    covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j) *
        (extDerivFun f x (b a) * g.ricciAt x (b i) (b j)) /
          (diag a * diag i * diag j) =
      ((diag a)⁻¹ * extDerivFun f x (b a)) *
        covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j) *
          ((diag i)⁻¹ * (diag j)⁻¹ * g.ricciAt x (b i) (b j))
  ring_nf

set_option maxHeartbeats 20000000 in
/-- The raw `∇R ⊗ Ric` norm factors into the scalar-gradient norm and Ricci norm. -/
theorem pinchingScalarRicciGradientProductAt_eq_scalarGradNormSqAt_mul_ricciNormSqAt
    (x : M) :
    g.pinchingScalarRicciGradientProductAt x =
      g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  rw [g.scalarGradNormSqAt_eq_metricOrthogonalBasis_sum x,
    g.ricciNormSqAt_eq_metricOrthogonalBasis_sum x]
  dsimp [pinchingScalarRicciGradientProductAt]
  change
    (∑ a, ∑ i, ∑ j,
      (extDerivFun (fun y : M ↦ g.scalarAt y) x (b a) *
          g.ricciAt x (b i) (b j)) ^ 2 /
        (diag a * diag i * diag j)) =
      (∑ a, (extDerivFun (fun y : M ↦ g.scalarAt y) x (b a)) ^ 2 / diag a) *
        ∑ i, ∑ j, (g.ricciAt x (b i) (b j)) ^ 2 / (diag i * diag j)
  rw [finset_sum_mul_sum₂
    (A := fun a ↦ (extDerivFun (fun y : M ↦ g.scalarAt y) x (b a)) ^ 2 / diag a)
    (B := fun i j ↦ (g.ricciAt x (b i) (b j)) ^ 2 / (diag i * diag j))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring_nf

set_option maxHeartbeats 3000000 in
/-- Orthogonal-frame expansion of Hamilton's completed gradient square. -/
theorem pinchingGradientSquareAt_eq_completedSquareExpansion (x : M) :
    g.pinchingGradientSquareAt x =
      (g.scalarAt x) ^ 2 * covRicciNormSqAt g x
        - 2 * g.scalarAt x * g.pinchingMixedGradientPairingAt x
        + g.pinchingScalarRicciGradientProductAt x := by
  classical
  dsimp [pinchingGradientSquareAt, covRicciNormSqAt,
    pinchingMixedGradientPairingAt, pinchingScalarRicciGradientProductAt]
  simp_rw [div_eq_mul_inv]
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
      extDerivFun (fun y : M ↦ g.scalarAt y) x (b a) *
        g.ricciAt x (b i) (b j)
  let W :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦
      ((g.metricBilinAt x (b a) (b a)) *
        (g.metricBilinAt x (b i) (b i)) *
        (g.metricBilinAt x (b j) (b j)))⁻¹
  simpa [b, A, B, W] using
    finset_sum_completed_square (R := g.scalarAt x) (A := A) (B := B) (W := W)

end ClosedSmoothRiemannianMetric

namespace ClosedSmoothRiemannianMetric

/--
Local gradient form of the quotient product-rule trick.  If `q * v = u`
eventually at `x`, then `v ∇q = ∇u - q ∇v` at `x`.
-/
theorem gradientAt_quotient_eq_of_eventually_product_rule
    (g : ClosedSmoothRiemannianMetric n M)
    {u v q : M → ℝ} {x : M}
    (hprod : (fun y : M ↦ q y * v y) =ᶠ[nhds x] u)
    (hq : MDifferentiableAt I 𝓘(ℝ) q x)
    (hv : MDifferentiableAt I 𝓘(ℝ) v x) :
    v x • g.gradientAt q x =
      g.gradientAt u x - q x • g.gradientAt v x := by
  have hmul := g.gradientAt_mul (f := q) (h := v) hq hv
  have hgrad :
      g.gradientAt (q * v) x = g.gradientAt u x :=
    g.gradientAt_congr_of_eventuallyEq hprod
  rw [← hgrad, hmul]
  simp [add_comm]

/--
Local Laplacian form of the quotient product-rule trick.  If `q * v = u`
eventually at `x` and `v x ≠ 0`, then `Δq` is obtained from `Δ(qv)` by
solving the product rule.
-/
theorem laplacianAt_quotient_eq_of_eventually_product_rule
    (g : ClosedSmoothRiemannianMetric n M)
    {u v q : M → ℝ} {x : M}
    (hprod : (fun y : M ↦ q y * v y) =ᶠ[nhds x] u)
    (hvx : v x ≠ 0)
    (hq : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) q y)
    (hv : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) v y)
    (hgradq : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient q)) x)
    (hgradv : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient v)) x)
    (hgradprod :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient (q * v))) x)
    (hgradu : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient u)) x) :
    g.laplacianAt q x =
      (g.laplacianAt u x - q x * g.laplacianAt v x
          - 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x)) / v x := by
  have hmul :=
    g.laplacianAt_mul (f := q) (h := v) (x := x) hq hv hgradq hgradv
  have hlap :
      g.laplacianAt (q * v) x = g.laplacianAt u x :=
    g.laplacianAt_congr_of_eventuallyEq hprod hgradprod hgradu
  have hu :
      g.laplacianAt u x =
        q x * g.laplacianAt v x + v x * g.laplacianAt q x
          + 2 * g.inner x (g.gradientAt q x) (g.gradientAt v x) := by
    rw [← hlap]
    exact hmul
  rw [eq_div_iff hvx]
  linarith

set_option maxHeartbeats 12000000 in
/--
Spatial quotient/drift expansion for Hamilton's scalar-normalized Ricci
pinching quotient on the positive-scalar domain.
-/
theorem pinchingQuotient_spatial_expansion
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hRpos : 0 < g.scalarAt x)
    (hScalarCont : ContinuousAt (fun y : M ↦ g.scalarAt y) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ g.scalarAt z) y)
    (hQuotDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ g.pinchingQuotientAt z) y)
    (hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.scalarAt y))) x)
    (hQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.pinchingQuotientAt y))) x)
    (hScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦
          g.scalarAt y * g.scalarAt y))) x)
    (hQuotScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient ((fun y : M ↦ g.pinchingQuotientAt y) *
          (fun y : M ↦ g.scalarAt y * g.scalarAt y)))) x)
    (hRicNormGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (g.gradient (fun y : M ↦ g.ricciNormSqAt y))) x) :
    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
        + g.pinchingQuotientGradientDrift3At x =
      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
        - 2 * g.ricciNormSqAt x *
            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
        - 4 * g.pinchingMixedGradientPairingAt x / (g.scalarAt x) ^ 3
        + 2 * g.pinchingScalarRicciGradientProductAt x / (g.scalarAt x) ^ 4 := by
  classical
  let Rf : M → ℝ := fun y ↦ g.scalarAt y
  let Nf : M → ℝ := fun y ↦ g.ricciNormSqAt y
  let Qf : M → ℝ := fun y ↦ g.pinchingQuotientAt y
  let Vf : M → ℝ := fun y ↦ Rf y * Rf y
  let R : ℝ := Rf x
  let N : ℝ := Nf x
  let S : ℝ := g.scalarGradNormSqAt x
  let B : ℝ := g.pinchingMixedGradientPairingAt x
  let G : ℝ := g.pinchingScalarRicciGradientProductAt x
  let IQ : ℝ := g.inner x (g.gradientAt Qf x) (g.gradientAt Rf x)
  have hRne : R ≠ 0 := ne_of_gt (by simpa [R, Rf] using hRpos)
  have hVdiff : ∀ y : M, MDifferentiableAt I 𝓘(ℝ) Vf y := by
    intro y
    dsimp [Vf, Rf]
    exact (hScalarDiff y).mul (hScalarDiff y)
  have hGradQ :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient Qf)) x := by
    simpa [Qf] using hQuotGrad
  have hGradV :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient Vf)) x := by
    simpa [Vf, Rf] using hScalarSqGrad
  have hGradProd :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient (Qf * Vf))) x := by
    simpa [Qf, Vf, Rf] using hQuotScalarSqGrad
  have hGradN :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient Nf)) x := by
    simpa [Nf] using hRicNormGrad
  have hRpos_event : ∀ᶠ y in nhds x, 0 < Rf y := by
    simpa [Rf] using hScalarCont.eventually (eventually_gt_nhds hRpos)
  have hprod : (fun y : M ↦ Qf y * Vf y) =ᶠ[nhds x] Nf := by
    filter_upwards [hRpos_event] with y hy
    dsimp [Qf, Vf, Rf, Nf]
    rw [g.pinchingQuotientAt_eq y]
    field_simp [ne_of_gt hy, pow_two]
    rw [mul_div_assoc, div_self (ne_of_gt hy), mul_one]
  have hVxne : Vf x ≠ 0 := by
    dsimp [Vf, Rf]
    exact mul_ne_zero hRne hRne
  have hLapQuot :
      g.laplacianAt Qf x =
        (g.laplacianAt Nf x - Qf x * g.laplacianAt Vf x
            - 2 * g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x)) / Vf x :=
    g.laplacianAt_quotient_eq_of_eventually_product_rule
      hprod hVxne hQuotDiff hVdiff hGradQ hGradV hGradProd hGradN
  have hGradQuot :
      Vf x • g.gradientAt Qf x =
        g.gradientAt Nf x - Qf x • g.gradientAt Vf x :=
    g.gradientAt_quotient_eq_of_eventually_product_rule
      hprod (hQuotDiff x) (hVdiff x)
  have hGradVeq :
      g.gradientAt Vf x = (2 * R) • g.gradientAt Rf x := by
    have h := g.gradientAt_mul (f := Rf) (h := Rf)
      (x := x) (hScalarDiff x) (hScalarDiff x)
    change g.gradientAt (Rf * Rf) x = (2 * R) • g.gradientAt Rf x
    calc
      g.gradientAt (Rf * Rf) x =
          Rf x • g.gradientAt Rf x + Rf x • g.gradientAt Rf x := h
      _ = (2 * R) • g.gradientAt Rf x := by
          rw [← add_smul]
          congr 1
          ring
  have hLapVeq :
      g.laplacianAt Vf x =
        2 * R * g.laplacianAt Rf x + 2 * S := by
    have h := g.laplacianAt_mul (f := Rf) (h := Rf)
      (x := x) hScalarDiff hScalarDiff
      (by simpa [Rf] using hScalarGrad)
      (by simpa [Rf] using hScalarGrad)
    change g.laplacianAt (Rf * Rf) x =
      2 * R * g.laplacianAt Rf x + 2 * S
    rw [h]
    simp [Rf, R, S, scalarGradNormSqAt, mul_comm, mul_left_comm]
    ring
  have hInnerQV :
      g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x) = (2 * R) * IQ := by
    rw [hGradVeq]
    simp [IQ, smul_eq_mul]
  have hINR :
      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) = 2 * B := by
    calc
      g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x) =
          extDerivFun Nf x (g.gradientAt Rf x) := by
            simpa [Nf] using
              g.inner_gradientAt Nf x (g.gradientAt Rf x)
      _ = 2 * covRicciRicciPairingAt g x (g.gradientAt Rf x) := by
            simpa [Nf, Rf] using
              extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
                (g := g) x (g.gradientAt Rf x)
      _ = 2 * B := by
            rw [← g.pinchingMixedGradientPairingAt_eq_covRicciRicciPairingAt_gradientAt_scalarAt x]
  have hIVR :
      g.inner x (g.gradientAt Vf x) (g.gradientAt Rf x) = (2 * R) * S := by
    rw [hGradVeq]
    simp [S, Rf, scalarGradNormSqAt, smul_eq_mul]
  have hQx : Qf x = N / R ^ 2 := by
    simpa [Qf, N, R, Rf] using g.pinchingQuotientAt_eq x
  have hInnerQuot :
      Vf x * IQ =
        g.inner x (g.gradientAt Nf x) (g.gradientAt Rf x)
          - Qf x * g.inner x (g.gradientAt Vf x) (g.gradientAt Rf x) := by
    have h := congrArg
      (fun v : TM x ↦ g.inner x v (g.gradientAt Rf x)) hGradQuot
    simpa [IQ, smul_eq_mul, map_sub, map_smul] using h
  have hInnerRel :
      R ^ 2 * IQ = 2 * B - (N / R ^ 2) * ((2 * R) * S) := by
    rw [hINR, hIVR, hQx] at hInnerQuot
    simpa [Vf, Rf, R, pow_two, mul_comm, mul_left_comm, mul_assoc] using hInnerQuot
  have hIQR :
      IQ = (2 * B - (N / R ^ 2) * ((2 * R) * S)) / R ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hRne)]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hInnerRel
  have hDrift :
      g.pinchingQuotientGradientDrift3At x = (2 / R) * IQ := by
    dsimp [pinchingQuotientGradientDrift3At, R, Rf, Qf, IQ]
    rw [g.inner_symm x (g.gradientAt (fun y : M ↦ g.scalarAt y) x)
      (g.gradientAt (fun y : M ↦ g.pinchingQuotientAt y) x)]
  have hRaw : g.pinchingScalarRicciGradientProductAt x = S * N := by
    simpa [S, N] using
      g.pinchingScalarRicciGradientProductAt_eq_scalarGradNormSqAt_mul_ricciNormSqAt x
  calc
    g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
        + g.pinchingQuotientGradientDrift3At x =
        (g.laplacianAt Nf x - Qf x * g.laplacianAt Vf x
            - 2 * g.inner x (g.gradientAt Qf x) (g.gradientAt Vf x)) / Vf x
          + (2 / R) * IQ := by
          rw [hLapQuot, hDrift]
    _ =
      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
        - 2 * g.ricciNormSqAt x *
            g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
        - 4 * g.pinchingMixedGradientPairingAt x / (g.scalarAt x) ^ 3
        + 2 * g.pinchingScalarRicciGradientProductAt x / (g.scalarAt x) ^ 4 := by
        rw [hLapVeq, hInnerQV, hIQR, hQx, hRaw]
        simp [Vf, Rf, Nf, S, B, R, N, pow_two]
        field_simp [hRne]
        ring

end ClosedSmoothRiemannianMetric

private lemma pinching_completed_square_algebra
    {R N lapN lapR A B G lapQ drift square : ℝ} (hR : R ≠ 0)
    (hSpatial :
      lapQ + drift =
        lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 4 * B / R ^ 3
          + 2 * G / R ^ 4)
    (hSquare : square = R ^ 2 * A - 2 * R * B + G) :
    lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2 =
      lapQ + drift + (-(2 / R ^ 4) * square) := by
  subst square
  rw [hSpatial]
  field_simp [hR]
  ring

theorem pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M)
    (hSpatial : g.scalarAt x ≠ 0 →
      g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
          + g.pinchingQuotientGradientDrift3At x =
        g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x / (g.scalarAt x) ^ 2
          - 2 * g.ricciNormSqAt x *
              g.laplacianAt (fun y : M ↦ g.scalarAt y) x / (g.scalarAt x) ^ 3
          - 4 * g.pinchingMixedGradientPairingAt x / (g.scalarAt x) ^ 3
          + 2 * g.pinchingScalarRicciGradientProductAt x / (g.scalarAt x) ^ 4) :
    PinchingQuotientCompletedSquareIdentityAt g x := by
  intro hR
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let A : ℝ := covRicciNormSqAt g x
  let B : ℝ := g.pinchingMixedGradientPairingAt x
  let G : ℝ := g.pinchingScalarRicciGradientProductAt x
  have hSquare :
      g.pinchingGradientSquareAt x = R ^ 2 * A - 2 * R * B + G := by
    simpa [R, A, B, G] using
      g.pinchingGradientSquareAt_eq_completedSquareExpansion x
  have hAlg := pinching_completed_square_algebra
    (R := R) (N := N)
    (lapN := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x)
    (lapR := g.laplacianAt (fun y : M ↦ g.scalarAt y) x)
    (A := A) (B := B) (G := G)
    (lapQ := g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x)
    (drift := g.pinchingQuotientGradientDrift3At x)
    (square := g.pinchingGradientSquareAt x)
    (by simpa [R] using hR)
    (by simpa [R, N, B, G] using hSpatial hR)
    hSquare
  simpa [PinchingQuotientCompletedSquareIdentityAt,
    ClosedSmoothRiemannianMetric.pinchingGradientDampingAt, R, N, A] using hAlg

set_option maxHeartbeats 5000000 in
/--
Exact 3D `|Ric|^2` parabolic form before dropping the nonnegative
`|∇Ric|^2` term.
-/
theorem hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hEvol : SatisfiesRicciEvolutionAt gt t₀ x) (hn : n = 3)
    (hRicNorm₂ : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).ricciNormSqAt y) x)
    (hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt (gt t₀) y (extend E w y)) x)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (ricciVariationField (gt t₀)) x) :
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let δRic3 : TM x → TM x → ℝ :=
      fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
    let hRic3 : ∀ u w : TM x,
        HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
      SatisfiesRicciEvolutionAt.reaction3
        (gt := gt) (t₀ := t₀) (x := x) hEvol hn
    let fullTrace : ℝ :=
      2 * LinearMap.trace ℝ (TM x)
        ((((raise'.comp (g.ricciDualContinuousAt x) +
            (g.metricRaiseContinuousAt x).comp
              (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
            (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
    HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
      (g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
        - 2 * covRicciNormSqAt g x
        + g.pinchingRicciNormReactionMotionTraceAt x fullTrace) t₀ := by
  classical
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let δRic3 : TM x → TM x → ℝ :=
    fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
  let hRic3 : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
    SatisfiesRicciEvolutionAt.reaction3
      (gt := gt) (t₀ := t₀) (x := x) hEvol hn
  let fullTrace : ℝ :=
    2 * LinearMap.trace ℝ (TM x)
      ((((raise'.comp (g.ricciDualContinuousAt x) +
          (g.metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
          (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
  change HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x)
    (g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
      - 2 * covRicciNormSqAt g x
      + g.pinchingRicciNormReactionMotionTraceAt x fullTrace) t₀
  have hDeriv :
      HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x) fullTrace t₀ := by
    simpa [g, δRic3, hRic3, fullTrace] using
      hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt_reaction3
        (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
        hRaise hEvol hn
  have hBochner :
      g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x =
        2 * roughRicciLaplacianPairingAt g x + 2 * covRicciNormSqAt g x := by
    simpa [g] using
      laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq
        (g := gt t₀) (x := x) hRicNorm₂ hPairDiff hRicSecond
  convert hDeriv using 1
  simp [ClosedSmoothRiemannianMetric.pinchingRicciNormReactionMotionTraceAt]
  linarith

set_option maxHeartbeats 8000000 in
/--
Assemble the corrected quotient evolution from the proved scalar and
Ricci-norm parabolic forms, with the spatial completed-square algebra kept as
an explicit named hypothesis.  No reaction-sign assumption is used.
-/
theorem satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_completed_square
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x)
    (hScalar : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hn : n = 3)
    (hRpos : 0 < (gt t₀).scalarAt x)
    (hRicNorm₂ : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).ricciNormSqAt y) x)
    (hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt (gt t₀) y (extend E w y)) x)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (ricciVariationField (gt t₀)) x)
    (hSquare :
      PinchingQuotientCompletedSquareIdentityAt (gt t₀) x) :
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let δRic3 : TM x → TM x → ℝ :=
      fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
    let hRic3 : ∀ u w : TM x,
        HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
      SatisfiesRicciEvolutionAt.reaction3
        (gt := gt) (t₀ := t₀) (x := x) hRicci hn
    let fullTrace : ℝ :=
      2 * LinearMap.trace ℝ (TM x)
        ((((raise'.comp (g.ricciDualContinuousAt x) +
            (g.metricRaiseContinuousAt x).comp
              (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
            (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
      (g.pinchingRicciNormReactionMotionTraceAt x fullTrace) := by
  classical
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let δRic3 : TM x → TM x → ℝ :=
    fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
  let hRic3 : ∀ u w : TM x,
      HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
    SatisfiesRicciEvolutionAt.reaction3
      (gt := gt) (t₀ := t₀) (x := x) hRicci hn
  let fullTrace : ℝ :=
    2 * LinearMap.trace ℝ (TM x)
      ((((raise'.comp (g.ricciDualContinuousAt x) +
          (g.metricRaiseContinuousAt x).comp
            (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
              (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
          (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
        TM x →ₗ[ℝ] TM x)
  change ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
      (g.pinchingRicciNormReactionMotionTraceAt x fullTrace)
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let lapN : ℝ := g.laplacianAt (fun y : M ↦ g.ricciNormSqAt y) x
  let lapR : ℝ := g.laplacianAt (fun y : M ↦ g.scalarAt y) x
  let A : ℝ := covRicciNormSqAt g x
  let Mreact : ℝ := g.pinchingRicciNormReactionMotionTraceAt x fullTrace
  let Sreact : ℝ := g.pinchingScalarReactionAt x
  let Nrhs : ℝ := lapN - 2 * A + Mreact
  let Rrhs : ℝ := lapR + Sreact
  have hRne : R ≠ 0 := ne_of_gt (by simpa [g, R] using hRpos)
  have hN :
      HasDerivAt (fun t ↦ (gt t).ricciNormSqAt x) Nrhs t₀ := by
    simpa [g, δRic3, hRic3, fullTrace, R, N, lapN, A, Mreact, Nrhs] using
      hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3
        (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
        hRaise hRicci hn hRicNorm₂ hPairDiff hRicSecond
  have hR :
      HasDerivAt (fun t ↦ (gt t).scalarAt x) Rrhs t₀ := by
    simpa [SatisfiesHamiltonScalarEvolutionAt, g, lapR, Sreact, Rrhs,
      ClosedSmoothRiemannianMetric.pinchingScalarReactionAt] using hScalar
  have hQ :
      HasDerivAt (fun t ↦ (gt t).pinchingQuotientAt x)
        (ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
          (gt := gt) (t₀ := t₀) (x := x)
          Nrhs Rrhs) t₀ :=
    ClosedSmoothRiemannianMetric.hasDerivAt_pinchingQuotientAt_of_scalar_and_ricciNorm
      (gt := gt) (t₀ := t₀) (x := x) hN hR (by simpa [g, R] using hRne)
  refine ⟨by simpa [g, R] using hRpos, ?_⟩
  refine ⟨ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
    (gt := gt) (t₀ := t₀) (x := x)
    Nrhs Rrhs, hQ, ?_⟩
  have hSquare' :
      lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2 =
        g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
          + g.pinchingQuotientGradientDrift3At x
          + g.pinchingGradientDampingAt x := by
    simpa [PinchingQuotientCompletedSquareIdentityAt, g, R, N, A, lapN, lapR] using
      hSquare hRne
  have hReaction :
      Mreact / R ^ 2 - 2 * N * Sreact / R ^ 3 =
        (2 / R ^ 4) * (g.pinchingReactionRemainderAt x Mreact) := by
    simpa [ClosedSmoothRiemannianMetric.pinchingReactionRemainderAt,
      R, N, Sreact, Mreact] using
      pinching_reaction_remainder_algebra
        (R := R) (N := N) (M := Mreact) (S := Sreact) hRne
  have hDerivAlg :
      ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
          (gt := gt) (t₀ := t₀) (x := x)
          Nrhs Rrhs =
        (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2)
          + (Mreact / R ^ 2 - 2 * N * Sreact / R ^ 3) := by
    change
      (Nrhs * R ^ 2 - N * (2 * R ^ (2 - 1) * Rrhs)) / (R ^ 2) ^ 2 =
        (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2)
          + (Mreact / R ^ 2 - 2 * N * Sreact / R ^ 3)
    rw [quotient_derivative_sq_algebra (R := R) (N := N)
      (N' := Nrhs) (R' := Rrhs) hRne]
    dsimp [Nrhs, Rrhs]
    ring_nf
  have hFinalEq :
      ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
          (gt := gt) (t₀ := t₀) (x := x) Nrhs Rrhs =
        g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
          + g.pinchingQuotientGradientDrift3At x
          + g.pinchingGradientDampingAt x
          + (2 / (g.scalarAt x) ^ 4) *
              (g.pinchingReactionRemainderAt x Mreact) := by
    calc
      ClosedSmoothRiemannianMetric.pinchingQuotientDerivativeAt
          (gt := gt) (t₀ := t₀) (x := x) Nrhs Rrhs
          = (lapN / R ^ 2 - 2 * N * lapR / R ^ 3 - 2 * A / R ^ 2)
              + (Mreact / R ^ 2 - 2 * N * Sreact / R ^ 3) := hDerivAlg
      _ = (g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
            + g.pinchingQuotientGradientDrift3At x
            + g.pinchingGradientDampingAt x)
          + (2 / R ^ 4) * (g.pinchingReactionRemainderAt x Mreact) := by
            rw [hSquare', hReaction]
      _ = g.laplacianAt (fun y : M ↦ g.pinchingQuotientAt y) x
            + g.pinchingQuotientGradientDrift3At x
            + g.pinchingGradientDampingAt x
            + (2 / (g.scalarAt x) ^ 4) *
                (g.pinchingReactionRemainderAt x Mreact) := by
            simp [R, add_assoc]
  exact le_of_eq hFinalEq

set_option maxHeartbeats 8000000 in
/--
Quotient evolution assembly with the completed-square obligation replaced by
the explicit spatial quotient/drift expansion.
-/
theorem satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x)
    (hScalar : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hn : n = 3)
    (hRpos : 0 < (gt t₀).scalarAt x)
    (hRicNorm₂ : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).ricciNormSqAt y) x)
    (hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt (gt t₀) y (extend E w y)) x)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (ricciVariationField (gt t₀)) x)
    (hSpatial : (gt t₀).scalarAt x ≠ 0 →
      (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).pinchingQuotientAt y) x
          + (gt t₀).pinchingQuotientGradientDrift3At x =
        (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).ricciNormSqAt y) x /
            ((gt t₀).scalarAt x) ^ 2
          - 2 * (gt t₀).ricciNormSqAt x *
              (gt t₀).laplacianAt (fun y : M ↦ (gt t₀).scalarAt y) x /
                ((gt t₀).scalarAt x) ^ 3
          - 4 * (gt t₀).pinchingMixedGradientPairingAt x /
                ((gt t₀).scalarAt x) ^ 3
          + 2 * (gt t₀).pinchingScalarRicciGradientProductAt x /
                ((gt t₀).scalarAt x) ^ 4) :
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let δRic3 : TM x → TM x → ℝ :=
      fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
    let hRic3 : ∀ u w : TM x,
        HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
      SatisfiesRicciEvolutionAt.reaction3
        (gt := gt) (t₀ := t₀) (x := x) hRicci hn
    let fullTrace : ℝ :=
      2 * LinearMap.trace ℝ (TM x)
        ((((raise'.comp (g.ricciDualContinuousAt x) +
            (g.metricRaiseContinuousAt x).comp
              (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
            (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
      (g.pinchingRicciNormReactionMotionTraceAt x fullTrace) := by
  exact satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_completed_square
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hRaise hRicci hScalar hn hRpos hRicNorm₂ hPairDiff hRicSecond
    (pinchingQuotientCompletedSquareIdentityAt_of_spatial_expansions
      (g := gt t₀) (x := x) hSpatial)

set_option maxHeartbeats 8000000 in
/--
Unconditional quotient evolution assembly from Ricci flow and the proved
spatial quotient/drift expansion.  The remaining hypotheses are regularity
classes consumed by the scalar, Ricci-norm, and quotient product-rule APIs.
-/
theorem satisfiesPinchingQuotientEvolutionAt_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hRicci : SatisfiesRicciEvolutionAt gt t₀ x)
    (hScalar : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hn : n = 3)
    (hRpos : 0 < (gt t₀).scalarAt x)
    (hRicNorm₂ : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).ricciNormSqAt y) x)
    (hPairDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ covRicciRicciPairingAt (gt t₀) y (extend E w y)) x)
    (hRicSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (ricciVariationField (gt t₀)) x)
    (hScalarCont : ContinuousAt (fun y : M ↦ (gt t₀).scalarAt y) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hQuotDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).pinchingQuotientAt z) y)
    (hScalarGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt t₀).gradient (fun y : M ↦ (gt t₀).scalarAt y))) x)
    (hQuotGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt t₀).gradient (fun y : M ↦ (gt t₀).pinchingQuotientAt y))) x)
    (hScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt t₀).gradient (fun y : M ↦
          (gt t₀).scalarAt y * (gt t₀).scalarAt y))) x)
    (hQuotScalarSqGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt t₀).gradient ((fun y : M ↦ (gt t₀).pinchingQuotientAt y) *
          (fun y : M ↦ (gt t₀).scalarAt y * (gt t₀).scalarAt y)))) x) :
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let δRic3 : TM x → TM x → ℝ :=
      fun u w ↦ ricciEvolution3ReactionRHSAt g x u w
    let hRic3 : ∀ u w : TM x,
        HasDerivAt (fun t ↦ (gt t).ricciAt x u w) (δRic3 u w) t₀ :=
      SatisfiesRicciEvolutionAt.reaction3
        (gt := gt) (t₀ := t₀) (x := x) hRicci hn
    let fullTrace : ℝ :=
      2 * LinearMap.trace ℝ (TM x)
        ((((raise'.comp (g.ricciDualContinuousAt x) +
            (g.metricRaiseContinuousAt x).comp
              (ClosedSmoothRiemannianMetric.ricciDerivativeDualContinuousAt
                (gt := gt) (t₀ := t₀) (x := x) δRic3 hRic3)).comp
            (g.ricciEndoContinuousAt x)) : TM x →L[ℝ] TM x) :
          TM x →ₗ[ℝ] TM x)
    ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt t₀ x
      (g.pinchingRicciNormReactionMotionTraceAt x fullTrace) := by
  have hRicNormGrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt t₀).gradient (fun y : M ↦ (gt t₀).ricciNormSqAt y))) x := by
    simpa using (gt t₀).mdifferentiableAt_gradient hRicNorm₂
  exact satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hRaise hRicci hScalar hn hRpos hRicNorm₂ hPairDiff hRicSecond
    (by
      intro _
      exact (gt t₀).pinchingQuotient_spatial_expansion
        x hRpos hScalarCont hScalarDiff hQuotDiff
        hScalarGrad hQuotGrad hScalarSqGrad hQuotScalarSqGrad hRicNormGrad)

namespace ClosedSmoothRiemannianMetric

section StaticFlat

variable (g : ClosedSmoothRiemannianMetric n M)
variable [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]

/-- A vanishing Ricci bilinear form has zero raised Ricci endomorphism. -/
theorem ricciEndoAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciEndoAt x = 0 := by
  ext u
  simp only [LinearMap.zero_apply]
  exact LeviCivitaExistence.metric_nondegenerate g x (g.ricciEndoAt x u) fun w ↦ by
    rw [g.inner_ricciEndoAt, hric u w]

/-- A vanishing Ricci bilinear form has zero pointwise squared Ricci norm. -/
theorem ricciNormSqAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.ricciNormSqAt x = 0 := by
  rw [g.ricciNormSqAt_eq_trace, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/-- A vanishing Ricci bilinear form has zero scalar curvature. -/
theorem scalarAt_eq_zero_of_ricciAt_eq_zero {x : M}
    (hric : ∀ u w : TM x, g.ricciAt x u w = 0) :
    g.scalarAt x = 0 := by
  rw [g.scalarAt_eq_trace_ricciEndoAt, g.ricciEndoAt_eq_zero_of_ricciAt_eq_zero hric]
  simp

/--
If the Ricci bilinear form vanishes everywhere, then the scalar curvature
function is identically zero, so its Laplacian vanishes by `laplacianAt_const`.
-/
theorem laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) (x : M) :
    g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 := by
  have hscalar :
      (fun y : M ↦ g.scalarAt y) = fun _ : M ↦ 0 := by
    funext y
    exact g.scalarAt_eq_zero_of_ricciAt_eq_zero (hric y)
  rw [hscalar]
  exact g.laplacianAt_const 0 x

/-- Along a time-constant metric family, scalar curvature has zero time derivative. -/
theorem hasDerivAt_scalarAt_const (t₀ : ℝ) (x : M) :
    HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ := by
  simpa using hasDerivAt_const t₀ (g.scalarAt x)

end StaticFlat

end ClosedSmoothRiemannianMetric

/--
Static Ricci-flat closed metrics satisfy the closed Hamilton scalar evolution
equation.

The Ricci-flatness hypothesis is the genuine pointwise bilinear vanishing
needed here: it implies both `scalarAt ≡ 0` and `ricciNormSqAt = 0`.
-/
theorem hamilton_scalar_evolution_static_flat
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (t₀ : ℝ) (x : M)
    (hric : ∀ y : M, ∀ u w : TM y, g.ricciAt y u w = 0) :
    SatisfiesHamiltonScalarEvolutionAt (fun _ : ℝ ↦ g) t₀ x := by
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (((fun _ : ℝ ↦ g) t).leviCivita) 1 :=
    fun _ ↦ inferInstance
  have hderiv : HasDerivAt (fun _ : ℝ ↦ g.scalarAt x) 0 t₀ :=
    g.hasDerivAt_scalarAt_const t₀ x
  have hlap : g.laplacianAt (fun y ↦ g.scalarAt y) x = 0 :=
    g.laplacianAt_scalarAt_eq_zero_of_ricciAt_eq_zero hric x
  have hnorm : g.ricciNormSqAt x = 0 :=
    g.ricciNormSqAt_eq_zero (hric x)
  have hrhs : g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x = 0 := by
    rw [hlap, hnorm]
    ring
  unfold SatisfiesHamiltonScalarEvolutionAt
  rw [hrhs]
  simpa using hderiv

/--
The predicate package still needed to turn the closed scalar-variation formula
into Hamilton's scalar evolution at one spacetime point.
-/
def HamiltonScalarEvolutionPredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceAssemblyAt gt t₀ x ∧
    DeltaGammaContractionTraceAssemblyAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

/--
Variant predicate package where the two `δΓ` divergence assemblies are supplied
in Hessian-trace form.  The conversion to `HamiltonScalarEvolutionPredicatesAt`
uses only `laplacianAt_eq_sum_hessianAt`.
-/
def HamiltonScalarEvolutionHessianPredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x ∧
    DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

/--
Variant predicate package where the two Hessian assemblies are supplied by the
more local second-order trace-derivative bridges.
-/
def HamiltonScalarEvolutionTraceDerivativePredicatesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1] :
    Prop :=
  ∃ raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x,
    ClosedRicciFlowExtensionRegularAt gt t₀ x ∧
    MetricFlowRegularAt gt t₀ x ∧
    TimeDifferentiableAt gt t₀ x ∧
    HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀ ∧
    DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x ∧
    DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x ∧
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x ∧
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x ∧
    TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x ∧
    ClosedContractedBianchiAt (gt t₀) x

theorem hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionHessianPredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionPredicatesAt gt t₀ x := by
  rcases hPred with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact
    ⟨raise', hext, hreg, hgt, hRaise,
      deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv,
      deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩

theorem hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionTraceDerivativePredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionHessianPredicatesAt gt t₀ x := by
  rcases hPred with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact
    ⟨raise', hext, hreg, hgt, hRaise,
      deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative hDiv,
      deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩

theorem hamiltonScalarEvolutionPredicatesAt_of_traceDerivativePredicates
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hPred : HamiltonScalarEvolutionTraceDerivativePredicatesAt gt t₀ x) :
    HamiltonScalarEvolutionPredicatesAt gt t₀ x :=
  hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
    (hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates hPred)

/--
Hamilton scalar evolution follows from a closed Ricci-flow solution once the
closed scalar-variation predicates and contracted-Bianchi obligation are
available at the point.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hEq : ∀ v w : TM x,
      timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w :=
    fun v w ↦
      isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt hflow hext v w
  have hHas :=
    hasDerivAt_scalarAt_lichnerowicz
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hreg hgt hRaise hDiv hCon
  have hPair :
      metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        -2 * (gt t₀).ricciNormSqAt x :=
    metricVariationRicciPairingAt_timeDeriv_eq_negTwoRicci
      (gt := gt) (t₀ := t₀) (x := x) hEq
  have hTensorNeg :
      tensorDoubleDivergenceAt (gt t₀)
          (negTwoRicciVariationField (gt t₀)) x =
        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x :=
    tensorDoubleDivergenceAt_negTwoRicci_eq_neg_laplacian_scalar
      (gt t₀) x hlin hBianchi
  have hTensorTime :
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x =
        -(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x := by
    rw [hTensorSub, hTensorNeg]
  have hRhs :
      tensorDoubleDivergenceAt (gt t₀) (timeDerivAt gt t₀) x
          - (gt t₀).laplacianAt
            (fun y ↦ traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) y) x
          - metricVariationRicciPairingAt (gt t₀) (timeDerivAt gt t₀) x =
        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x +
          2 * (gt t₀).ricciNormSqAt x := by
    rw [hTensorTime, hTraceLap, hPair]
    ring
  unfold SatisfiesHamiltonScalarEvolutionAt
  convert hHas using 1
  exact hRhs.symm

/--
Hamilton scalar evolution with the three algebraic substitution predicates
discharged from a Ricci-flow solution on a neighborhood of `x`.

The remaining non-algebraic curvature identity is the closed twice-contracted
Bianchi predicate; the other hypotheses are the regularity and assembly data
needed by the existing scalar-variation formula and by the Laplacian/double
divergence linearity lemmas.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hflow : IsClosedRicciFlowSolutionAt gt t₀ x :=
    (hNearFlow.self_of_nhds).1
  have hext : ClosedRicciFlowExtensionRegularAt gt t₀ x :=
    (hNearFlow.self_of_nhds).2
  have hTensorSub :
      TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x :=
    TensorDoubleDivergenceTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
      (gt := gt) (t₀ := t₀) (x := x) hNearFlow
  have hTraceLap :
      TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x :=
    TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt.of_isClosedRicciFlowSolutionAt_near
      (gt := gt) (t₀ := t₀) (x := x) hNearFlow
      hTraceGrad hNegScalarGrad hScalarDiff hScalarGrad
  have hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x :=
    TensorDoubleDivergenceNegTwoRicciLinearityAt.of_covTensor2Regular
      (gt t₀) x hRicDiff hRicDivDiff
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hflow hext hreg hgt hRaise hDiv hCon
      hTensorSub hTraceLap hlin hBianchi

/--
Hamilton scalar evolution for a closed Ricci-flow solution, with the closed
contracted-Bianchi identity discharged by the canonical second-Bianchi chain.

The remaining hypotheses are the regularity and scalar-variation assembly
data consumed by the existing variation formula and substitution lemmas.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
    (hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hScalar₂ :
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t₀).scalarAt y) x)
    (hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ (gt t₀).scalarAt z) y (extend E w y)) x)
    (hRicDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    simpa using (gt t₀).mdifferentiableAt_gradient hScalar₂
  have hBianchi : ClosedContractedBianchiAt (gt t₀) x :=
    closedContractedBianchiAt_canonical
      (g := gt t₀) (x := x) hScalar₂ hScalarExt₂
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation_algebraic_tail
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hNearFlow hreg hgt hRaise hDiv hCon hTraceGrad hNegScalarGrad
    hScalarDiff hScalarGrad hRicDiff hRicDivDiff hBianchi

/-
Remaining hypotheses in `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'`.

* `hNearFlow`: neighborhood Ricci-flow equation plus extension regularity; used
  to substitute `timeDerivAt = -2 Ric` in the algebraic tail.
* `hNearRegExt`: neighborhood metric-flow regularity and differentiated metric
  entries in canonical extension slots; supplies `hreg` and the `hExt` witness
  for both Hessian-trace `δΓ` discharge wrappers.
* `hgt`: pointwise metric time differentiability for every nearby fiber; gives
  the actual bilinear witnesses for trace-entry regularity and supplies the
  base-point `TimeDifferentiableAt` hypothesis.
* `hRaise`: derivative of the metric-raise map at `x`; this is the remaining
  time derivative witness needed by the scalar-variation formula.
* `hBridge`: the scalar-entry derivative bridge for `δΓ`; this is the
  contraction-side canonical wrapper input.
* `hSecond`, `hTimeCovDiff`: second and first covariant differentiability of
  `timeDerivAt`; these discharge the divergence-side Hessian trace.
* `hEntries`: `C²` trace-entry regularity for `timeDerivAt`; this discharges
  the contraction-side Hessian derivative and the trace-gradient witness.
* `hScalar₂`: scalar curvature is `C²` at every point of the time-slice; this
  supplies scalar differentiability, the scalar gradient witness, and the
  canonical contracted-Bianchi scalar-extension witnesses.
* `hRicDivDiff`: differentiability of the Ricci divergence one-form at `x`;
  together with canonical Ricci tensor differentiability it supplies the
  `-2 Ric` double-divergence linearity predicate.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hNearFlow :
      ∀ᶠ y in nhds x,
        IsClosedRicciFlowSolutionAt gt t₀ y ∧
        ClosedRicciFlowExtensionRegularAt gt t₀ y)
    (hNearRegExt :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀))
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x)
    (hTimeCovDiff :
      ∀ y : M, CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y)
    (hEntries : TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2)
    (hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t₀).scalarAt z) y)
    (hRicDivDiff : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (extend E w y)) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  have hreg : MetricFlowRegularAt gt t₀ x :=
    (hNearRegExt.self_of_nhds).1
  have hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun t ↦
            extDerivFun
              (fun y : M ↦ (gt t).inner y (extend E b y) (extend E c y))
              x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t₀ y (extend E b y) (extend E c y))
            x a) t₀ :=
    (hNearRegExt.self_of_nhds).2
  have hNearCon :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀) := by
    filter_upwards [hNearRegExt] with y hy
    exact ⟨hy.1, hTimeCovDiff y, hy.2⟩
  have hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x :=
    deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly
      (deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular
        (gt := gt) (t₀ := t₀) (x := x)
        hreg hgt hExt hNearRegExt hBridge hSecond hTimeCovDiff
        (by
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
          let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
          have hTrace₂ :
              ContMDiffAt I 𝓘(ℝ) 2 f x := by
            simpa [g, H, f] using
              traceMetricVariationAt_contMDiffAt_two_of_entries
                (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
                hEntries
                (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
                (by intro y p q; rfl)
          simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂))
  have hConHessian :
      DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x :=
    deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative
      (deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt
        (gt := gt) (t₀ := t₀) (x := x)
        hBridge hreg hgt hExt hNearCon hEntries
        (by
          let g : ClosedSmoothRiemannianMetric n M := gt t₀
          let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
          let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
          have hTrace₂ :
              ContMDiffAt I 𝓘(ℝ) 2 f x := by
            simpa [g, H, f] using
              traceMetricVariationAt_contMDiffAt_two_of_entries
                (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
                hEntries
                (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
                (by intro y p q; rfl)
          simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂))
  have hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x :=
    deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hConHessian
  have hTraceGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
    let f : M → ℝ := fun y ↦ traceMetricVariationAt g H y
    have hTrace₂ : ContMDiffAt I 𝓘(ℝ) 2 f x := by
      simpa [g, H, f] using
        traceMetricVariationAt_contMDiffAt_two_of_entries
          (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
          hEntries
          (fun y ↦ timeDerivBilinAt gt t₀ y (hgt y))
          (by intro y p q; rfl)
    simpa [g, H, f] using (gt t₀).mdifferentiableAt_gradient hTrace₂
  have hNegScalarGrad :
      let g : ClosedSmoothRiemannianMetric n M := gt t₀
      let f : M → ℝ := fun y ↦ (-2 : ℝ) * g.scalarAt y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    let g : ClosedSmoothRiemannianMetric n M := gt t₀
    let f : M → ℝ := fun y ↦ g.scalarAt y
    have hNeg₂ :
        ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (-2 : ℝ) * g.scalarAt y) x := by
      have hconst :
          ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ (-2 : ℝ)) x :=
        contMDiffAt_const
      simpa [g, f, Pi.smul_apply, smul_eq_mul] using
        hconst.smul (hScalar₂ x)
    simpa [g] using (gt t₀).mdifferentiableAt_gradient hNeg₂
  have hScalarDiff : ∀ y : M,
      MDifferentiableAt I 𝓘(ℝ) (fun z : M ↦ (gt t₀).scalarAt z) y :=
    fun y ↦ (hScalar₂ y).mdifferentiableAt two_ne_zero
  have hScalarExt₂ : ∀ w : TM x,
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦
          extDerivFun (fun z : M ↦ (gt t₀).scalarAt z) y (extend E w y)) x := by
    intro w
    have hW : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E w)) x := by
      simpa using (mdifferentiableAt_extend I E w)
    exact CovariantDerivative.mdiffAt_extDerivFun_apply (hScalar₂ x) hW
  exact
    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
      (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
      hNearFlow hreg (hgt x) hRaise hDiv hCon hTraceGrad hNegScalarGrad
      hScalarDiff (hScalar₂ x) hScalarExt₂
      (fun y ↦
        covTensor2ExtDifferentiableAt_ricciVariationField_canonical
          (g := gt t₀) (x := y))
      hRicDivDiff

/--
Hamilton scalar evolution from the Hessian-trace form of the two `δΓ`
assemblies.
-/
theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceHessianAssemblyAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianAssemblyAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
  satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise
    (deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly hDiv)
    (deltaGammaContractionTraceAssemblyAt_of_hessianAssembly hCon)
    hTensorSub hTraceLap hlin hBianchi

theorem satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_trace_derivative_variation
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {raise' : (TM x →L[ℝ] ℝ) →L[ℝ] TM x}
    (hflow : IsClosedRicciFlowSolutionAt gt t₀ x)
    (hext : ClosedRicciFlowExtensionRegularAt gt t₀ x)
    (hreg : MetricFlowRegularAt gt t₀ x)
    (hgt : TimeDifferentiableAt gt t₀ x)
    (hRaise : HasDerivAt (fun t ↦ (gt t).metricRaiseContinuousAt x) raise' t₀)
    (hDiv : DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x)
    (hCon : DeltaGammaContractionTraceHessianDerivativeAt gt t₀ x)
    (hTensorSub : TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x)
    (hTraceLap : TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x)
    (hlin : TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x)
    (hBianchi : ClosedContractedBianchiAt (gt t₀) x) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x :=
  satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_hessian_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise
    (deltaGammaDivergenceTraceHessianAssemblyAt_of_innerHessianDerivative hDiv)
    (deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative hCon)
    hTensorSub hTraceLap hlin hBianchi

/-- The Ricci pinching inequality gives the Hamilton reaction lower bound. -/
theorem hamilton_scalar_reaction_bound_at
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (hn : 0 < (n : ℝ)) :
    (2 / (n : ℝ)) * g.scalarAt x ^ 2 ≤ 2 * g.ricciNormSqAt x := by
  have hpinch := g.scalarAt_sq_le_nat_mul_ricciNormSqAt x
  have hscale :=
    mul_le_mul_of_nonneg_left hpinch
      (show 0 ≤ 2 / (n : ℝ) by positivity)
  calc
    (2 / (n : ℝ)) * g.scalarAt x ^ 2
        ≤ (2 / (n : ℝ)) * ((n : ℝ) * g.ricciNormSqAt x) := hscale
    _ = 2 * g.ricciNormSqAt x := by
        field_simp [ne_of_gt hn]

/--
Pointwise Hamilton-Riccati supersolution:
`∂ₜR ≥ ΔR + (2/n) R²`, with the derivative supplied by
`SatisfiesHamiltonScalarEvolutionAt`.
-/
theorem hamilton_scalar_riccati_supersolution_at
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ))
    (hHam : SatisfiesHamiltonScalarEvolutionAt gt t₀ x) :
    ∃ R',
      HasDerivAt (fun t ↦ (gt t).scalarAt x) R' t₀ ∧
        (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
            + (2 / (n : ℝ)) * (gt t₀).scalarAt x ^ 2 ≤ R' := by
  refine ⟨(gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x
      + 2 * (gt t₀).ricciNormSqAt x, ?_, ?_⟩
  · simpa [SatisfiesHamiltonScalarEvolutionAt] using hHam
  · have hreact :=
      hamilton_scalar_reaction_bound_at
        (g := gt t₀) (x := x) hn
    linarith

/--
At a spatial minimum, the Laplacian contribution is nonnegative, so the scalar
minimum obeys the pointwise Riccati differential inequality.  The hypothesis
`hMinLap` is the honest spatial-minimum witness `0 ≤ ΔR` at `x`.
-/
theorem hamilton_scalar_minimum_riccati_step_at
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ))
    (hHam : SatisfiesHamiltonScalarEvolutionAt gt t₀ x)
    (hMinLap :
      0 ≤ (gt t₀).laplacianAt (fun y ↦ (gt t₀).scalarAt y) x) :
    ∃ R',
      HasDerivAt (fun t ↦ (gt t).scalarAt x) R' t₀ ∧
        (2 / (n : ℝ)) * (gt t₀).scalarAt x ^ 2 ≤ R' := by
  rcases hamilton_scalar_riccati_supersolution_at
      (gt := gt) (t₀ := t₀) (x := x) hn hHam with
    ⟨R', hR', hineq⟩
  exact ⟨R', hR', by linarith⟩

/--
At a local spatial minimum, the closed scalar Laplacian is nonnegative.

The proof passes to the fixed chart at `x`, applies the local flat
second-derivative test to the chart representative, and then uses the
canonical-extension Hessian identity.  The connection correction vanishes
because `df x = 0` at a local minimum.
-/
theorem laplacianAt_nonneg_of_isLocalMin
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hgrad :
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x)
    (hmin : IsLocalMin f x) :
    0 ≤ g.laplacianAt f x := by
  letI : NormedAddCommGroup (TM x) := inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TM x) := inferInstanceAs (NormedSpace ℝ E)
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : T2Space (TM x) := inferInstanceAs (T2Space E)
  let F : E → ℝ := f ∘ (extChartAt I x).symm
  let z₀ : E := extChartAt I x x
  have hF₂ : ContDiffAt ℝ 2 F z₀ := by
    have h := (contMDiffAt_iff.mp hf).2
    rw [ModelWithCorners.range_eq_univ I, contDiffWithinAt_univ] at h
    have heq : (extChartAt 𝓘(ℝ, ℝ) (f x)) ∘ f ∘ (extChartAt I x).symm = F := by
      funext z
      simp [F]
    rwa [heq] at h
  have hsymm_x : (extChartAt I x).symm z₀ = x := by
    simp [z₀]
  have hFmin : IsLocalMin F z₀ := by
    have hxmin : IsLocalMin f ((extChartAt I x).symm z₀) := by
      rw [hsymm_x]
      exact hmin
    have hcont : ContinuousAt ((extChartAt I x).symm : E → M) z₀ := by
      exact continuousAt_extChartAt_symm x
    simpa [F] using hxmin.comp_continuous hcont
  have hdf0 : (extDerivFun f x : TM x →L[ℝ] ℝ) = 0 := by
    ext ξ
    have hchart :=
      extDerivFun_apply_chart
        (f := f) (x := x) (hf.mdifferentiableAt two_ne_zero) ξ
    have hzero :=
      congrArg (fun L : E →L[ℝ] ℝ => L (ξ : E)) hFmin.fderiv_eq_zero
    rw [hchart]
    simpa [F, z₀] using hzero
  have hdiag : ∀ v : TM x, 0 ≤ g.hessianContinuousAt f x v v := by
    intro v
    have hflat :
        0 ≤ fderiv ℝ (fderiv ℝ F) z₀ (v : E) (v : E) :=
      RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt hF₂ hFmin (v : E)
    have hchart :=
      extDerivFun_extDerivFun_extend_eq_fderiv_fderiv_chart
        (f := f) (x := x) hf v
    have hhess :=
      extDerivFun_extDerivFun_extend_eq_hessianAt_add
        (g := g) (f := f) (x := x) hgrad v v
    have hcorr :
        extDerivFun f x (g.leviCivita (extend E v) x v) = 0 := by
      rw [hdf0]
      rfl
    have hEq :
        g.hessianAt f x v v =
          fderiv ℝ (fderiv ℝ F) z₀ (v : E) (v : E) := by
      have hsum :
          g.hessianAt f x v v +
              extDerivFun f x (g.leviCivita (extend E v) x v) =
            fderiv ℝ (fderiv ℝ F) z₀ (v : E) (v : E) := by
        rw [← hhess, hchart]
      rwa [hcorr, add_zero] at hsum
    simpa [ClosedSmoothRiemannianMetric.hessianContinuousAt_apply, hEq] using hflat
  rw [g.laplacianAt_eq_trace_hessianContinuousAt f x]
  exact RicciFlow.trace_dual_comp_nonneg
    (g.metricBilinAt x) (g.metricBilinAt_nondegenerate x)
    (g.metricBilinAt_isSymm x) (fun v hv ↦ g.metricBilinAt_pos x hv)
    (g.hessianContinuousAt f x) hdiag

/-- On a compact closed manifold, scalar curvature attains a global minimum. -/
theorem exists_scalarAt_isMinOn
    [CompactSpace M] [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hscalar :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x) :
    ∃ x : M, IsMinOn (fun y : M ↦ g.scalarAt y) Set.univ x := by
  obtain ⟨x, hx, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty) (fun y _ ↦ (hscalar y).continuousAt.continuousWithinAt)
  exact ⟨x, hmin⟩

/-- The closed scalar-curvature minimum, defined as the infimum of the scalar range. -/
noncomputable def scalarMinimumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  sInf (Set.range fun y : M ↦ g.scalarAt y)

/-- The scalar-minimum track based at geometric time `t₀`. -/
noncomputable def scalarMinimumTrack
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) : ℝ → ℝ :=
  fun τ ↦ scalarMinimumAt (gt (t₀ + τ))

/-- If scalar curvature attains its minimum at `x`, then the infimum definition equals it. -/
theorem scalarMinimumAt_eq_of_isMinOn
    (g : ClosedSmoothRiemannianMetric n M) {x : M}
    (hmin : IsMinOn (fun y : M ↦ g.scalarAt y) Set.univ x) :
    scalarMinimumAt g = g.scalarAt x := by
  apply le_antisymm
  · exact csInf_le
      ⟨g.scalarAt x, fun y ⟨z, hzy⟩ ↦ hzy ▸ hmin trivial⟩
      ⟨x, rfl⟩
  · exact le_csInf ⟨g.scalarAt x, ⟨x, rfl⟩⟩
      fun y ⟨z, hzy⟩ ↦ hzy ▸ hmin trivial

/-- The scalar-curvature infimum lies below every point value on a compact closed slice. -/
theorem scalarMinimumAt_le_scalarAt
    [CompactSpace M] [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hscalar :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ g.scalarAt y) x)
    (x : M) :
    scalarMinimumAt g ≤ g.scalarAt x := by
  obtain ⟨x₀, hx₀min⟩ := exists_scalarAt_isMinOn (g := g) hscalar
  rw [scalarMinimumAt_eq_of_isMinOn (g := g) hx₀min]
  exact hx₀min trivial

/-- On a compact closed manifold, the pinching quotient attains a global maximum. -/
theorem exists_pinchingQuotientAt_isMaxOn
    [CompactSpace M] [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hQ :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ g.pinchingQuotientAt y) x) :
    ∃ x : M, IsMaxOn (fun y : M ↦ g.pinchingQuotientAt y) Set.univ x := by
  obtain ⟨x, hx, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty) (fun y _ ↦ (hQ y).continuousAt.continuousWithinAt)
  exact ⟨x, hmax⟩

/-- The closed pinching-quotient maximum, defined as the supremum of the range. -/
noncomputable def pinchingMaximumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
  sSup (Set.range fun y : M ↦ g.pinchingQuotientAt y)

/-- The pinching-quotient maximum track based at geometric time `t₀`. -/
noncomputable def pinchingMaximumTrack
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) : ℝ → ℝ :=
  fun τ ↦ pinchingMaximumAt (gt (t₀ + τ))

/-- If the pinching quotient attains its maximum at `x`, the supremum definition equals it. -/
theorem pinchingMaximumAt_eq_of_isMaxOn
    (g : ClosedSmoothRiemannianMetric n M) {x : M}
    (hmax : IsMaxOn (fun y : M ↦ g.pinchingQuotientAt y) Set.univ x) :
    pinchingMaximumAt g = g.pinchingQuotientAt x := by
  let S : Set ℝ := Set.range fun y : M ↦ g.pinchingQuotientAt y
  have hne : S.Nonempty := ⟨g.pinchingQuotientAt x, ⟨x, rfl⟩⟩
  have hupper : ∀ y ∈ S, y ≤ g.pinchingQuotientAt x := by
    intro y hy
    rcases hy with ⟨z, hzy⟩
    exact hzy ▸ hmax trivial
  have hbdd : BddAbove S := ⟨g.pinchingQuotientAt x, hupper⟩
  apply le_antisymm
  · exact csSup_le hne hupper
  · exact le_csSup hbdd ⟨x, rfl⟩

/-- The pinching-quotient supremum lies above every point value on a compact closed slice. -/
theorem pinchingQuotientAt_le_pinchingMaximumAt
    [CompactSpace M] [Nonempty M]
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (hQ :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ g.pinchingQuotientAt y) x)
    (x : M) :
    g.pinchingQuotientAt x ≤ pinchingMaximumAt g := by
  obtain ⟨x₀, hx₀max⟩ := exists_pinchingQuotientAt_isMaxOn (g := g) hQ
  rw [pinchingMaximumAt_eq_of_isMaxOn (g := g) hx₀max]
  exact hx₀max trivial

omit [T2Space M] in
/--
Strict compact-manifold parabolic minimum principle with a time-dependent
abstract Laplacian.  The only geometric input is the nonnegativity of the
Laplacian at a spatial minimum.
-/
theorem closed_parabolic_min_principle_strict_var
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T : ℝ}
    (hu_cont : Continuous ↿u)
    (hud : ∀ x : M, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x < u' t x)
    (hmin_lap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 < u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, 0 < u t x := by
  by_contra hviol
  push Not at hviol
  obtain ⟨t₁, ht₁, x₁, hux₁⟩ := hviol
  set m : ℝ → ℝ := fun t ↦ sInf (u t '' (Set.univ : Set M)) with hm
  have hmcont : Continuous m := (isCompact_univ : IsCompact (Set.univ : Set M)).continuous_sInf hu_cont
  have hattain : ∀ t, ∃ x : M, IsMinOn (u t) Set.univ x ∧ m t = u t x := by
    intro t
    obtain ⟨x, hxK, hxmin⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn
        (Set.univ_nonempty) ((hu_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
    refine ⟨x, hxmin, le_antisymm ?_ ?_⟩
    · exact csInf_le
        ⟨u t x, fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz⟩
        ⟨x, hxK, rfl⟩
    · exact le_csInf ((Set.univ_nonempty : (Set.univ : Set M).Nonempty).image (u t))
        fun y ⟨z, hz, hzy⟩ ↦ hzy ▸ hxmin hz
  have hmle : ∀ t (x : M), m t ≤ u t x := by
    intro t x
    exact csInf_le
      ⟨m t, fun y ⟨z, hz, hzy⟩ ↦ by
        obtain ⟨x', hmin', hmx'⟩ := hattain t
        rw [← hzy, hmx']
        exact hmin' hz⟩
      ⟨x, trivial, rfl⟩
  have hm0 : 0 < m 0 := by
    obtain ⟨x, _, hmx⟩ := hattain 0
    rw [hmx]
    exact h0 x
  have hmbad : ∃ t ∈ Icc (0 : ℝ) T, m t ≤ 0 :=
    ⟨t₁, ht₁, le_trans (hmle t₁ x₁) hux₁⟩
  obtain ⟨t₀, ht₀, hmt₀, hbefore⟩ :=
    RicciFlow.exists_first_zero (hmcont.continuousOn) hm0 hmbad
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht₀.1, ht₀.2⟩
  obtain ⟨x₀, hx₀min, hmx₀⟩ := hattain t₀
  have hux₀ : u t₀ x₀ = 0 := by rw [← hmx₀, hmt₀]
  have hder := hud x₀ t₀ ht₀Icc
  have hleft : u' t₀ x₀ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hslope := hasDerivAt_iff_tendsto_slope.mp hder
    have hev : ∀ᶠ s in nhdsWithin t₀ {t₀}ᶜ,
        0 < slope (fun s ↦ u s x₀) t₀ s :=
      hslope.eventually (eventually_gt_nhds hpos)
    have hlt : ∀ᶠ s in nhdsWithin t₀ (Iio t₀),
        0 < slope (fun s ↦ u s x₀) t₀ s := by
      apply hev.filter_mono
      apply nhdsWithin_mono
      intro s hs
      exact ne_of_lt hs
    have hIoo : ∀ᶠ s in nhdsWithin t₀ (Iio t₀), s ∈ Ioo (0 : ℝ) t₀ :=
      Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.1) fun s hs ↦ hs
    obtain ⟨s, hsl, hsIoo⟩ := (hlt.and hIoo).exists
    have hneg : u s x₀ < 0 := by
      have hde : slope (fun s ↦ u s x₀) t₀ s =
          (u s x₀ - u t₀ x₀) / (s - t₀) := by
        rw [slope_def_field]
      rw [hde, hux₀, sub_zero] at hsl
      have hst : s - t₀ < 0 := by linarith [hsIoo.2]
      by_contra hge
      push Not at hge
      have : u s x₀ / (s - t₀) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hge (le_of_lt hst)
      linarith
    have hmpos := hbefore s ⟨le_of_lt hsIoo.1, hsIoo.2⟩
    have := hmle s x₀
    linarith
  have hsup := hsuper t₀ ht₀Icc x₀
  have hlap := hmin_lap t₀ ht₀Icc x₀ hx₀min
  rw [hux₀] at hsup
  simp only [mul_zero] at hsup
  linarith

omit [T2Space M] in
/--
Compact-manifold parabolic minimum principle with variable zeroth-order
coefficient.  The constant-additivity hypothesis is only required for the
specific evolving function `u`, which is exactly what the epsilon perturbation
uses.
-/
theorem closed_parabolic_min_principle_var
    [CompactSpace M] [Nonempty M]
    {lap : ℝ → (M → ℝ) → M → ℝ}
    {u u' : ℝ → M → ℝ} {c : ℝ → M → ℝ} {T M₀ : ℝ}
    (hcM : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, c t x ≤ M₀)
    (hu_cont : Continuous ↿u)
    (hud : ∀ x : M, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ u s x) (u' t x) t)
    (hlap_add_const : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : ℝ, ∀ x : M,
      lap t (fun y : M ↦ u t y + k) x = lap t (u t) x)
    (hsuper : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      lap t (u t) x + c t x * u t x ≤ u' t x)
    (hmin_lap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      IsMinOn (u t) Set.univ x → 0 ≤ lap t (u t) x)
    (h0 : ∀ x : M, 0 ≤ u 0 x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, 0 ≤ u t x := by
  intro t ht x
  by_contra hneg
  push Not at hneg
  set M' : ℝ := max M₀ 0 + 1 with hM'
  set ε : ℝ := -u t x / (2 * Real.exp (M' * t)) with hε
  have hexp : (0 : ℝ) < Real.exp (M' * t) := Real.exp_pos _
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by positivity)
  have hvpos := closed_parabolic_min_principle_strict_var
    (lap := lap)
    (u := fun s y ↦ u s y + ε * Real.exp (M' * s))
    (u' := fun s y ↦ u' s y + ε * M' * Real.exp (M' * s))
    (c := c) (T := T)
    (by
      apply Continuous.add hu_cont
      exact (continuous_const.mul ((continuous_const.mul
        continuous_fst).rexp)).comp continuous_id)
    (by
      intro y s hs
      have h1 := hud y s hs
      have h2 : HasDerivAt (fun r ↦ ε * Real.exp (M' * r))
          (ε * M' * Real.exp (M' * s)) s := by
        have h3 := (((hasDerivAt_id s).const_mul M').exp).const_mul ε
        simp only [id_eq] at h3
        convert h3 using 1
        ring
      simpa using h1.add h2)
    (by
      intro s hs y
      have hsup := hsuper s hs y
      have hlap : lap s (fun z : M ↦ u s z + ε * Real.exp (M' * s)) y =
          lap s (u s) y :=
        hlap_add_const s hs (ε * Real.exp (M' * s)) y
      simp only
      rw [hlap]
      have hcy := hcM s hs y
      have hM1 : c s y < M' := by
        rw [hM']
        have : M₀ ≤ max M₀ 0 := le_max_left M₀ 0
        linarith
      have heps : 0 < ε * Real.exp (M' * s) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hM1 heps])
    (by
      intro s hs y hminv
      have hminu : IsMinOn (u s) Set.univ y := by
        intro z hz
        have := hminv hz
        simpa using this
      have hlapu := hmin_lap s hs y hminu
      rwa [hlap_add_const s hs (ε * Real.exp (M' * s)) y])
    (by
      intro y
      have := h0 y
      positivity)
  have := hvpos t ht x
  simp only at this
  rw [hε] at this
  have hne : Real.exp (M' * t) ≠ 0 := ne_of_gt hexp
  field_simp at this
  linarith

/--
Hamilton's positive scalar lower bound on a compact closed Ricci-flow track.
If the initial scalar minimum is at least `c > 0`, then scalar curvature stays
above the Riccati barrier `c / (1 - (2/n)cτ)` while that barrier is finite.
-/
theorem hamilton_scalar_lower_bound
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T c B : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ)) (hc : 0 < c) (hT0 : 0 ≤ T)
    (hT : (2 / (n : ℝ)) * c * T < 1)
    (hR_cont : Continuous ↿(fun τ (x : M) ↦ (gt (t₀ + τ)).scalarAt x))
    (hHam : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x)
    (hScalar₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x)
    (hRB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).scalarAt x ≤ B)
    (h0 : c ≤ scalarMinimumTrack gt t₀ 0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      c / (1 - (2 / (n : ℝ)) * c * τ) ≤ (gt (t₀ + τ)).scalarAt x := by
  let a : ℝ := 2 / (n : ℝ)
  let R : ℝ → M → ℝ := fun τ x ↦ (gt (t₀ + τ)).scalarAt x
  let R' : ℝ → M → ℝ := fun τ x ↦
    (gt (t₀ + τ)).laplacianAt (R τ) x +
      2 * (gt (t₀ + τ)).ricciNormSqAt x
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hRd : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' τ x) τ := by
    intro x τ hτ
    have hbase :
        HasDerivAt (fun t ↦ (gt t).scalarAt x) (R' τ x) (t₀ + τ) := by
      simpa [SatisfiesHamiltonScalarEvolutionAt, R, R'] using hHam τ hτ x
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [R] using hbase.comp τ hshift
  have hevol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).laplacianAt (R τ) x + a * (R τ x) ^ 2 ≤ R' τ x := by
    intro τ hτ x
    have hreact :=
      hamilton_scalar_reaction_bound_at
        (g := gt (t₀ + τ)) (x := x) hn
    dsimp [a, R, R']
    linarith
  have hscalar0 :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t₀).scalarAt y) x := by
    intro x
    simpa using hScalar₂ 0 ⟨le_refl 0, hT0⟩ x
  have h0point : ∀ x : M, c ≤ R 0 x := by
    intro x
    have hminle :=
      scalarMinimumAt_le_scalarAt
        (g := gt t₀) hscalar0 x
    exact le_trans h0 (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
  set δ : ℝ := (1 - a * c * T) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set φ : ℝ → ℝ := fun t ↦ c / max (1 - a * c * t) δ with hφ
  have hφeq : ∀ t ∈ Icc (0 : ℝ) T,
      φ t = c / (1 - a * c * t) := by
    intro t ht
    rw [hφ]
    simp only
    congr 1
    apply max_eq_left
    have h1 : a * c * t ≤ a * c * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    rw [hδ]
    linarith
  have hden : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 - a * c * t := by
    intro t ht
    have h1 : a * c * t ≤ a * c * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have hφd : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt φ (a * (φ t) ^ 2) t := by
    intro t ht
    have hd := hden t ht
    have hf : HasDerivAt (fun s ↦ 1 - a * c * s) (-(a * c)) t := by
      simpa using ((hasDerivAt_id t).const_mul (a * c)).const_sub 1
    have hinv : HasDerivAt (fun s ↦ (1 - a * c * s)⁻¹)
        (a * c / (1 - a * c * t) ^ 2) t := by
      have h2 := hf.inv (ne_of_gt hd)
      convert h2 using 1
      field_simp
    have hexact := hinv.const_mul c
    have hopen : ∀ᶠ s in nhds t, φ s = c * (1 - a * c * s)⁻¹ := by
      have hcont : Continuous (fun s ↦ 1 - a * c * s) := by
        continuity
      have hδlt : δ < 1 - a * c * t := by
        have h1 : a * c * t ≤ a * c * T := by
          apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
        rw [hδ]
        linarith
      have hev : ∀ᶠ s in nhds t, δ < 1 - a * c * s :=
        hcont.continuousAt.eventually_const_lt hδlt
      filter_upwards [hev] with s hs
      rw [hφ]
      simp only
      rw [max_eq_left (le_of_lt hs), div_eq_mul_inv]
    have hres : HasDerivAt φ (c * (a * c / (1 - a * c * t) ^ 2)) t :=
      hexact.congr_of_eventuallyEq hopen
    convert hres using 1
    rw [hφeq t ht]
    field_simp
  have hφmono : ∀ t ∈ Icc (0 : ℝ) T, φ t ≤ φ T := by
    intro t ht
    rw [hφeq t ht, hφeq T ⟨hT0, le_refl T⟩]
    apply div_le_div_of_nonneg_left (le_of_lt hc) (hden T ⟨hT0, le_refl T⟩)
    have : a * c * t ≤ a * c * T := by
      apply mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have hkey := closed_parabolic_min_principle_var
    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
    (u := fun τ x ↦ R τ x - φ τ)
    (u' := fun τ x ↦ R' τ x - a * (φ τ) ^ 2)
    (c := fun τ x ↦ a * (R τ x + φ τ))
    (T := T) (M₀ := a * (B + φ T))
    (by
      intro τ hτ x
      have h1 := hRB τ hτ x
      have h2 := hφmono τ hτ
      nlinarith)
    (by
      apply hR_cont.sub
      have hφcont : Continuous φ := by
        rw [hφ]
        apply Continuous.div continuous_const
        · exact (Continuous.max (by continuity) continuous_const)
        · intro s
          have : δ ≤ max (1 - a * c * s) δ := le_max_right _ _
          intro hzero
          rw [hzero] at this
          linarith
      exact hφcont.comp continuous_fst)
    (by
      intro x τ hτ
      exact (hRd x τ hτ).sub (hφd τ hτ))
    (by
      intro τ hτ k x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun z : M ↦ R τ z - φ τ) y := by
        intro y
        have hconst : ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ φ τ) y :=
          contMDiffAt_const
        exact (hScalar₂ τ hτ y).sub hconst
      have hk : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
        fun _ ↦ contMDiffAt_const
      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ + k) x =
        (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
      rw [show (fun y : M ↦ R τ y - φ τ + k) =
          (fun z : M ↦ R τ z - φ τ) + fun _ : M ↦ k from by
            rfl]
      rw [(gt (t₀ + τ)).laplacianAt_add'
        (f := fun z : M ↦ R τ z - φ τ) (h := fun _ : M ↦ k)
        (x := x) hf hk]
      rw [(gt (t₀ + τ)).laplacianAt_const k x]
      ring)
    (by
      intro τ hτ x
      have hev := hevol τ hτ x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (R τ) y := by
        intro y
        exact hScalar₂ τ hτ y
      have hconst : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2
          (fun _ : M ↦ -(φ τ)) y :=
        fun _ ↦ contMDiffAt_const
      have hlap : (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x =
          (gt (t₀ + τ)).laplacianAt (R τ) x := by
        rw [show (fun y : M ↦ R τ y - φ τ) =
            (fun y : M ↦ R τ y) + fun _ : M ↦ -(φ τ) from by
              funext y
              rw [sub_eq_add_neg]
              rfl]
        rw [(gt (t₀ + τ)).laplacianAt_add'
          (f := R τ) (h := fun _ : M ↦ -(φ τ)) (x := x) hf hconst]
        rw [(gt (t₀ + τ)).laplacianAt_const (-(φ τ)) x]
        ring
      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y - φ τ) x
          + a * (R τ x + φ τ) * (R τ x - φ τ) ≤ R' τ x - a * φ τ ^ 2
      rw [hlap]
      nlinarith [hev])
    (by
      intro τ hτ x hmin
      have hf : ContMDiffAt I 𝓘(ℝ) 2
          (fun y : M ↦ R τ y - φ τ) x := by
        have hconst : ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ φ τ) x :=
          contMDiffAt_const
        exact (hScalar₂ τ hτ x).sub hconst
      exact laplacianAt_nonneg_of_isLocalMin
        (g := gt (t₀ + τ))
        (f := fun y : M ↦ R τ y - φ τ)
        (x := x) hf ((gt (t₀ + τ)).mdifferentiableAt_gradient hf)
        (hmin.isLocalMin Filter.univ_mem))
    (by
      intro x
      have h00 := h0point x
      have hφ0 : φ 0 = c := by
        rw [hφeq 0 ⟨le_refl 0, hT0⟩]
        simp
      simp only
      rw [hφ0]
      exact sub_nonneg.mpr h00)
  intro τ hτ x
  have hfin := hkey τ hτ x
  simp only at hfin
  have hφle : φ τ ≤ R τ x := by linarith
  rw [hφeq τ hτ] at hφle
  simpa [a, R] using hφle

/--
Hamilton's headline nonnegative-scalar-curvature preservation theorem on a
compact closed Ricci-flow track.
-/
theorem hamilton_scalar_nonneg_preserved
    [CompactSpace M] [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ)) (hT0 : 0 ≤ T)
    (hR_cont : Continuous ↿(fun τ (x : M) ↦ (gt (t₀ + τ)).scalarAt x))
    (hHam : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x)
    (hScalar₂ : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x)
    (h0 : 0 ≤ scalarMinimumTrack gt t₀ 0) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      0 ≤ (gt (t₀ + τ)).scalarAt x := by
  let R : ℝ → M → ℝ := fun τ x ↦ (gt (t₀ + τ)).scalarAt x
  let R' : ℝ → M → ℝ := fun τ x ↦
    (gt (t₀ + τ)).laplacianAt (R τ) x +
      2 * (gt (t₀ + τ)).ricciNormSqAt x
  have hRd : ∀ x : M, ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun s ↦ R s x) (R' τ x) τ := by
    intro x τ hτ
    have hbase :
        HasDerivAt (fun t ↦ (gt t).scalarAt x) (R' τ x) (t₀ + τ) := by
      simpa [SatisfiesHamiltonScalarEvolutionAt, R, R'] using hHam τ hτ x
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [R] using hbase.comp τ hshift
  have hevol : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : M,
      (gt (t₀ + τ)).laplacianAt (R τ) x ≤ R' τ x := by
    intro τ hτ x
    have hreact :=
      hamilton_scalar_reaction_bound_at
        (g := gt (t₀ + τ)) (x := x) hn
    have hsquare :
        0 ≤ (2 / (n : ℝ)) * (gt (t₀ + τ)).scalarAt x ^ 2 := by
      positivity
    dsimp [R, R']
    linarith
  have hscalar0 :
      ∀ x : M, ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t₀).scalarAt y) x := by
    intro x
    simpa using hScalar₂ 0 ⟨le_refl 0, hT0⟩ x
  have h0point : ∀ x : M, 0 ≤ R 0 x := by
    intro x
    have hminle :=
      scalarMinimumAt_le_scalarAt
        (g := gt t₀) hscalar0 x
    exact le_trans h0 (by simpa [scalarMinimumTrack, scalarMinimumAt, R] using hminle)
  have hkey := closed_parabolic_min_principle_var
    (lap := fun τ f x ↦ (gt (t₀ + τ)).laplacianAt f x)
    (u := R) (u' := R') (c := fun _ _ ↦ (0 : ℝ))
    (T := T) (M₀ := 0)
    (by intro τ hτ x; exact le_refl (0 : ℝ))
    hR_cont
    hRd
    (by
      intro τ hτ k x
      have hf : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (R τ) y := by
        intro y
        exact hScalar₂ τ hτ y
      have hk : ∀ y : M, ContMDiffAt I 𝓘(ℝ) 2 (fun _ : M ↦ k) y :=
        fun _ ↦ contMDiffAt_const
      change (gt (t₀ + τ)).laplacianAt (fun y : M ↦ R τ y + k) x =
        (gt (t₀ + τ)).laplacianAt (R τ) x
      rw [show (fun y : M ↦ R τ y + k) = (R τ) + fun _ : M ↦ k from by
        rfl]
      rw [(gt (t₀ + τ)).laplacianAt_add'
        (f := R τ) (h := fun _ : M ↦ k) (x := x) hf hk]
      rw [(gt (t₀ + τ)).laplacianAt_const k x]
      ring)
    (by
      intro τ hτ x
      have hev := hevol τ hτ x
      simpa using hev)
    (by
      intro τ hτ x hmin
      have hf : ContMDiffAt I 𝓘(ℝ) 2 (R τ) x :=
        hScalar₂ τ hτ x
      exact laplacianAt_nonneg_of_isLocalMin
        (g := gt (t₀ + τ))
        (f := R τ)
        (x := x) hf ((gt (t₀ + τ)).mdifferentiableAt_gradient hf)
        (hmin.isLocalMin Filter.univ_mem))
    h0point
  intro τ hτ x
  simpa [R] using hkey τ hτ x

/--
Finite-time Riccati obstruction for a closed Hamilton scalar evolution track.

The interval variable is shifted: `τ ∈ [0,T]` corresponds to geometric time
`t₀ + τ`.  The hypothesis `hMinLap` is the spatial-minimum input along the
track.  Thus any smooth extension satisfying these Hamilton/minimum hypotheses
on `[t₀, t₀ + T]` must have `T < n / (2 R(t₀,x₀))`.
-/
theorem hamilton_finite_time_singularity
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ} {x₀ : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ)) (hT0 : 0 ≤ T)
    (hHam : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x₀)
    (hMinLap : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      0 ≤ (gt (t₀ + τ)).laplacianAt
        (fun y ↦ (gt (t₀ + τ)).scalarAt y) x₀)
    (hRpos : 0 < (gt t₀).scalarAt x₀) :
    T < (n : ℝ) / (2 * (gt t₀).scalarAt x₀) := by
  let u : ℝ → ℝ := fun τ ↦ (gt (t₀ + τ)).scalarAt x₀
  let u' : ℝ → ℝ := fun τ ↦
    (gt (t₀ + τ)).laplacianAt
        (fun y ↦ (gt (t₀ + τ)).scalarAt y) x₀
      + 2 * (gt (t₀ + τ)).ricciNormSqAt x₀
  have ha : 0 < 2 / (n : ℝ) := by positivity
  have hd : ∀ τ ∈ Set.Icc (0 : ℝ) T, HasDerivAt u (u' τ) τ := by
    intro τ hτ
    have hbase :
        HasDerivAt (fun t ↦ (gt t).scalarAt x₀) (u' τ) (t₀ + τ) := by
      simpa [SatisfiesHamiltonScalarEvolutionAt, u'] using hHam τ hτ
    have hshift : HasDerivAt (fun s : ℝ ↦ t₀ + s) 1 τ := by
      simpa using (hasDerivAt_id τ).const_add t₀
    simpa [u] using hbase.comp τ hshift
  have hineq : ∀ τ ∈ Set.Icc (0 : ℝ) T, (2 / (n : ℝ)) * u τ ^ 2 ≤ u' τ := by
    intro τ hτ
    have hreact :=
      hamilton_scalar_reaction_bound_at
        (g := gt (t₀ + τ)) (x := x₀) hn
    have hlap := hMinLap τ hτ
    dsimp [u, u']
    linarith
  have hfinite :=
    RicciFlow.riccati_forces_finite_time
      (u := u) (u' := u') (a := 2 / (n : ℝ)) (T := T)
      ha hT0 hd hineq (by simpa [u] using hRpos)
  have hu0pos : 0 < u 0 := by
    simpa [u] using hRpos
  calc
    T < 1 / ((2 / (n : ℝ)) * u 0) := hfinite
    _ = (n : ℝ) / (2 * u 0) := by
        field_simp [ne_of_gt hn, ne_of_gt hu0pos]
    _ = (n : ℝ) / (2 * (gt t₀).scalarAt x₀) := by
        simp [u]

/--
Finite-time Riccati obstruction using honest spatial minimum hypotheses rather
than prepackaged Laplacian nonnegativity.
-/
theorem hamilton_finite_time_singularity'
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ} {x₀ : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hn : 0 < (n : ℝ)) (hT0 : 0 ≤ T)
    (hHam : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      SatisfiesHamiltonScalarEvolutionAt gt (t₀ + τ) x₀)
    (hScalar₂ : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) x₀)
    (hScalarGrad : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% ((gt (t₀ + τ)).gradient
          (fun y : M ↦ (gt (t₀ + τ)).scalarAt y))) x₀)
    (hMin : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      IsMinOn (fun y : M ↦ (gt (t₀ + τ)).scalarAt y) Set.univ x₀)
    (hRpos : 0 < (gt t₀).scalarAt x₀) :
    T < (n : ℝ) / (2 * (gt t₀).scalarAt x₀) := by
  refine hamilton_finite_time_singularity
    (gt := gt) (t₀ := t₀) (T := T) (x₀ := x₀)
    hn hT0 hHam ?_ hRpos
  intro τ hτ
  exact laplacianAt_nonneg_of_isLocalMin
    (g := gt (t₀ + τ))
    (f := fun y : M ↦ (gt (t₀ + τ)).scalarAt y)
    (x := x₀) (hScalar₂ τ hτ) (hScalarGrad τ hτ)
    ((hMin τ hτ).isLocalMin Filter.univ_mem)

/--
The unproven closed-manifold Hamilton scalar evolution frontier.

This definition is a target statement, not a theorem: every closed Ricci-flow
solution should satisfy `∂ₜ R = ΔR + 2 |Ric|²` once the required curvature
regularity for each time-slice is available.  The single-chart analogues are
`hamilton_scalar_evolution_of_bianchi`,
`hamilton_scalar_evolution_of_bianchi_curved`,
`hamilton_scalar_evolution_ricci_flow`,
`curved_ricci_flow_scalar_evolution`, and
`curved_ricci_flow_scalar_evolution_trace_form` in `ModelLaplacian.lean`.
-/
def HamiltonScalarEvolutionProgram : Prop :=
  ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
    IsClosedRicciFlowSolutionAt gt t₀ x →
      ∀ hcurv : ∀ t : ℝ,
        CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
        letI : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
          hcurv
        SatisfiesHamiltonScalarEvolutionAt gt t₀ x

/--
Predicate-discharge version of the Hamilton scalar evolution program.

This is deliberately conditional: it packages the current closed-manifold
analytic obligations instead of asserting the unconditional program.
-/
theorem hamiltonScalarEvolutionProgram_of_predicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionPredicatesAt (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) := by
  intro gt t₀ x hflow hcurv
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
    hcurv
  rcases hPred gt t₀ x hflow hcurv with
    ⟨raise', hext, hreg, hgt, hRaise, hDiv, hCon,
      hTensorSub, hTraceLap, hlin, hBianchi⟩
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_variation
    (gt := gt) (t₀ := t₀) (x := x) (raise' := raise')
    hflow hext hreg hgt hRaise hDiv hCon hTensorSub hTraceLap hlin hBianchi

theorem hamiltonScalarEvolutionProgram_of_hessianPredicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionHessianPredicatesAt (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) :=
  hamiltonScalarEvolutionProgram_of_predicates
    (n := n) (M := M)
    (fun gt t₀ x hflow hcurv ↦ by
      letI : ∀ t : ℝ,
          CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
        hcurv
      exact hamiltonScalarEvolutionPredicatesAt_of_hessianPredicates
        (hPred gt t₀ x hflow hcurv))

theorem hamiltonScalarEvolutionProgram_of_traceDerivativePredicates
    (hPred :
      ∀ (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M),
        IsClosedRicciFlowSolutionAt gt t₀ x →
          ∀ hcurv : ∀ t : ℝ,
            CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1,
            letI : ∀ t : ℝ,
                CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
              hcurv
            HamiltonScalarEvolutionTraceDerivativePredicatesAt
              (n := n) (M := M) gt t₀ x) :
    HamiltonScalarEvolutionProgram (n := n) (M := M) :=
  hamiltonScalarEvolutionProgram_of_hessianPredicates
    (n := n) (M := M)
    (fun gt t₀ x hflow hcurv ↦ by
      letI : ∀ t : ℝ,
          CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1 :=
        hcurv
      exact hamiltonScalarEvolutionHessianPredicatesAt_of_traceDerivativePredicates
        (hPred gt t₀ x hflow hcurv))

end Poincare
