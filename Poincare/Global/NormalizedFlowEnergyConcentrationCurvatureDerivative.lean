import Poincare.Global.NormalizedFlowEnergyConcentrationLipschitzBridge
import Poincare.Global.NormalizedFlowScalarIntegralVariation
import Poincare.Global.ScalarEvolution
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Curvature-derivative source of normalized-flow energy concentration

This file contracts intrinsic first covariant-derivative data for traceless
Ricci curvature to the manifold derivative bound used by
`NormalizedFlowEnergyConcentrationLipschitzBridge`.

The scalar derivative identity is proved from the repository's actual Ricci
and scalar derivative identities:

`d |Ric°|^2(v) = 2 ⟨∇_v Ric°, Ric°⟩`.

The current tensor vocabulary defines the squared norms of `∇ Ric` and of
`dR`, but does not yet provide the Hilbert--Schmidt Cauchy--Schwarz theorem
for their traceless contraction.  Consequently that one coordinate-free
finite-dimensional inequality is recorded as an explicit proposition.  No
scalar-valued Shi estimate is reinterpreted as a uniform constant here.
-/

noncomputable section

open Bundle FiberBundle Filter Manifold MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

section IntrinsicTracelessRicciDerivative

variable {n : ℕ} {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/--
The intrinsic contraction `⟨∇_v Ric°, Ric°⟩`.  Expanding
`Ric° = Ric - (R/n)g` and using metric compatibility leaves exactly the
single trace-correction term below.
-/
noncomputable def tracelessCovRicciRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x) : ℝ :=
  covRicciRicciPairingAt g x w -
    (g.scalarAt x / (n : ℝ)) *
      extDerivFun (fun y : M ↦ g.scalarAt y) x w

/--
The squared Hilbert--Schmidt norm `|∇ Ric°|²`, in trace-decomposed
form.  It is `|∇ Ric|² - |dR|²/n` because the Levi-Civita connection
is metric compatible.
-/
noncomputable def tracelessCovRicciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) : ℝ :=
  covRicciNormSqAt g x - g.scalarGradNormSqAt x / (n : ℝ)

/-- Squared traceless Ricci curvature is manifold-differentiable. -/
theorem tracelessRicciNormSqAt_mdifferentiableAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x := by
  have hRic := ricciNormSqAt_mdifferentiableAt g x
  have hScalar := scalarAt_mdifferentiableAt (g := g) x
  have hScalarSq : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ g.scalarAt y * g.scalarAt y) x :=
    hScalar.mul hScalar
  have hScaled : MDifferentiableAt I 𝓘(ℝ)
      ((1 / (n : ℝ)) • (fun y : M ↦ g.scalarAt y * g.scalarAt y)) x :=
    hScalarSq.const_smul (1 / (n : ℝ))
  have hEq :
      (fun y : M ↦ g.tracelessRicciNormSqAt y) =
        (fun y : M ↦ g.ricciNormSqAt y) -
          ((1 / (n : ℝ)) • (fun y : M ↦ g.scalarAt y * g.scalarAt y)) := by
    funext y
    simp [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_two, div_eq_mul_inv]
    ring
  rw [hEq]
  exact hRic.sub hScaled

omit [T2Space M] in
private theorem extDerivFun_const_smul_curvatureDerivative
    {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) :
    (extDerivFun (c • f) x : TM x →L[ℝ] ℝ) =
      c • (extDerivFun f x : TM x →L[ℝ] ℝ) := by
  ext w
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun _ : M ↦ c) (q := f) (x := x)
      mdifferentiableAt_const hf w
  simp [Pi.smul_apply, smul_eq_mul] at hmul ⊢
  exact hmul

/--
The actual first derivative of squared traceless Ricci curvature is twice the
intrinsic traceless covariant-derivative contraction.
-/
theorem extDerivFun_tracelessRicciNormSqAt_eq_two_tracelessCovRicciRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M) (w : TM x) :
    extDerivFun (fun y : M ↦ g.tracelessRicciNormSqAt y) x w =
      2 * tracelessCovRicciRicciPairingAt g x w := by
  let Rf : M → ℝ := fun y ↦ g.scalarAt y
  let Nf : M → ℝ := fun y ↦ g.ricciNormSqAt y
  let Sf : M → ℝ := fun y ↦ Rf y ^ 2
  have hRic : MDifferentiableAt I 𝓘(ℝ) Nf x := by
    simpa [Nf] using ricciNormSqAt_mdifferentiableAt g x
  have hScalar : MDifferentiableAt I 𝓘(ℝ) Rf x := by
    simpa [Rf] using scalarAt_mdifferentiableAt (g := g) x
  have hSq : MDifferentiableAt I 𝓘(ℝ) Sf x := by
    simpa [Sf, pow_two] using hScalar.mul hScalar
  have hTraceEq :
      (fun y : M ↦ g.tracelessRicciNormSqAt y) =
        Nf + (-((1 : ℝ) / (n : ℝ))) • Sf := by
    funext y
    simp [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt,
      Nf, Rf, Sf, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hSum := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L w)
    (extDerivFun_add hRic
      (hSq.const_smul (-((1 : ℝ) / (n : ℝ)))))
  have hScale := congrArg (fun L : TM x →L[ℝ] ℝ ↦ L w)
    (extDerivFun_const_smul_curvatureDerivative
      (n := n) (M := M) hSq (-((1 : ℝ) / (n : ℝ))))
  have hProduct := CovariantDerivative.extDerivFun_mul
    (p := Rf) (q := Rf) (x := x) hScalar hScalar w
  rw [hTraceEq]
  have hSum' :
      extDerivFun (Nf + (-((1 : ℝ) / (n : ℝ))) • Sf) x w =
        extDerivFun Nf x w +
          extDerivFun ((-((1 : ℝ) / (n : ℝ))) • Sf) x w := by
    simpa using hSum
  rw [hSum']
  have hScale' :
      extDerivFun ((-((1 : ℝ) / (n : ℝ))) • Sf) x w =
        (-((1 : ℝ) / (n : ℝ))) * extDerivFun Sf x w := by
    simpa [smul_eq_mul] using hScale
  rw [hScale']
  have hProduct' :
      extDerivFun Sf x w = 2 * Rf x * extDerivFun Rf x w := by
    have hProduct'' :
        extDerivFun Sf x w =
          Rf x * extDerivFun Rf x w + extDerivFun Rf x w * Rf x := by
      simpa [Sf, pow_two] using hProduct
    rw [hProduct'']
    ring
  rw [hProduct']
  rw [extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
    (g := g) x w]
  simp only [tracelessCovRicciRicciPairingAt, Rf]
  ring

end IntrinsicTracelessRicciDerivative

section CurvatureDerivativeContraction

variable {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/-- In dimension three, the trace-decomposed norm `|∇ Ric°|²` is nonnegative. -/
theorem tracelessCovRicciNormSqAt_nonneg
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    0 ≤ tracelessCovRicciNormSqAt g x := by
  have hTrace := g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
  unfold tracelessCovRicciNormSqAt
  norm_num at ⊢
  linarith

private def weightedDiagonalMetric
    {β : Type*} [DecidableEq β] (diag : β → ℝ) (i j : β) : ℝ :=
  if i = j then diag i else 0

private lemma weightedDiagonalMetric_contraction
    {β : Type*} [Fintype β] [DecidableEq β]
    (diag : β → ℝ) (hdiag : ∀ i, 0 < diag i) (Φ : β → β → ℝ) :
    (∑ i, ∑ j,
      Φ i j * weightedDiagonalMetric diag i j / (diag i * diag j)) =
      ∑ i, Φ i i / diag i := by
  classical
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_eq_single i]
  · simp [weightedDiagonalMetric]
    field_simp [ne_of_gt (hdiag i)]
  · intro j _ hji
    simp [weightedDiagonalMetric, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma weightedDiagonalMetric_norm_sq
    {β : Type*} [Fintype β] [DecidableEq β]
    (hcard : Fintype.card β = 3)
    (diag : β → ℝ) (hdiag : ∀ i, 0 < diag i) :
    (∑ i, ∑ j,
      (weightedDiagonalMetric diag i j) ^ 2 / (diag i * diag j)) = 3 := by
  have h := weightedDiagonalMetric_contraction diag hdiag
    (weightedDiagonalMetric diag)
  simpa [pow_two, weightedDiagonalMetric, ne_of_gt (hdiag _), hcard,
    div_eq_mul_inv] using h

private lemma finset_sum_double_completed_square
    {α β : Type*} [Fintype α] [Fintype β]
    (c : ℝ) (A B W : α → β → ℝ) :
    (∑ i, ∑ j, (A i j - c * B i j) ^ 2 * W i j) =
      (∑ i, ∑ j, (A i j) ^ 2 * W i j)
        - 2 * c * (∑ i, ∑ j, A i j * B i j * W i j)
        + c ^ 2 * (∑ i, ∑ j, (B i j) ^ 2 * W i j) := by
  simp_rw [sub_sq, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring_nf
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  ring_nf

private lemma finset_sum_double_completed_pairing
    {α β : Type*} [Fintype α] [Fintype β]
    (c d : ℝ) (A B K W : α → β → ℝ) :
    (∑ i, ∑ j, (A i j - c * K i j) * (B i j - d * K i j) * W i j) =
      (∑ i, ∑ j, A i j * B i j * W i j)
        - d * (∑ i, ∑ j, A i j * K i j * W i j)
        - c * (∑ i, ∑ j, K i j * B i j * W i j)
        + c * d * (∑ i, ∑ j, (K i j) ^ 2 * W i j) := by
  have hconst : ∀ (z : ℝ) (F : α → β → ℝ),
      (∑ i, ∑ j, z * F i j) = z * (∑ i, ∑ j, F i j) := by
    intro z F
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
  have hc :
      (∑ i, ∑ j, c * K i j * B i j * W i j) =
        c * (∑ i, ∑ j, K i j * B i j * W i j) := by
    calc
      (∑ i, ∑ j, c * K i j * B i j * W i j) =
          ∑ i, ∑ j, c * (K i j * B i j * W i j) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
      _ = c * (∑ i, ∑ j, K i j * B i j * W i j) :=
        hconst c (fun i j ↦ K i j * B i j * W i j)
  have hd :
      (∑ i, ∑ j, A i j * d * K i j * W i j) =
        d * (∑ i, ∑ j, A i j * K i j * W i j) := by
    calc
      (∑ i, ∑ j, A i j * d * K i j * W i j) =
          ∑ i, ∑ j, d * (A i j * K i j * W i j) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
      _ = d * (∑ i, ∑ j, A i j * K i j * W i j) :=
        hconst d (fun i j ↦ A i j * K i j * W i j)
  have hcd :
      (∑ i, ∑ j, c * d * K i j ^ 2 * W i j) =
        c * d * (∑ i, ∑ j, K i j ^ 2 * W i j) := by
    calc
      (∑ i, ∑ j, c * d * K i j ^ 2 * W i j) =
          ∑ i, ∑ j, (c * d) * (K i j ^ 2 * W i j) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
      _ = (c * d) * (∑ i, ∑ j, K i j ^ 2 * W i j) :=
        hconst (c * d) (fun i j ↦ K i j ^ 2 * W i j)
  simp only [sub_mul, mul_sub, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring_nf
  rw [hc, hd, hcd]
  ring

private lemma weighted_traceless_matrix_norm_identity
    {β : Type*} [Fintype β] [DecidableEq β]
    (hcard : Fintype.card β = 3)
    (diag : β → ℝ) (hdiag : ∀ i, 0 < diag i)
    (A : β → β → ℝ) (R : ℝ)
    (htrace : R = ∑ i, A i i / diag i) :
    (∑ i, ∑ j,
      (A i j - (R / 3) * weightedDiagonalMetric diag i j) ^ 2 /
        (diag i * diag j)) =
      (∑ i, ∑ j, (A i j) ^ 2 / (diag i * diag j)) - R ^ 2 / 3 := by
  let K : β → β → ℝ := weightedDiagonalMetric diag
  have hCross :
      (∑ i, ∑ j, A i j * K i j / (diag i * diag j)) = R := by
    rw [weightedDiagonalMetric_contraction diag hdiag A]
    exact htrace.symm
  have hK : (∑ i, ∑ j, (K i j) ^ 2 / (diag i * diag j)) = 3 := by
    simpa [K] using weightedDiagonalMetric_norm_sq hcard diag hdiag
  have hExpand := finset_sum_double_completed_square
    (R / 3) A K (fun i j ↦ (diag i * diag j)⁻¹)
  calc
    (∑ i, ∑ j,
      (A i j - (R / 3) * weightedDiagonalMetric diag i j) ^ 2 /
        (diag i * diag j)) =
        (∑ i, ∑ j, (A i j) ^ 2 / (diag i * diag j))
          - 2 * (R / 3) *
            (∑ i, ∑ j, A i j * K i j / (diag i * diag j))
          + (R / 3) ^ 2 *
            (∑ i, ∑ j, (K i j) ^ 2 / (diag i * diag j)) := by
              simpa [K, div_eq_mul_inv] using hExpand
    _ = (∑ i, ∑ j, (A i j) ^ 2 / (diag i * diag j)) - R ^ 2 / 3 := by
      rw [hCross, hK]
      ring

private lemma weighted_traceless_covariant_norm_identity
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hcard : Fintype.card β = 3)
    (diagA : α → ℝ) (diagB : β → ℝ)
    (hdiagA : ∀ a, 0 < diagA a) (hdiagB : ∀ i, 0 < diagB i)
    (C : α → β → β → ℝ) (S : α → ℝ)
    (htrace : ∀ a, S a = ∑ i, C a i i / diagB i) :
    (∑ a, ∑ i, ∑ j,
      (C a i j - (S a / 3) * weightedDiagonalMetric diagB i j) ^ 2 /
        (diagA a * diagB i * diagB j)) =
      (∑ a, ∑ i, ∑ j,
        (C a i j) ^ 2 / (diagA a * diagB i * diagB j))
        - (∑ a, (S a) ^ 2 / diagA a) / 3 := by
  let K : β → β → ℝ := weightedDiagonalMetric diagB
  have hPer : ∀ a,
      (∑ i, ∑ j, (C a i j - (S a / 3) * K i j) ^ 2 /
          (diagB i * diagB j)) =
        (∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) -
          (S a) ^ 2 / 3 := by
    intro a
    simpa [K] using
      weighted_traceless_matrix_norm_identity hcard diagB hdiagB
        (C a) (S a) (htrace a)
  have hRegroup : ∀ (F : α → β → β → ℝ),
      (∑ a, ∑ i, ∑ j, F a i j / (diagA a * diagB i * diagB j)) =
        ∑ a, (∑ i, ∑ j, F a i j / (diagB i * diagB j)) / diagA a := by
    intro F
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp [ne_of_gt (hdiagA a), ne_of_gt (hdiagB i), ne_of_gt (hdiagB j)]
  rw [hRegroup]
  have hPer' : ∀ a,
      (∑ i, ∑ j,
        (C a i j - (S a / 3) * weightedDiagonalMetric diagB i j) ^ 2 /
          (diagB i * diagB j)) =
        (∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) -
          (S a) ^ 2 / 3 := by
    intro a
    simpa [K] using hPer a
  simp_rw [hPer']
  rw [hRegroup]
  calc
    (∑ a, ((∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) -
        (S a) ^ 2 / 3) / diagA a) =
        ∑ a, ((∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) /
          diagA a - ((S a) ^ 2 / diagA a) / 3) := by
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      ring
    _ = (∑ a, (∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) /
          diagA a) - ∑ a, ((S a) ^ 2 / diagA a) / 3 :=
      by rw [Finset.sum_sub_distrib]
    _ = (∑ a, (∑ i, ∑ j, (C a i j) ^ 2 / (diagB i * diagB j)) /
          diagA a) - (∑ a, (S a) ^ 2 / diagA a) / 3 := by
      rw [Finset.sum_div]

private lemma weighted_traceless_pairing_identity
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (hcard : Fintype.card β = 3)
    (diag : β → ℝ) (hdiag : ∀ i, 0 < diag i)
    (u : α → ℝ) (C : α → β → β → ℝ)
    (A : β → β → ℝ) (S : α → ℝ) (R : ℝ)
    (htraceA : R = ∑ i, A i i / diag i)
    (htraceC : ∀ a, S a = ∑ i, C a i i / diag i) :
    (∑ a, ∑ i, ∑ j,
      u a * (C a i j - (S a / 3) * weightedDiagonalMetric diag i j) *
        (A i j - (R / 3) * weightedDiagonalMetric diag i j) /
          (diag i * diag j)) =
      (∑ a, ∑ i, ∑ j, u a * C a i j * A i j / (diag i * diag j))
        - (R / 3) * ∑ a, u a * S a := by
  let K : β → β → ℝ := weightedDiagonalMetric diag
  have hK : (∑ i, ∑ j, (K i j) ^ 2 / (diag i * diag j)) = 3 := by
    simpa [K] using weightedDiagonalMetric_norm_sq hcard diag hdiag
  have hCrossA : (∑ i, ∑ j, K i j * A i j / (diag i * diag j)) = R := by
    have h := weightedDiagonalMetric_contraction diag hdiag A
    rw [htraceA]
    simpa [K, mul_comm] using h
  have hCrossC : ∀ a,
      (∑ i, ∑ j, C a i j * K i j / (diag i * diag j)) = S a := by
    intro a
    rw [weightedDiagonalMetric_contraction diag hdiag (C a)]
    exact (htraceC a).symm
  have hPer : ∀ a,
      (∑ i, ∑ j,
        (C a i j - (S a / 3) * K i j) *
          (A i j - (R / 3) * K i j) / (diag i * diag j)) =
        (∑ i, ∑ j, C a i j * A i j / (diag i * diag j)) -
          (R / 3) * S a := by
    intro a
    have hExpand := finset_sum_double_completed_pairing
      (S a / 3) (R / 3) (C a) A K (fun i j ↦ (diag i * diag j)⁻¹)
    calc
      (∑ i, ∑ j,
        (C a i j - (S a / 3) * K i j) *
          (A i j - (R / 3) * K i j) / (diag i * diag j)) =
          (∑ i, ∑ j, C a i j * A i j / (diag i * diag j))
            - (R / 3) *
              (∑ i, ∑ j, C a i j * K i j / (diag i * diag j))
            - (S a / 3) *
              (∑ i, ∑ j, K i j * A i j / (diag i * diag j))
            + (S a / 3) * (R / 3) *
              (∑ i, ∑ j, (K i j) ^ 2 / (diag i * diag j)) := by
                simpa [div_eq_mul_inv] using hExpand
      _ = (∑ i, ∑ j, C a i j * A i j / (diag i * diag j)) -
          (R / 3) * S a := by
        rw [hCrossC a, hCrossA, hK]
        ring
  calc
    (∑ a, ∑ i, ∑ j,
      u a * (C a i j - (S a / 3) * weightedDiagonalMetric diag i j) *
        (A i j - (R / 3) * weightedDiagonalMetric diag i j) /
          (diag i * diag j)) =
        ∑ a, u a *
          (∑ i, ∑ j,
            (C a i j - (S a / 3) * K i j) *
              (A i j - (R / 3) * K i j) / (diag i * diag j)) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [K]
          ring
    _ = ∑ a, u a *
          ((∑ i, ∑ j, C a i j * A i j / (diag i * diag j)) -
            (R / 3) * S a) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [hPer a]
    _ = (∑ a, ∑ i, ∑ j,
          u a * C a i j * A i j / (diag i * diag j)) -
          (R / 3) * ∑ a, u a * S a := by
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          rw [Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            ring
          · refine Finset.sum_congr rfl fun a _ ↦ ?_
            ring

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

private lemma weighted_triple_contraction_sq_le
    {α β : Type*} [Fintype α] [Fintype β]
    (diagA : α → ℝ) (diagB : β → ℝ)
    (hdiagA : ∀ a, 0 < diagA a) (hdiagB : ∀ i, 0 < diagB i)
    (u : α → ℝ) (A : β → β → ℝ)
    (B : α → β → β → ℝ) :
    (∑ a, ∑ i, ∑ j, u a * B a i j * A i j / (diagB i * diagB j)) ^ 2 ≤
      (∑ i, ∑ j, (A i j) ^ 2 / (diagB i * diagB j)) *
        (∑ a, ∑ i, ∑ j,
          (B a i j) ^ 2 / (diagA a * diagB i * diagB j)) *
        (∑ a, (u a) ^ 2 * diagA a) := by
  classical
  let r : (α × β × β) → ℝ := fun p ↦
    u p.1 * B p.1 p.2.1 p.2.2 * A p.2.1 p.2.2 /
      (diagB p.2.1 * diagB p.2.2)
  let f : (α × β × β) → ℝ := fun p ↦
    (B p.1 p.2.1 p.2.2) ^ 2 /
      (diagA p.1 * diagB p.2.1 * diagB p.2.2)
  let q : (α × β × β) → ℝ := fun p ↦
    ((u p.1) ^ 2 * diagA p.1) *
      ((A p.2.1 p.2.2) ^ 2 / (diagB p.2.1 * diagB p.2.2))
  have hf : ∀ p ∈ (Finset.univ : Finset (α × β × β)), 0 ≤ f p := by
    intro p _
    exact div_nonneg (sq_nonneg _)
      (le_of_lt (mul_pos (mul_pos (hdiagA p.1) (hdiagB p.2.1)) (hdiagB p.2.2)))
  have hq : ∀ p ∈ (Finset.univ : Finset (α × β × β)), 0 ≤ q p := by
    intro p _
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hdiagA p.1).le)
      (div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (hdiagB p.2.1) (hdiagB p.2.2))))
  have hr : ∀ p ∈ (Finset.univ : Finset (α × β × β)),
      (r p) ^ 2 = f p * q p := by
    intro p _
    dsimp [r, f, q]
    field_simp [ne_of_gt (hdiagA p.1), ne_of_gt (hdiagB p.2.1),
      ne_of_gt (hdiagB p.2.2)]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := (Finset.univ : Finset (α × β × β))) hf hq hr
  have hCS' :
      (∑ a, ∑ i, ∑ j, r (a, i, j)) ^ 2 ≤
        (∑ a, ∑ i, ∑ j, f (a, i, j)) *
          (∑ a, ∑ i, ∑ j, q (a, i, j)) := by
    simpa [Fintype.sum_prod_type] using hCS
  have hqFactor :
      (∑ a, ∑ i, ∑ j, q (a, i, j)) =
        (∑ a, (u a) ^ 2 * diagA a) *
          (∑ i, ∑ j, (A i j) ^ 2 / (diagB i * diagB j)) := by
    simpa [q] using
      (finset_sum_mul_sum₂
        (fun a ↦ (u a) ^ 2 * diagA a)
        (fun i j ↦ (A i j) ^ 2 / (diagB i * diagB j))).symm
  simpa [r, f, hqFactor, mul_comm, mul_left_comm, mul_assoc] using hCS'

set_option maxHeartbeats 5000000 in
/--
The exact Hilbert--Schmidt Cauchy--Schwarz contraction needed for the
traceless covariant derivative:

`|⟨∇_v Ric°, Ric°⟩|² ≤ |Ric°|² |∇ Ric°|² |v|²`.

The proof expands the repository's actual covariant Ricci derivative in its
chosen metric-orthogonal frame and applies weighted finite-dimensional
Cauchy--Schwarz on the triple frame index.
-/
theorem TracelessRicciCovariantDerivativeCauchySchwarz
    (g : ClosedSmoothRiemannianMetric 3 M) :
  ∀ x (w : TM x),
    (tracelessCovRicciRicciPairingAt g x w) ^ 2 ≤
      g.tracelessRicciNormSqAt x * tracelessCovRicciNormSqAt g x *
        g.inner x w w := by
  intro x w
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ (ClosedSmoothModel 3))
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  let u : Fin (Module.finrank ℝ (TM x)) → ℝ := fun a ↦ b.coord a w
  let A : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun i j ↦ g.ricciAt x (b i) (b j)
  let C : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦
      covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)
  let R : ℝ := g.scalarAt x
  let S : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a ↦ extDerivFun (fun y : M ↦ g.scalarAt y) x (b a)
  let A₀ : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun i j ↦ A i j - (R / 3) * weightedDiagonalMetric diag i j
  let C₀ : Fin (Module.finrank ℝ (TM x)) →
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦ C a i j - (S a / 3) * weightedDiagonalMetric diag i j
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TM x))) = 3 := by
    simp [ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq
      (n := 3) (M := M) x]
  have hdiag : ∀ k, 0 < diag k := by
    intro k
    exact g.metricBilinAt_pos x (b.ne_zero k)
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    simpa [b, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hTraceA : R = ∑ i, A i i / diag i := by
    rw [show R = g.scalarAt x from rfl, g.scalarAt_eq_trace_ricciEndoAt x,
      LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have hdual :
        metricDualVectorAt g x (b.coord i) = (diag i)⁻¹ • b i := by
      simpa [diag] using
        metricDualVectorAt_orthogonalBasis_coord_eq
          (g := g) (x := x) (b := b) hOrtho i
    calc
      b.coord i (g.ricciEndoAt x (b i)) =
          g.inner x (g.ricciEndoAt x (b i))
            (metricDualVectorAt g x (b.coord i)) :=
        coord_eq_inner_metricDualVectorAt_of_basis g x b i _
      _ = g.ricciAt x (b i) (metricDualVectorAt g x (b.coord i)) := by
        rw [g.inner_ricciEndoAt]
      _ = A i i / diag i := by
        rw [hdual]
        rw [g.ricciAt_smul_right]
        simp [A, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hTraceC : ∀ a, S a = ∑ i, C a i i / diag i := by
    intro a
    simpa [S, C, b, diag] using
      g.extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace x (b a)
  have hRicNorm :
      g.ricciNormSqAt x = ∑ i, ∑ j, (A i j) ^ 2 / (diag i * diag j) := by
    simpa [A, b, diag] using g.ricciNormSqAt_eq_metricOrthogonalBasis_sum x
  have hCovNorm :
      covRicciNormSqAt g x =
        ∑ a, ∑ i, ∑ j, (C a i j) ^ 2 / (diag a * diag i * diag j) := by
    simpa [C, b, diag] using covRicciNormSqAt_eq_metricOrthogonalBasis_sum (g := g) x
  have hGradNorm :
      g.scalarGradNormSqAt x = ∑ a, (S a) ^ 2 / diag a := by
    simpa [S, b, diag] using g.scalarGradNormSqAt_eq_metricOrthogonalBasis_sum x
  have hrepr : (∑ a, u a • b a) = w := by
    simpa [u] using b.sum_repr w
  have hPairLinear :
      covRicciRicciPairingAt g x w =
        ∑ a, u a * covRicciRicciPairingAt g x (b a) := by
    let df : TM x →L[ℝ] ℝ := extDerivFun (fun y : M ↦ g.ricciNormSqAt y) x
    calc
      covRicciRicciPairingAt g x w = (1 / 2 : ℝ) * df w := by
        rw [extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
          (g := g) x w]
        ring
      _ = (1 / 2 : ℝ) * df (∑ a, u a • b a) := by rw [hrepr]
      _ = (1 / 2 : ℝ) * ∑ a, u a * df (b a) := by
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp [smul_eq_mul]
      _ = ∑ a, u a * covRicciRicciPairingAt g x (b a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        dsimp only [df]
        rw [extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
          (g := g) x (b a)]
        ring
  have hPairBasis : ∀ a,
      covRicciRicciPairingAt g x (b a) =
        ∑ i, ∑ j, C a i j * A i j / (diag i * diag j) := by
    intro a
    rw [g.covRicciRicciPairingAt_eq_metricOrthogonalBasis_sum x (b a)]
    dsimp only [A, C, b, diag]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [div_eq_mul_inv]
    ring
  have hPairRaw :
      covRicciRicciPairingAt g x w =
        ∑ a, ∑ i, ∑ j, u a * C a i j * A i j / (diag i * diag j) := by
    rw [hPairLinear]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hPairBasis a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hScalarLinear :
      extDerivFun (fun y : M ↦ g.scalarAt y) x w = ∑ a, u a * S a := by
    calc
      extDerivFun (fun y : M ↦ g.scalarAt y) x w =
          extDerivFun (fun y : M ↦ g.scalarAt y) x (∑ a, u a • b a) := by
        rw [hrepr]
      _ = ∑ a, u a * S a := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp [S, smul_eq_mul]
  have hInner : g.inner x w w = ∑ a, (u a) ^ 2 * diag a := by
    have hFirst := sum_basis_coord_inner_eq_inner (g := g) (x := x) b w w
    calc
      g.inner x w w = ∑ a, u a * g.inner x (b a) w := by
        simpa [u] using hFirst.symm
      _ = ∑ a, u a * (∑ c, u c * g.inner x (b c) (b a)) := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        have hSecond := sum_basis_coord_inner_eq_inner (g := g) (x := x) b w (b a)
        rw [g.inner_symm x (b a) w]
        simpa [u] using congrArg (fun z : ℝ ↦ u a * z) hSecond.symm
      _ = ∑ a, (u a) ^ 2 * diag a := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_eq_single a]
        · rw [← g.metricBilinAt_apply x (b a) (b a)]
          dsimp only [diag]
          rw [pow_two]
          ring
        · intro c _ hca
          have hzero : g.inner x (b c) (b a) = 0 :=
            (LinearMap.isOrthoᵢ_def.mp hOrtho) c a hca
          simp [hzero]
        · intro ha
          exact False.elim (ha (Finset.mem_univ a))
  have hPairAdjusted :
      tracelessCovRicciRicciPairingAt g x w =
        ∑ a, ∑ i, ∑ j, u a * C₀ a i j * A₀ i j / (diag i * diag j) := by
    have hIdentity := weighted_traceless_pairing_identity
      hcard diag hdiag u C A S R hTraceA hTraceC
    rw [tracelessCovRicciRicciPairingAt, hPairRaw, hScalarLinear]
    simpa [A₀, C₀, R] using hIdentity.symm
  have hRicAdjusted :
      g.tracelessRicciNormSqAt x =
        ∑ i, ∑ j, (A₀ i j) ^ 2 / (diag i * diag j) := by
    have hIdentity := weighted_traceless_matrix_norm_identity
      hcard diag hdiag A R hTraceA
    rw [ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt, hRicNorm]
    norm_num
    simpa [A₀, R] using hIdentity.symm
  have hCovAdjusted :
      tracelessCovRicciNormSqAt g x =
        ∑ a, ∑ i, ∑ j,
          (C₀ a i j) ^ 2 / (diag a * diag i * diag j) := by
    have hIdentity := weighted_traceless_covariant_norm_identity
      hcard diag diag hdiag hdiag C S hTraceC
    rw [tracelessCovRicciNormSqAt, hCovNorm, hGradNorm]
    norm_num
    simpa [C₀] using hIdentity.symm
  have hWeighted := weighted_triple_contraction_sq_le
    diag diag hdiag hdiag u A₀ C₀
  rw [hPairAdjusted, hRicAdjusted, hCovAdjusted, hInner]
  exact hWeighted

/--
Uniform pointwise bounds `|Ric°| ≤ A` and `|∇ Ric°| ≤ B`, stated
using the squared intrinsic norms already defined in the repository.
-/
def UniformTracelessRicciAndCovariantDerivativeNormBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    (A B : ℝ) : Prop :=
  0 < A ∧ 0 < B ∧ ∀ i x,
    (g i).tracelessRicciNormSqAt x ≤ A ^ 2 ∧
      tracelessCovRicciNormSqAt (g i) x ≤ B ^ 2

/-- Uniform pointwise `|Ric°| ≤ A`, separated from derivative control. -/
def UniformTracelessRicciNormBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    (A : ℝ) : Prop :=
  0 < A ∧ ∀ i x, (g i).tracelessRicciNormSqAt x ≤ A ^ 2

/-- The spatial `C¹` regularity needed to integrate the derivative bound. -/
def UniformTracelessRicciEnergyCOne
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ i, ContMDiff I 𝓘(ℝ) 1
    (fun x : M ↦ (g i).tracelessRicciNormSqAt x)

/-- Honest uniform full covariant-Ricci derivative control
`|∇ Ric| ≤ D`, stated using the repository's squared intrinsic norm.

Unlike `UniformTracelessRicciAndCovariantDerivativeNormBound`, this includes
the trace derivative and therefore controls the scalar gradient. -/
def UniformCovariantRicciDerivativeNormBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    (D : ℝ) : Prop :=
  0 < D ∧ ∀ i x, covRicciNormSqAt (g i) x ≤ D ^ 2

/-- A full `|∇ Ric| ≤ D` bound controls `|∇ Ric°| ≤ D`, since
`|∇ Ric°|² = |∇ Ric|² - |dR|² / 3`.  Combined with an
independent `|Ric°|` bound, it constructs the older paired contract. -/
theorem uniformTracelessRicciAndCovariantDerivativeNormBound_of_tracelessRicci_of_covariantRicciDerivative
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    {A D : ℝ}
    (hRic : UniformTracelessRicciNormBound g A)
    (hCov : UniformCovariantRicciDerivativeNormBound g D) :
    UniformTracelessRicciAndCovariantDerivativeNormBound g A D := by
  refine ⟨hRic.1, hCov.1, ?_⟩
  intro i x
  refine ⟨hRic.2 i x, ?_⟩
  unfold tracelessCovRicciNormSqAt
  have hGradNonneg : 0 ≤ (g i).scalarGradNormSqAt x := by
    unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
    exact (g i).inner_nonneg x _
  exact
    (sub_le_self _ (div_nonneg hGradNonneg (by norm_num))).trans
      (hCov.2 i x)

/-- Spatial `C¹` regularity of scalar curvature along a metric family.
This is the regularity component needed by the intrinsic derivative-to-global
Lipschitz bridge. -/
def UniformScalarCurvatureCOne
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ i, ContMDiff I 𝓘(ℝ) 1 (fun x : M ↦ (g i).scalarAt x)

/-- In dimension three, the trace inequality
`|dR|² ≤ 3 |∇ Ric|²` gives the convenient directional bound
`|dR(v)| ≤ 3 D |v|` from `|∇ Ric| ≤ D`.

The constant `3 * D` is deliberately non-sharp; avoiding a square root keeps
the downstream uniform positivity and `ENNReal.ofReal` conversion direct. -/
theorem abs_extDerivFun_scalarAt_le_of_covariantRicciDerivativeNormBound
    (g : ClosedSmoothRiemannianMetric 3 M) {D : ℝ}
    (hD : 0 ≤ D)
    (hCov : ∀ x, covRicciNormSqAt g x ≤ D ^ 2)
    (x : M) (w : TM x) :
    |extDerivFun (fun y : M ↦ g.scalarAt y) x w| ≤
      (letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
        g.toRiemannianBundle;
        (3 * D) * ‖w‖) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  let gradR : TM x := g.gradientAt (fun y : M ↦ g.scalarAt y) x
  have hGradNormSq : g.scalarGradNormSqAt x = ‖gradR‖ ^ 2 := by
    unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
    rw [← ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
    exact real_inner_self_eq_norm_sq gradR
  have hGradSq : g.scalarGradNormSqAt x ≤ 3 * D ^ 2 :=
    (g.scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x).trans
      (mul_le_mul_of_nonneg_left (hCov x) (by norm_num))
  have hGradNorm : ‖gradR‖ ≤ 3 * D := by
    apply (sq_le_sq₀ (norm_nonneg gradR) (mul_nonneg (by norm_num) hD)).mp
    rw [← hGradNormSq]
    nlinarith [sq_nonneg D]
  have hCauchy : |g.inner x gradR w| ≤ ‖gradR‖ * ‖w‖ := by
    rw [← ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
    exact abs_real_inner_le_norm gradR w
  rw [← g.inner_gradientAt (fun y : M ↦ g.scalarAt y) x w]
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hGradNorm (norm_nonneg w))

/-- Full uniform `|∇ Ric|` control contracts to the scalar manifold-derivative
bound consumed by the path-integral Lipschitz theorem. -/
theorem uniformClosedRiemannianMFDerivBound_scalarAt_of_covariantRicciDerivativeNormBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    {D : ℝ}
    (hCOne : UniformScalarCurvatureCOne g)
    (hBound : UniformCovariantRicciDerivativeNormBound g D) :
    UniformClosedRiemannianMFDerivBound g
      (fun i x ↦ (g i).scalarAt x) (3 * D) := by
  have hL : 0 < 3 * D := mul_pos (by norm_num) hBound.1
  refine ⟨hL, hCOne, ?_⟩
  intro i x w
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    (g i).toRiemannianBundle
  have hReal :=
    abs_extDerivFun_scalarAt_le_of_covariantRicciDerivativeNormBound
      (g i) hBound.1.le (fun y ↦ hBound.2 i y) x w
  simpa only [extDerivFun, ContinuousLinearMap.comp_apply,
    enorm_tangentSpace_vectorSpace, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_mul hL.le, ofReal_norm_eq_enorm] using
      ENNReal.ofReal_le_ofReal hReal

/-- The same full covariant-Ricci derivative control supplies the global
slice-wise scalar Lipschitz bound with constant `3 * D`. -/
theorem uniformClosedRiemannianLipschitzBound_scalarAt_of_covariantRicciDerivativeNormBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    {D : ℝ}
    (hCOne : UniformScalarCurvatureCOne g)
    (hBound : UniformCovariantRicciDerivativeNormBound g D) :
    UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ (g i).scalarAt x) (3 * D) :=
  uniformClosedRiemannianLipschitzBound_of_mfderivBound g
    (fun i x ↦ (g i).scalarAt x)
    (uniformClosedRiemannianMFDerivBound_scalarAt_of_covariantRicciDerivativeNormBound
      g hCOne hBound)

/--
Tensor Cauchy--Schwarz plus the two intrinsic norm bounds contracts to the
ordinary directional estimate
`|d |Ric°|²(v)| ≤ 2 A B |v|`.
-/
theorem abs_extDerivFun_tracelessRicciNormSqAt_le_of_covariantDerivativeBound
    (g : ClosedSmoothRiemannianMetric 3 M) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRic : ∀ x, g.tracelessRicciNormSqAt x ≤ A ^ 2)
    (hCov : ∀ x, tracelessCovRicciNormSqAt g x ≤ B ^ 2)
    (x : M) (w : TM x) :
    |extDerivFun (fun y : M ↦ g.tracelessRicciNormSqAt y) x w| ≤
      (letI : RiemannianBundle
          (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
        g.toRiemannianBundle;
        (2 * A * B) * ‖w‖) := by
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    g.toRiemannianBundle
  have hCov0 : 0 ≤ tracelessCovRicciNormSqAt g x :=
    tracelessCovRicciNormSqAt_nonneg g x
  have hInner0 : 0 ≤ g.inner x w w := g.inner_nonneg x w
  have hNormSq : g.inner x w w = ‖w‖ ^ 2 := by
    rw [← ClosedSmoothRiemannianMetric.fiber_inner_eq (g := g) x]
    exact real_inner_self_eq_norm_sq w
  have hNormProduct :
      g.tracelessRicciNormSqAt x * tracelessCovRicciNormSqAt g x ≤
        A ^ 2 * B ^ 2 :=
    mul_le_mul (hRic x) (hCov x) hCov0 (sq_nonneg A)
  have hPairSq :
      (tracelessCovRicciRicciPairingAt g x w) ^ 2 ≤
        (A * B * ‖w‖) ^ 2 := by
    calc
      (tracelessCovRicciRicciPairingAt g x w) ^ 2 ≤
          g.tracelessRicciNormSqAt x * tracelessCovRicciNormSqAt g x *
            g.inner x w w := TracelessRicciCovariantDerivativeCauchySchwarz g x w
      _ ≤ (A ^ 2 * B ^ 2) * g.inner x w w :=
        mul_le_mul_of_nonneg_right hNormProduct hInner0
      _ = (A * B * ‖w‖) ^ 2 := by rw [hNormSq]; ring
  have hPair :
      |tracelessCovRicciRicciPairingAt g x w| ≤ A * B * ‖w‖ :=
    abs_le_of_sq_le_sq hPairSq
      (mul_nonneg (mul_nonneg hA hB) (norm_nonneg w))
  rw [extDerivFun_tracelessRicciNormSqAt_eq_two_tracelessCovRicciRicciPairingAt
    (g := g) x w]
  calc
    |2 * tracelessCovRicciRicciPairingAt g x w| =
        2 * |tracelessCovRicciRicciPairingAt g x w| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    _ ≤ 2 * (A * B * ‖w‖) :=
      mul_le_mul_of_nonneg_left hPair (by norm_num)
    _ = (2 * A * B) * ‖w‖ := by ring

/--
Uniform `|Ric°|` and `|∇ Ric°|` bounds give the exact intrinsic manifold
derivative contract consumed by the path-integral Lipschitz bridge.
-/
theorem uniformClosedRiemannianMFDerivBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    {A B : ℝ}
    (hCOne : UniformTracelessRicciEnergyCOne g)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound g A B) :
    UniformClosedRiemannianMFDerivBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) (2 * A * B) := by
  have hL : 0 < 2 * A * B := mul_pos (mul_pos (by norm_num) hBounds.1) hBounds.2.1
  refine ⟨hL, hCOne, ?_⟩
  intro i x w
  letI : RiemannianBundle
      (ClosedSmoothRiemannianMetric.tangentBundle (n := 3) (M := M)) :=
    (g i).toRiemannianBundle
  have hReal :=
    abs_extDerivFun_tracelessRicciNormSqAt_le_of_covariantDerivativeBound
      (g i) hBounds.1.le hBounds.2.1.le
      (fun y ↦ (hBounds.2.2 i y).1)
      (fun y ↦ (hBounds.2.2 i y).2) x w
  simpa only [extDerivFun, ContinuousLinearMap.comp_apply,
    enorm_tangentSpace_vectorSpace, Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_mul hL.le, ofReal_norm_eq_enorm] using
      ENNReal.ofReal_le_ofReal hReal

/-- The same intrinsic curvature data directly supplies the global Lipschitz contract. -/
theorem uniformClosedRiemannianLipschitzBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
    {ι : Type*} (g : ι → ClosedSmoothRiemannianMetric 3 M)
    {A B : ℝ}
    (hCOne : UniformTracelessRicciEnergyCOne g)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound g A B) :
    UniformClosedRiemannianLipschitzBound g
      (fun i x ↦ (g i).tracelessRicciNormSqAt x) (2 * A * B) :=
  uniformClosedRiemannianLipschitzBound_of_mfderivBound g
    (fun i x ↦ (g i).tracelessRicciNormSqAt x)
    (uniformClosedRiemannianMFDerivBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
      g hCOne hBounds)

end CurvatureDerivativeContraction

section CurvatureDerivativeConcentration

variable {M : Type v}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Intrinsic uniform bounds on `Ric°` and `∇ Ric°` close the spatial
regularity input of the compactness-free energy-concentration theorem.
-/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_covariantDerivativeBound
    (g : ℕ → ClosedSmoothRiemannianMetric 3 M)
    {A B : ℝ}
    (hCOne : UniformTracelessRicciEnergyCOne g)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound g A B)
    (hNoncollapse : UniformClosedRiemannianBallVolumeLower g)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_mfderivBound
    g (by norm_num)
      (uniformClosedRiemannianMFDerivBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
        g hCOne hBounds)
      hNoncollapse hEnergyZero

/-- Cubic-noncollapse form of the intrinsic curvature-derivative endpoint. -/
theorem tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_covariantDerivativeBound_of_cubicNoncollapse
    (g : ℕ → ClosedSmoothRiemannianMetric 3 M)
    {A B kappa r0 : ℝ}
    (hCOne : UniformTracelessRicciEnergyCOne g)
    (hBounds : UniformTracelessRicciAndCovariantDerivativeNormBound g A B)
    (hNoncollapse : UniformClosedRiemannianCubicNoncollapse g kappa r0)
    (hEnergyZero :
      Tendsto
        (fun i ↦ ∫ x, (g i).tracelessRicciNormSqAt x
          ∂(volumeMeasure (g i))) atTop (nhds 0)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in atTop, ∀ x : M, (g i).tracelessRicciNormSqAt x < epsilon :=
  tracelessRicciNormSqAt_eventually_uniformly_small_of_energy_tendsto_zero_of_mfderivBound_of_cubicNoncollapse
    g (by norm_num)
      (uniformClosedRiemannianMFDerivBound_tracelessRicciNormSqAt_of_covariantDerivativeBound
        g hCOne hBounds)
      hNoncollapse hEnergyZero

end CurvatureDerivativeConcentration

end Poincare
