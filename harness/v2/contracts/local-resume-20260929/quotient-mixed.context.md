# Exact source context for quotient-mixed

These excerpts record existing source at base 2da86427. Search and read nearest definitions/imports when using further symbols.

## Poincare/Global/ScalarEvolution.lean:1-62

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Poincare.Global.Laplacian
import Poincare.Global.RicciNorm
import Poincare.Global.RicciFlow
import Poincare.Global.ScalarVariation
import Poincare.Global.MetricRaiseTimeDerivative
import Poincare.Global.DeltaGammaFieldRegularity
import Poincare.Global.RicciFlowScalarRegularity
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

private lemma real_fromTangentSpace_toSpanSingleton_apply
    (a b c : ℝ) (u : TangentSpace 𝓘(ℝ, ℝ) a) :
    (@NormedSpace.fromTangentSpace ℝ _ ℝ _ _ b).toContinuousLinearMap
        ((ContinuousLinearMap.toSpanSingleton ℝ c) u) =
      c * (@NormedSpace.fromTangentSpace ℝ _ ℝ _ _ a).toContinuousLinearMap u := by
  simp [NormedSpace.fromTangentSpace, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, mul_comm]

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
```

## Poincare/Global/ScalarEvolution.lean:900-1318

```lean
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

theorem extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace
    (x : M) (w : TM x) :
    extDerivFun (fun y : M ↦ g.scalarAt y) x w =
      (let b := metricOrthogonalBasisAt g x
      let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
        fun k ↦ g.metricBilinAt x (b k) (b k)
      ∑ i,
        covTensor2DerivAt g (ricciVariationField g) x w (b i) (b i) /
          diag i) := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  let H : ∀ y : M, TM y → TM y → ℝ :=
    fun y p q ↦ covTensor2DerivAt g (ricciVariationField g) y (extend E w y) p q
  let B : LinearMap.BilinForm ℝ (TM x) :=
    LinearMap.mk₂ ℝ
      (fun p q ↦ covTensor2DerivAt g (ricciVariationField g) x w p q)
      (fun p p' q ↦
        covTensor2DerivAt_add_left
          (g := g) (h := ricciVariationField g) (x := x)
          (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
            (g := g) (x := x))
          (tensor2AddLeft_ricciVariationField g) w p p' q)
      (fun c p q ↦ by
        simpa [smul_eq_mul] using
          covTensor2DerivAt_smul_left
            (g := g) (h := ricciVariationField g) (x := x)
            (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
              (g := g) (x := x))
            (tensor2SMulLeft_ricciVariationField g) c w p q)
      (fun p q q' ↦
        covTensor2DerivAt_add_right
          (g := g) (h := ricciVariationField g) (x := x)
          (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
            (g := g) (x := x))
          (tensor2AddRight_ricciVariationField g) w p q q')
      (fun c p q ↦ by
        simpa [smul_eq_mul] using
          covTensor2DerivAt_smul_right
            (g := g) (h := ricciVariationField g) (x := x)
            (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
              (g := g) (x := x))
            (tensor2SMulRight_ricciVariationField g) c w p q)
  have hB : ∀ p q : TM x, B p q = H x p q := by
    intro p q
    simp [B, H]
  have hTraceDeriv : TraceMetricVariationDerivAt g (ricciVariationField g) x :=
    traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt
      (g := g) (h := ricciVariationField g) (x := x)
      (covTensor2ExtDifferentiableAt_ricciVariationField_canonical
        (g := g) (x := x))
      (tensor2AddLeft_ricciVariationField g)
      (tensor2SMulLeft_ricciVariationField g)
      (tensor2AddRight_ricciVariationField g)
      (tensor2SMulRight_ricciVariationField g)
      (ricciVariationBilinForm g)
      (by intro y p q; rfl)
  have hTraceH :
      traceMetricVariationAt g H x =
        extDerivFun (fun y : M ↦ g.scalarAt y) x w := by
    calc
      traceMetricVariationAt g H x =
          (letI : FiniteDimensional ℝ (TM x) :=
              inferInstanceAs (FiniteDimensional ℝ E)
            ∑ i,
              covTensor2DerivAt g (ricciVariationField g) x w
                ((Module.finBasis ℝ (TM x)) i)
                (metricDualVectorAt g x
                  ((Module.finBasis ℝ (TM x)).coord i))) := by
            simp [traceMetricVariationAt, H]
      _ = extDerivFun
            (fun y ↦ traceMetricVariationAt g (ricciVariationField g) y)
            x w := hTraceDeriv w
      _ = extDerivFun (fun y : M ↦ g.scalarAt y) x w := by
            exact extDerivFun_traceMetricVariationAt_ricci (g := g) x w
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    simpa [b, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  calc
    extDerivFun (fun y : M ↦ g.scalarAt y) x w =
        traceMetricVariationAt g H x := hTraceH.symm
    _ = metricTraceInBasisAt g x B b :=
        traceMetricVariationAt_eq_metricTraceInBasisAt
          (g := g) (h := H) (x := x) (B := B) (b := b) hB
    _ =
        (let b := metricOrthogonalBasisAt g x
        let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
          fun k ↦ g.metricBilinAt x (b k) (b k)
        ∑ i,
          covTensor2DerivAt g (ricciVariationField g) x w (b i) (b i) /
            diag i) := by
        unfold metricTraceInBasisAt
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [metricDualVectorAt_orthogonalBasis_coord_eq
          (g := g) (x := x) (b := b) hOrtho i]
        simp [B, b, smul_eq_mul, div_eq_mul_inv]
        ring

theorem scalarGradNormSqAt_le_three_covRicciNormSqAt
    (hn : n = 3) (x : M) :
    g.scalarGradNormSqAt x ≤ 3 * covRicciNormSqAt g x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun k ↦ g.metricBilinAt x (b k) (b k)
  let D : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a ↦ extDerivFun (fun y : M ↦ g.scalarAt y) x (b a)
  let C :
      Fin (Module.finrank ℝ (TM x)) →
        Fin (Module.finrank ℝ (TM x)) →
          Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun a i j ↦ covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)
  have hcard :
      Fintype.card (Fin (Module.finrank ℝ (TM x))) = 3 := by
    simp [ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq
      (n := n) (M := M) x, hn]
  have hdiag : ∀ k, 0 < diag k := by
    intro k
    exact g.metricBilinAt_pos x (b.ne_zero k)
  have hD : ∀ a, D a = ∑ i, C a i i / diag i := by
    intro a
    simpa [D, C, b, diag] using
      g.extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace x (b a)
  rw [g.scalarGradNormSqAt_eq_metricOrthogonalBasis_sum x,
    covRicciNormSqAt_eq_metricOrthogonalBasis_sum (g := g) x]
  simpa [D, C, b, diag] using
    weighted_trace_gradient_sq_le_three
      (hcardβ := hcard) (diagA := diag) (diagB := diag)
      hdiag hdiag D C hD

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

/--
Direct mixed-pairing control in the form needed by the traceless gradient
absorption.  This is the Cauchy-Schwarz content of the completed square
`|R ∇Ric - ∇R ⊗ Ric|² ≥ 0`.
-/
theorem pinchingMixedGradientPairingAt_absorption_bound (x : M) :
    2 * g.scalarAt x * g.pinchingMixedGradientPairingAt x ≤
      (g.scalarAt x) ^ 2 * covRicciNormSqAt g x
        + g.scalarGradNormSqAt x * g.ricciNormSqAt x := by
  have hsquare_nonneg : 0 ≤ g.pinchingGradientSquareAt x :=
    g.pinchingGradientSquareAt_nonneg x
  have hsquare :
      g.pinchingGradientSquareAt x =
        (g.scalarAt x) ^ 2 * covRicciNormSqAt g x
          - 2 * g.scalarAt x * g.pinchingMixedGradientPairingAt x
          + g.pinchingScalarRicciGradientProductAt x :=
    g.pinchingGradientSquareAt_eq_completedSquareExpansion x
  have hraw :
      g.pinchingScalarRicciGradientProductAt x =
        g.scalarGradNormSqAt x * g.ricciNormSqAt x :=
    g.pinchingScalarRicciGradientProductAt_eq_scalarGradNormSqAt_mul_ricciNormSqAt x
  rw [hsquare, hraw] at hsquare_nonneg
  linarith

/--
Total sign of the corrected traceless gradient contribution.  The estimate
uses the reserve route: the completed-square mixed absorption plus
`|∇R|² ≤ 3 |∇Ric|²`.  No epsilon-pinching hypothesis is needed for the gradient
part itself; the honest admissible range here is `0 ≤ δ ≤ 2`.
```

## Poincare/Global/ScalarVariation.lean:6230-6285

```lean
  ring

/-- A metric-orthogonal tangent frame, chosen noncomputably from the
pointwise positive-definite metric bilinear form. -/
noncomputable def metricOrthogonalBasisAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : Module.Basis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x) :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  Classical.choose
    (LinearMap.BilinForm.exists_orthogonal_basis
      (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))

/-- Pointwise squared norm of the covariant Ricci derivative.

In the chosen metric-orthogonal frame this is the triple trace of
`∇Ric ⊗ ∇Ric`, with the three diagonal metric weights divided out. -/
noncomputable def covRicciNormSqAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := metricOrthogonalBasisAt g x
  ∑ a : Fin (Module.finrank ℝ (TM x)), ∑ i : Fin (Module.finrank ℝ (TM x)),
    ∑ j : Fin (Module.finrank ℝ (TM x)),
      (covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)) ^ 2 /
        (g.metricBilinAt x (b a) (b a) *
          g.metricBilinAt x (b i) (b i) *
          g.metricBilinAt x (b j) (b j))

theorem covRicciNormSqAt_eq_metricOrthogonalBasis_sum
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    covRicciNormSqAt g x =
      let b := metricOrthogonalBasisAt g x
      ∑ a : Fin (Module.finrank ℝ (TM x)), ∑ i : Fin (Module.finrank ℝ (TM x)),
        ∑ j : Fin (Module.finrank ℝ (TM x)),
          (covTensor2DerivAt g (ricciVariationField g) x (b a) (b i) (b j)) ^ 2 /
            (g.metricBilinAt x (b a) (b a) *
              g.metricBilinAt x (b i) (b i) *
              g.metricBilinAt x (b j) (b j)) := by
  rfl

/--
Metric pairing of the first covariant Ricci derivative with Ricci:
`⟨∇_v Ric, Ric⟩_g`.
-/
noncomputable def covRicciRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v : TM x) : ℝ :=
  letI : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b.coord i)
```

## Poincare/Global/ScalarVariation.lean:15025-15053

```lean
        ricciPairingRicciFirstCovariantGroup g x v
          + ricciPairingRicciSecondCovariantGroup g x v := by
          unfold ricciPairingGramProductRuleRHS
          rw [hRic.1, hRic.2]
          linarith only [hCancel]
    _ = 2 * covRicciRicciPairingAt g x v := hCov

/-- Direct `|Ric|^2` first-derivative form of the Ricci/Ricci pairing theorem. -/
theorem extDerivFun_ricciNormSqAt_eq_two_covRicciRicciPairingAt
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (v : TM x) :
    extDerivFun (fun y : M ↦ g.ricciNormSqAt y) x v =
      2 * covRicciRicciPairingAt g x v := by
  calc
    extDerivFun (fun y : M ↦ g.ricciNormSqAt y) x v =
        extDerivFun
          (fun y : M ↦ metricVariationRicciPairingAt g (ricciVariationField g) y)
          x v := by
          exact extDerivFun_ricciNormSqAt_eq_metricVariationRicciPairingAt_ricci
            (g := g) (x := x) (w := v)
    _ = 2 * covRicciRicciPairingAt g x v :=
        extDerivFun_ricciPairing_eq_two_covRicciRicciPairingAt
          (g := g) x v

theorem eventually_tensorDivergenceOneFormAt_ricciVariationField_eq_closedRicciDivergenceTraceAt_canonical
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∀ᶠ y in nhds x, ∀ w : TM y,
      tensorDivergenceOneFormAt g (ricciVariationField g) y w =
```

## Poincare/Global/Laplacian.lean:1-88

```lean
import Poincare.Global.Curvature
import Poincare.ModelLaplacian

/-!
# Scalar gradients, Hessians, and Laplacians on closed smooth manifolds

This module specializes the scalar Laplacian infrastructure to a
`ClosedSmoothRiemannianMetric`.  It mirrors the trace pattern used for scalar
curvature: build a dual-valued Hessian, raise the dual index with the metric,
and take the trace.

The Hessian is defined as `g(∇ grad f, ·)` using the canonical
`g.leviCivita`.  Linearity theorems carry explicit differentiability
hypotheses for the gradient fields.  Ledger task `M1-lc-regularity` is
responsible for discharging those hypotheses from smoothness of `f` and the
canonical Levi-Civita construction.
-/

noncomputable section

open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u

namespace Poincare
namespace ClosedSmoothRiemannianMetric

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

@[reducible] private def tangentFiniteDimensional (x : M) :
    FiniteDimensional ℝ (TM x) :=
  (inferInstance : FiniteDimensional ℝ E)

@[reducible] private def tangentT2Space (x : M) :
    T2Space (TM x) :=
  (inferInstance : T2Space E)

omit [T2Space M] [IsManifold I ∞ M] in
private theorem extDerivFun_const (c : ℝ) (x : M) :
    (extDerivFun (fun _ : M ↦ c) x : TM x →L[ℝ] ℝ) = 0 := by
  unfold extDerivFun
  rw [(hasMFDerivAt_const c x).mfderiv]
  ext v
  simp

omit [T2Space M] in
private theorem extDerivFun_const_smul {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) :
    (extDerivFun (c • f) x : TM x →L[ℝ] ℝ) =
      c • (extDerivFun f x : TM x →L[ℝ] ℝ) := by
  ext v
  have hmul := CovariantDerivative.extDerivFun_mul
    (p := fun _ : M ↦ c) (q := f) (x := x) mdifferentiableAt_const hf v
  simp [Pi.smul_apply, smul_eq_mul, extDerivFun_const] at hmul ⊢
  exact hmul

/-- The Riemannian gradient at a point, obtained by raising `df` with `g`. -/
noncomputable def gradientAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) : TM x :=
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  (LinearMap.BilinForm.toDual (g.metricBilinAt x)
      (g.metricBilinAt_nondegenerate x)).symm
    (LinearMap.toContinuousLinearMap.symm
      (extDerivFun f x : TM x →L[ℝ] ℝ))

/-- The gradient vector field of a scalar function. -/
noncomputable def gradient (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) : ∀ x : M, TM x :=
  fun x ↦ g.gradientAt f x

/-- The defining property of `gradientAt`: pairing with the metric recovers `df`. -/
theorem inner_gradientAt (g : ClosedSmoothRiemannianMetric n M)
    (f : M → ℝ) (x : M) (w : TM x) :
    g.inner x (g.gradientAt f x) w = extDerivFun f x w := by
  letI : FiniteDimensional ℝ (TM x) := tangentFiniteDimensional x
  letI : T2Space (TM x) := tangentT2Space x
  unfold gradientAt
  let A :=
    LinearMap.BilinForm.toDual (g.metricBilinAt x)
```
