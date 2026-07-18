import Poincare.Global.ScalarVariation

/-!
# Spatial regularity of the connection variation

The scalar Koszul identity already determines every metric pairing of
`deltaGammaFieldAt` by first covariant derivatives of the metric variation.
This file reconstructs a tangent field from those scalar pairings through a
local inverse-Gram formula.  Consequently the scalar-entry derivative bridge
used by the Hamilton scalar-evolution proof is a theorem, not an independent
hypothesis.
-/

noncomputable section

open Bundle FiberBundle
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
A tangent field is differentiable at an anchor when its metric pairings with
the canonical Gram frame are differentiable there.

The proof is local: invertibility of the anchor Gram matrix persists on a
neighborhood, where inverse-Gram coefficients reconstruct the field exactly.
-/
theorem tangentField_mdifferentiableAt_of_gram_pairings
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    {K : ∀ y : M, TM y}
    (hpair : ∀ j : Fin (Module.finrank ℝ (TM x)),
      MDifferentiableAt I 𝓘(ℝ)
        (fun y : M ↦ g.inner y (K y) (gramFrame x y j)) x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% K) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let coeff : Fin (Module.finrank ℝ (TM x)) → M → ℝ := fun i y ↦
    ∑ j, (gramMatrix g x y)⁻¹ i j *
      g.inner y (K y) (gramFrame x y j)
  let R : ∀ y : M, TM y := fun y ↦
    ∑ i, coeff i y • gramFrame x y i
  have hcoeff : ∀ i,
      MDifferentiableAt I 𝓘(ℝ) (coeff i) x := by
    intro i
    have hsum : MDifferentiableAt I 𝓘(ℝ)
        (∑ j, fun y : M ↦ (gramMatrix g x y)⁻¹ i j *
          g.inner y (K y) (gramFrame x y j)) x := by
      refine MDifferentiableAt.sum (t := Finset.univ) ?_
      intro j _
      exact (gramMatrix_inv_entry_mdiffAt (g := g) x i j).mul (hpair j)
    change MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ ∑ j, (gramMatrix g x y)⁻¹ i j *
        g.inner y (K y) (gramFrame x y j)) x
    exact hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ by simp)
  have hframe : ∀ i,
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦ gramFrame (n := n) (M := M) x y i)) x := by
    intro i
    let b := Module.finBasis ℝ (TM x)
    simpa [gramFrame, b] using (mdifferentiableAt_extend I E (b i))
  have hsummand : ∀ i,
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (fun y : M ↦ coeff i y •
          gramFrame (n := n) (M := M) x y i)) x := by
    intro i
    exact (hcoeff i).smul_section (hframe i)
  have hR : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% R) x := by
    simpa [R] using (MDifferentiableAt.sum_section fun i ↦ hsummand i)
  have heq : K =ᶠ[nhds x] R := by
    filter_upwards [gramMatrix_eventually_isUnit (g := g) x] with y hG
    letI : FiniteDimensional ℝ (TM y) :=
      inferInstanceAs (FiniteDimensional ℝ E)
    let B := gramFrameBasis g x y hG
    have hcoord : ∀ i, B.coord i (K y) = coeff i y := by
      intro i
      calc
        B.coord i (K y) =
            g.inner y (K y) (metricDualVectorAt g y (B.coord i)) :=
          coord_eq_inner_metricDualVectorAt_of_basis g y B i (K y)
        _ = g.inner y (K y)
            (∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j) := by
          rw [metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv
            (g := g) (x := x) (y := y) hG i]
        _ = ∑ j, (gramMatrix g x y)⁻¹ i j *
            g.inner y (K y) (gramFrame x y j) := by
          rw [map_sum]
          simp [smul_eq_mul]
        _ = coeff i y := by rfl
    calc
      K y = ∑ i, B.coord i (K y) • B i := (B.sum_repr (K y)).symm
      _ = ∑ i, coeff i y • gramFrame x y i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoord i, gramFrameBasis_apply]
      _ = R y := by rfl
  refine MDifferentiableAt.congr_of_eventuallyEq hR ?_
  filter_upwards [heq] with y hy
  rw [hy]

/-- Canonical extensions are `C²` at every point of some neighborhood of
their anchor. -/
theorem eventually_contMDiffAt_two_canonical_extend
    {x : M} (v : TM x) :
    ∀ᶠ y in nhds x,
      ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% (extend E v)) y := by
  obtain ⟨s, hs, hscont⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 2) (by norm_num)).mp
      (FiberBundle.contMDiffAt_extend' (k := 2) I E v)
  filter_upwards [interior_mem_nhds.mpr hs] with y hy
  exact ((hscont.mono interior_subset) y hy).contMDiffAt
    (isOpen_interior.mem_nhds hy)

/--
Second scalar-entry regularity of a bilinear tensor, together with first
regularity on nearby fibers, differentiates its actual covariant-derivative
entry field.

This is the differentiability content of
`covTensor2DerivAt_moving_extDerivFun_expansion`, separated out so callers do
not need to assume `CovTensor2DerivExtDifferentiableAt` independently.
-/
theorem covTensor2DerivExtDifferentiableAt_of_extSecond
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {h : ∀ y : M, TM y → TM y → ℝ} {x : M}
    (hSecond : CovTensor2ExtSecondDifferentiableAt h x)
    (hDiff : ∀ y : M, CovTensor2ExtDifferentiableAt h y)
    (hAddL : Tensor2AddLeft h) (hSMulL : Tensor2SMulLeft h)
    (hAddR : Tensor2AddRight h) (hSMulR : Tensor2SMulRight h) :
    CovTensor2DerivExtDifferentiableAt g h x := by
  intro v p q
  let A : M → ℝ := fun y : M ↦
    extDerivFun
      (fun z : M ↦ h z (extend E p z) (extend E q z)) y
      (extend E v y)
  let B : M → ℝ := fun y : M ↦
    h y
      (g.leviCivita (extend E p) y (extend E v y))
      (extend E q y)
  let C : M → ℝ := fun y : M ↦
    h y (extend E p y)
      (g.leviCivita (extend E q) y (extend E v y))
  have hevent :
      (fun y : M ↦ covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y)) =ᶠ[nhds x]
        fun y : M ↦ A y - B y - C y := by
    have hp_event :=
      eventually_contMDiffAt_two_canonical_extend (n := n) (M := M) p
    have hq_event :=
      eventually_contMDiffAt_two_canonical_extend (n := n) (M := M) q
    filter_upwards [hp_event, hq_event] with y hp2 hq2
    have hp_mdiff :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E p)) y :=
      hp2.mdifferentiableAt two_ne_zero
    have hq_mdiff :
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (extend E q)) y :=
      hq2.mdifferentiableAt two_ne_zero
    have hbridge :=
      tensor2_moving_both_extDerivFun_eq_covTensor2DerivAt_add_corrections
        (g := g) (h := h) (x := y)
        (K := extend E p) (L := extend E q)
        hp_mdiff hq_mdiff
        (hDiff y) hAddL hSMulL hAddR hSMulR (extend E v y)
    change
      covTensor2DerivAt g h y
          (extend E v y) (extend E p y) (extend E q y) =
        extDerivFun
            (fun z : M ↦ h z (extend E p z) (extend E q z)) y
            (extend E v y)
          - h y
              (g.leviCivita (extend E p) y (extend E v y))
              (extend E q y)
          - h y (extend E p y)
              (g.leviCivita (extend E q) y (extend E v y))
    rw [hbridge]
    ring
  have hA : MDifferentiableAt I 𝓘(ℝ) A x := by
    simpa [A, CovTensor2ExtSecondDifferentiableAt] using hSecond p q v
  let Γp : ∀ y : M, TM y :=
    fun y : M ↦ g.leviCivita (extend E p) y (extend E v y)
  let Γq : ∀ y : M, TM y :=
    fun y : M ↦ g.leviCivita (extend E q) y (extend E v y)
  have hΓp : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Γp) x := by
    simpa [Γp] using
      leviCivita_extend_connection_field_mdiffAt
        (g := g) (x := x) p v
  have hΓq : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Γq) x := by
    simpa [Γq] using
      leviCivita_extend_connection_field_mdiffAt
        (g := g) (x := x) q v
  have hB : MDifferentiableAt I 𝓘(ℝ) B x := by
    simpa [B, Γp] using
      tensor2_moving_left_mdiffAt
        (g := g) (h := h) (x := x) (K := Γp)
        hΓp (hDiff x) hAddL hSMulL q
  have hC : MDifferentiableAt I 𝓘(ℝ) C x := by
    simpa [C, Γq] using
      tensor2_moving_right_mdiffAt
        (g := g) (h := h) (x := x) (K := Γq)
        hΓq (hDiff x) hAddR hSMulR p
  exact ((hA.sub hB).sub hC).congr_of_eventuallyEq hevent

/-- Global C² canonical entries of a metric variation discharge the older
`∇h` entry-field regularity predicate. -/
theorem covTensor2DerivExtDifferentiableAt_timeDeriv_of_global_entries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hEntries : ∀ y : M,
      TimeVariationTraceEntriesExtContMDiffAt gt t₀ y 2) :
    CovTensor2DerivExtDifferentiableAt
      (gt t₀) (timeDerivAt gt t₀) x := by
  have hDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (timeDerivAt gt t₀) y := fun y ↦
    (timeVariationTraceEntriesExtContMDiffAt_two_old_regularities
      (hEntries y)).1
  have hSecond :
      CovTensor2ExtSecondDifferentiableAt (timeDerivAt gt t₀) x :=
    (timeVariationTraceEntriesExtContMDiffAt_two_old_regularities
      (hEntries x)).2.1
  exact covTensor2DerivExtDifferentiableAt_of_extSecond
    (g := gt t₀) (h := timeDerivAt gt t₀) (x := x)
    hSecond hDiff
    (tensor2AddLeft_timeDerivAt hgt)
    (tensor2SMulLeft_timeDerivAt hgt)
    (tensor2AddRight_timeDerivAt hgt)
    (tensor2SMulRight_timeDerivAt hgt)

/--
The Koszul identity and differentiability of the covariant metric-variation
entries imply differentiability of the actual vector-valued `δΓ` field.
-/
theorem deltaGammaFieldMDifferentiableAt_of_koszul_regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
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
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    DeltaGammaFieldMDifferentiableAt gt t₀ x := by
  intro p w
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  let H : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t₀
  apply tangentField_mdifferentiableAt_of_gram_pairings (g := g) (x := x)
  intro j
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let S : M → ℝ := fun y ↦
    g.inner y
      (deltaGammaAt gt t₀ y (extend E p y) (extend E w y))
      (extend E (b j) y)
  let A : M → ℝ := fun y ↦
    covTensor2DerivAt g H y
      (extend E p y) (extend E w y) (extend E (b j) y)
  let B : M → ℝ := fun y ↦
    covTensor2DerivAt g H y
      (extend E w y) (extend E p y) (extend E (b j) y)
  let C : M → ℝ := fun y ↦
    covTensor2DerivAt g H y
      (extend E (b j) y) (extend E p y) (extend E w y)
  have hevent := deltaGamma_koszul_eventually
    (gt := gt) (t₀ := t₀) (x := x) hgt hNear p w (b j)
  have heq : S =ᶠ[nhds x] fun y ↦ (1 / 2 : ℝ) * (A y + B y - C y) := by
    filter_upwards [hevent] with y hy
    change 2 * S y = A y + B y - C y at hy
    rw [← hy]
    ring
  have hA : MDifferentiableAt I 𝓘(ℝ) A x := by
    simpa [A, g, H] using hSecond p w (b j)
  have hB : MDifferentiableAt I 𝓘(ℝ) B x := by
    simpa [B, g, H] using hSecond w p (b j)
  have hC : MDifferentiableAt I 𝓘(ℝ) C x := by
    simpa [C, g, H] using hSecond (b j) p w
  have hscale : MDifferentiableAt I 𝓘(ℝ)
      (fun y : M ↦ (1 / 2 : ℝ) * (A y + B y - C y)) x := by
    have hc : MDifferentiableAt I 𝓘(ℝ)
        (fun _ : M ↦ (1 / 2 : ℝ)) x := mdifferentiableAt_const
    exact hc.mul ((hA.add hB).sub hC)
  have hS : MDifferentiableAt I 𝓘(ℝ) S x :=
    hscale.congr_of_eventuallyEq heq
  simpa [S, g, deltaGammaFieldAt, gramFrame, b] using hS

/-- The scalar `δΓ` entry bridge is generated by the Koszul regularity
already consumed by the scalar-evolution proof. -/
theorem deltaGammaEntryDerivativeBridgeAt_of_koszul_regular
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hgt : ∀ y : M, TimeDifferentiableAt gt t₀ y)
    (hNear :
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
    (hSecond :
      CovTensor2DerivExtDifferentiableAt
        (gt t₀) (timeDerivAt gt t₀) x) :
    DeltaGammaEntryDerivativeBridgeAt gt t₀ x :=
  deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt
    (deltaGammaFieldMDifferentiableAt_of_koszul_regular hgt hNear hSecond)

end Poincare
