import Poincare.Global.DeTurckSummandRegularity

/-!
# Honest local-frame regularity for the DeTurck contraction

The pointwise `Module.finBasis` used by `deTurckVectorFieldAt` is not a
geometric global frame.  In particular, its raw fiber coordinates should not
be treated as a globally smooth tangent field on an arbitrary manifold.

This file replaces that unsafe global step by an anchored local construction.
At a fixed point `x`, the canonical extensions of a basis of `T_x M` form a
smooth local frame.  The inverse Gram matrix gives its metric-raised dual
frame.  Those raised fields are `C³` at `x`, so applying the difference of the
two `C²` Levi-Civita connections gives a `C²` local DeTurck contraction.
The resulting local field has exactly the value of the pointwise DeTurck field
at `x`; no neighborhood equality with the raw pointwise-finBasis definition is
asserted.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

section General

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

private theorem contMDiffAt_three_finset_sum_real
    {ι : Type} [DecidableEq ι] {s : Finset ι}
    {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) 3 (f i) x) :
    ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ ∑ i ∈ s, f i y) x := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simpa using
      (contMDiffAt_const :
        ContMDiffAt I 𝓘(ℝ) 3 (fun _ : M ↦ (0 : ℝ)) x)
  · intro a s ha ih hf
    have hfa : ContMDiffAt I 𝓘(ℝ) 3 (f a) x :=
      hf a (Finset.mem_insert_self a s)
    have hs : ContMDiffAt I 𝓘(ℝ) 3
        (fun y : M ↦ ∑ i ∈ s, f i y) x :=
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using hfa.add hs

private theorem contMDiffAt_three_finset_prod_real
    {ι : Type} [DecidableEq ι] {s : Finset ι}
    {f : ι → M → ℝ} {x : M}
    (hf : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) 3 (f i) x) :
    ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ ∏ i ∈ s, f i y) x := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simpa using
      (contMDiffAt_const :
        ContMDiffAt I 𝓘(ℝ) 3 (fun _ : M ↦ (1 : ℝ)) x)
  · intro a s ha ih hf
    have hfa : ContMDiffAt I 𝓘(ℝ) 3 (f a) x :=
      hf a (Finset.mem_insert_self a s)
    have hs : ContMDiffAt I 𝓘(ℝ) 3
        (fun y : M ↦ ∏ i ∈ s, f i y) x :=
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.prod_insert ha, smul_eq_mul] using hfa.smul hs

/-- Smooth metric pairings preserve `C³` regularity at a point. -/
theorem metric_pairing_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) {x : M}
    {A B : ∀ y : M, TM y}
    (hA : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% A) x)
    (hB : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% B) x) :
    ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ g.inner y (A y) (B y)) x := by
  letI : RiemannianBundle TM := g.toRiemannianBundle
  haveI : IsContMDiffRiemannianBundle I ∞ E TM :=
    g.toIsContMDiffRiemannianBundle
  have hinner : ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ inner ℝ (A y) (B y)) x :=
    ContMDiffAt.inner_bundle hA hB
  simpa [ClosedSmoothRiemannianMetric.fiber_inner_eq] using hinner

/-- The anchored Gram entries are `C³`. -/
theorem gramMatrix_entry_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ gramMatrix g x y i j) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  exact metric_pairing_contMDiffAt_three g
    (by simpa [gramFrame, b] using
      (FiberBundle.contMDiffAt_extend' (k := 3) I E (b i)))
    (by simpa [gramFrame, b] using
      (FiberBundle.contMDiffAt_extend' (k := 3) I E (b j)))

private theorem gramMatrix_det_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ (gramMatrix g x y).det) x := by
  classical
  rw [show (fun y : M ↦ (gramMatrix g x y).det) =
      fun y : M ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ (TM x))),
        ((↑↑(Equiv.Perm.sign σ) : ℝ) *
          ∏ i, gramMatrix g x y (σ i) i) by
    funext y
    rw [Matrix.det_apply']]
  refine contMDiffAt_three_finset_sum_real
    (s := (Finset.univ :
      Finset (Equiv.Perm (Fin (Module.finrank ℝ (TM x)))))) ?_
  intro σ _hσ
  have hprod : ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ ∏ i, gramMatrix g x y (σ i) i) x := by
    simpa using
      (contMDiffAt_three_finset_prod_real
        (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
        (f := fun i y ↦ gramMatrix g x y (σ i) i)
        (fun i _hi ↦ gramMatrix_entry_contMDiffAt_three g x (σ i) i))
  have hconst : ContMDiffAt I 𝓘(ℝ) 3
      (fun _ : M ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) x := contMDiffAt_const
  simpa [smul_eq_mul] using hconst.smul hprod

private theorem gramMatrix_adjugate_entry_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ (gramMatrix g x y).adjugate i j) x := by
  let row : Fin (Module.finrank ℝ (TM x)) → ℝ := Pi.single i (1 : ℝ)
  let A : M → Matrix (Fin (Module.finrank ℝ (TM x)))
      (Fin (Module.finrank ℝ (TM x))) ℝ :=
    fun y : M ↦ (gramMatrix g x y).updateRow j row
  have hentries : ∀ a b,
      ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ A y a b) x := by
    intro a b
    by_cases ha : a = j
    · subst a
      simpa [A, Matrix.updateRow] using
        (contMDiffAt_const :
          ContMDiffAt I 𝓘(ℝ) 3 (fun _ : M ↦ row b) x)
    · simpa [A, Matrix.updateRow, ha] using
        gramMatrix_entry_contMDiffAt_three g x a b
  have hdet : ContMDiffAt I 𝓘(ℝ) 3 (fun y : M ↦ (A y).det) x := by
    classical
    rw [show (fun y : M ↦ (A y).det) =
        fun y : M ↦ ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ (TM x))),
          ((↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, A y (σ k) k) by
      funext y
      rw [Matrix.det_apply']]
    refine contMDiffAt_three_finset_sum_real
      (s := (Finset.univ :
        Finset (Equiv.Perm (Fin (Module.finrank ℝ (TM x)))))) ?_
    intro σ _hσ
    have hprod : ContMDiffAt I 𝓘(ℝ) 3
        (fun y : M ↦ ∏ k, A y (σ k) k) x := by
      simpa using
        (contMDiffAt_three_finset_prod_real
          (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
          (f := fun k y ↦ A y (σ k) k)
          (fun k _hk ↦ hentries (σ k) k))
    have hconst : ContMDiffAt I 𝓘(ℝ) 3
        (fun _ : M ↦ (↑↑(Equiv.Perm.sign σ) : ℝ)) x := contMDiffAt_const
    simpa [smul_eq_mul] using hconst.smul hprod
  exact hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    simp [A, row, Matrix.adjugate_apply])

/-- Inverse entries of the anchored Gram matrix are `C³` at the anchor. -/
theorem gramMatrix_inv_entry_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i j : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ (gramMatrix g x y)⁻¹ i j) x := by
  have hdetInv : ContMDiffAt I 𝓘(ℝ) 3
      (fun y : M ↦ ((gramMatrix g x y).det)⁻¹) x :=
    (gramMatrix_det_contMDiffAt_three g x).inv₀
      (gramMatrix_at_base_det_ne_zero (g := g) (x := x))
  have hadj := gramMatrix_adjugate_entry_contMDiffAt_three g x i j
  exact (hdetInv.smul hadj).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ by simp [Matrix.inv_def])

/--
The metric-raised dual of the anchored canonical frame, expressed by inverse
Gram coefficients.  This is a genuine local-frame field, unlike the raw
pointwise `finBasis` field.
-/
noncomputable def deTurckAnchoredRaisedBasisField
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) : ∀ y : M, TM y :=
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  fun y ↦ ∑ j, (gramMatrix g x y)⁻¹ i j • gramFrame x y j

/-- The anchored raised dual field is `C³` at its anchor. -/
theorem deTurckAnchoredRaisedBasisField_contMDiffAt_three
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3
      (T% (deTurckAnchoredRaisedBasisField g x i)) x := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  unfold deTurckAnchoredRaisedBasisField
  refine ContMDiffAt.sum_section
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x))))) ?_
  intro j _hj
  exact (gramMatrix_inv_entry_contMDiffAt_three g x i j).smul_section
    (by simpa [gramFrame, b] using
      (FiberBundle.contMDiffAt_extend' (k := 3) I E (b j)))

/-- At the anchor, the corrected raised field is the actual metric-raised dual basis vector. -/
theorem deTurckAnchoredRaisedBasisField_apply_anchor
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) :
    deTurckAnchoredRaisedBasisField g x i x =
      (letI : FiniteDimensional ℝ (TM x) :=
        inferInstanceAs (FiniteDimensional ℝ E)
      metricDualVectorAt g x ((Module.finBasis ℝ (TM x)).coord i)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  rw [metricDualVectorAt_finBasis_coord_eq_sum_gram_inv]
  simp [deTurckAnchoredRaisedBasisField, gramFrame]

/--
Applying the difference of two canonical Levi-Civita connections to honest
`C³` and `C²` tangent fields gives a `C²` tangent field at the point.
-/
theorem connectionDifference_apply_contMDiffAt_two
    (g bg : ClosedSmoothRiemannianMetric n M) {x : M}
    {Z W : ∀ y : M, TM y}
    (hZ : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3 (T% Z) x)
    (hW : ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2 (T% W) x) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
      (T% (fun y : M ↦
        g.leviCivita Z y (W y) - bg.leviCivita Z y (W y))) x := by
  have hg := CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
    (cov := g.leviCivita) hZ hW
  have hbg := CovariantDerivative.contMDiffAt_cov_section_of_contMDiffAt_two
    (cov := bg.leviCivita) hZ hW
  exact hg.sub_section hbg

/--
The vector-valued metric contraction of the connection difference is
independent of the finite basis used to compute it.

The proof pairs the contraction with an arbitrary metric covector and invokes
the existing scalar metric-trace basis invariance.
-/
theorem deTurckVectorFieldAt_eq_trace_in_basis
    (g bg : ClosedSmoothRiemannianMetric n M) (y : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM y)) :
    deTurckVectorFieldAt g bg y =
      ∑ i, deTurckConnectionDifferenceAt g bg y (b i)
        (metricDualVectorAt g y (b.coord i)) := by
  classical
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  apply (LinearMap.BilinForm.toDual (g.metricBilinAt y)
    (g.metricBilinAt_nondegenerate y)).injective
  ext w
  let B : LinearMap.BilinForm ℝ (TM y) :=
    LinearMap.mk₂ ℝ
      (fun p q ↦ g.inner y (deTurckConnectionDifferenceAt g bg y p q) w)
      (fun p p' q ↦ by
        dsimp
        rw [deTurckConnectionDifferenceAt_add_left]
        exact congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
          (map_add (g.inner y)
            (deTurckConnectionDifferenceAt g bg y p q)
            (deTurckConnectionDifferenceAt g bg y p' q)))
      (fun c p q ↦ by
        dsimp
        rw [deTurckConnectionDifferenceAt_smul_left]
        simpa [smul_eq_mul] using
          (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
            (map_smul (g.inner y) c
              (deTurckConnectionDifferenceAt g bg y p q)) : _))
      (fun p q q' ↦ by
        dsimp
        rw [deTurckConnectionDifferenceAt_add_right]
        exact congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
          (map_add (g.inner y)
            (deTurckConnectionDifferenceAt g bg y p q)
            (deTurckConnectionDifferenceAt g bg y p q')))
      (fun c p q ↦ by
        dsimp
        rw [deTurckConnectionDifferenceAt_smul_right]
        simpa [smul_eq_mul] using
          (congrArg (fun L : TM y →L[ℝ] ℝ ↦ L w)
            (map_smul (g.inner y) c
              (deTurckConnectionDifferenceAt g bg y p q)) : _))
  have htrace :
      metricTraceInBasisAt g y B (Module.finBasis ℝ (TM y)) =
        metricTraceInBasisAt g y B b :=
    metricTraceInBasisAt_eq_metricTraceInBasisAt
      (g := g) (x := y) (B := B)
      (b := Module.finBasis ℝ (TM y)) (c := b)
  simpa [deTurckVectorFieldAt, metricTraceInBasisAt, B,
    LinearMap.BilinForm.toDual_def,
    ClosedSmoothRiemannianMetric.metricBilinAt_apply] using htrace

/-- One corrected anchored local-frame summand of the DeTurck contraction. -/
noncomputable def deTurckAnchoredLocalFrameSummand
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) : ∀ y : M, TM y :=
  fun y ↦
    g.leviCivita (deTurckAnchoredRaisedBasisField g x i) y (gramFrame x y i) -
      bg.leviCivita (deTurckAnchoredRaisedBasisField g x i) y (gramFrame x y i)

/-- Every corrected anchored local-frame summand is `C²` at its anchor. -/
theorem deTurckAnchoredLocalFrameSummand_contMDiffAt_two
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
      (T% (deTurckAnchoredLocalFrameSummand g bg x i)) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  apply connectionDifference_apply_contMDiffAt_two g bg
    (deTurckAnchoredRaisedBasisField_contMDiffAt_three g x i)
  simpa [gramFrame] using
    (FiberBundle.contMDiffAt_extend' (k := 2) I E
      ((Module.finBasis ℝ (TM x)) i))

/-- The corrected summand has the exact pointwise DeTurck summand value at its anchor. -/
theorem deTurckAnchoredLocalFrameSummand_apply_anchor
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (i : Fin (Module.finrank ℝ (TM x))) :
    deTurckAnchoredLocalFrameSummand g bg x i x =
      deTurckVectorFieldSummand g bg i x := by
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let Z : ∀ y : M, TM y := deTurckAnchoredRaisedBasisField g x i
  let W : ∀ y : M, TM y := fun y ↦ gramFrame x y i
  have hZ : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% Z) x :=
    (deTurckAnchoredRaisedBasisField_contMDiffAt_three g x i).mdifferentiableAt
      (by norm_num)
  have hdiff := IsCovariantDerivativeOn.difference_apply
    (g.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (bg.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (x := x) (σ := Z) (s := Set.univ) (by trivial) hZ
  have hdiffApply := congrArg (fun L : TM x →L[ℝ] TM x ↦ L (W x)) hdiff
  have hlocal :
      deTurckAnchoredLocalFrameSummand g bg x i x =
        ((g.leviCivita.difference bg.leviCivita) x (Z x)) (W x) := by
    simpa [deTurckAnchoredLocalFrameSummand, Z, W] using hdiffApply.symm
  rw [hlocal]
  dsimp [Z, W]
  rw [deTurckAnchoredRaisedBasisField_apply_anchor]
  simpa [W, gramFrame] using
    (deTurckVectorFieldSummand_eq_difference g bg i x).symm

/-- The corrected local-frame representative of the full DeTurck trace at `x`. -/
noncomputable def deTurckAnchoredLocalFrameField
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) : ∀ y : M, TM y :=
  fun y ↦ ∑ i : Fin (Module.finrank ℝ (TM x)),
    deTurckAnchoredLocalFrameSummand g bg x i y

/-- The corrected local-frame representative is `C²` at its anchor. -/
theorem deTurckAnchoredLocalFrameField_contMDiffAt_two
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
      (T% (deTurckAnchoredLocalFrameField g bg x)) x := by
  classical
  unfold deTurckAnchoredLocalFrameField
  exact ContMDiffAt.sum_section
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TM x)))))
    (fun i _hi ↦ deTurckAnchoredLocalFrameSummand_contMDiffAt_two g bg x i)

/-- The corrected local representative has exactly the DeTurck field value at its anchor. -/
theorem deTurckAnchoredLocalFrameField_apply_anchor
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    deTurckAnchoredLocalFrameField g bg x x = deTurckVectorFieldAt g bg x := by
  classical
  rw [deTurckVectorFieldAt_eq_sum_summands]
  exact Finset.sum_congr rfl fun i _hi ↦
    deTurckAnchoredLocalFrameSummand_apply_anchor g bg x i

/--
At a point where the anchored Gram frame is a basis and every anchored raised
field is differentiable, the corrected local-frame contraction is the actual
basis-independent DeTurck trace.
-/
theorem deTurckAnchoredLocalFrameField_apply_of_isUnit
    (g bg : ClosedSmoothRiemannianMetric n M) (x y : M)
    (hG : IsUnit (gramMatrix g x y))
    (hRaised : ∀ i : Fin (Module.finrank ℝ (TM x)),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
        (T% (deTurckAnchoredRaisedBasisField g x i)) y) :
    deTurckAnchoredLocalFrameField g bg x y =
      deTurckVectorFieldAt g bg y := by
  classical
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := gramFrameBasis g x y hG
  rw [deTurckVectorFieldAt_eq_trace_in_basis g bg y b]
  unfold deTurckAnchoredLocalFrameField
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  let Z : ∀ z : M, TM z := deTurckAnchoredRaisedBasisField g x i
  have hdiff := IsCovariantDerivativeOn.difference_apply
    (g.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (bg.leviCivita.isCovariantDerivativeOn (s := Set.univ))
    (x := y) (σ := Z) (s := Set.univ) (by trivial) (hRaised i)
  have hdiffApply :=
    congrArg (fun L : TM y →L[ℝ] TM y ↦ L (gramFrame x y i)) hdiff
  calc
    deTurckAnchoredLocalFrameSummand g bg x i y =
        ((g.leviCivita.difference bg.leviCivita) y (Z y))
          (gramFrame x y i) := by
      simpa [deTurckAnchoredLocalFrameSummand, Z] using hdiffApply.symm
    _ = deTurckConnectionDifferenceAt g bg y (b i)
          (metricDualVectorAt g y (b.coord i)) := by
      rw [deTurckConnectionDifferenceAt_eq_difference]
      simp [b, Z, deTurckAnchoredRaisedBasisField,
        metricDualVectorAt_gramFrameBasis_coord_eq_sum_inv]

/--
Near its anchor, the corrected local-frame representative equals the actual
pointwise DeTurck field.

The Gram matrix is invertible near the anchor, while C-three regularity of the
finitely many raised frame fields persists on a possibly smaller
neighborhood.
-/
theorem deTurckAnchoredLocalFrameField_eventuallyEq
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    (fun y : M ↦ deTurckAnchoredLocalFrameField g bg x y) =ᶠ[nhds x]
      (fun y : M ↦ deTurckVectorFieldAt g bg y) := by
  have hRaised :
      ∀ i : Fin (Module.finrank ℝ (TM x)),
        ∀ᶠ y in nhds x,
          MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
            (T% (deTurckAnchoredRaisedBasisField g x i)) y := by
    intro i
    have hC3 :
        ∀ᶠ y in nhds x,
          ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 3
            (T% (deTurckAnchoredRaisedBasisField g x i)) y :=
      (contMDiffAt_iff_contMDiffAt_nhds (n := 3) (by norm_num)).mp
        (deTurckAnchoredRaisedBasisField_contMDiffAt_three g x i)
    exact hC3.mono fun y hy ↦ hy.mdifferentiableAt (by norm_num)
  have hRaisedAll :
      ∀ᶠ y in nhds x, ∀ i : Fin (Module.finrank ℝ (TM x)),
        MDifferentiableAt I ((I).prod 𝓘(ℝ, E))
          (T% (deTurckAnchoredRaisedBasisField g x i)) y :=
    Filter.eventually_all.mpr hRaised
  filter_upwards [gramMatrix_eventually_isUnit (g := g) x, hRaisedAll]
    with y hG hy
  exact deTurckAnchoredLocalFrameField_apply_of_isUnit g bg x y hG hy

/--
The pointwise, basis-defined DeTurck field is honestly C-two at every point.
The proof is local: it transfers regularity from the anchored Gram-frame
representative through the neighborhood equality above.
-/
theorem deTurckVectorFieldAt_contMDiffAt_two
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E)) 2
      (T% (fun y : M ↦ deTurckVectorFieldAt g bg y)) x := by
  have hlocal := deTurckAnchoredLocalFrameField_contMDiffAt_two g bg x
  apply hlocal.congr_of_eventuallyEq
  have heq := deTurckAnchoredLocalFrameField_eventuallyEq g bg x
  filter_upwards [heq] with y hy
  rw [Bundle.TotalSpace.mk_inj]
  exact hy.symm

/-- The concrete DeTurck field of two smooth metrics is a closed C-two tangent field. -/
theorem deTurckVectorFieldAt_closedC2
    (g bg : ClosedSmoothRiemannianMetric n M) :
    ClosedC2TangentField (n := n) (M := M)
      (fun y : M ↦ deTurckVectorFieldAt g bg y) := by
  intro x
  exact deTurckVectorFieldAt_contMDiffAt_two g bg x

/-- The regularity clause for the concrete time-slice DeTurck field is unconditional. -/
theorem deTurckVectorFieldRegularAt_holds
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ) :
    DeTurckVectorFieldRegularAt gt bg t := by
  simpa [DeTurckVectorFieldRegularAt, deTurckVectorField] using
    (deTurckVectorFieldAt_closedC2 (g := gt t) (bg := bg))

end General

end Poincare
