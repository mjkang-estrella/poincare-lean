import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The bounded parabolic Hölder space, with the sum norm.

An element is represented by a bounded function, zero off the cylinder, and
its bounded scaled differences. The graph equations determine the second
component uniquely. Thus the carrier includes every bounded Hölder function,
with no approximation or continuity condition. The graph is closed in the
sum of two complete spaces of bounded functions.
-/

noncomputable section

namespace Poincare.ParabolicHolder

open Set
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parabolicDist (p q : ℝ × E) : ℝ :=
  ‖p.2 - q.2‖ + Real.sqrt |p.1 - q.1|

theorem parabolicDist_nonneg (p q : ℝ × E) : 0 ≤ parabolicDist p q := by
  exact add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

theorem parabolicDist_symm (p q : ℝ × E) :
    parabolicDist p q = parabolicDist q p := by
  simp only [parabolicDist, norm_sub_rev, abs_sub_comm]

theorem parabolicDist_pos {p q : ℝ × E} (h : p ≠ q) : 0 < parabolicDist p q := by
  by_cases hx : p.2 = q.2
  · have ht : p.1 ≠ q.1 := fun ht => h (Prod.ext ht hx)
    exact add_pos_of_nonneg_of_pos (norm_nonneg _)
      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.2 ht)))
  · exact add_pos_of_pos_of_nonneg (norm_pos_iff.2 (sub_ne_zero.2 hx))
      (Real.sqrt_nonneg _)

def cylinder (T : ℝ) : Set (ℝ × E) := Icc 0 T ×ˢ univ

def HasHolderBound (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) (K : ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ‖f p - f q‖ ≤ K * parabolicDist p q ^ α

/-- Distinct ordered pairs in the set; the diagonal contributes zero. -/
def Pairs (S : Set (ℝ × E)) :=
  {pq : (ℝ × E) × (ℝ × E) // pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1 ≠ pq.2}

/-- Inserting zero also specifies the seminorm on the empty set. -/
def holderSeminorm (α : ℝ) (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
  sSup (insert 0 (range fun i : Pairs S =>
    ‖f i.1.1 - f i.1.2‖ / parabolicDist i.1.1 i.1.2 ^ α))

def supNorm (S : Set (ℝ × E)) (f : ℝ × E → F) : ℝ :=
  sSup (insert 0 (range fun p : S => ‖f p‖))

/-- The first factor stores values and the second stores scaled differences. -/
abbrev Ambient (T : ℝ) (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  WithLp 1 (lp (fun _ : ℝ × E => F) ∞ × lp (fun _ : Pairs (cylinder (E := E) T) => F) ∞)

def holderSubmodule (α T : ℝ) : Submodule ℝ (Ambient T E F) where
  carrier := {v | (∀ p, p ∉ cylinder T → v.fst p = 0) ∧
    ∀ i : Pairs (cylinder (E := E) T), v.snd i =
      (parabolicDist i.1.1 i.1.2 ^ α)⁻¹ • (v.fst i.1.1 - v.fst i.1.2)}
  zero_mem' := by
    constructor
    · intro p _
      rfl
    · intro i
      change (0 : F) = _ • (0 - 0)
      simp
  add_mem' := by
    intro v w hv hw
    constructor
    · intro p hp
      change v.fst p + w.fst p = 0
      rw [hv.1 p hp, hw.1 p hp, add_zero]
    · intro i
      change v.snd i + w.snd i = _
      rw [hv.2 i, hw.2 i, ← smul_add]
      congr 1
      change _ = (v.fst i.1.1 + w.fst i.1.1) - (v.fst i.1.2 + w.fst i.1.2)
      abel
  smul_mem' := by
    intro c v hv
    constructor
    · intro p hp
      change c • v.fst p = 0
      rw [hv.1 p hp, smul_zero]
    · intro i
      change c • v.snd i = _
      rw [hv.2 i, smul_comm]
      congr 1
      exact smul_sub c _ _

/-- The graph subtype stores the boundedness witnesses in its two `lp` factors.
The support equation selects the unique extension that is zero off the cylinder. -/
abbrev Y (α T : ℝ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  ↥(holderSubmodule (E := E) (F := F) α T)

variable {α T : ℝ}

instance instCoeFun : CoeFun (Y (E := E) α T F) (fun _ => ℝ × E → F) := ⟨fun f => f.val.fst⟩

theorem zero_off (f : Y (E := E) α T F) {p : ℝ × E} (hp : p ∉ cylinder T) :
    f p = 0 := f.property.1 p hp

theorem increment_eq (f : Y (E := E) α T F) (i : Pairs (cylinder (E := E) T)) :
    f.val.snd i = (parabolicDist i.1.1 i.1.2 ^ α)⁻¹ • (f i.1.1 - f i.1.2) :=
  f.property.2 i

theorem increment_norm (f : Y (E := E) α T F) (i : Pairs (cylinder (E := E) T)) :
    ‖f.val.snd i‖ = ‖f i.1.1 - f i.1.2‖ / parabolicDist i.1.1 i.1.2 ^ α := by
  rw [increment_eq, norm_smul, Real.norm_of_nonneg
    (inv_nonneg.2 (Real.rpow_pos_of_pos (parabolicDist_pos i.2.2.2) α).le)]
  exact mul_comm _ _

theorem norm_eq_parts (f : Y (E := E) α T F) :
    ‖f‖ = ‖f.val.fst‖ + ‖f.val.snd‖ :=
  WithLp.prod_norm_eq_of_L1 f.val

theorem norm_le (f : Y (E := E) α T F) (p : ℝ × E) : ‖f p‖ ≤ ‖f‖ := by
  rw [norm_eq_parts]
  exact (lp.norm_apply_le_norm (by simp) f.val.fst p).trans
    (le_add_of_nonneg_right (norm_nonneg _))

theorem holder_le (f : Y (E := E) α T F) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖f p - f q‖ ≤ ‖f‖ * parabolicDist p q ^ α := by
  by_cases h : p = q
  · subst q
    simp only [sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
  · let i : Pairs (cylinder (E := E) T) := ⟨(p, q), hp, hq, h⟩
    have hi := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) f.val.snd i
    rw [increment_norm] at hi
    have hbound : ‖f.val.snd‖ ≤ ‖f‖ := by
      rw [norm_eq_parts]
      exact le_add_of_nonneg_left (norm_nonneg _)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos h) α)).1
      (hi.trans hbound)

theorem bounded (f : Y (E := E) α T F) :
    ∃ M : ℝ, ∀ p ∈ cylinder T, ‖f p‖ ≤ M := ⟨‖f‖, fun p _ => norm_le f p⟩

theorem hasHolderBound (f : Y (E := E) α T F) :
    HasHolderBound α (cylinder T) f ‖f‖ := fun _ hp _ hq => holder_le f hp hq

theorem scaledDifference_norm (α : ℝ) (f : ℝ × E → F) {p q : ℝ × E} (h : p ≠ q) :
    ‖(parabolicDist p q ^ α)⁻¹ • (f p - f q)‖ =
      ‖f p - f q‖ / parabolicDist p q ^ α := by
  rw [norm_smul, Real.norm_of_nonneg
    (inv_nonneg.2 (Real.rpow_pos_of_pos (parabolicDist_pos h) α).le)]
  exact mul_comm _ _

/-- Construct an element from exactly the boundedness and Hölder witnesses. -/
def ofFunction (f : ℝ × E → F) (hoff : ∀ p, p ∉ cylinder T → f p = 0)
    (hb : ∃ M : ℝ, ∀ p ∈ cylinder T, ‖f p‖ ≤ M)
    (hh : ∃ K : ℝ, HasHolderBound α (cylinder T) f K) : Y (E := E) α T F := by
  let v : lp (fun _ : ℝ × E => F) ∞ := ⟨f, by
    obtain ⟨M, hM⟩ := hb
    apply memℓp_infty
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨p, rfl⟩
    dsimp only
    by_cases hp : p ∈ cylinder T
    · exact (hM p hp).trans (le_max_left _ _)
    · rw [hoff p hp, norm_zero]
      exact le_max_right _ _⟩
  let w : lp (fun _ : Pairs (cylinder (E := E) T) => F) ∞ :=
    ⟨fun i => (parabolicDist i.1.1 i.1.2 ^ α)⁻¹ • (f i.1.1 - f i.1.2), by
      obtain ⟨K, hK⟩ := hh
      apply memℓp_infty
      refine ⟨K, ?_⟩
      rintro _ ⟨i, rfl⟩
      dsimp only
      rw [scaledDifference_norm α f i.2.2.2]
      exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos i.2.2.2) α)).2
        (hK _ i.2.1 _ i.2.2.1)⟩
  exact ⟨WithLp.toLp 1 (v, w), hoff, fun _ => rfl⟩

@[simp] theorem ofFunction_apply (f : ℝ × E → F) (hoff hb hh) (p : ℝ × E) :
    ofFunction (α := α) (T := T) f hoff hb hh p = f p := rfl

/-- The graph representation imposes exactly the three function-level conditions. -/
theorem exists_rep_iff (f : ℝ × E → F) :
    (∃ y : Y (E := E) α T F, ∀ p, y p = f p) ↔
      (∀ p, p ∉ cylinder T → f p = 0) ∧
      (∃ M : ℝ, ∀ p ∈ cylinder T, ‖f p‖ ≤ M) ∧
      (∃ K : ℝ, HasHolderBound α (cylinder T) f K) := by
  constructor
  · rintro ⟨y, hy⟩
    have hf : (y : ℝ × E → F) = f := funext hy
    rw [← hf]
    exact ⟨fun _ hp => zero_off y hp, bounded y, ‖y‖, hasHolderBound y⟩
  · rintro ⟨hoff, hb, hh⟩
    exact ⟨ofFunction f hoff hb hh, fun _ => rfl⟩

@[simp] theorem zero_apply (p : ℝ × E) : (0 : Y (E := E) α T F) p = 0 := rfl

@[simp] theorem add_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
    (f + g) p = f p + g p := rfl

@[simp] theorem sub_apply (f g : Y (E := E) α T F) (p : ℝ × E) :
    (f - g) p = f p - g p := rfl

@[simp] theorem smul_apply (c : ℝ) (f : Y (E := E) α T F) (p : ℝ × E) :
    (c • f) p = c • f p := rfl

@[ext] theorem ext {f g : Y (E := E) α T F} (h : ∀ p ∈ cylinder T, f p = g p) :
    f = g := by
  have hval : f.val.fst = g.val.fst := by
    apply lp.ext
    funext p
    by_cases hp : p ∈ cylinder T
    · exact h p hp
    · exact (zero_off f hp).trans (zero_off g hp).symm
  apply Subtype.ext
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext hval
  apply lp.ext
  funext i
  change f.val.snd i = g.val.snd i
  rw [increment_eq, increment_eq]
  change _ • (f.val.fst _ - f.val.fst _) = _ • (g.val.fst _ - g.val.fst _)
  rw [hval]

theorem holderSeminorm_bddAbove (f : Y (E := E) α T F) :
    BddAbove (insert 0 (range fun i : Pairs (cylinder (E := E) T) =>
      ‖f i.1.1 - f i.1.2‖ / parabolicDist i.1.1 i.1.2 ^ α)) := by
  refine ⟨‖f.val.snd‖, ?_⟩
  rintro r (rfl | ⟨i, rfl⟩)
  · exact norm_nonneg _
  · dsimp only
    rw [← increment_norm]
    exact lp.norm_apply_le_norm (by simp) _ _

theorem holderSeminorm_eq (f : Y (E := E) α T F) :
    holderSeminorm α (cylinder T) f = ‖f.val.snd‖ := by
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    rintro r (rfl | ⟨i, rfl⟩)
    · exact norm_nonneg _
    · dsimp only
      rw [← increment_norm]
      exact lp.norm_apply_le_norm (by simp) _ _
  · apply lp.norm_le_of_forall_le
    · exact le_csSup (holderSeminorm_bddAbove f) (mem_insert _ _)
    · intro i
      rw [increment_norm]
      exact le_csSup (holderSeminorm_bddAbove f) (mem_insert_of_mem _ (mem_range_self i))

theorem supNorm_bddAbove (f : Y (E := E) α T F) :
    BddAbove (insert 0 (range fun p : cylinder (E := E) T => ‖f p‖)) := by
  refine ⟨‖f.val.fst‖, ?_⟩
  rintro r (rfl | ⟨p, rfl⟩)
  · exact norm_nonneg _
  · exact lp.norm_apply_le_norm (by simp) _ _

theorem supNorm_eq (f : Y (E := E) α T F) :
    supNorm (cylinder T) f = ‖f.val.fst‖ := by
  apply le_antisymm
  · apply csSup_le (insert_nonempty _ _)
    rintro r (rfl | ⟨p, rfl⟩)
    · exact norm_nonneg _
    · exact lp.norm_apply_le_norm (by simp) _ _
  · have h0 : 0 ≤ supNorm (cylinder T) f :=
      le_csSup (supNorm_bddAbove f) (mem_insert _ _)
    apply lp.norm_le_of_forall_le h0
    intro p
    by_cases hp : p ∈ cylinder T
    · exact le_csSup (supNorm_bddAbove f)
        (mem_insert_of_mem _ (mem_range_self (⟨p, hp⟩ : cylinder T)))
    · change ‖f p‖ ≤ _
      rw [zero_off f hp, norm_zero]
      exact h0

/-- The norm is the requested sum, not the maximum norm on the ordinary product. -/
theorem norm_eq (f : Y (E := E) α T F) :
    ‖f‖ = supNorm (cylinder T) f + holderSeminorm α (cylinder T) f := by
  rw [supNorm_eq, holderSeminorm_eq, norm_eq_parts]

theorem norm_le_of_bounds (f : Y (E := E) α T F) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ M) (hh : HasHolderBound α (cylinder T) f K) :
    ‖f‖ ≤ M + K := by
  rw [norm_eq_parts]
  apply add_le_add
  · apply lp.norm_le_of_forall_le hM
    intro p
    by_cases hp : p ∈ cylinder T
    · exact hb p hp
    · change ‖f p‖ ≤ M
      simpa [zero_off f hp] using hM
  · apply lp.norm_le_of_forall_le hK
    intro i
    rw [increment_norm]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos i.2.2.2) α)).2
      (hh _ i.2.1 _ i.2.2.1)

theorem isClosed_holderSubmodule :
    IsClosed (holderSubmodule (E := E) (F := F) α T : Set (Ambient T E F)) := by
  [PROOF_BODY_OMITTED_FOR_STATEMENT_REVIEW]

instance instCompleteSpace [CompleteSpace F] : CompleteSpace (Y (E := E) α T F) :=
  isClosed_holderSubmodule.isComplete.completeSpace_coe

theorem supNorm_nonneg (f : Y (E := E) α T F) : 0 ≤ supNorm (cylinder T) f := by
  rw [supNorm_eq]
  exact norm_nonneg _

theorem holderSeminorm_nonneg (f : Y (E := E) α T F) :
    0 ≤ holderSeminorm α (cylinder T) f := by
  rw [holderSeminorm_eq]
  exact norm_nonneg _

theorem le_supNorm (f : Y (E := E) α T F) (p : ℝ × E) :
    ‖f p‖ ≤ supNorm (cylinder T) f := by
  rw [supNorm_eq]
  exact lp.norm_apply_le_norm (by simp) _ _

theorem hasHolderBound_seminorm (f : Y (E := E) α T F) :
    HasHolderBound α (cylinder T) f (holderSeminorm α (cylinder T) f) := by
  intro p hp q hq
  rw [holderSeminorm_eq]
  by_cases h : p = q
  · subst q
    simp only [sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (parabolicDist_nonneg p p) _)
  · let i : Pairs (cylinder (E := E) T) := ⟨(p, q), hp, hq, h⟩
    have hi := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) f.val.snd i
    rw [increment_norm] at hi
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (parabolicDist_pos h) α)).1 hi

/-- The product estimate keeps the two sup norms separate from the two seminorms. -/
theorem product_holderBound (f g : Y (E := E) α T ℝ) :
    HasHolderBound α (cylinder T) (fun p => f p * g p)
      (supNorm (cylinder T) f * holderSeminorm α (cylinder T) g +
        holderSeminorm α (cylinder T) f * supNorm (cylinder T) g) := by
  intro p hp q hq
  calc
    ‖f p * g p - f q * g q‖ =
        ‖f p * (g p - g q) + (f p - f q) * g q‖ := by congr 1; ring
    _ ≤ ‖f p * (g p - g q)‖ + ‖(f p - f q) * g q‖ := norm_add_le _ _
    _ = ‖f p‖ * ‖g p - g q‖ + ‖f p - f q‖ * ‖g q‖ := by rw [norm_mul, norm_mul]
    _ ≤ supNorm (cylinder T) f *
          (holderSeminorm α (cylinder T) g * parabolicDist p q ^ α) +
        (holderSeminorm α (cylinder T) f * parabolicDist p q ^ α) *
          supNorm (cylinder T) g := by
      apply add_le_add
      · exact mul_le_mul (le_supNorm f p) (hasHolderBound_seminorm g p hp q hq)
          (norm_nonneg _) (supNorm_nonneg f)
      · exact mul_le_mul (hasHolderBound_seminorm f p hp q hq) (le_supNorm g q)
          (norm_nonneg _) (mul_nonneg (holderSeminorm_nonneg f)
            (Real.rpow_nonneg (parabolicDist_nonneg p q) _))
    _ = _ := by ring

def pointwiseMul (f g : Y (E := E) α T ℝ) : Y (E := E) α T ℝ :=
  ofFunction (fun p => f p * g p)
    (fun p hp => by dsimp only; rw [zero_off f hp, zero_mul])
    ⟨supNorm (cylinder T) f * supNorm (cylinder T) g, fun p _ => by
      rw [norm_mul]
      exact mul_le_mul (le_supNorm f p) (le_supNorm g p) (norm_nonneg _) (supNorm_nonneg f)⟩
    ⟨_, product_holderBound f g⟩

instance instMul : Mul (Y (E := E) α T ℝ) := ⟨pointwiseMul⟩

@[simp] theorem mul_apply (f g : Y (E := E) α T ℝ) (p : ℝ × E) :
    (f * g) p = f p * g p := rfl

theorem norm_mul_le (f g : Y (E := E) α T ℝ) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  have hb : ‖f * g‖ ≤ supNorm (cylinder T) f * supNorm (cylinder T) g +
      (supNorm (cylinder T) f * holderSeminorm α (cylinder T) g +
        holderSeminorm α (cylinder T) f * supNorm (cylinder T) g) := by
    apply norm_le_of_bounds (f * g)
    · exact mul_nonneg (supNorm_nonneg f) (supNorm_nonneg g)
    · exact add_nonneg
        (mul_nonneg (supNorm_nonneg f) (holderSeminorm_nonneg g))
        (mul_nonneg (holderSeminorm_nonneg f) (supNorm_nonneg g))
    · intro p _
      rw [mul_apply, norm_mul]
      exact mul_le_mul (le_supNorm f p) (le_supNorm g p) (norm_nonneg _) (supNorm_nonneg f)
    · exact product_holderBound f g
  rw [norm_eq f, norm_eq g]
  nlinarith [mul_nonneg (holderSeminorm_nonneg f) (holderSeminorm_nonneg g)]

/-- Pointwise multiplication stays in the carrier, with the sharp norm bound. -/
theorem mul_mem (f g : Y (E := E) α T ℝ) :
    (∀ p, (f * g) p = f p * g p) ∧ ‖f * g‖ ≤ ‖f‖ * ‖g‖ :=
  ⟨mul_apply f g, norm_mul_le f g⟩

omit [NormedAddCommGroup E] in
theorem cylinder_mono {T' : ℝ} (hT : T' ≤ T) :
    cylinder (E := E) T' ⊆ cylinder T := by
  intro p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans hT⟩, hp.2⟩

/-- Restriction uses the zero extension on the smaller cylinder. -/
def restrict {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F) : Y (E := E) α T' F := by
  classical
  exact ofFunction (fun p => if p ∈ cylinder T' then f p else 0)
    (fun p hp => if_neg hp)
    ⟨‖f‖, fun p hp => by dsimp only; rw [if_pos hp]; exact norm_le f p⟩
    ⟨‖f‖, fun p hp q hq => by
      dsimp only
      rw [if_pos hp, if_pos hq]
      exact holder_le f (cylinder_mono hT hp) (cylinder_mono hT hq)⟩

@[simp] theorem restrict_apply {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F)
    {p : ℝ × E} (hp : p ∈ cylinder T') : restrict hT f p = f p := by
  classical
  exact if_pos hp

theorem restrict_le {T' : ℝ} (hT : T' ≤ T) (f : Y (E := E) α T F) :
    ‖restrict hT f‖ ≤ ‖f‖ := by
  rw [norm_eq f]
  apply norm_le_of_bounds _ (supNorm_nonneg f) (holderSeminorm_nonneg f)
  · intro p hp
    rw [restrict_apply hT f hp]
    exact le_supNorm f p
  · intro p hp q hq
    rw [restrict_apply hT f hp, restrict_apply hT f hq]
    exact hasHolderBound_seminorm f p (cylinder_mono hT hp) q (cylinder_mono hT hq)

end Poincare.ParabolicHolder
