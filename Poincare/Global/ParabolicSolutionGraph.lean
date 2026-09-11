import Poincare.Global.ParabolicHolderSpace
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.TransferInstance

/-! The zero initial trace space of genuine parabolic derivative graphs. -/

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace Poincare.ParabolicSolutionGraph

open Set Filter
open scoped Topology
open ParabolicHolder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Graph (α T : ℝ) where
  u : Y (E := E) α T ℝ
  ut : Y (E := E) α T ℝ
  du : Y (E := E) α T (E →L[ℝ] ℝ)
  ddu : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)
  zero_trace : ∀ x : E, u (0, x) = 0
  hasFDeriv : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasFDerivAt (fun z : E => u (t, z)) (du (t, x)) x
  hasFDeriv_du : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasFDerivAt (fun z : E => du (t, z)) (ddu (t, x)) x
  hasDeriv_time : ∀ t ∈ Icc 0 T, ∀ x : E,
    HasDerivWithinAt (fun s : ℝ => u (s, x)) (ut (t, x)) (Icc 0 T) t

abbrev Ambient (α T : ℝ) :=
  WithLp 1 (WithLp 1 (Y (E := E) α T ℝ × Y (E := E) α T ℝ) ×
    WithLp 1 (Y (E := E) α T (E →L[ℝ] ℝ) ×
      Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)))

def graphSubmodule (α T : ℝ) : Submodule ℝ (Ambient (E := E) α T) where
  carrier := {v | (∀ x : E, v.fst.fst (0, x) = 0) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => v.fst.fst (t, z)) (v.snd.fst (t, x)) x) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasFDerivAt (fun z : E => v.snd.fst (t, z)) (v.snd.snd (t, x)) x) ∧
    (∀ t ∈ Icc 0 T, ∀ x : E,
      HasDerivWithinAt (fun s : ℝ => v.fst.fst (s, x)) (v.fst.snd (t, x)) (Icc 0 T) t)}
  zero_mem' := by
    refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
    · intro t ht x; exact hasFDerivAt_const (0 : ℝ) x
    · intro t ht x; exact hasFDerivAt_const (0 : E →L[ℝ] ℝ) x
    · intro t ht x; exact hasDerivWithinAt_const t (Icc 0 T) (0 : ℝ)
  add_mem' := by
    intro v w hv hw
    exact ⟨fun x => by change v.fst.fst (0,x) + w.fst.fst (0,x) = 0; rw [hv.1, hw.1, add_zero],
      fun t ht x => (hv.2.1 t ht x).add (hw.2.1 t ht x),
      fun t ht x => (hv.2.2.1 t ht x).add (hw.2.2.1 t ht x),
      fun t ht x => (hv.2.2.2 t ht x).add (hw.2.2.2 t ht x)⟩
  smul_mem' := by
    intro c v hv
    exact ⟨fun x => by change c • v.fst.fst (0,x) = 0; rw [hv.1, smul_zero],
      fun t ht x => (hv.2.1 t ht x).const_smul c,
      fun t ht x => (hv.2.2.1 t ht x).const_smul c,
      fun t ht x => (hv.2.2.2 t ht x).const_smul c⟩

variable {α T : ℝ}

def graphEquiv : Graph (E := E) α T ≃ ↥(graphSubmodule (E := E) α T) where
  toFun g := ⟨WithLp.toLp 1 (WithLp.toLp 1 (g.u, g.ut), WithLp.toLp 1 (g.du, g.ddu)),
    g.zero_trace, g.hasFDeriv, g.hasFDeriv_du, g.hasDeriv_time⟩
  invFun v := ⟨v.val.fst.fst, v.val.fst.snd, v.val.snd.fst, v.val.snd.snd,
    v.property.1, v.property.2.1, v.property.2.2.1, v.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instNormedAddCommGroup : NormedAddCommGroup (Graph (E := E) α T) :=
  graphEquiv.normedAddCommGroup

instance instModule : Module ℝ (Graph (E := E) α T) := graphEquiv.module ℝ

instance instNormedSpace : NormedSpace ℝ (Graph (E := E) α T) := by
  letI : NormedSpace ℝ (Ambient (E := E) α T) := inferInstance
  exact graphEquiv.normedSpace ℝ

theorem norm_eq (g : Graph (E := E) α T) :
    ‖g‖ = ‖g.u‖ + ‖g.ut‖ + ‖g.du‖ + ‖g.ddu‖ := by
  change ‖(graphEquiv g).val‖ = _
  simp only [WithLp.prod_norm_eq_of_L1]
  exact (add_assoc _ _ _).symm

theorem norm_u_le (g : Graph (E := E) α T) : ‖g.u‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_ut_le (g : Graph (E := E) α T) : ‖g.ut‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_du_le (g : Graph (E := E) α T) : ‖g.du‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem norm_ddu_le (g : Graph (E := E) α T) : ‖g.ddu‖ ≤ ‖g‖ := by
  rw [norm_eq]
  have := norm_nonneg g.u
  have := norm_nonneg g.ut
  have := norm_nonneg g.du
  have := norm_nonneg g.ddu
  linarith

theorem sup_u_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.u p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.u p).trans (norm_u_le g)

theorem holder_u_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.u p - g.u q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.u hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_u_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

theorem sup_ut_le (g : Graph (E := E) α T) (p : ℝ × E) :
    ‖g.ut p‖ ≤ ‖g‖ :=
  (ParabolicHolder.norm_le g.ut p).trans (norm_ut_le g)

theorem holder_ut_le (g : Graph (E := E) α T) {p q : ℝ × E}
    (hp : p ∈ cylinder T) (hq : q ∈ cylinder T) :
    ‖g.ut p - g.ut q‖ ≤ ‖g‖ * parabolicDist p q ^ α :=
  (ParabolicHolder.holder_le g.ut hp hq).trans
    (mul_le_mul_of_nonneg_right (norm_ut_le g)
      (Real.rpow_nonneg (parabolicDist_nonneg p q) _))

end Poincare.ParabolicSolutionGraph
