import Poincare.Global.DeTurckFlowSymmetricVariationalIdentification

/-!
# Physical-time form of the symmetric inverse DeTurck point flow

The symmetric variational-identification theorem is naturally stated in the
relative time variable `s`, with the restart time represented by `s = 0`.
This file translates that *same* two-sided family to physical time
`t = t₀ + s`.  In particular, no positive/negative-time branches are glued.
-/

noncomputable section

open Function Metric Set

namespace Poincare

section SymmetricPhysicalTime

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The symmetric inverse-gauge point flow and its variational identification in
physical time.

The returned family `Phi t x` starts from `x` at `t = t₀`, solves the
inverse-gauge point ODE on the closed symmetric physical-time interval, and
has initial-point derivative `J t` at the base point `x₀`.  The last
equality records the corresponding `fderiv` identity explicitly for later
pullback constructions.
-/
theorem exists_local_inverseGaugePointFlow_variationalIdentification_physicalTime
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDWcont : ContDiff ℝ 1 (Function.uncurry DW))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ),
      ∃ Phi : ℝ → E → E, ∃ J : ℝ → E →L[ℝ] E,
        (∀ x ∈ closedBall x₀ r,
          Phi t₀ x = x ∧
            ∀ t ∈ Icc (t₀ - T) (t₀ + T),
              HasDerivWithinAt (fun tau : ℝ ↦ Phi tau x)
                (-W t (Phi t x)) (Icc (t₀ - T) (t₀ + T)) t) ∧
        J t₀ = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc (t₀ - T) (t₀ + T),
          HasDerivWithinAt J
            (-((DW t (Phi t x₀)).comp (J t)))
            (Icc (t₀ - T) (t₀ + T)) t) ∧
        ∀ t ∈ Icc (t₀ - T) (t₀ + T),
          HasFDerivAt (Phi t) (J t) x₀ ∧
            fderiv ℝ (Phi t) x₀ = J t := by
  rcases exists_local_inverseGaugePointFlow_variationalIdentification_symmetric
      W DW hW hDWcont hDW t₀ x₀ with
    ⟨T, hT, r, hr, phi, D, hphi, hD₀, hD, hendpoint⟩
  let Phi : ℝ → E → E := fun t x ↦ phi x (t - t₀)
  let J : ℝ → E →L[ℝ] E := fun t ↦ D (t - t₀)
  have hshift : MapsTo (fun t : ℝ ↦ t - t₀)
      (Icc (t₀ - T) (t₀ + T)) (Icc (-T) T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨T, hT, r, hr, Phi, J, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · simpa [Phi] using (hphi x hx).1
    · intro t ht
      have houter := (hphi x hx).2 (t - t₀) (hshift ht)
      have hinner : HasDerivWithinAt (fun tau : ℝ ↦ tau - t₀) 1
          (Icc (t₀ - T) (t₀ + T)) t :=
        ((hasDerivAt_id t).sub_const t₀).hasDerivWithinAt
      convert HasFDerivWithinAt.comp_hasDerivWithinAt t
        houter.hasFDerivWithinAt hinner hshift using 1
      all_goals simp [Phi]
  · simpa [J] using hD₀
  · intro t ht
    have houter := hD (t - t₀) (hshift ht)
    have hinner : HasDerivWithinAt (fun tau : ℝ ↦ tau - t₀) 1
        (Icc (t₀ - T) (t₀ + T)) t :=
      ((hasDerivAt_id t).sub_const t₀).hasDerivWithinAt
    convert HasFDerivWithinAt.comp_hasDerivWithinAt t
      houter.hasFDerivWithinAt hinner hshift using 1
    all_goals simp [Phi, J]
  · intro t ht
    have h := hendpoint (t - t₀) (hshift ht)
    refine ⟨?_, ?_⟩
    · simpa [Phi, J] using h
    · simpa [Phi, J] using h.fderiv

end SymmetricPhysicalTime

end Poincare
