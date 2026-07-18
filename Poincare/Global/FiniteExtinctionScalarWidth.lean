import Poincare.Global.ScalarCurvatureBarrier
import Poincare.Global.ThreeDimensionalRicciTraceInequality

/-!
# Coupling scalar curvature to Perelman's width extinction inequality

This file connects two previously separate analytic pieces.  The
three-dimensional scalar-minimum barrier turns the raw width evolution

`W' ≤ -c - (1/2) r W`

into Perelman's standard

`W' ≤ -c + (3/4)(t+C)⁻¹ W`.

The terminal theorem then combines scalar Riccati comparison, surgery-jump
control, and the segmented integrating-factor argument to rule out a global
nonnegative width evolution.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Interval Topology BigOperators

namespace Poincare

/-- The Gauss--Bonnet forcing constant in Perelman's width inequality is
strictly positive. -/
theorem perelman_four_pi_pos : 0 < (4 : ℝ) * Real.pi :=
  mul_pos (by norm_num) Real.pi_pos

/-- Any finite-index failure has a first failure index, and every earlier
index is still alive. -/
theorem exists_first_extinction_index
    (Alive : ℕ → Prop) (h : ∃ k, ¬ Alive k) :
    ∃ k, (¬ Alive k) ∧ ∀ j < k, Alive j := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  intro j hj
  exact Classical.not_not.mp (Nat.find_min h hj)

/-- The scalar lower barrier converts the raw scalar-curvature term in the
width evolution into the standard three-quarter coefficient. -/
theorem three_quarter_width_inequality_of_scalar_lower_bound
    {C c t r W dW : ℝ}
    (htC : 0 < t + C) (hW : 0 ≤ W)
    (hr : -(3 / (2 * (t + C))) ≤ r)
    (hraw : dW ≤ -c - ((1 : ℝ) / 2) * r * W) :
    dW ≤ -c + ((3 : ℝ) / 4) * (t + C)⁻¹ * W := by
  have hbar : -((3 : ℝ) / 2) * (t + C)⁻¹ ≤ r := by
    convert hr using 1 <;> field_simp [htC.ne'] <;> ring
  have hmul :
      (-((3 : ℝ) / 2) * (t + C)⁻¹) * W ≤ r * W :=
    mul_le_mul_of_nonneg_right hbar hW
  have hcurvature :
      -((1 : ℝ) / 2) * (r * W) ≤
        -((1 : ℝ) / 2) *
          ((-((3 : ℝ) / 2) * (t + C)⁻¹) * W) :=
    mul_le_mul_of_nonpos_left hmul (by norm_num)
  nlinarith

/-- Exact `4π` specialization of the scalar-to-width conversion. -/
theorem perelman_three_quarter_width_inequality_of_scalar_lower_bound
    {C t r W dW : ℝ}
    (htC : 0 < t + C) (hW : 0 ≤ W)
    (hr : -(3 / (2 * (t + C))) ≤ r)
    (hraw : dW ≤ -((4 : ℝ) * Real.pi) - ((1 : ℝ) / 2) * r * W) :
    dW ≤ -((4 : ℝ) * Real.pi) +
      ((3 : ℝ) / 4) * (t + C)⁻¹ * W :=
  three_quarter_width_inequality_of_scalar_lower_bound htC hW hr hraw

/-- End-to-end scalar/width extinction mechanism for an infinite locally
finite surgery schedule.  The theorem consumes the geometric maximum-
principle and raw width-evolution inequalities pointwise, derives the scalar
barrier on every smooth segment, converts the width equation to the standard
three-quarter form, and obtains the integrating-factor contradiction. -/
theorem no_global_nonnegative_width_of_scalar_riccati_surgery_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (r dr W dW : ℕ → ℝ → ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (hrRiccati : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      ((2 : ℝ) / 3) * (r k t) ^ 2 ≤ dr k t)
    (hrSurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  have hscalar :=
    three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier
      hC r dr start hmono hrCont hrDeriv hrRiccati hrSurgery hrInitial
  have hstartMonotone : Monotone start := monotone_nat_of_le_succ hmono
  have hstartNonneg : ∀ k, 0 ≤ start k := by
    intro k
    rw [← hstart0]
    exact hstartMonotone (Nat.zero_le k)
  apply no_global_nonnegative_of_three_quarter_segmented_surgery_schedule
    hC hc W dW start hstart0 hmono hstartTop hWCont hWDeriv hWNonneg
  · intro k t ht
    have ht0 : 0 ≤ t := (hstartNonneg k).trans ht.1.le
    have htC : 0 < t + C := add_pos_of_nonneg_of_pos ht0 hC
    have hrLower : -(3 / (2 * (t + C))) ≤ r k t := by
      have h := hscalar k t ⟨ht.1.le, ht.2.le⟩
      simpa [hstart0, add_comm] using h
    exact three_quarter_width_inequality_of_scalar_lower_bound
      htC (hWNonneg k t ⟨ht.1.le, ht.2.le⟩) hrLower
        (hWidthRaw k t ht)
  · intro k
    exact mul_le_mul_of_nonneg_left (hWidthSurgery k)
      (inv_nonneg.mpr
        (add_nonneg (hstartNonneg (k + 1)) hC.le))

/-- Geometric-evolution form of the preceding extinction theorem.  Instead of
assuming the scalar Riccati inequality, callers provide the three Ricci
eigenvalues, a nonnegative Laplacian at the scalar minimum, and the scalar
evolution equation.  The dimension-three trace inequality derives the
Riccati premise internally. -/
theorem no_global_nonnegative_width_of_three_ricci_eigenvalue_surgery_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (r dr lap W dW : ℕ → ℝ → ℝ)
    (eig : ℕ → ℝ → Fin 3 → ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (htrace : ∀ k t, r k t = ∑ i, eig k t i)
    (hlap : ∀ k t, 0 ≤ lap k t)
    (hevolution : ∀ k t,
      dr k t = lap k t + 2 * ∑ i, (eig k t i) ^ 2)
    (hrSurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  apply no_global_nonnegative_width_of_scalar_riccati_surgery_schedule
    hC hc r dr W dW start hstart0 hmono hstartTop hrCont hrDeriv
  · intro k t ht
    exact scalar_riccati_inequality_of_three_ricci_eigenvalues
      (eig k t) (htrace k t) (hlap k t) (hevolution k t)
  · exact hrSurgery
  · exact hrInitial
  · exact hWCont
  · exact hWDeriv
  · exact hWNonneg
  · exact hWidthRaw
  · exact hWidthSurgery

/-- Orthonormal-frame matrix form of the end-to-end extinction theorem.  This
avoids choosing Ricci eigenvalues: the trace/Frobenius inequality derives the
same scalar Riccati estimate directly from the coordinate Ricci matrix. -/
theorem no_global_nonnegative_width_of_three_ricci_matrix_surgery_schedule
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (r dr lap W dW : ℕ → ℝ → ℝ)
    (A : ℕ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k,
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (htrace : ∀ k t, r k t = (A k t).trace)
    (hlap : ∀ k t, 0 ≤ lap k t)
    (hevolution : ∀ k t,
      dr k t = lap k t + 2 * ∑ i, ∑ j, (A k t i j) ^ 2)
    (hrSurgery : ∀ k,
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k,
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, ∀ t ∈ Set.Icc (start k) (start (k + 1)),
      0 ≤ W k t)
    (hWidthRaw : ∀ k, ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
      dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k,
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) : False := by
  apply no_global_nonnegative_width_of_scalar_riccati_surgery_schedule
    hC hc r dr W dW start hstart0 hmono hstartTop hrCont hrDeriv
  · intro k t ht
    exact scalar_riccati_inequality_of_three_ricci_matrix
      (A k t) (htrace k t) (hlap k t) (hevolution k t)
  · exact hrSurgery
  · exact hrInitial
  · exact hWCont
  · exact hWDeriv
  · exact hWNonneg
  · exact hWidthRaw
  · exact hWidthSurgery

/-- Finite-index extinction conclusion.  If the scalar/width evolution laws
are available on every segment that is still alive, then not every segment
can remain alive: some finite surgery index has no surviving component.
Unlike the global contradiction theorem, this exposes an existential
extinction index directly. -/
theorem exists_extinct_segment_of_three_ricci_matrix_width_evolution
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (Alive : ℕ → Prop)
    (r dr lap W dW : ℕ → ℝ → ℝ)
    (A H : ℕ → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (start : ℕ → ℝ)
    (hstart0 : start 0 = 0)
    (hmono : ∀ k, start k ≤ start (k + 1))
    (hstartTop : Tendsto start atTop atTop)
    (hrCont : ∀ k, Alive k →
      ContinuousOn (r k) (Set.Icc (start k) (start (k + 1))))
    (hrDeriv : ∀ k, Alive k →
      ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
        HasDerivWithinAt (r k) (dr k t) (Set.Ioi t) t)
    (htrace : ∀ k, Alive k → ∀ t, r k t = (A k t).trace)
    (hlapTrace : ∀ k, Alive k → ∀ t, lap k t = (H k t).trace)
    (hHdiag : ∀ k, Alive k → ∀ t i, 0 ≤ H k t i i)
    (hevolution : ∀ k, Alive k → ∀ t,
      dr k t = lap k t + 2 * ∑ i, ∑ j, (A k t i j) ^ 2)
    (hrSurgery : ∀ k, Alive k → Alive (k + 1) →
      r k (start (k + 1)) ≤ r (k + 1) (start (k + 1)))
    (hrInitial : -(3 / (2 * C)) ≤ r 0 (start 0))
    (hWCont : ∀ k, Alive k →
      ContinuousOn (W k) (Set.Icc (start k) (start (k + 1))))
    (hWDeriv : ∀ k, Alive k →
      ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
        HasDerivWithinAt (W k) (dW k t) (Set.Ioi t) t)
    (hWNonneg : ∀ k, Alive k →
      ∀ t ∈ Set.Icc (start k) (start (k + 1)), 0 ≤ W k t)
    (hWidthRaw : ∀ k, Alive k →
      ∀ t ∈ Set.Ioo (start k) (start (k + 1)),
        dW k t ≤ -c - ((1 : ℝ) / 2) * r k t * W k t)
    (hWidthSurgery : ∀ k, Alive k → Alive (k + 1) →
      W (k + 1) (start (k + 1)) ≤ W k (start (k + 1))) :
    ∃ k, ¬ Alive k := by
  by_contra hnone
  have hall : ∀ k, Alive k := by
    intro k
    by_contra hk
    exact hnone ⟨k, hk⟩
  exact no_global_nonnegative_width_of_three_ricci_matrix_surgery_schedule
    hC hc r dr lap W dW A start hstart0 hmono hstartTop
    (fun k => hrCont k (hall k))
    (fun k => hrDeriv k (hall k))
    (fun k => htrace k (hall k))
    (fun k t => by
      rw [hlapTrace k (hall k) t]
      exact matrix_trace_nonneg_of_diagonal_nonneg
        (H k t) (hHdiag k (hall k) t))
    (fun k => hevolution k (hall k))
    (fun k => hrSurgery k (hall k) (hall (k + 1)))
    hrInitial
    (fun k => hWCont k (hall k))
    (fun k => hWDeriv k (hall k))
    (fun k => hWNonneg k (hall k))
    (fun k => hWidthRaw k (hall k))
    (fun k => hWidthSurgery k (hall k) (hall (k + 1)))

end Poincare
