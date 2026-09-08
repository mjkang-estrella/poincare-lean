import Poincare.Global.GeodesicFlowJointDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Uniform normal neighborhoods for one fixed-chart flow

The exponential here is the position endpoint of the supplied joint flow.
It makes no identification with any separately selected per-anchor exponential.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology ContDiff NNReal

namespace Poincare.FixedChartUniformNormalRadius

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The position endpoint at the common time. -/
def expChart (α : (E × E) → ℝ → E × E) (T : ℝ) (z v : E) : E :=
  (α (z, v) T).1

/-- The joint anchor and endpoint map. -/
def F (α : (E × E) → ℝ → E × E) (T : ℝ) (p : E × E) : E × E :=
  (p.1, expChart α T p.1 p.2)

/-- The free-motion fundamental solution, including both initial directions. -/
def freeVariation (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  ((ContinuousLinearMap.fst ℝ E E) + t • (ContinuousLinearMap.snd ℝ E E)).prod
    (ContinuousLinearMap.snd ℝ E E)

/-- The derivative of the joint anchor and endpoint map. -/
def endpointDerivative (t : ℝ) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E).prod
    ((ContinuousLinearMap.fst ℝ E E) + t • (ContinuousLinearMap.snd ℝ E E))

/-- A zero-velocity trajectory is stationary on the entire common interval. -/
theorem flow_zero_velocity [FiniteDimensional ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hF : ContDiff ℝ 1 (geodesicFlowField Γ))
    {γ : ℝ → E × E} {z : E} {T : ℝ} (hT : 0 < T)
    (h0 : γ 0 = (z, 0))
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt γ
      (geodesicFlowField Γ (γ t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, γ t = (z, 0) := by
  have hc := HasDerivWithinAt.continuousOn hd
  obtain ⟨a, ha⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_closedBall (z, 0)
  have hm : ∀ t ∈ Icc (-T) T, γ t ∈ closedBall (z, 0) a :=
    fun t ht => ha (mem_image_of_mem γ ht)
  have hz := hm 0 (by constructor <;> linarith)
  rw [h0] at hz
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (z, 0) a) (isCompact_closedBall (z, 0) a)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicFlowField Γ)
    (s := fun _ => closedBall (z, 0) a) (fun _ _ => hK)
    (by constructor <;> linarith) hc
    (fun t ht => (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hm t (Ioo_subset_Icc_self ht)) continuousOn_const
    (fun t _ => by simpa [geodesicFlowField] using hasDerivAt_const t (z, (0 : E)))
    (fun _ _ => hz) h0

/-- At zero velocity the linearized field sends `(u,w)` to `(w,0)`. -/
theorem linearized_zero_velocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z) (p : E × E) :
    linearizedGeodesicFlowOperator Γ (z, 0) p = (p.2, 0) := by
  rw [linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator hΓ]
  simp [coordinateJacobiAcceleration]

/-- The entire fundamental solution at zero velocity is free motion. -/
theorem fundamentalSolution_zero_velocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : DifferentiableAt ℝ Γ z)
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)} {T : ℝ} (hT : 0 < T)
    (h0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hd : ∀ t ∈ Icc (-T) T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator Γ (z, 0)).comp (Φ t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, Φ t = freeVariation t := by
  intro t ht
  apply ContinuousLinearMap.ext
  intro p
  let A := linearizedGeodesicFlowOperator Γ (z, 0)
  have hlin : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun u => Φ u p)
      (A (Φ s p)) (Icc (-T) T) s := by
    intro s hs
    simpa [A] using (hd s hs).clm_apply (hasDerivWithinAt_const s (Icc (-T) T) p)
  have hexpl : ∀ s : ℝ, HasDerivAt (fun u => freeVariation u p)
      (A (freeVariation s p)) s := by
    intro s
    simpa [freeVariation, A, linearized_zero_velocity hΓ] using
      ((hasDerivAt_const s p.1).add ((hasDerivAt_id s).smul_const p.2)).prodMk
        (hasDerivAt_const s p.2)
  have heq := ODE_solution_unique_of_mem_Icc
    (v := fun _ => A) (s := fun _ => univ)
    (fun _ _ => A.lipschitz.lipschitzOnWith)
    (by constructor <;> linarith : (0 : ℝ) ∈ Ioo (-T) T)
    (HasDerivWithinAt.continuousOn hlin)
    (fun s hs => (hlin s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (fun _ _ => mem_univ _) (fun s _ => (hexpl s).continuousAt.continuousWithinAt)
    (fun s _ => hexpl s) (fun _ _ => mem_univ _)
    (by simp [h0, freeVariation])
  exact heq ht

/-- The endpoint derivative is invertible at every positive common time. -/
def endpointEquiv (T : ℝ) (hT : T ≠ 0) : (E × E) ≃L[ℝ] (E × E) where
  toLinearEquiv :=
    { toLinearMap := (endpointDerivative T).toLinearMap
      invFun := fun p => (p.1, T⁻¹ • (p.2 - p.1))
      left_inv := by
        intro p
        simp [endpointDerivative, smul_smul, hT]
      right_inv := by
        intro p
        simp [endpointDerivative, smul_smul, hT] }
  continuous_toFun := (endpointDerivative T).continuous
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub continuous_fst).const_smul T⁻¹)


/-- A joint inverse gives uniform fiber injectivity and target-ball coverage.
The preimage velocities can be required to lie in any prescribed ball of
positive radius `R`. The partial homeomorphism's source stays in `D`. -/
theorem uniform_normal_radius_near_of_strict [CompleteSpace E]
    {α : (E × E) → ℝ → E × E} {T : ℝ} {z₀ : E} {D : Set (E × E)}
    (hT : 0 < T) (hD : IsOpen D) (hz₀ : (z₀, (0 : E)) ∈ D)
    (hzero : expChart α T z₀ 0 = z₀)
    (hd : HasStrictFDerivAt (F α T) (endpointDerivative T) (z₀, 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      (e : (E × E) → E × E) = F α T ∧
      (z₀, (0 : E)) ∈ e.source ∧ e.source ⊆ D ∧
      e.source ⊆ univ ×ˢ ball (0 : E) R ∧
      ball z₀ ρ ×ˢ ball (0 : E) ρ ⊆ e.source ∧
      ∀ z ∈ ball z₀ ρ,
        InjOn (expChart α T z) (ball (0 : E) ρ) ∧
        ball z ρ ⊆ expChart α T z '' ball (0 : E) R := by
  let hd' : HasStrictFDerivAt (F α T) (endpointEquiv (E := E) T hT.ne').toContinuousLinearMap
      (z₀, 0) := by
    convert hd using 1
  let e₀ := hd'.toOpenPartialHomeomorph (F α T)
  let e := e₀.restrOpen (D ∩ (univ ×ˢ ball (0 : E) R))
    (hD.inter (isOpen_univ.prod isOpen_ball))
  have he : (e : (E × E) → E × E) = F α T := rfl
  have hm : (z₀, (0 : E)) ∈ e.source :=
    ⟨hd'.mem_toOpenPartialHomeomorph_source, hz₀, mem_univ _, mem_ball_self hR⟩
  have hsource : e.source ⊆ D ∩ (univ ×ˢ ball (0 : E) R) := fun _ hp => hp.2
  have htarget : (z₀, z₀) ∈ e.target := by
    simpa [he, F, hzero] using e.map_source hm
  obtain ⟨a, ha, has⟩ := Metric.isOpen_iff.mp e.open_source _ hm
  obtain ⟨b, hb, hbt⟩ := Metric.isOpen_iff.mp e.open_target _ htarget
  let ρ := min a (b / 2)
  have hρ : 0 < ρ := lt_min ha (half_pos hb)
  have hρa : ρ ≤ a := min_le_left _ _
  have hρb : ρ ≤ b / 2 := min_le_right _ _
  have hs : ball z₀ ρ ×ˢ ball (0 : E) ρ ⊆ e.source := by
    rw [ball_prod_same]
    exact (ball_subset_ball hρa).trans has
  refine ⟨ρ, hρ, e, he, hm, fun p hp => (hsource hp).1,
    fun p hp => (hsource hp).2, hs, ?_⟩
  intro z hz
  constructor
  · intro v hv w hw hvw
    have heq : e (z, v) = e (z, w) := by simp [he, F, hvw]
    exact congrArg Prod.snd (e.injOn (hs ⟨hz, hv⟩) (hs ⟨hz, hw⟩) heq)
  · intro y hy
    have hz' : dist z z₀ < b := (mem_ball.mp hz).trans_le (by linarith)
    have hy' : dist y z₀ < b := lt_of_le_of_lt (dist_triangle y z z₀)
      (by have := mem_ball.mp hy; have := mem_ball.mp hz; linarith)
    have ht : (z, y) ∈ e.target := hbt (by simp [mem_ball, Prod.dist_eq, hz', hy'])
    have hp := e.map_target ht
    have hi : F α T (e.symm (z, y)) = (z, y) := by
      rw [← he]
      exact e.right_inv ht
    have hfirst : (e.symm (z, y)).1 = z := congrArg Prod.fst hi
    refine ⟨(e.symm (z, y)).2, (hsource hp).2.2, ?_⟩
    have hsecond := congrArg Prod.snd hi
    simpa only [F, hfirst] using hsecond

/-- A finite subcover makes the injectivity and coverage radius uniform on
any compact set of anchors. The velocity bound `R` remains prescribed. -/
theorem exists_uniform_normal_radius_on_compact_of_strict [CompleteSpace E]
    {α : (E × E) → ℝ → E × E} {T : ℝ} {D : Set (E × E)} {K : Set E}
    (hT : 0 < T) (hD : IsOpen D) (hK : IsCompact K)
    (hKD : ∀ z ∈ K, (z, (0 : E)) ∈ D)
    (hzero : ∀ z ∈ K, expChart α T z 0 = z)
    (hd : ∀ z ∈ K, HasStrictFDerivAt (F α T) (endpointDerivative T) (z, 0))
    {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ∀ z ∈ K,
      InjOn (expChart α T z) (ball (0 : E) ρ) ∧
      ball z ρ ⊆ expChart α T z '' ball (0 : E) R := by
  classical
  have hlocal : ∀ x : K, ∃ ρ > (0 : ℝ), ∀ z ∈ ball x.1 ρ,
      InjOn (expChart α T z) (ball (0 : E) ρ) ∧
      ball z ρ ⊆ expChart α T z '' ball (0 : E) R := by
    intro x
    obtain ⟨ρ, hρ, e, he, hm, hsub, hv, hs, h⟩ :=
      uniform_normal_radius_near_of_strict hT hD (hKD x x.2)
        (hzero x x.2) (hd x x.2) hR
    exact ⟨ρ, hρ, h⟩
  choose rad hrad hlocal using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.1 (rad x))
    (fun _ => isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hrad ⟨z, hz⟩)⟩)
  have hmin : ∀ s : Finset K, ∃ ρ > (0 : ℝ), ∀ x ∈ s, ρ ≤ rad x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨ρ, hρ, hρs⟩ := ih
      refine ⟨min (rad x) ρ, lt_min (hrad x) hρ, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hρs y hy)
  obtain ⟨ρ, hρ, hρs⟩ := hmin s
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hs hz)
  exact ⟨(hlocal x z hzx).1.mono (ball_subset_ball (hρs x hx)),
    (ball_subset_ball (hρs x hx)).trans (hlocal x z hzx).2⟩

section Flow

variable [FiniteDimensional ℝ E]
variable {Γ : E → E →L[ℝ] E →L[ℝ] E}
variable {α : (E × E) → ℝ → E × E}
variable {Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E)}
variable {c z : E} {r T : ℝ}
variable (hΓ : ContDiff ℝ 1 Γ) (hT : 0 < T)
variable (hα : ∀ q ∈ ball (c, (0 : E)) r, α q 0 = q ∧
  ∀ t ∈ Icc (-T) T, HasDerivWithinAt (α q)
    (geodesicFlowField Γ (α q t)) (Icc (-T) T) t)
variable (hΦ0 : ∀ q ∈ ball (c, (0 : E)) r, Φ q 0 = ContinuousLinearMap.id ℝ _)
variable (hΦ : ∀ q ∈ ball (c, (0 : E)) r, ∀ t ∈ Icc (-T) T,
  HasDerivWithinAt (Φ q)
    ((linearizedGeodesicFlowOperator Γ (α q t)).comp (Φ q t)) (Icc (-T) T) t)
variable (hf : ∀ q ∈ ball (c, (0 : E)) r,
  HasFDerivAt (fun y => α y T) (Φ q T) q)

include hΓ hT hα hΦ0 hΦ

/-- The supplied joint flow has the explicit zero-velocity fundamental solution. -/
theorem flow_fundamentalSolution_zero_velocity (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    ∀ t ∈ Icc (-T) T, Φ (z, 0) t = freeVariation t := by
  have hs := flow_zero_velocity (contDiff_geodesicFlowField hΓ) hT
    (hα (z, 0) hz).1 (hα (z, 0) hz).2
  apply fundamentalSolution_zero_velocity (hΓ.differentiable one_ne_zero z) hT (hΦ0 _ hz)
  intro t ht
  simpa only [hs t ht] using hΦ (z, 0) hz t ht

include hf

/-- The full anchor/endpoint derivative is the triangular isomorphism. -/
theorem hasFDerivAt_F_at_zero_velocity (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    HasFDerivAt (F α T) (endpointDerivative T) (z, 0) := by
  have heq := flow_fundamentalSolution_zero_velocity hΓ hT hα hΦ0 hΦ hz T
    (by constructor <;> linarith)
  have hd := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.prodMk (hf (z, 0) hz).fst
  rw [heq] at hd
  convert hd using 1

/-- Joint C1 regularity upgrades this derivative to a strict derivative. -/
theorem hasStrictFDerivAt_F
    (hC1 : ContDiffOn ℝ 1 (fun q => α q T) (ball (c, (0 : E)) r))
    (hz : (z, (0 : E)) ∈ ball (c, 0) r) :
    HasStrictFDerivAt (F α T) (endpointDerivative T) (z, 0) := by
  have hc := hC1.contDiffAt (isOpen_ball.mem_nhds hz)
  exact (contDiffAt_fst.prodMk hc.fst).hasStrictFDerivAt'
    (hasFDerivAt_F_at_zero_velocity hΓ hT hα hΦ0 hΦ hf hz) one_ne_zero

/-- Uniform normal neighborhoods for the supplied concrete geodesic flow.
The open partial homeomorphism stays in the original state ball. -/
theorem uniform_normal_radius_near
    (hC1 : ContDiffOn ℝ 1 (fun q => α q T) (ball (c, (0 : E)) r))
    (hz : (z, (0 : E)) ∈ ball (c, 0) r) {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      (e : (E × E) → E × E) = F α T ∧
      (z, (0 : E)) ∈ e.source ∧ e.source ⊆ ball (c, (0 : E)) r ∧
      e.source ⊆ univ ×ˢ ball (0 : E) R ∧
      ball z ρ ×ˢ ball (0 : E) ρ ⊆ e.source ∧
      ∀ y ∈ ball z ρ,
        InjOn (expChart α T y) (ball (0 : E) ρ) ∧
        ball y ρ ⊆ expChart α T y '' ball (0 : E) R := by
  apply uniform_normal_radius_near_of_strict hT isOpen_ball hz ?_
    (hasStrictFDerivAt_F hΓ hT hα hΦ0 hΦ hf hC1 hz) hR
  exact congrArg Prod.fst (flow_zero_velocity (contDiff_geodesicFlowField hΓ) hT
    (hα (z, 0) hz).1 (hα (z, 0) hz).2 T (by constructor <;> linarith))

/-- Every compact anchor set in the fixed chart state ball has one positive
normal radius. Coverage holds within any prescribed positive velocity bound. -/
theorem exists_uniform_normal_radius_on_compact
    (hC1 : ContDiffOn ℝ 1 (fun q => α q T) (ball (c, (0 : E)) r))
    {K : Set E} (hK : IsCompact K) (hKr : K ⊆ ball c r)
    {R : ℝ} (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ∀ z ∈ K,
      InjOn (expChart α T z) (ball (0 : E) ρ) ∧
      ball z ρ ⊆ expChart α T z '' ball (0 : E) R := by
  have hm : ∀ z ∈ K, (z, (0 : E)) ∈ ball (c, 0) r := by
    intro z hz
    simpa using hKr hz
  apply exists_uniform_normal_radius_on_compact_of_strict hT isOpen_ball hK hm ?_ ?_ hR
  · intro z hz
    exact congrArg Prod.fst (flow_zero_velocity (contDiff_geodesicFlowField hΓ) hT
      (hα (z, 0) (hm z hz)).1 (hα (z, 0) (hm z hz)).2 T
      (by constructor <;> linarith))
  · intro z hz
    exact hasStrictFDerivAt_F hΓ hT hα hΦ0 hΦ hf hC1 (hm z hz)

end Flow

end Poincare.FixedChartUniformNormalRadius
