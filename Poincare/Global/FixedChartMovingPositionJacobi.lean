import Poincare.Global.FixedChartUniformJacobiComparison

/-!
# Metric invariants along retained moving-position geodesics

The initial state ranges over the original patch ball. Time is never shrunk.
-/

noncomputable section
set_option maxHeartbeats 1200000
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartMovingPositionJacobi
open GeodesicTransport
open FixedChartUniformJacobiComparison

/-- Every retained position lies in the chart target and has cutoff one on a
neighborhood, including at both endpoint times. -/
theorem flow_mem_target_cutoffOne {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (C.α q t).1 ∈ (extChartAt I x₀).target ∧
      (∀ᶠ z in 𝓝 (C.α q t).1, cutoff (n := 3) x₀ z = 1) := by
  have hcut := hU (C.position_mem q hq t ht)
  refine ⟨?_, hcut⟩
  exact cutoff_tsupport x₀ (subset_tsupport _
    (Function.mem_support.mpr (by rw [hcut.self_of_nhds]; exact one_ne_zero)))

/-- Speed preservation on the entire retained interval, at arbitrary initial
position and velocity in the original closed state ball. -/
theorem flow_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      chartGeodesicMetric g x₀ q.1 q.2 q.2 := by
  have hder := (C.flow_law q hq).2
  have hcont := HasDerivWithinAt.continuousOn hder
  have hmetric : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have heq : EqOn
      (fun t => chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2)
      (fun _ => chartGeodesicMetric g x₀ q.1 q.2 q.2) (Ioo (-C.T) C.T) := by
    intro s hs
    have h := chart_geodesic_speed_constantOn_Ioo g x₀
      (fun τ hτ => (hder τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)) hs
      (show (0 : ℝ) ∈ Ioo (-C.T) C.T from ⟨by linarith [C.T_pos], C.T_pos⟩)
    simpa only [(C.flow_law q hq).1] using h
  exact heq.of_subset_closure
    (((hmetric.comp_continuousOn hcont.fst).clm_apply hcont.snd).clm_apply hcont.snd)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show -C.T ≠ C.T by linarith [C.T_pos])]) ht

/-- On a cutoff-one patch the same invariant is the actual chart metric,
measured at the moving initial position. -/
theorem flow_chartMetric_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    CovariantDerivative.chartMetric g.inner x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      CovariantDerivative.chartMetric g.inner x₀ q.1 q.2 q.2 := by
  have h0 : (0 : ℝ) ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos.le⟩
  have hc0 := (flow_mem_target_cutoffOne C hU hq h0).2.self_of_nhds
  rw [(C.flow_law q hq).1] at hc0
  have h := flow_speed_eq_initial C hq ht
  dsimp only [chartGeodesicMetric] at h
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) (flow_mem_target_cutoffOne C hU hq ht).2.self_of_nhds,
    blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hc0] at h
  exact h

/-- Nearby initial-velocity variations preserve speed with their own moving
initial velocity. This is the eventual equality required by the Gauss lemma. -/
theorem perturbed_flow_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    (w : E) {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (fun s : ℝ => chartGeodesicMetric g x₀ (C.α (z, v + s • w) t).1
      (C.α (z, v + s • w) t).2 (C.α (z, v + s • w) t).2) =ᶠ[𝓝 0]
    (fun s : ℝ => chartGeodesicMetric g x₀ z (v + s • w) (v + s • w)) := by
  have hc : ContinuousAt (fun s : ℝ => (z, v + s • w)) 0 :=
    continuousAt_const.prodMk (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
  have he : ∀ᶠ s : ℝ in 𝓝 0,
      (z, v + s • w) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) :=
    hc.eventually (isOpen_ball.mem_nhds (by simpa using hq))
  filter_upwards [he] with s hs
  exact flow_speed_eq_initial C (ball_subset_closedBall hs) ht

/-- The arbitrary fundamental solution differentiates an actual velocity
variation of the retained flow at every retained time. -/
theorem velocityVariation_hasDerivAt {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    HasDerivAt (fun s : ℝ => C.α (z, v + s • w) t) (Φ t (0, w)) 0 := by
  have hs : HasDerivAt (fun s : ℝ => (z, v + s • w)) (0, w) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) z).prodMk
      ((hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const w))
  have hf := flow_hasFDerivAt_of_fundamentalSolution C hq hΦ0 hΦ ht
  have hf' : HasFDerivAt (fun y => C.α y t) (Φ t) (z, v + (0 : ℝ) • w) := by
    simpa only [zero_smul, add_zero] using hf
  exact hf'.comp_hasDerivAt 0 hs

/-- Initial transverse vectors remain orthogonal to the velocity through the
closed endpoints. All flow-variation and speed premises are discharged. -/
theorem transverse_orthogonal {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) (horth : CovariantDerivative.chartMetric g.inner x₀ z v w = 0)
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    CovariantDerivative.chartMetric g.inner x₀ (C.α (z, v) t).1
      (Φ t (0, w)).1 (C.α (z, v) t).2 = 0 := by
  have hqc := ball_subset_closedBall hq
  have h0 : (0 : ℝ) ∈ Ioo (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos⟩
  have hc0 := (flow_mem_target_cutoffOne C hU hqc (Ioo_subset_Icc_self h0)).2.self_of_nhds
  rw [(C.flow_law _ hqc).1] at hc0
  have horth' : chartGeodesicMetric g x₀ z v w = 0 := by
    dsimp only [chartGeodesicMetric]
    rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hc0]
    exact horth
  have hΨ : ∀ s ∈ Icc (-C.T) C.T, HasDerivWithinAt (fun s => Φ s (0, w))
      (linearizedGeodesicFlowFieldAlong (chartChristoffelField g x₀)
        (C.α (z, v)) s (Φ s (0, w))) (Icc (-C.T) C.T) s := by
    intro s hs
    simpa using (hΦ s hs).clm_apply (hasDerivWithinAt_const s (Icc (-C.T) C.T) (0, w))
  have heq : EqOn
      (fun s => chartGeodesicMetric g x₀ (C.α (z, v) s).1
        (Φ s (0, w)).1 (C.α (z, v) s).2) (fun _ => 0) (Ioo (-C.T) C.T) := by
    intro s hs
    exact chart_initialVelocity_integrated_transverse_gauss_orthogonal g x₀
      (α := C.α) (z₀ := z) (v := v) (w := w) (Ψ := fun τ => Φ τ (0, w))
      (a := -C.T) (b := C.T) (t := s)
      (fun τ hτ => ((C.flow_law _ hqc).2 τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2))
      (fun τ hτ => (hΨ τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2))
      (fun τ hτ => velocityVariation_hasDerivAt C hq hΦ0 hΦ w (Ioo_subset_Icc_self hτ))
      (fun τ hτ => perturbed_flow_speed_eq_initial C hq w (Ioo_subset_Icc_self hτ))
      (fun τ _ => IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ _)
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z)
      (C.flow_law _ hqc).1 (by simp [hΦ0]) h0 horth' hs
  have hc := HasDerivWithinAt.continuousOn (C.flow_law _ hqc).2
  have hm : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have hall := heq.of_subset_closure
    (((hm.comp_continuousOn hc.fst).clm_apply
      (HasDerivWithinAt.continuousOn hΨ).fst).clm_apply hc.snd)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show -C.T ≠ C.T by linarith [C.T_pos])]) ht
  dsimp only [chartGeodesicMetric] at hall
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀)
    (flow_mem_target_cutoffOne C hU hqc ht).2.self_of_nhds] at hall
  exact hall

/-- For initial data `(0,w)` orthogonal to the moving initial velocity,
the corrected norm triple satisfies `(A',B',C') = (2B,C-s²A,-2s²B)`.
Only initial speed and initial orthogonality are assumptions. -/
theorem transverse_normSystem [T2Space M] {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) (horth : CovariantDerivative.chartMetric g.inner x₀ z v w = 0)
    {speed : ℝ} (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speed ^ 2)
    {t : ℝ} (ht : t ∈ Ioo (-C.T) C.T) :
    let N := GronwallMembership.normState g x₀ (C.α (z, v)) (fun s => Φ s (0, w))
    HasDerivAt N (2 * (N t).2.1, (N t).2.2 - speed ^ 2 * (N t).1,
      -2 * speed ^ 2 * (N t).2.1) t := by
  have hqc := ball_subset_closedBall hq
  have htc := Ioo_subset_Icc_self ht
  have hzone := flow_mem_target_cutoffOne C hU hqc htc
  have hΨ : HasDerivAt (fun s => Φ s (0, w))
      (linearizedGeodesicFlowFieldAlong (chartChristoffelField g x₀)
        (C.α (z, v)) t (Φ t (0, w))) t := by
    simpa using ((hΦ t htc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).clm_apply
      (hasDerivAt_const t (0, w))
  simpa only [RigidityComplete.speedNormSystemAop_apply] using
    GronwallMembership.normState_hasDerivAt_speed g hcurv x₀
      (RigidityComplete.speedNormSystemAop speed) (RigidityComplete.speedNormSystemAop_apply speed)
      (((C.flow_law _ hqc).2 t htc).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      hΨ hzone.1 hzone.2 ((flow_chartMetric_speed_eq_initial C hU hqc htc).trans hspeed)
      (transverse_orthogonal C hU hq hΦ0 hΦ w horth htc)
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ _)

/-- The scalar norm system has its sine/cosine solution on any prescribed
finite interval. No Picard radius or short-time bound is needed. -/
theorem normSystem_eq_pinned {T speed q : ℝ} (hT : 0 < T) (hs : speed ≠ 0)
    {N : ℝ → ℝ × ℝ × ℝ} (hc : ContinuousOn N (Icc (-T) T))
    (hd : ∀ t ∈ Ioo (-T) T, HasDerivAt N
      (2 * (N t).2.1, (N t).2.2 - speed ^ 2 * (N t).1,
        -2 * speed ^ 2 * (N t).2.1) t)
    (h0 : N 0 = (0, 0, q)) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    N t = (JacobiNormSystem.speedPinnedA speed q t,
      JacobiNormSystem.speedPinnedB speed q t,
      JacobiNormSystem.speedPinnedC speed q t) := by
  let A := RigidityComplete.speedNormSystemAop speed
  let P : ℝ → ℝ × ℝ × ℝ := fun t =>
    (JacobiNormSystem.speedPinnedA speed q t,
      JacobiNormSystem.speedPinnedB speed q t,
      JacobiNormSystem.speedPinnedC speed q t)
  have hP : ∀ t, HasDerivAt P (A (P t)) t := by
    intro t
    simpa only [A, P, RigidityComplete.speedNormSystemAop_apply] using
      (JacobiNormSystem.speedPinnedA_hasDerivAt hs q t).prodMk
        ((JacobiNormSystem.speedPinnedB_hasDerivAt hs q t).prodMk
          (JacobiNormSystem.speedPinnedC_hasDerivAt hs q t))
  exact ODE_solution_unique_of_mem_Icc
    (v := fun _ => A) (s := fun _ => univ)
    (fun _ _ => A.lipschitz.lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-T) T by constructor <;> linarith)
    hc (fun t ht => by simpa only [A, RigidityComplete.speedNormSystemAop_apply] using hd t ht)
    (fun _ _ => mem_univ _) (fun t _ => (hP t).continuousAt.continuousWithinAt)
    (fun t _ => hP t) (fun _ _ => mem_univ _)
    (by simpa only [P, JacobiNormSystem.speedPinnedA_zero,
      JacobiNormSystem.speedPinnedB_zero, JacobiNormSystem.speedPinnedC_zero] using h0) ht

/-- The actual transverse norm triple equals the sine/cosine solution through
both retained endpoints, with the moving anchor metric as initial norm. -/
theorem transverse_norms_eq_pinned [T2Space M] {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) (horth : CovariantDerivative.chartMetric g.inner x₀ z v w = 0)
    {speed : ℝ} (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speed ^ 2)
    (hs : speed ≠ 0) {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    let q := CovariantDerivative.chartMetric g.inner x₀ z w w
    GronwallMembership.normState g x₀ (C.α (z, v)) (fun s => Φ s (0, w)) t =
      (JacobiNormSystem.speedPinnedA speed q t,
        JacobiNormSystem.speedPinnedB speed q t,
        JacobiNormSystem.speedPinnedC speed q t) := by
  have hqc := ball_subset_closedBall hq
  have hc := HasDerivWithinAt.continuousOn (C.flow_law _ hqc).2
  have hJ := (HasDerivWithinAt.continuousOn hΦ).clm_apply
    (continuousOn_const : ContinuousOn (fun _ : ℝ => ((0 : E), w)) (Icc (-C.T) C.T))
  have hm : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have hΓ := (chartChristoffelField_contDiff g x₀).continuous.comp_continuousOn hc.fst
  have hD := hJ.snd.add ((hΓ.clm_apply hc.snd).clm_apply hJ.fst)
  have hG := hm.comp_continuousOn hc.fst
  have hN : ContinuousOn
      (GronwallMembership.normState g x₀ (C.α (z, v)) (fun s => Φ s (0, w)))
      (Icc (-C.T) C.T) :=
    ((hG.clm_apply hJ.fst).clm_apply hJ.fst).prodMk
      (((hG.clm_apply hJ.fst).clm_apply hD).prodMk ((hG.clm_apply hD).clm_apply hD))
  have hz : (0 : ℝ) ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos.le⟩
  have hcut := (flow_mem_target_cutoffOne C hU hqc hz).2.self_of_nhds
  rw [(C.flow_law _ hqc).1] at hcut
  apply normSystem_eq_pinned C.T_pos hs hN
    (fun s hs => transverse_normSystem C hcurv hU hq hΦ0 hΦ w horth hspeed hs) ?_ ht
  simp only [GronwallMembership.normState, GronwallMembership.correctedD,
    JacobiNormSystem.normA, JacobiNormSystem.normB, JacobiNormSystem.normC,
    hΦ0, ContinuousLinearMap.id_apply, (C.flow_law _ hqc).1, map_zero, add_zero,
    ContinuousLinearMap.zero_apply]
  dsimp only [chartGeodesicMetric]
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hcut]

/-- Differentiating the time-dilation state produces a radial Jacobi solution
at any interior time, independently of the initial position. -/
theorem radial_state_hasDerivAt {x₀ : M} {γ : ℝ → E × E} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicFlowField (chartChristoffelField g x₀) (γ t)) t) :
    let Γ := chartChristoffelField g x₀
    let A := fun s => -(Γ (γ s).1 (γ s).2 (γ s).2)
    let R := fun s => (s • (γ s).2, (γ s).2 + s • A s)
    HasDerivAt R (linearizedGeodesicFlowOperator Γ (γ t) (R t)) t := by
  dsimp only
  let Γ := chartChristoffelField g x₀
  let V := fun s => (γ s).2
  let A := fun s => -(Γ (γ s).1 (V s) (V s))
  have hz := geodesic_position_hasDerivAt hγ
  have hv : HasDerivAt V (A t) t := geodesic_velocity_hasDerivAt hγ
  have hΓd := (chartChristoffelField_contDiff g x₀).differentiable (by norm_num) (γ t).1
  have hΓ := hΓd.hasFDerivAt.comp_hasDerivAt t hz
  have hA : HasDerivAt A
      (-(((fderiv ℝ Γ (γ t).1) (V t)) (V t) (V t) +
        Γ (γ t).1 (A t) (V t) + Γ (γ t).1 (V t) (A t))) t := by
    simpa only [Γ, A, V, ContinuousLinearMap.add_apply] using
      ((hΓ.clm_apply hv).clm_apply hv).neg
  have hR := ((hasDerivAt_id t).smul hv).prodMk
    (hv.add ((hasDerivAt_id t).smul hA))
  rw [linearizedGeodesicFlowOperator_eq_coordinateJacobiFlowOperator hΓd]
  convert hR using 1
  simp only [coordinateJacobiFlowOperator_apply, coordinateJacobiAcceleration,
      map_smul, map_add, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      one_smul, Γ, A, V, id_eq]
  congr 1 <;> module

/-- The radial position variation is time times the transported velocity,
on the full retained interval and at arbitrary moving initial position. -/
theorem radial_position_eq_time_smul_velocity {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α q t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (Φ t (0, q.2)).1 = t • (C.α q t).2 := by
  let Γ := chartChristoffelField g x₀
  let A := fun s => linearizedGeodesicFlowOperator Γ (C.α q s)
  let V := fun s => (C.α q s).2
  let R := fun s => (s • V s, V s + s • (-(Γ (C.α q s).1 (V s) (V s))))
  have hc := HasDerivWithinAt.continuousOn (C.flow_law _ hq).2
  have hΓ := (chartChristoffelField_contDiff g x₀).continuous.comp_continuousOn hc.fst
  have hRc : ContinuousOn R (Icc (-C.T) C.T) :=
    (continuousOn_id.smul hc.snd).prodMk (hc.snd.add
      (continuousOn_id.smul (((hΓ.clm_apply hc.snd).clm_apply hc.snd).neg)))
  have hRd : ∀ s ∈ Ioo (-C.T) C.T, HasDerivAt R (A s (R s)) s := by
    intro s hs
    exact radial_state_hasDerivAt
      (((C.flow_law _ hq).2 s (Ioo_subset_Icc_self hs)).hasDerivAt
        (Icc_mem_nhds hs.1 hs.2))
  have hlin : ∀ s ∈ Icc (-C.T) C.T, HasDerivWithinAt (fun s => Φ s (0, q.2))
      (A s (Φ s (0, q.2))) (Icc (-C.T) C.T) s := by
    intro s hs
    simpa [A] using (hΦ s hs).clm_apply
      (hasDerivWithinAt_const s (Icc (-C.T) C.T) (0, q.2))
  have hF := geodesicFlowField_chartChristoffelField_contDiff_two g x₀
  have hAc : ContinuousOn A (Icc (-C.T) C.T) :=
    ((hF.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuous_fderiv one_ne_zero).comp_continuousOn hc
  obtain ⟨k, hk⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  let K : ℝ≥0 := ⟨max k 0, le_max_right _ _⟩
  have hK : ∀ s ∈ Ioo (-C.T) C.T, ‖A s‖₊ ≤ K := by
    intro s hs
    exact_mod_cast (hk s (Ioo_subset_Icc_self hs)).trans (le_max_left k 0)
  have heq := ODE_solution_unique_of_mem_Icc
    (v := fun t => A t) (s := fun _ => univ)
    (fun s hs => ((A s).lipschitz.weaken (hK s hs)).lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-C.T) C.T by constructor <;> linarith [C.T_pos])
    (HasDerivWithinAt.continuousOn hlin)
    (fun s hs => (hlin s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2))
    (fun _ _ => mem_univ _) hRc hRd (fun _ _ => mem_univ _)
    (by simp [hΦ0, R, V, (C.flow_law _ hq).1])
  exact congrArg Prod.fst (heq ht)

/-- Radial isometry and transverse norm scaling determine every pairing.
This algebra uses the same anchor bilinear form for both components. -/
theorem pairing_of_radial_transverse
    (B G : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E) (v : E) (κ : ℝ)
    (hB : ∀ a b, B a b = B b a) (hG : ∀ a b, G a b = G b a)
    (hv : B v v ≠ 0) (hr : G (J v) (J v) = B v v)
    (ho : ∀ w, B v w = 0 → G (J w) (J v) = 0)
    (hn : ∀ w, B v w = 0 → G (J w) (J w) = κ * B w w) (a b : E) :
    G (J a) (J b) = κ * B a b + (1 - κ) * (B a v * B b v / B v v) := by
  have hd : ∀ a, G (J a) (J a) =
      κ * B a a + (1 - κ) * (B a v * B a v / B v v) := by
    intro a
    let c := B a v / B v v
    let w := a - c • v
    have hw : B v w = 0 := by
      simp only [w, map_sub, map_smul, smul_eq_mul]
      rw [hB v a]
      dsimp [c]
      field_simp
      ring
    have how := ho w hw
    have how' : G (J v) (J w) = 0 := (hG _ _).trans how
    have hnw := hn w hw
    have he : a = c • v + w := by dsimp [w]; module
    have hj : J a = c • J v + J w := by rw [he, map_add, map_smul]
    rw [hj]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, hr, how, how', mul_zero, add_zero, zero_add]
    rw [hnw]
    simp only [w, map_sub, map_smul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hB v a]
    dsimp [c]
    field_simp
    ring
  have h := hd (a + b)
  simp only [map_add, ContinuousLinearMap.add_apply] at h
  rw [hG (J b) (J a), hB b a, hd a, hd b] at h
  field_simp at h ⊢
  nlinarith

/-- Time normalization cancels the patch time from the radial term and from
the transverse sine factor. The formula uses only the moving anchor metric. -/
theorem normalized_pairing_formula [T2Space M] {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {z v : E} (hq : (z, C.T⁻¹ • v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, C.T⁻¹ • v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    {speed : ℝ} (hspeed : CovariantDerivative.chartMetric g.inner x₀ z v v = speed ^ 2)
    (hs : speed ≠ 0) (a b : E) :
    let B := CovariantDerivative.chartMetric g.inner x₀ z
    let κ := Real.sin speed ^ 2 / speed ^ 2
    CovariantDerivative.chartMetric g.inner x₀ (C.α (z, C.T⁻¹ • v) C.T).1
      (Φ C.T (0, C.T⁻¹ • a)).1 (Φ C.T (0, C.T⁻¹ • b)).1 =
      κ * B a b + (1 - κ) * (B a v * B b v / B v v) := by
  let B := CovariantDerivative.chartMetric g.inner x₀ z
  let G := CovariantDerivative.chartMetric g.inner x₀ (C.α (z, C.T⁻¹ • v) C.T).1
  let J : E →L[ℝ] E := ((ContinuousLinearMap.fst ℝ E E).comp (Φ C.T)).comp
    ((0 : E →L[ℝ] E).prod (C.timeRescaling : E →L[ℝ] E))
  have hJ : ∀ a, J a = (Φ C.T (0, C.T⁻¹ • a)).1 := fun _ => rfl
  have hT := C.T_pos.ne'
  have hqc := ball_subset_closedBall hq
  have ht : C.T ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], le_rfl⟩
  have hraw : B (C.T⁻¹ • v) (C.T⁻¹ • v) = (speed / C.T) ^ 2 := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change C.T⁻¹ * (C.T⁻¹ * (CovariantDerivative.chartMetric g.inner x₀ z v v)) = _
    rw [hspeed]
    field_simp
  have hrad : J v = C.T • (C.α (z, C.T⁻¹ • v) C.T).2 :=
    radial_position_eq_time_smul_velocity C hqc hΦ0 hΦ ht
  have hr : G (J v) (J v) = B v v := by
    rw [hrad]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hv := flow_chartMetric_speed_eq_initial C hU hqc ht
    change G _ _ = B _ _ at hv
    rw [hv, hraw]
    change _ = CovariantDerivative.chartMetric g.inner x₀ z v v
    rw [hspeed]
    field_simp
  have ho : ∀ w, B v w = 0 → G (J w) (J v) = 0 := by
    intro w hw
    have horth : B (C.T⁻¹ • v) (C.T⁻¹ • w) = 0 := by simp [hw]
    have h := transverse_orthogonal C hU hq hΦ0 hΦ (C.T⁻¹ • w) horth ht
    rw [hrad]
    simpa only [map_smul, smul_eq_mul, hJ w, mul_zero] using congrArg (C.T * ·) h
  have hn : ∀ w, B v w = 0 → G (J w) (J w) =
      (Real.sin speed ^ 2 / speed ^ 2) * B w w := by
    intro w hw
    have horth : B (C.T⁻¹ • v) (C.T⁻¹ • w) = 0 := by simp [hw]
    have hN := transverse_norms_eq_pinned C hcurv hU hq hΦ0 hΦ
      (C.T⁻¹ • w) horth hraw (div_ne_zero hs hT) ht
    have h := congrArg Prod.fst hN
    dsimp only [GronwallMembership.normState, JacobiNormSystem.normA, chartGeodesicMetric] at h
    rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀)
      (flow_mem_target_cutoffOne C hU hqc ht).2.self_of_nhds] at h
    change G (J w) (J w) = JacobiNormSystem.speedPinnedA (speed / C.T)
      (B (C.T⁻¹ • w) (C.T⁻¹ • w)) C.T at h
    rw [h]
    simp only [JacobiNormSystem.speedPinnedA, JacobiNormSystem.speedPinnedScale,
      div_mul_cancel₀ speed hT, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  exact pairing_of_radial_transverse B G J v _
    (CovariantDerivative.chartMetric_symm g.inner g.inner_symm x₀ z)
    (CovariantDerivative.chartMetric_symm g.inner g.inner_symm x₀ _)
    (by change CovariantDerivative.chartMetric g.inner x₀ z v v ≠ 0; rw [hspeed]; exact pow_ne_zero 2 hs)
    hr ho hn a b

/-- At zero velocity the retained flow is stationary and every normalized
position variation is exactly its input vector. -/
theorem normalized_zero_velocity {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {z : E} (hq : (z, (0 : E)) ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, 0) t)).comp (Φ t)) (Icc (-C.T) C.T) t) :
    C.α (z, 0) C.T = (z, 0) ∧ ∀ a : E, (Φ C.T (0, C.T⁻¹ • a)).1 = a := by
  have hγ := FixedChartUniformNormalRadius.flow_zero_velocity
    (contDiff_geodesicFlowField (chartChristoffelField_contDiff g x₀))
    C.T_pos (C.flow_law _ hq).1 (C.flow_law _ hq).2
  have ht : C.T ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], le_rfl⟩
  have hF := FixedChartUniformNormalRadius.fundamentalSolution_zero_velocity
    ((chartChristoffelField_contDiff g x₀).differentiable (by norm_num) z)
    C.T_pos hΦ0 (fun t ht => by simpa only [hγ t ht] using hΦ t ht) C.T ht
  refine ⟨hγ C.T ht, fun a => ?_⟩
  rw [hF]
  simp [FixedChartUniformNormalRadius.freeVariation, smul_smul, C.T_pos.ne']

variable [T2Space M]
open CartanSuppliedDifferentialSuccessor FixedChartLocalSuccessorExistence
open FixedChartUniformDifferentialPullback

/-- Moving initial positions on the source and sphere have identical Jacobi
pairings under the fixed-chart tangent alignment, with independent patch times. -/
theorem movingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) :
    FixedChartUniformJacobiComparison.MovingInitialPositionJacobiComparison g := by
  intro x₀ p₀ U V C D hcurv hU hV x hx p hp L v
  dsimp only
  intro hvs hvt Φs Φt hs0 hsode ht0 htode a b
  let l := linear (patch C D) ⟨x, p, L⟩
  have hqs : (extChartAt I x₀ x, C.T⁻¹ • v) ∈
      ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := C.P_source_subset hvs.1.2
  have hqt : (extChartAt I p₀ p, D.T⁻¹ • l v) ∈
      ball (extChartAt I p₀ p₀, 0) (D.r : ℝ) := D.P_source_subset hvt.1.2
  have hl := linear_metric C D x hx p hp L
  by_cases hv : v = 0
  · subst v
    have hs := normalized_zero_velocity C
      (show (extChartAt I x₀ x, (0 : E)) ∈ closedBall _ (C.r : ℝ) by
        simpa using ball_subset_closedBall hqs) hs0 (by simpa using hsode)
    have ht := normalized_zero_velocity D
      (show (extChartAt I p₀ p, (0 : E)) ∈ closedBall _ (D.r : ℝ) by
        simpa only [map_zero, smul_zero] using ball_subset_closedBall hqt)
      ht0 (by simpa only [map_zero, smul_zero] using htode)
    simp only [map_zero, smul_zero, hs.1, ht.1, hs.2, ht.2]
    exact hl a b
  · let B := CovariantDerivative.chartMetric g.inner x₀ (extChartAt I x₀ x)
    have hzero : (0 : ℝ) ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos.le⟩
    have hcut := (flow_mem_target_cutoffOne C hU (ball_subset_closedBall hqs) hzero).2.self_of_nhds
    rw [(C.flow_law _ (ball_subset_closedBall hqs)).1] at hcut
    have hBpos : 0 < B v v := CovariantDerivative.chartMetric_posDef g.inner
      (fun y w hw => g.inner_pos y hw) x₀
      (cutoff_support_invertible x₀ _ (by rw [hcut]; exact one_ne_zero)) hv
    let speed := Real.sqrt (B v v)
    have hs : speed ≠ 0 := (Real.sqrt_pos.mpr hBpos).ne'
    have hspeed : B v v = speed ^ 2 := (Real.sq_sqrt hBpos.le).symm
    have hspeedt : CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        (extChartAt I p₀ p) (l v) (l v) = speed ^ 2 := (hl v v).trans hspeed
    have hsource := normalized_pairing_formula C hcurv hU hqs hs0 hsode hspeed hs a b
    have htarget := normalized_pairing_formula D
      roundSphereMetric3_hasConstantSectionalCurvature_one hV hqt ht0 htode hspeedt hs (l a) (l b)
    dsimp only at hsource htarget
    rw [hsource, htarget, hl a b, hl a v, hl b v, hl v v]

variable [CompactSpace M] [ConnectedSpace M]

/-- The moving-position comparison discharges the uniform nonzero metric
pullback obligation for the actual retained endpoint maps. -/
theorem uniformNonzeroMetricPullback (g : ClosedSmoothRiemannianMetric 3 M) :
    FixedChartUniformDifferentialPullback.UniformNonzeroMetricPullback g :=
  FixedChartUniformJacobiComparison.target_of_movingInitialPositionJacobiComparison
    (movingInitialPositionJacobiComparison g)

end FixedChartMovingPositionJacobi
end Poincare
