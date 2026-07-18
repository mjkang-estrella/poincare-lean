import Poincare.Global.QuadraticSemilinearHeatBUC
import Poincare.Global.SemilinearHeatBUCFixedPointRegularity

/-!
# Uniform local quadratic semilinear heat theory on bounded `BUC` data

For initial data in the norm ball `‖u₀‖ ≤ K`, this module chooses one positive
lifespan, independent of the individual datum.  On that common interval the
corrected quadratic Picard map preserves the unit ball about the homogeneous
heat orbit and is uniformly contractive.  The resulting locally unique mild
solutions depend Lipschitz-continuously on their initial data.

Only the bounded bilinear estimate for the quadratic nonlinearity is used; no
global Lipschitz hypothesis is imposed on `u ↦ B u u`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Uniform local Lipschitz constant for `u ↦ B u u` when the initial datum
has norm at most `K` and paths stay within `R` of its homogeneous heat orbit. -/
def quadraticBUCUniformBallLipschitzConstant
    (β K R : ℝ≥0) : ℝ≥0 :=
  2 * β * (K + R)

/-- Uniform quadratic bound on the same family of orbit balls. -/
def quadraticBUCUniformBallBound (β K R : ℝ≥0) : ℝ≥0 :=
  β * (K + R) ^ 2

/-- One lifespan for every initial datum in the closed norm ball of radius
`K`.  The solution is constructed in the unit ball about its heat orbit. -/
def quadraticBUCUniformLifespan (β K : ℝ≥0) : ℝ≥0 :=
  1 / (2 * (quadraticBUCUniformBallBound β K 1 +
    quadraticBUCUniformBallLipschitzConstant β K 1 + 1))

theorem quadraticBUCBallBound_le_uniform
    (β K R : ℝ≥0) (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ)) :
    quadraticBUCBallBound β u₀ R ≤
      quadraticBUCUniformBallBound β K R := by
  rw [← NNReal.coe_le_coe]
  change (β : ℝ) * (‖u₀‖ + (R : ℝ)) ^ 2 ≤
    (β : ℝ) * ((K : ℝ) + (R : ℝ)) ^ 2
  gcongr

theorem quadraticBUCBallLipschitzConstant_le_uniform
    (β K R : ℝ≥0) (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ)) :
    quadraticBUCBallLipschitzConstant β u₀ R ≤
      quadraticBUCUniformBallLipschitzConstant β K R := by
  rw [← NNReal.coe_le_coe]
  change 2 * (β : ℝ) * (‖u₀‖ + (R : ℝ)) ≤
    2 * (β : ℝ) * ((K : ℝ) + (R : ℝ))
  gcongr

theorem quadraticBUCUniformLifespan_pos (β K : ℝ≥0) :
    0 < quadraticBUCUniformLifespan β K := by
  simp only [quadraticBUCUniformLifespan]
  positivity

/-- The uniform lifespan makes the unit orbit ball invariant. -/
theorem quadraticBUCUniformLifespan_mul_bound_le_one (β K : ℝ≥0) :
    (quadraticBUCUniformLifespan β K : ℝ) *
        (quadraticBUCUniformBallBound β K 1 : ℝ) ≤ 1 := by
  let A := (quadraticBUCUniformBallBound β K 1 : ℝ)
  let L := (quadraticBUCUniformBallLipschitzConstant β K 1 : ℝ)
  have hA : 0 ≤ A := (quadraticBUCUniformBallBound β K 1).property
  have hL : 0 ≤ L := (quadraticBUCUniformBallLipschitzConstant β K 1).property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * A ≤ 1
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hD]
  nlinarith

/-- The same lifespan gives a uniform strict contraction factor. -/
theorem quadraticBUCUniformLifespan_mul_lipschitz_lt_one (β K : ℝ≥0) :
    quadraticBUCUniformLifespan β K *
        quadraticBUCUniformBallLipschitzConstant β K 1 < 1 := by
  rw [← NNReal.coe_lt_coe]
  let A := (quadraticBUCUniformBallBound β K 1 : ℝ)
  let L := (quadraticBUCUniformBallLipschitzConstant β K 1 : ℝ)
  have hA : 0 ≤ A := (quadraticBUCUniformBallBound β K 1).property
  have hL : 0 ≤ L := (quadraticBUCUniformBallLipschitzConstant β K 1).property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * L < 1
  rw [one_div, inv_mul_eq_div, div_lt_iff₀ hD]
  nlinarith

/-- An orbit-ball path based at data of norm at most `K` lies in the common
zero-centered path ball of radius `K + R`. -/
theorem mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
    (T K R : ℝ≥0) (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    {u : DuhamelPath T BUC}
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ) := by
  apply Metric.closedBall_subset_closedBall
    (show ‖u₀‖ + (R : ℝ) ≤ ((K + R : ℝ≥0) : ℝ) by
      simpa using add_le_add_right hu₀ (R : ℝ))
  exact mem_zero_ball_of_mem_heatLinearBUCPath_ball
    (E := E) (F := F) T u₀ R hu

/-- Uniform pointwise contraction estimate on the common zero-centered path
ball. -/
theorem norm_semilinearHeatBUCPicard_quadratic_sub_le_uniform_zero_ball
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (u v : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ))
    (hv : v ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ‖semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) u t -
        semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) v t‖ ≤
      ((T * quadraticBUCUniformBallLipschitzConstant β K R : ℝ≥0) : ℝ) *
        ‖u - v‖ := by
  rw [semilinearHeatBUCPicard_sub_eq_projectedDuhamelDifference
    (E := E) (F := F) T u₀ (quadraticOfCLM B)
    (continuous_quadraticOfCLM B) u v t]
  let Q : ℝ≥0 := K + R
  let L : ℝ≥0 := quadraticBUCUniformBallLipschitzConstant β K R
  have hlocal :=
    lipschitzOnWith_quadraticOfCLM_closedBall_center_of_bound
      B β hB (0 : BUC) Q
  have hbound :=
    norm_projectedDuhamelDifference_le_of_lipschitzOn_closedBall
      T 1 L (vectorHeatSemigroupBUCExtended (E := E) (F := F))
      (quadraticOfCLM B) (0 : BUC)
      (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
        (E := E) (F := F) r)
      (by simpa [L, Q, quadraticBUCUniformBallLipschitzConstant,
          quadraticBUCBallLipschitzConstant] using hlocal)
      u v hu hv t
  simpa [L] using hbound

/-- On each orbit ball over `‖u₀‖ ≤ K`, the Picard map has the same
contraction factor `T L(K,R)`. -/
theorem dist_semilinearHeatBUCPicard_quadratic_le_uniform_on_orbit_ball
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (u v : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
    (hv : v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    dist
      (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B) u)
      (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B) v) ≤
      ((T * quadraticBUCUniformBallLipschitzConstant β K R : ℝ≥0) : ℝ) *
        dist u v := by
  apply (ContinuousMap.dist_le
    (mul_nonneg (T * quadraticBUCUniformBallLipschitzConstant β K R).property
      dist_nonneg)).mpr
  intro t
  rw [dist_eq_norm]
  rw [dist_eq_norm u v]
  exact norm_semilinearHeatBUCPicard_quadratic_sub_le_uniform_zero_ball
    (E := E) (F := F) T K R B β hB u₀ u v
    (mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T K R u₀ hu₀ hu)
    (mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T K R u₀ hu₀ hv) t

/-- Uniform ball preservation under the bound formed from `K`, not the
individual initial datum. -/
theorem semilinearHeatBUCPicard_quadratic_mapsTo_uniform_orbit_ball
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (hmap : (T : ℝ) * (quadraticBUCUniformBallBound β K R : ℝ) ≤ (R : ℝ)) :
    MapsTo
      (semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
        (continuous_quadraticOfCLM B))
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) := by
  apply semilinearHeatBUCPicard_quadratic_mapsTo_closedBall
    T B β hB u₀ R
  calc
    (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤
        (T : ℝ) * (quadraticBUCUniformBallBound β K R : ℝ) := by
      gcongr
      exact_mod_cast quadraticBUCBallBound_le_uniform β K R u₀ hu₀
    _ ≤ (R : ℝ) := hmap

/-- Uniform local existence and uniqueness on an orbit ball. -/
theorem exists_semilinearHeatBUC_quadratic_fixedPoint_uniform
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (hmap : (T : ℝ) * (quadraticBUCUniformBallBound β K R : ℝ) ≤ (R : ℝ))
    (hsmall : T * quadraticBUCUniformBallLipschitzConstant β K R < 1) :
    ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
      semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) u = u ∧
      ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
        semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) v = v → v = u := by
  apply exists_semilinearHeatBUC_quadratic_fixedPoint_mem_closedBall
    T B β hB u₀ R
  · calc
      (T : ℝ) * (quadraticBUCBallBound β u₀ R : ℝ) ≤
          (T : ℝ) * (quadraticBUCUniformBallBound β K R : ℝ) := by
        gcongr
        exact_mod_cast quadraticBUCBallBound_le_uniform β K R u₀ hu₀
      _ ≤ (R : ℝ) := hmap
  · exact lt_of_le_of_lt
      (mul_le_mul_left' (quadraticBUCBallLipschitzConstant_le_uniform
        β K R u₀ hu₀) T) hsmall

/-- A single positive time works for every datum in `‖u₀‖ ≤ K`. -/
theorem exists_single_time_semilinearHeatBUC_quadratic_fixedPoints
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) :
    let T := quadraticBUCUniformLifespan β K
    0 < T ∧ ∀ u₀ : BUC, ‖u₀‖ ≤ (K : ℝ) →
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) u = u ∧
        ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
          semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
              (continuous_quadraticOfCLM B) v = v → v = u := by
  dsimp only
  refine ⟨quadraticBUCUniformLifespan_pos β K, ?_⟩
  intro u₀ hu₀
  exact exists_semilinearHeatBUC_quadratic_fixedPoint_uniform
    (E := E) (F := F) (quadraticBUCUniformLifespan β K) K 1
    B β hB u₀ hu₀
    (quadraticBUCUniformLifespan_mul_bound_le_one β K)
    (quadraticBUCUniformLifespan_mul_lipschitz_lt_one β K)

/-- Quantitative continuous dependence for any two local quadratic fixed
points lying in their respective orbit balls.  The nonlinear comparison is
made on the common zero-centered ball of radius `K + R`. -/
theorem dist_semilinearHeatBUC_quadratic_fixedPoints_le_uniform
    (T K R : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ v₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ)) (hv₀ : ‖v₀‖ ≤ (K : ℝ))
    (hsmall : T * quadraticBUCUniformBallLipschitzConstant β K R < 1)
    (u v : DuhamelPath T BUC)
    (huBall : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
    (hvBall : v ∈ Metric.closedBall (heatLinearBUCPath T v₀) (R : ℝ))
    (hu : semilinearHeatBUCPicard T u₀ (quadraticOfCLM B)
      (continuous_quadraticOfCLM B) u = u)
    (hv : semilinearHeatBUCPicard T v₀ (quadraticOfCLM B)
      (continuous_quadraticOfCLM B) v = v) :
    dist u v ≤
      (1 - (((T * quadraticBUCUniformBallLipschitzConstant β K R : ℝ≥0) : ℝ)))⁻¹ *
        dist u₀ v₀ := by
  let N := quadraticOfCLM B
  let hN : Continuous N := continuous_quadraticOfCLM B
  let Φu := semilinearHeatBUCPicard T u₀ N hN
  let Φv := semilinearHeatBUCPicard T v₀ N hN
  let q : ℝ≥0 := T * quadraticBUCUniformBallLipschitzConstant β K R
  have huZero :
      u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
        ((K + R : ℝ≥0) : ℝ) :=
    mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T K R u₀ hu₀ huBall
  have hvZero :
      v ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
        ((K + R : ℝ≥0) : ℝ) :=
    mem_uniform_zero_ball_of_mem_heatLinearBUCPath_ball
      (E := E) (F := F) T K R v₀ hv₀ hvBall
  have hnonlin : dist (Φu u) (Φu v) ≤ (q : ℝ) * dist u v := by
    apply (ContinuousMap.dist_le (mul_nonneg q.property dist_nonneg)).mpr
    intro t
    rw [dist_eq_norm]
    rw [dist_eq_norm u v]
    simpa [Φu, N, hN, q] using
      norm_semilinearHeatBUCPicard_quadratic_sub_le_uniform_zero_ball
        (E := E) (F := F) T K R B β hB u₀ u v huZero hvZero t
  have hshift : dist (Φu v) (Φv v) ≤ dist u₀ v₀ := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    simp only [Φu, Φv, N, hN, semilinearHeatBUCPicard_apply]
    rw [dist_add_right]
    exact dist_vectorHeatSemigroupBUCExtended_apply_le
      (E := E) (F := F) (t : ℝ) u₀ v₀
  have htotal : dist u v ≤ (q : ℝ) * dist u v + dist u₀ v₀ := by
    calc
      dist u v = dist (Φu u) (Φv v) := by
        simp only [Φu, Φv, N, hN]
        rw [hu, hv]
      _ ≤ dist (Φu u) (Φu v) + dist (Φu v) (Φv v) :=
        dist_triangle _ _ _
      _ ≤ (q : ℝ) * dist u v + dist u₀ v₀ :=
        add_le_add hnonlin hshift
  have hq : (q : ℝ) < 1 := by exact_mod_cast hsmall
  have hden : 0 < 1 - (q : ℝ) := sub_pos.mpr hq
  change dist u v ≤ (1 - (q : ℝ))⁻¹ * dist u₀ v₀
  rw [le_inv_mul_iff₀ hden]
  nlinarith

/-- The bounded set of initial data on which the common local solution map is
defined. -/
abbrev QuadraticBUCBoundedData (K : ℝ≥0) :=
  {u : BUC // ‖u‖ ≤ (K : ℝ)}

/-- Existence package used to select the common-time local quadratic solution. -/
theorem exists_quadraticSemilinearHeatBUCUniformSolution
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K) :
    let T := quadraticBUCUniformLifespan β K
    ∃ u ∈ Metric.closedBall (heatLinearBUCPath T (u₀ : BUC)) (1 : ℝ),
      semilinearHeatBUCPicard T (u₀ : BUC) (quadraticOfCLM B)
          (continuous_quadraticOfCLM B) u = u ∧
      ∀ v ∈ Metric.closedBall (heatLinearBUCPath T (u₀ : BUC)) (1 : ℝ),
        semilinearHeatBUCPicard T (u₀ : BUC) (quadraticOfCLM B)
            (continuous_quadraticOfCLM B) v = v → v = u := by
  dsimp only
  exact (exists_single_time_semilinearHeatBUC_quadratic_fixedPoints
    (E := E) (F := F) K B β hB).2 u₀ u₀.property

/-- Canonical locally unique quadratic mild solution on the common lifespan
for the bounded data ball. -/
noncomputable def quadraticSemilinearHeatBUCUniformSolution
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (quadraticBUCUniformLifespan β K) BUC :=
  Classical.choose
    (exists_quadraticSemilinearHeatBUCUniformSolution
      (E := E) (F := F) K B β hB u₀)

/-- The selected solution lies in its unit homogeneous-orbit ball. -/
theorem quadraticSemilinearHeatBUCUniformSolution_mem_orbit_ball
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K) :
    quadraticSemilinearHeatBUCUniformSolution K B β hB u₀ ∈
      Metric.closedBall
        (heatLinearBUCPath (quadraticBUCUniformLifespan β K) (u₀ : BUC))
        (1 : ℝ) := by
  exact (Classical.choose_spec
    (exists_quadraticSemilinearHeatBUCUniformSolution
      (E := E) (F := F) K B β hB u₀)).1

/-- The selected solution is a fixed point of the corrected quadratic heat
Picard map. -/
theorem quadraticSemilinearHeatBUCUniformSolution_isFixedPt
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCPicard (quadraticBUCUniformLifespan β K) (u₀ : BUC)
        (quadraticOfCLM B) (continuous_quadraticOfCLM B)
        (quadraticSemilinearHeatBUCUniformSolution K B β hB u₀) =
      quadraticSemilinearHeatBUCUniformSolution K B β hB u₀ := by
  exact (Classical.choose_spec
    (exists_quadraticSemilinearHeatBUCUniformSolution
      (E := E) (F := F) K B β hB u₀)).2.1

/-- Exact corrected mild formula for the selected uniform-time solution. -/
theorem quadraticSemilinearHeatBUCUniformSolution_mild
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (quadraticBUCUniformLifespan β K : ℝ)) :
    quadraticSemilinearHeatBUCUniformSolution K B β hB u₀ t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) (u₀ : BUC) +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (quadraticOfCLM B
              (quadraticSemilinearHeatBUCUniformSolution K B β hB u₀
                (Set.projIcc 0 (quadraticBUCUniformLifespan β K : ℝ)
                  (quadraticBUCUniformLifespan β K).property s))) := by
  have h := congrArg
    (fun w : DuhamelPath (quadraticBUCUniformLifespan β K) BUC ↦ w t)
    (quadraticSemilinearHeatBUCUniformSolution_isFixedPt
      (E := E) (F := F) K B β hB u₀)
  simpa using h.symm

/-- For generator-domain initial data, the canonical bounded-data quadratic
solution has the exact strong right derivative `A u₀ + B(u₀,u₀)` at time
zero.  This uses only fixed-point regularity, not a global Lipschitz estimate
for the quadratic nonlinearity. -/
theorem quadraticSemilinearHeatBUCUniformSolution_hasDerivWithinAt_zero
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖)
    (u₀ : QuadraticBUCBoundedData (E := E) (F := F) K) (Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u₀ : BUC) Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ quadraticSemilinearHeatBUCUniformSolution K B β hB u₀
        (Set.projIcc 0 (quadraticBUCUniformLifespan β K : ℝ)
          (quadraticBUCUniformLifespan β K).property t))
      (Au₀ + quadraticOfCLM B (u₀ : BUC))
      (Set.Icc 0 (quadraticBUCUniformLifespan β K : ℝ)) 0 := by
  exact semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (E := E) (F := F) (quadraticBUCUniformLifespan β K)
    (u₀ : BUC) Au₀ (quadraticOfCLM B) (continuous_quadraticOfCLM B)
    (quadraticSemilinearHeatBUCUniformSolution K B β hB u₀)
    (quadraticSemilinearHeatBUCUniformSolution_isFixedPt
      (E := E) (F := F) K B β hB u₀) hu₀

/-- The common-time canonical quadratic solution map is Lipschitz on the
bounded initial-data subtype. -/
theorem lipschitzWith_quadraticSemilinearHeatBUCUniformSolution
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) :
    LipschitzWith
      (heatDuhamelBUCIntrinsicStabilityConstant
        (quadraticBUCUniformLifespan β K)
        (quadraticBUCUniformBallLipschitzConstant β K 1)
        (quadraticBUCUniformLifespan_mul_lipschitz_lt_one β K))
      (fun u₀ : QuadraticBUCBoundedData (E := E) (F := F) K ↦
        quadraticSemilinearHeatBUCUniformSolution K B β hB u₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro u₀ v₀
  have h := dist_semilinearHeatBUC_quadratic_fixedPoints_le_uniform
    (E := E) (F := F)
    (quadraticBUCUniformLifespan β K) K 1 B β hB
    (u₀ : BUC) (v₀ : BUC) u₀.property v₀.property
    (quadraticBUCUniformLifespan_mul_lipschitz_lt_one β K)
    (quadraticSemilinearHeatBUCUniformSolution K B β hB u₀)
    (quadraticSemilinearHeatBUCUniformSolution K B β hB v₀)
    (quadraticSemilinearHeatBUCUniformSolution_mem_orbit_ball
      (E := E) (F := F) K B β hB u₀)
    (quadraticSemilinearHeatBUCUniformSolution_mem_orbit_ball
      (E := E) (F := F) K B β hB v₀)
    (quadraticSemilinearHeatBUCUniformSolution_isFixedPt
      (E := E) (F := F) K B β hB u₀)
    (quadraticSemilinearHeatBUCUniformSolution_isFixedPt
      (E := E) (F := F) K B β hB v₀)
  simpa [heatDuhamelBUCIntrinsicStabilityConstant, Subtype.dist_eq] using h

/-- In particular, the common-time local quadratic solution map is
continuous on every bounded initial-data ball. -/
theorem continuous_quadraticSemilinearHeatBUCUniformSolution
    (K : ℝ≥0) (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) :
    Continuous
      (fun u₀ : QuadraticBUCBoundedData (E := E) (F := F) K ↦
        quadraticSemilinearHeatBUCUniformSolution K B β hB u₀) :=
  (lipschitzWith_quadraticSemilinearHeatBUCUniformSolution
    (E := E) (F := F) K B β hB).continuous

end Poincare
