import Poincare.Global.SemilinearHeatBUCFixedPointRegularity
import Poincare.Global.DuhamelLocalContraction

/-!
# Uniform local semilinear heat theory from bounded-ball moduli

This module removes the quadratic hypothesis from the local `BUC` theory.
A continuous nonlinearity is supplied together with explicit bounds and
Lipschitz constants on every zero-centered closed ball.  These moduli give a
single positive lifespan for every initial datum in a prescribed bounded
set, local uniqueness on the controlled orbit ball, and a Lipschitz solution
map on that bounded set.
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

/-- Explicit bounded-ball information for a continuous semilinear
nonlinearity.  No global boundedness or global Lipschitz hypothesis is
required. -/
structure SemilinearHeatBUCLocalData (N : BUC → BUC) where
  continuous : Continuous N
  growth : ℝ≥0 → ℝ≥0
  lipschitz : ℝ≥0 → ℝ≥0
  norm_le_growth : ∀ (R : ℝ≥0) (x : BUC), ‖x‖ ≤ (R : ℝ) →
    ‖N x‖ ≤ (growth R : ℝ)
  lipschitzOn_closedBall : ∀ R : ℝ≥0,
    LipschitzOnWith (lipschitz R) N (Metric.closedBall (0 : BUC) (R : ℝ))

/-- Uniform nonlinearity bound for paths within `R` of a homogeneous heat
orbit based at data of norm at most `K`. -/
def semilinearHeatBUCUniformBallBound {N : BUC → BUC}
    (data : SemilinearHeatBUCLocalData N) (K R : ℝ≥0) : ℝ≥0 :=
  data.growth (K + R)

/-- Uniform Lipschitz constant on the same family of orbit balls. -/
def semilinearHeatBUCUniformBallLipschitzConstant {N : BUC → BUC}
    (data : SemilinearHeatBUCLocalData N) (K R : ℝ≥0) : ℝ≥0 :=
  data.lipschitz (K + R)

/-- One explicit lifespan for every datum in `‖u₀‖ ≤ K`.  Solutions are
constructed in the unit ball about their homogeneous heat orbit. -/
def semilinearHeatBUCUniformLifespan {N : BUC → BUC}
    (data : SemilinearHeatBUCLocalData N) (K : ℝ≥0) : ℝ≥0 :=
  1 / (2 * (semilinearHeatBUCUniformBallBound data K 1 +
    semilinearHeatBUCUniformBallLipschitzConstant data K 1 + 1))

theorem semilinearHeatBUCUniformLifespan_pos {N : BUC → BUC}
    (data : SemilinearHeatBUCLocalData N) (K : ℝ≥0) :
    0 < semilinearHeatBUCUniformLifespan data K := by
  simp only [semilinearHeatBUCUniformLifespan]
  positivity

/-- The explicit lifespan makes the unit orbit ball invariant. -/
theorem semilinearHeatBUCUniformLifespan_mul_bound_le_one {N : BUC → BUC}
    (data : SemilinearHeatBUCLocalData N) (K : ℝ≥0) :
    (semilinearHeatBUCUniformLifespan data K : ℝ) *
        (semilinearHeatBUCUniformBallBound data K 1 : ℝ) ≤ 1 := by
  let A := (semilinearHeatBUCUniformBallBound data K 1 : ℝ)
  let L := (semilinearHeatBUCUniformBallLipschitzConstant data K 1 : ℝ)
  have hA : 0 ≤ A := (semilinearHeatBUCUniformBallBound data K 1).property
  have hL : 0 ≤ L :=
    (semilinearHeatBUCUniformBallLipschitzConstant data K 1).property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * A ≤ 1
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hD]
  nlinarith

/-- The same lifespan gives a strict contraction factor. -/
theorem semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one
    {N : BUC → BUC} (data : SemilinearHeatBUCLocalData N) (K : ℝ≥0) :
    semilinearHeatBUCUniformLifespan data K *
        semilinearHeatBUCUniformBallLipschitzConstant data K 1 < 1 := by
  rw [← NNReal.coe_lt_coe]
  let A := (semilinearHeatBUCUniformBallBound data K 1 : ℝ)
  let L := (semilinearHeatBUCUniformBallLipschitzConstant data K 1 : ℝ)
  have hA : 0 ≤ A := (semilinearHeatBUCUniformBallBound data K 1).property
  have hL : 0 ≤ L :=
    (semilinearHeatBUCUniformBallLipschitzConstant data K 1).property
  have hD : 0 < 2 * (A + L + 1) := by positivity
  change (1 / (2 * (A + L + 1))) * L < 1
  rw [one_div, inv_mul_eq_div, div_lt_iff₀ hD]
  nlinarith

/-- The homogeneous heat orbit is uniformly bounded by its initial datum. -/
theorem norm_heatLinearBUCPath_le_local (T : ℝ≥0) (u₀ : BUC) :
    ‖heatLinearBUCPath T u₀‖ ≤ ‖u₀‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  calc
    ‖heatLinearBUCPath T u₀ t‖
        ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ)‖ * ‖u₀‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right
      (norm_vectorHeatSemigroupBUCExtended_le_one (E := E) (F := F) (t : ℝ))
      (norm_nonneg _)
    _ = ‖u₀‖ := one_mul _

/-- An orbit-ball path based at data of norm at most `K` lies in the common
zero-centered path ball of radius `K + R`. -/
theorem mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
    (T K R : ℝ≥0) (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    {u : DuhamelPath T BUC}
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ) := by
  rw [Metric.mem_closedBall] at hu ⊢
  apply (ContinuousMap.dist_le (K + R).property).mpr
  intro t
  have horbit : dist (heatLinearBUCPath T u₀ t) (0 : BUC) ≤ (K : ℝ) := by
    have hnorm : ‖heatLinearBUCPath T u₀ t‖ ≤ (K : ℝ) := by
      calc
      ‖heatLinearBUCPath T u₀ t‖ ≤ ‖u₀‖ := by
        calc
          ‖heatLinearBUCPath T u₀ t‖ ≤ ‖heatLinearBUCPath T u₀‖ :=
            ContinuousMap.norm_coe_le_norm _ _
          _ ≤ ‖u₀‖ := norm_heatLinearBUCPath_le_local T u₀
      _ ≤ (K : ℝ) := hu₀
    simpa [dist_eq_norm] using hnorm
  calc
    dist (u t) (constantDuhamelPathGeneric T (0 : BUC) t) =
        dist (u t) (0 : BUC) := rfl
    _ ≤ dist (u t) (heatLinearBUCPath T u₀ t) +
          dist (heatLinearBUCPath T u₀ t) 0 := dist_triangle _ _ _
    _ ≤ dist u (heatLinearBUCPath T u₀) + (K : ℝ) :=
      add_le_add (ContinuousMap.dist_apply_le_dist t) horbit
    _ ≤ (R : ℝ) + (K : ℝ) := add_le_add hu le_rfl
    _ = ((K + R : ℝ≥0) : ℝ) := by norm_num [add_comm]

/-- Pointwise contraction estimate on a common zero-centered path ball. -/
theorem norm_semilinearHeatBUCPicard_sub_le_uniform_zero_ball
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (u v : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ))
    (hv : v ∈ Metric.closedBall (constantDuhamelPathGeneric T (0 : BUC))
      ((K + R : ℝ≥0) : ℝ))
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    ‖semilinearHeatBUCPicard T u₀ N data.continuous u t -
        semilinearHeatBUCPicard T u₀ N data.continuous v t‖ ≤
      ((T * semilinearHeatBUCUniformBallLipschitzConstant data K R : ℝ≥0) : ℝ) *
        ‖u - v‖ := by
  rw [semilinearHeatBUCPicard_sub_eq_projectedDuhamelDifference
    (E := E) (F := F) T u₀ N data.continuous u v t]
  have hbound :=
    norm_projectedDuhamelDifference_le_of_lipschitzOn_closedBall
      T 1 (semilinearHeatBUCUniformBallLipschitzConstant data K R)
      (vectorHeatSemigroupBUCExtended (E := E) (F := F)) N (0 : BUC)
      (fun r _hr ↦ norm_vectorHeatSemigroupBUCExtended_le_one
        (E := E) (F := F) r)
      (by simpa [semilinearHeatBUCUniformBallLipschitzConstant] using
        data.lipschitzOn_closedBall (K + R))
      u v hu hv t
  simpa using hbound

/-- A Picard iterate based at bounded data stays within `T M(K,R)` of the
homogeneous heat orbit, provided the input lies in the orbit ball. -/
theorem dist_semilinearHeatBUCPicard_heatLinearPath_le_local
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (u : DuhamelPath T BUC)
    (hu : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) :
    dist (semilinearHeatBUCPicard T u₀ N data.continuous u)
        (heatLinearBUCPath T u₀) ≤
      (T : ℝ) * (semilinearHeatBUCUniformBallBound data K R : ℝ) := by
  apply (ContinuousMap.dist_le
    (mul_nonneg T.property
      (semilinearHeatBUCUniformBallBound data K R).property)).mpr
  intro t
  rw [semilinearHeatBUCPicard_apply, heatLinearBUCPath_apply, dist_eq_norm,
    add_sub_cancel_left]
  have huZero := mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
    (E := E) (F := F) T K R u₀ hu₀ hu
  have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
        (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖ ≤
        (semilinearHeatBUCUniformBallBound data K R : ℝ) := by
    intro s _hs
    let p : Set.Icc (0 : ℝ) (T : ℝ) :=
      Set.projIcc 0 (T : ℝ) T.property s
    have hup : u p ∈ Metric.closedBall (0 : BUC) (((K + R : ℝ≥0) : ℝ)) :=
      eval_mem_closedBall_of_path_mem_closedBall T (0 : BUC) huZero p
    have huNorm : ‖u p‖ ≤ (((K + R : ℝ≥0) : ℝ)) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hup
    have hNbound : ‖N (u p)‖ ≤
        (semilinearHeatBUCUniformBallBound data K R : ℝ) := by
      simpa [semilinearHeatBUCUniformBallBound] using
        data.norm_le_growth (K + R) (u p) huNorm
    calc
      ‖vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u p))‖
          ≤ ‖vectorHeatSemigroupBUCExtended (E := E) (F := F)
              ((t : ℝ) - s)‖ * ‖N (u p)‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (semilinearHeatBUCUniformBallBound data K R : ℝ) :=
        mul_le_mul
          (norm_vectorHeatSemigroupBUCExtended_le_one
            (E := E) (F := F) ((t : ℝ) - s))
          hNbound (norm_nonneg _) zero_le_one
      _ = (semilinearHeatBUCUniformBallBound data K R : ℝ) := one_mul _
  calc
    ‖∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
          (N (u (Set.projIcc 0 (T : ℝ) T.property s)))‖
        ≤ (semilinearHeatBUCUniformBallBound data K R : ℝ) *
            |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (semilinearHeatBUCUniformBallBound data K R : ℝ) * (t : ℝ) := by
      rw [sub_zero, abs_of_nonneg t.property.1]
    _ ≤ (semilinearHeatBUCUniformBallBound data K R : ℝ) * (T : ℝ) :=
      mul_le_mul_of_nonneg_left t.property.2
        (semilinearHeatBUCUniformBallBound data K R).property
    _ = (T : ℝ) * (semilinearHeatBUCUniformBallBound data K R : ℝ) :=
      mul_comm _ _

/-- Uniform preservation of the orbit ball over the data ball `‖u₀‖ ≤ K`. -/
theorem semilinearHeatBUCPicard_mapsTo_uniform_orbit_ball
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (hmap : (T : ℝ) * (semilinearHeatBUCUniformBallBound data K R : ℝ) ≤
      (R : ℝ)) :
    MapsTo (semilinearHeatBUCPicard T u₀ N data.continuous)
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
      (Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ)) := by
  intro u hu
  exact (dist_semilinearHeatBUCPicard_heatLinearPath_le_local
    (E := E) (F := F) T K R N data u₀ hu₀ u hu).trans hmap

/-- Uniform local existence and uniqueness on a controlled orbit ball. -/
theorem exists_semilinearHeatBUC_fixedPoint_uniform_local
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ))
    (hmap : (T : ℝ) * (semilinearHeatBUCUniformBallBound data K R : ℝ) ≤
      (R : ℝ))
    (hsmall : T * semilinearHeatBUCUniformBallLipschitzConstant data K R < 1) :
    ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
      semilinearHeatBUCPicard T u₀ N data.continuous u = u ∧
      ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ),
        semilinearHeatBUCPicard T u₀ N data.continuous v = v → v = u := by
  let L := semilinearHeatBUCUniformBallLipschitzConstant data K R
  let Φ := semilinearHeatBUCPicard T u₀ N data.continuous
  letI : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) :=
    ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩
  apply exists_fixedPoint_mem_closedBall_of_pointwise_contraction
    (X := BUC) (q := T * L) Φ (heatLinearBUCPath T u₀) R.property
  · exact semilinearHeatBUCPicard_mapsTo_uniform_orbit_ball
      (E := E) (F := F) T K R N data u₀ hu₀ hmap
  · intro u v hu hv t
    change ‖Φ u t - Φ v t‖ ≤ ((T * L : ℝ≥0) : ℝ) * ‖u - v‖
    exact norm_semilinearHeatBUCPicard_sub_le_uniform_zero_ball
      (E := E) (F := F) T K R N data u₀ u v
      (mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
        (E := E) (F := F) T K R u₀ hu₀ hu)
      (mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
        (E := E) (F := F) T K R u₀ hu₀ hv) t
  · simpa [L] using hsmall

/-- A single positive time works for every datum in the closed `K`-ball. -/
theorem exists_single_time_semilinearHeatBUC_fixedPoints_local
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N) :
    let T := semilinearHeatBUCUniformLifespan data K
    0 < T ∧ ∀ u₀ : BUC, ‖u₀‖ ≤ (K : ℝ) →
      ∃ u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
        semilinearHeatBUCPicard T u₀ N data.continuous u = u ∧
        ∀ v ∈ Metric.closedBall (heatLinearBUCPath T u₀) (1 : ℝ),
          semilinearHeatBUCPicard T u₀ N data.continuous v = v → v = u := by
  dsimp only
  refine ⟨semilinearHeatBUCUniformLifespan_pos data K, ?_⟩
  intro u₀ hu₀
  exact exists_semilinearHeatBUC_fixedPoint_uniform_local
    (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K) K 1
    N data u₀ hu₀
    (semilinearHeatBUCUniformLifespan_mul_bound_le_one data K)
    (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K)

/-- Quantitative dependence of controlled local fixed points on their initial
data. -/
theorem dist_semilinearHeatBUC_fixedPoints_le_uniform_local
    (T K R : ℝ≥0) (N : BUC → BUC)
    (data : SemilinearHeatBUCLocalData N)
    (u₀ v₀ : BUC) (hu₀ : ‖u₀‖ ≤ (K : ℝ)) (hv₀ : ‖v₀‖ ≤ (K : ℝ))
    (hsmall : T * semilinearHeatBUCUniformBallLipschitzConstant data K R < 1)
    (u v : DuhamelPath T BUC)
    (huBall : u ∈ Metric.closedBall (heatLinearBUCPath T u₀) (R : ℝ))
    (hvBall : v ∈ Metric.closedBall (heatLinearBUCPath T v₀) (R : ℝ))
    (hu : semilinearHeatBUCPicard T u₀ N data.continuous u = u)
    (hv : semilinearHeatBUCPicard T v₀ N data.continuous v = v) :
    dist u v ≤
      (1 - (((T * semilinearHeatBUCUniformBallLipschitzConstant data K R :
        ℝ≥0) : ℝ)))⁻¹ * dist u₀ v₀ := by
  let Φu := semilinearHeatBUCPicard T u₀ N data.continuous
  let Φv := semilinearHeatBUCPicard T v₀ N data.continuous
  let q : ℝ≥0 := T * semilinearHeatBUCUniformBallLipschitzConstant data K R
  have huZero := mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
    (E := E) (F := F) T K R u₀ hu₀ huBall
  have hvZero := mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
    (E := E) (F := F) T K R v₀ hv₀ hvBall
  have hnonlin : dist (Φu u) (Φu v) ≤ (q : ℝ) * dist u v := by
    apply (ContinuousMap.dist_le (mul_nonneg q.property dist_nonneg)).mpr
    intro t
    rw [dist_eq_norm, dist_eq_norm u v]
    simpa [Φu, q] using
      norm_semilinearHeatBUCPicard_sub_le_uniform_zero_ball
        (E := E) (F := F) T K R N data u₀ u v huZero hvZero t
  have hshift : dist (Φu v) (Φv v) ≤ dist u₀ v₀ := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    simp only [Φu, Φv, semilinearHeatBUCPicard_apply]
    rw [dist_add_right]
    exact dist_vectorHeatSemigroupBUCExtended_apply_le
      (E := E) (F := F) (t : ℝ) u₀ v₀
  have htotal : dist u v ≤ (q : ℝ) * dist u v + dist u₀ v₀ := by
    calc
      dist u v = dist (Φu u) (Φv v) := by
        change dist u v = dist
          (semilinearHeatBUCPicard T u₀ N data.continuous u)
          (semilinearHeatBUCPicard T v₀ N data.continuous v)
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

/-- Bounded initial data on which the common local solution map is defined. -/
abbrev SemilinearBUCBoundedData (K : ℝ≥0) :=
  {u : BUC // ‖u‖ ≤ (K : ℝ)}

theorem exists_semilinearHeatBUCUniformLocalSolution
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    let T := semilinearHeatBUCUniformLifespan data K
    ∃ u ∈ Metric.closedBall (heatLinearBUCPath T (u₀ : BUC)) (1 : ℝ),
      semilinearHeatBUCPicard T (u₀ : BUC) N data.continuous u = u ∧
      ∀ v ∈ Metric.closedBall (heatLinearBUCPath T (u₀ : BUC)) (1 : ℝ),
        semilinearHeatBUCPicard T (u₀ : BUC) N data.continuous v = v →
          v = u := by
  dsimp only
  exact (exists_single_time_semilinearHeatBUC_fixedPoints_local
    (E := E) (F := F) K N data).2 u₀ u₀.property

/-- Canonical locally unique mild solution on the common lifespan. -/
noncomputable def semilinearHeatBUCUniformLocalSolution
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC :=
  Classical.choose (exists_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K N data u₀)

theorem semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCUniformLocalSolution K N data u₀ ∈
      Metric.closedBall
        (heatLinearBUCPath (semilinearHeatBUCUniformLifespan data K)
          (u₀ : BUC)) (1 : ℝ) :=
  (Classical.choose_spec (exists_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K N data u₀)).1

/-- The selected solution stays in the common zero-centered path ball of
radius `K + 1`. -/
theorem semilinearHeatBUCUniformLocalSolution_mem_zero_ball
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCUniformLocalSolution K N data u₀ ∈
      Metric.closedBall
        (constantDuhamelPathGeneric (semilinearHeatBUCUniformLifespan data K)
          (0 : BUC)) ((K + 1 : ℝ≥0) : ℝ) :=
  mem_semilinearHeatBUC_uniform_zero_ball_of_mem_orbit_ball
    (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K) K 1
    (u₀ : BUC) u₀.property
    (semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
      (E := E) (F := F) K N data u₀)

/-- Pointwise form of the uniform `K + 1` solution bound. -/
theorem norm_semilinearHeatBUCUniformLocalSolution_le
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (semilinearHeatBUCUniformLifespan data K : ℝ)) :
    ‖semilinearHeatBUCUniformLocalSolution K N data u₀ t‖ ≤
      ((K + 1 : ℝ≥0) : ℝ) := by
  have hmem := eval_mem_closedBall_of_path_mem_closedBall
    (semilinearHeatBUCUniformLifespan data K) (0 : BUC)
    (semilinearHeatBUCUniformLocalSolution_mem_zero_ball
      (E := E) (F := F) K N data u₀) t
  simpa [Metric.mem_closedBall, dist_eq_norm] using hmem

theorem semilinearHeatBUCUniformLocalSolution_isFixedPt
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCPicard (semilinearHeatBUCUniformLifespan data K)
        (u₀ : BUC) N data.continuous
        (semilinearHeatBUCUniformLocalSolution K N data u₀) =
      semilinearHeatBUCUniformLocalSolution K N data u₀ :=
  (Classical.choose_spec (exists_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K N data u₀)).2.1

/-- Exact corrected mild formula for the selected local solution. -/
theorem semilinearHeatBUCUniformLocalSolution_mild
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (semilinearHeatBUCUniformLifespan data K : ℝ)) :
    semilinearHeatBUCUniformLocalSolution K N data u₀ t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) (u₀ : BUC) +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (N (semilinearHeatBUCUniformLocalSolution K N data u₀
              (Set.projIcc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)
                (semilinearHeatBUCUniformLifespan data K).property s))) := by
  have h := congrArg
    (fun w : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC ↦ w t)
    (semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀)
  simpa using h.symm

/-- The selected local solution starts at its prescribed initial datum. -/
theorem semilinearHeatBUCUniformLocalSolution_zero
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCUniformLocalSolution K N data u₀
        (⟨0, ⟨le_rfl, (semilinearHeatBUCUniformLifespan data K).property⟩⟩ :
          Set.Icc (0 : ℝ) (semilinearHeatBUCUniformLifespan data K : ℝ)) =
      (u₀ : BUC) := by
  simpa using semilinearHeatBUCUniformLocalSolution_mild
    (E := E) (F := F) K N data u₀
    (⟨0, ⟨le_rfl, (semilinearHeatBUCUniformLifespan data K).property⟩⟩ :
      Set.Icc (0 : ℝ) (semilinearHeatBUCUniformLifespan data K : ℝ))

/-- Generator-domain data give the exact strong right derivative
`A u₀ + N(u₀)` at time zero. -/
theorem semilinearHeatBUCUniformLocalSolution_hasDerivWithinAt_zero
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) (Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u₀ : BUC) Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ semilinearHeatBUCUniformLocalSolution K N data u₀
        (Set.projIcc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)
          (semilinearHeatBUCUniformLifespan data K).property t))
      (Au₀ + N (u₀ : BUC))
      (Set.Icc 0 (semilinearHeatBUCUniformLifespan data K : ℝ)) 0 := by
  exact semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
    (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K)
    (u₀ : BUC) Au₀ N data.continuous
    (semilinearHeatBUCUniformLocalSolution K N data u₀)
    (semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀) hu₀

/-- The common-time local solution map is Lipschitz on every bounded data
ball. -/
theorem lipschitzWith_semilinearHeatBUCUniformLocalSolution
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N) :
    LipschitzWith
      (heatDuhamelBUCIntrinsicStabilityConstant
        (semilinearHeatBUCUniformLifespan data K)
        (semilinearHeatBUCUniformBallLipschitzConstant data K 1)
        (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K))
      (fun u₀ : SemilinearBUCBoundedData (E := E) (F := F) K ↦
        semilinearHeatBUCUniformLocalSolution K N data u₀) := by
  apply LipschitzWith.of_dist_le_mul
  intro u₀ v₀
  have h := dist_semilinearHeatBUC_fixedPoints_le_uniform_local
    (E := E) (F := F) (semilinearHeatBUCUniformLifespan data K) K 1 N data
    (u₀ : BUC) (v₀ : BUC) u₀.property v₀.property
    (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one data K)
    (semilinearHeatBUCUniformLocalSolution K N data u₀)
    (semilinearHeatBUCUniformLocalSolution K N data v₀)
    (semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
      (E := E) (F := F) K N data u₀)
    (semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
      (E := E) (F := F) K N data v₀)
    (semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data u₀)
    (semilinearHeatBUCUniformLocalSolution_isFixedPt
      (E := E) (F := F) K N data v₀)
  simpa [heatDuhamelBUCIntrinsicStabilityConstant, Subtype.dist_eq] using h

theorem continuous_semilinearHeatBUCUniformLocalSolution
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N) :
    Continuous
      (fun u₀ : SemilinearBUCBoundedData (E := E) (F := F) K ↦
        semilinearHeatBUCUniformLocalSolution K N data u₀) :=
  (lipschitzWith_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K N data).continuous

end Poincare
