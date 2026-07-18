import Poincare.Global.SemilinearHeatBUCLocalUniform
import Poincare.Global.QuadraticHeatDuhamel

/-!
# Constructors for bounded-ball semilinear heat data

The Ricci--DeTurck coordinate remainder is assembled from simpler nonlinear
pieces.  This module makes the local-moduli package compositional: constants,
globally Lipschitz maps, sums, compositions, and bounded quadratic terms all
produce `SemilinearHeatBUCLocalData`.
-/

noncomputable section

open Set Function
open scoped NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

namespace SemilinearHeatBUCLocalData

/-- A globally Lipschitz nonlinearity has explicit local growth
`‖N(0)‖ + L R`. -/
def ofLipschitzWith (N : BUC → BUC) (L : ℝ≥0)
    (hN : LipschitzWith L N) : SemilinearHeatBUCLocalData N where
  continuous := hN.continuous
  growth R := ‖N 0‖₊ + L * R
  lipschitz _R := L
  norm_le_growth := by
    intro R x hx
    have hdiff : ‖N x - N 0‖ ≤ (L : ℝ) * ‖x‖ := by
      simpa [dist_eq_norm] using hN.dist_le_mul x 0
    calc
      ‖N x‖ = ‖(N x - N 0) + N 0‖ := by
        congr 1
        abel
      _ ≤ ‖N x - N 0‖ + ‖N 0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖x‖ + ‖N 0‖ := by gcongr
      _ ≤ (L : ℝ) * (R : ℝ) + ‖N 0‖ := by gcongr
      _ = ((‖N 0‖₊ + L * R : ℝ≥0) : ℝ) := by norm_num; ring
  lipschitzOn_closedBall := by
    intro _R
    apply LipschitzOnWith.of_dist_le_mul
    intro x _hx y _hy
    exact hN.dist_le_mul x y

/-- A continuous linear term has linear growth and its operator norm as a
global Lipschitz constant. -/
def continuousLinear (A : BUC →L[ℝ] BUC) :
    SemilinearHeatBUCLocalData (fun x : BUC ↦ A x) :=
  ofLipschitzWith (fun x : BUC ↦ A x) ‖A‖₊ A.lipschitz

/-- A constant forcing term has constant growth and zero Lipschitz modulus. -/
def const (c : BUC) :
    SemilinearHeatBUCLocalData (fun _x : BUC ↦ c) where
  continuous := continuous_const
  growth _R := ‖c‖₊
  lipschitz _R := 0
  norm_le_growth := by
    intro _R _x _hx
    exact le_rfl
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp

/-- The zero nonlinearity has zero growth and zero Lipschitz modulus. -/
def zero : SemilinearHeatBUCLocalData (fun _x : BUC ↦ (0 : BUC)) :=
  const (0 : BUC)

/-- Local-moduli packages are closed under pointwise negation. -/
def neg {N : BUC → BUC} (dataN : SemilinearHeatBUCLocalData N) :
    SemilinearHeatBUCLocalData (fun x ↦ -N x) where
  continuous := dataN.continuous.neg
  growth := dataN.growth
  lipschitz := dataN.lipschitz
  norm_le_growth := by
    intro R x hx
    simpa using dataN.norm_le_growth R x hx
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa using (dataN.lipschitzOn_closedBall R).dist_le_mul x hx y hy

/-- Local-moduli packages are closed under pointwise addition. -/
def add {N M : BUC → BUC}
    (dataN : SemilinearHeatBUCLocalData N)
    (dataM : SemilinearHeatBUCLocalData M) :
    SemilinearHeatBUCLocalData (fun x ↦ N x + M x) where
  continuous := dataN.continuous.add dataM.continuous
  growth R := dataN.growth R + dataM.growth R
  lipschitz R := dataN.lipschitz R + dataM.lipschitz R
  norm_le_growth := by
    intro R x hx
    calc
      ‖N x + M x‖ ≤ ‖N x‖ + ‖M x‖ := norm_add_le _ _
      _ ≤ (dataN.growth R : ℝ) + (dataM.growth R : ℝ) :=
        add_le_add (dataN.norm_le_growth R x hx)
          (dataM.norm_le_growth R x hx)
      _ = ((dataN.growth R + dataM.growth R : ℝ≥0) : ℝ) := by norm_num
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hN := (dataN.lipschitzOn_closedBall R).dist_le_mul x hx y hy
    have hM := (dataM.lipschitzOn_closedBall R).dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm] at hN hM ⊢
    calc
      ‖(N x + M x) - (N y + M y)‖ =
          ‖(N x - N y) + (M x - M y)‖ := by
        congr 1
        abel
      _ ≤ ‖N x - N y‖ + ‖M x - M y‖ := norm_add_le _ _
      _ ≤ (dataN.lipschitz R : ℝ) * ‖x - y‖ +
          (dataM.lipschitz R : ℝ) * ‖x - y‖ := add_le_add hN hM
      _ = ((dataN.lipschitz R + dataM.lipschitz R : ℝ≥0) : ℝ) *
          ‖x - y‖ := by norm_num; ring

/-- Local-moduli packages are closed under pointwise subtraction. -/
def sub {N M : BUC → BUC}
    (dataN : SemilinearHeatBUCLocalData N)
    (dataM : SemilinearHeatBUCLocalData M) :
    SemilinearHeatBUCLocalData (fun x ↦ N x - M x) := by
  simpa only [sub_eq_add_neg] using add dataN (neg dataM)

/-- Translation by a fixed background state has growth `‖c‖ + R` and
Lipschitz modulus one. -/
def translate (c : BUC) :
    SemilinearHeatBUCLocalData (fun x : BUC ↦ x + c) := by
  apply ofLipschitzWith (fun x : BUC ↦ x + c) 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa using dist_add_right x y c

/-- Local-moduli packages compose.  The outer modulus is evaluated at the
inner growth bound. -/
def comp {N M : BUC → BUC}
    (dataM : SemilinearHeatBUCLocalData M)
    (dataN : SemilinearHeatBUCLocalData N) :
    SemilinearHeatBUCLocalData (fun x ↦ M (N x)) where
  continuous := dataM.continuous.comp dataN.continuous
  growth R := dataM.growth (dataN.growth R)
  lipschitz R := dataM.lipschitz (dataN.growth R) * dataN.lipschitz R
  norm_le_growth := by
    intro R x hx
    apply dataM.norm_le_growth (dataN.growth R) (N x)
    exact dataN.norm_le_growth R x hx
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxNorm : ‖x‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyNorm : ‖y‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hNxNorm : ‖N x‖ ≤ (dataN.growth R : ℝ) :=
      dataN.norm_le_growth R x hxNorm
    have hNyNorm : ‖N y‖ ≤ (dataN.growth R : ℝ) :=
      dataN.norm_le_growth R y hyNorm
    have hNx : N x ∈ Metric.closedBall (0 : BUC) (dataN.growth R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hNxNorm
    have hNy : N y ∈ Metric.closedBall (0 : BUC) (dataN.growth R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hNyNorm
    have houter :=
      (dataM.lipschitzOn_closedBall (dataN.growth R)).dist_le_mul
        (N x) hNx (N y) hNy
    have hinner := (dataN.lipschitzOn_closedBall R).dist_le_mul x hx y hy
    calc
      dist (M (N x)) (M (N y)) ≤
          (dataM.lipschitz (dataN.growth R) : ℝ) * dist (N x) (N y) :=
        houter
      _ ≤ (dataM.lipschitz (dataN.growth R) : ℝ) *
          ((dataN.lipschitz R : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left hinner
          (dataM.lipschitz (dataN.growth R)).property
      _ = ((dataM.lipschitz (dataN.growth R) * dataN.lipschitz R :
          ℝ≥0) : ℝ) * dist x y := by norm_num; ring

/-- Precomposition by a background translation. -/
def translateInput {N : BUC → BUC}
    (dataN : SemilinearHeatBUCLocalData N) (c : BUC) :
    SemilinearHeatBUCLocalData (fun x ↦ N (x + c)) :=
  comp dataN (translate c)

/-- Recenter a nonlinearity at a background state.  The resulting perturbative
remainder is `x ↦ N(x+c) - N(c)` and vanishes at zero. -/
def recenter {N : BUC → BUC}
    (dataN : SemilinearHeatBUCLocalData N) (c : BUC) :
    SemilinearHeatBUCLocalData (fun x ↦ N (x + c) - N c) where
  continuous :=
    (dataN.continuous.comp (continuous_id.add continuous_const)).sub
      continuous_const
  growth R := dataN.lipschitz (‖c‖₊ + R) * R
  lipschitz R := dataN.lipschitz (‖c‖₊ + R)
  norm_le_growth := by
    intro R x hx
    have hxcNorm : ‖x + c‖ ≤ ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      calc
        ‖x + c‖ ≤ ‖x‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (R : ℝ) + ‖c‖ := add_le_add hx le_rfl
        _ = ((‖c‖₊ + R : ℝ≥0) : ℝ) := by norm_num [add_comm]
    have hcNorm : ‖c‖ ≤ ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      norm_num
    have hxc : x + c ∈ Metric.closedBall (0 : BUC)
        ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxcNorm
    have hc : c ∈ Metric.closedBall (0 : BUC)
        ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hcNorm
    have hlocal := (dataN.lipschitzOn_closedBall (‖c‖₊ + R)).dist_le_mul
      (x + c) hxc c hc
    calc
      ‖N (x + c) - N c‖ ≤
          (dataN.lipschitz (‖c‖₊ + R) : ℝ) * ‖x‖ := by
        simpa [dist_eq_norm] using hlocal
      _ ≤ (dataN.lipschitz (‖c‖₊ + R) : ℝ) * (R : ℝ) :=
        mul_le_mul_of_nonneg_left hx (dataN.lipschitz (‖c‖₊ + R)).property
      _ = ((dataN.lipschitz (‖c‖₊ + R) * R : ℝ≥0) : ℝ) := by norm_num
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxNorm : ‖x‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyNorm : ‖y‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hxcNorm : ‖x + c‖ ≤ ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      calc
        ‖x + c‖ ≤ ‖x‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (R : ℝ) + ‖c‖ := add_le_add hxNorm le_rfl
        _ = ((‖c‖₊ + R : ℝ≥0) : ℝ) := by norm_num [add_comm]
    have hycNorm : ‖y + c‖ ≤ ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      calc
        ‖y + c‖ ≤ ‖y‖ + ‖c‖ := norm_add_le _ _
        _ ≤ (R : ℝ) + ‖c‖ := add_le_add hyNorm le_rfl
        _ = ((‖c‖₊ + R : ℝ≥0) : ℝ) := by norm_num [add_comm]
    have hxc : x + c ∈ Metric.closedBall (0 : BUC)
        ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxcNorm
    have hyc : y + c ∈ Metric.closedBall (0 : BUC)
        ((‖c‖₊ + R : ℝ≥0) : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hycNorm
    have hlocal := (dataN.lipschitzOn_closedBall (‖c‖₊ + R)).dist_le_mul
      (x + c) hxc (y + c) hyc
    simpa [dist_sub_right] using hlocal

@[simp]
theorem recenter_apply_zero {N : BUC → BUC}
    (_dataN : SemilinearHeatBUCLocalData N) (c : BUC) :
    (fun x : BUC ↦ N (x + c) - N c) 0 = 0 := by
  simp

/-- A bounded bilinear contraction of two separately controlled nonlinear
expressions.  Its Lipschitz modulus is the usual product-rule bound
`β (L₁ G₂ + G₁ L₂)`. -/
def bilinearComp {N M : BUC → BUC}
    (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ z : BUC, ‖B z‖ ≤ (β : ℝ) * ‖z‖)
    (dataN : SemilinearHeatBUCLocalData N)
    (dataM : SemilinearHeatBUCLocalData M) :
    SemilinearHeatBUCLocalData (fun x ↦ B (N x) (M x)) where
  continuous :=
    (B.continuous.comp dataN.continuous).clm_apply dataM.continuous
  growth R := β * dataN.growth R * dataM.growth R
  lipschitz R := β *
    (dataN.lipschitz R * dataM.growth R +
      dataN.growth R * dataM.lipschitz R)
  norm_le_growth := by
    intro R x hx
    have hNx := dataN.norm_le_growth R x hx
    have hMx := dataM.norm_le_growth R x hx
    calc
      ‖B (N x) (M x)‖ ≤ ‖B (N x)‖ * ‖M x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((β : ℝ) * ‖N x‖) * ‖M x‖ :=
        mul_le_mul_of_nonneg_right (hB (N x)) (norm_nonneg (M x))
      _ ≤ ((β : ℝ) * (dataN.growth R : ℝ)) *
          (dataM.growth R : ℝ) := by gcongr
      _ = ((β * dataN.growth R * dataM.growth R : ℝ≥0) : ℝ) := by
        norm_num
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxNorm : ‖x‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hyNorm : ‖y‖ ≤ (R : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have hNx := dataN.norm_le_growth R x hxNorm
    have hNy := dataN.norm_le_growth R y hyNorm
    have hMx := dataM.norm_le_growth R x hxNorm
    have hMy := dataM.norm_le_growth R y hyNorm
    have hNdiff := (dataN.lipschitzOn_closedBall R).dist_le_mul x hx y hy
    have hMdiff := (dataM.lipschitzOn_closedBall R).dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm] at hNdiff hMdiff ⊢
    have hident :
        B (N x) (M x) - B (N y) (M y) =
          B (N x - N y) (M x) + B (N y) (M x - M y) := by
      simp [map_sub]
    rw [hident]
    calc
      ‖B (N x - N y) (M x) + B (N y) (M x - M y)‖ ≤
          ‖B (N x - N y) (M x)‖ +
            ‖B (N y) (M x - M y)‖ := norm_add_le _ _
      _ ≤ (((β : ℝ) * ‖N x - N y‖) * ‖M x‖) +
          (((β : ℝ) * ‖N y‖) * ‖M x - M y‖) := by
        apply add_le_add
        · exact (ContinuousLinearMap.le_opNorm (B (N x - N y)) (M x)).trans
            (mul_le_mul_of_nonneg_right (hB (N x - N y))
              (norm_nonneg (M x)))
        · exact (ContinuousLinearMap.le_opNorm (B (N y)) (M x - M y)).trans
            (mul_le_mul_of_nonneg_right (hB (N y))
              (norm_nonneg (M x - M y)))
      _ ≤ (((β : ℝ) *
              ((dataN.lipschitz R : ℝ) * ‖x - y‖)) *
            (dataM.growth R : ℝ)) +
          (((β : ℝ) * (dataN.growth R : ℝ)) *
            ((dataM.lipschitz R : ℝ) * ‖x - y‖)) := by
        gcongr
      _ = ((β * (dataN.lipschitz R * dataM.growth R +
          dataN.growth R * dataM.lipschitz R) : ℝ≥0) : ℝ) *
          ‖x - y‖ := by norm_num; ring

/-- A bounded diagonal bilinear term has the expected quadratic growth and
linear-in-radius Lipschitz modulus. -/
def quadratic (B : BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ℝ≥0)
    (hB : ∀ x : BUC, ‖B x‖ ≤ (β : ℝ) * ‖x‖) :
    SemilinearHeatBUCLocalData (quadraticOfCLM B) where
  continuous := continuous_quadraticOfCLM B
  growth R := β * R ^ 2
  lipschitz R := 2 * β * R
  norm_le_growth := by
    intro R x hx
    calc
      ‖quadraticOfCLM B x‖ ≤ (β : ℝ) * ‖x‖ ^ 2 :=
        norm_quadraticOfCLM_le_of_bound B β hB x
      _ ≤ (β : ℝ) * (R : ℝ) ^ 2 := by
        gcongr
      _ = ((β * R ^ 2 : ℝ≥0) : ℝ) := by norm_num
  lipschitzOn_closedBall := by
    intro R
    have h := lipschitzOnWith_quadraticOfCLM_closedBall_center_of_bound
      B β hB (0 : BUC) R
    simpa [quadraticBUCBallLipschitzConstant] using h

end SemilinearHeatBUCLocalData

end Poincare
