import Poincare.Global.SemilinearHeatBUCPolynomialLocalData

/-!
# Recentered DeTurck-shaped semilinear heat equations

Ricci--DeTurck is solved for a perturbation of a fixed background.  Given an
assembled coordinate remainder `N` and background `c`, the perturbative
nonlinearity is

`N_c(x) = N(x + c) - N(c)`.

It vanishes at zero and has the sharp local growth bound
`L(‖c‖ + R) R`.  This module specializes uniform local existence, canonical
solution, endpoint continuation, and maximal-time blow-up to that recentered
equation.  When the background is stationary (`N(c)=0`), the same zero path
also solves the unrecentered shifted equation `x ↦ N(x+c)`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction
  BigOperators

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- An assembled DeTurck-shaped remainder together with the background state
about which it is recentered.  The base package includes bounded linear,
finite quadratic, finite unary-composition, and finite bilinear-composition
terms. -/
structure RecenteredDeTurckShapedBUCRemainderData (ι κ : Type*) where
  base : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ
  background : BUC

namespace RecenteredDeTurckShapedBUCRemainderData

variable {ι κ : Type*}

/-- The perturbative coordinate nonlinearity. -/
def nonlinearity (D : RecenteredDeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) : BUC → BUC :=
  fun x ↦ D.base.nonlinearity (x + D.background) -
    D.base.nonlinearity D.background

/-- Expanded formula exhibiting the bounded linear, quadratic, unary
composition, and bilinear-composition terms before recentering. -/
theorem nonlinearity_apply_expanded
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (x : BUC) :
    D.nonlinearity x =
      (D.base.linear (x + D.background) +
        (∑ i ∈ D.base.quadraticTerms,
          quadraticOfCLM (D.base.quadratic i) (x + D.background)) +
        (∑ j ∈ D.base.compositionTerms,
          D.base.outer j (D.base.inner j (x + D.background))) +
        ∑ j ∈ D.base.bilinearTerms,
          D.base.bilinear j
            (D.base.left j (x + D.background))
            (D.base.right j (x + D.background))) -
      (D.base.linear D.background +
        (∑ i ∈ D.base.quadraticTerms,
          quadraticOfCLM (D.base.quadratic i) D.background) +
        (∑ j ∈ D.base.compositionTerms,
          D.base.outer j (D.base.inner j D.background)) +
        ∑ j ∈ D.base.bilinearTerms,
          D.base.bilinear j
            (D.base.left j D.background)
            (D.base.right j D.background)) :=
  rfl

/-- The recentered nonlinearity vanishes at the zero perturbation. -/
@[simp]
theorem nonlinearity_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    D.nonlinearity 0 = 0 := by
  simp [nonlinearity]

/-- Sharp local data for the perturbative remainder. -/
def localData (D : RecenteredDeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) :
    SemilinearHeatBUCLocalData D.nonlinearity :=
  SemilinearHeatBUCLocalData.recenter D.base.localData D.background

/-- Recentered growth vanishes linearly with the perturbation radius. -/
theorem localData_growth
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.growth R =
      D.base.localData.lipschitz (‖D.background‖₊ + R) * R :=
  rfl

/-- The recentered Lipschitz modulus is the base modulus on the enlarged ball
containing the translated perturbations. -/
theorem localData_lipschitz
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.lipschitz R =
      D.base.localData.lipschitz (‖D.background‖₊ + R) :=
  rfl

/-- If the background is stationary, recentering is just input translation. -/
theorem nonlinearity_eq_shift_of_stationary
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (hstationary : D.base.nonlinearity D.background = 0) :
    D.nonlinearity = fun x ↦ D.base.nonlinearity (x + D.background) := by
  funext x
  simp [nonlinearity, hstationary]

/-- Common lifespan on the perturbation-data ball `‖u₀‖ ≤ K`. -/
abbrev uniformLifespan
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) : ℝ≥0 :=
  semilinearHeatBUCUniformLifespan D.localData K

/-- Uniform local existence and uniqueness for the recentered equation. -/
theorem exists_single_time_fixedPoints
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    0 < D.uniformLifespan K ∧
      ∀ u₀ : BUC, ‖u₀‖ ≤ (K : ℝ) →
        ∃ u ∈ Metric.closedBall
            (heatLinearBUCPath (D.uniformLifespan K) u₀) (1 : ℝ),
          semilinearHeatBUCPicard (D.uniformLifespan K) u₀ D.nonlinearity
              D.localData.continuous u = u ∧
          ∀ v ∈ Metric.closedBall
              (heatLinearBUCPath (D.uniformLifespan K) u₀) (1 : ℝ),
            semilinearHeatBUCPicard (D.uniformLifespan K) u₀ D.nonlinearity
                D.localData.continuous v = v → v = u :=
  exists_single_time_semilinearHeatBUC_fixedPoints_local
    (E := E) (F := F) K D.nonlinearity D.localData

/-- Canonical common-time recentered solution. -/
noncomputable def uniformSolution
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (D.uniformLifespan K) BUC :=
  semilinearHeatBUCUniformLocalSolution K D.nonlinearity D.localData u₀

/-- The selected perturbative path satisfies the corrected mild equation. -/
theorem uniformSolution_isFixedPt
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCPicard (D.uniformLifespan K) (u₀ : BUC)
        D.nonlinearity D.localData.continuous (D.uniformSolution K u₀) =
      D.uniformSolution K u₀ :=
  semilinearHeatBUCUniformLocalSolution_isFixedPt
    (E := E) (F := F) K D.nonlinearity D.localData u₀

/-- Zero initial perturbation as an element of every bounded data ball. -/
def zeroBoundedData
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    SemilinearBUCBoundedData (E := E) (F := F) K :=
  ⟨0, by simp⟩

/-- The zero perturbation path. -/
def zeroPath
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (T : ℝ≥0) : DuhamelPath T BUC :=
  constantDuhamelPathGeneric T (0 : BUC)

@[simp]
theorem zeroPath_apply
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (T : ℝ≥0)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    D.zeroPath T t = 0 :=
  rfl

/-- Since the recentered nonlinearity vanishes at zero, the zero path is a
fixed point on every time interval. -/
theorem zeroPath_isFixedPt
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (T : ℝ≥0) :
    semilinearHeatBUCPicard T (0 : BUC) D.nonlinearity
        D.localData.continuous (D.zeroPath T) = D.zeroPath T := by
  apply ContinuousMap.ext
  intro t
  simp [semilinearHeatBUCPicard_apply, zeroPath, nonlinearity]

/-- The canonical solution selected from zero perturbation data is exactly
the zero path. -/
theorem uniformSolution_zero_eq_zeroPath
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    D.uniformSolution K (D.zeroBoundedData K) =
      D.zeroPath (D.uniformLifespan K) := by
  let T := D.uniformLifespan K
  let z₀ := D.zeroBoundedData K
  have hcenter : heatLinearBUCPath T (z₀ : BUC) = D.zeroPath T := by
    apply ContinuousMap.ext
    intro t
    simp [z₀, zeroBoundedData, zeroPath]
  have hzBall : D.zeroPath T ∈
      Metric.closedBall (heatLinearBUCPath T (z₀ : BUC)) (1 : ℝ) := by
    rw [hcenter]
    exact Metric.mem_closedBall_self (by norm_num)
  have huniq := (Classical.choose_spec
    (exists_semilinearHeatBUCUniformLocalSolution
      (E := E) (F := F) K D.nonlinearity D.localData z₀)).2.2
  have hz := huniq (D.zeroPath T) hzBall (D.zeroPath_isFixedPt T)
  exact hz.symm

/-- The same result stated pointwise. -/
theorem uniformSolution_zero_apply
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    D.uniformSolution K (D.zeroBoundedData K) t = 0 := by
  rw [D.uniformSolution_zero_eq_zeroPath K]
  rfl

/-- The unrecentered shifted nonlinearity and its explicit local data. -/
def shiftedNonlinearity
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) : BUC → BUC :=
  fun x ↦ D.base.nonlinearity (x + D.background)

def shiftedLocalData
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    SemilinearHeatBUCLocalData D.shiftedNonlinearity :=
  SemilinearHeatBUCLocalData.translateInput D.base.localData D.background

/-- For a stationary background, the zero perturbation also solves the
unrecentered shifted equation on every interval. -/
theorem zeroPath_isShiftedFixedPt_of_stationary
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (hstationary : D.base.nonlinearity D.background = 0)
    (T : ℝ≥0) :
    semilinearHeatBUCPicard T (0 : BUC) D.shiftedNonlinearity
        D.shiftedLocalData.continuous (D.zeroPath T) = D.zeroPath T := by
  apply ContinuousMap.ext
  intro t
  simp [semilinearHeatBUCPicard_apply, shiftedNonlinearity, zeroPath,
    hstationary]

/-- Common lifespan for the unrecentered shifted equation. -/
abbrev shiftedUniformLifespan
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) : ℝ≥0 :=
  semilinearHeatBUCUniformLifespan D.shiftedLocalData K

/-- Canonical short-time solution for the unrecentered shifted equation. -/
noncomputable def shiftedUniformSolution
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (D.shiftedUniformLifespan K) BUC :=
  semilinearHeatBUCUniformLocalSolution K D.shiftedNonlinearity
    D.shiftedLocalData u₀

/-- If the background is stationary, contraction uniqueness selects the zero
path as the canonical shifted solution from zero perturbation data. -/
theorem shiftedUniformSolution_zero_eq_zeroPath_of_stationary
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (hstationary : D.base.nonlinearity D.background = 0)
    (K : ℝ≥0) :
    D.shiftedUniformSolution K (D.zeroBoundedData K) =
      D.zeroPath (D.shiftedUniformLifespan K) := by
  let T := D.shiftedUniformLifespan K
  let z₀ := D.zeroBoundedData K
  have hcenter : heatLinearBUCPath T (z₀ : BUC) = D.zeroPath T := by
    apply ContinuousMap.ext
    intro t
    simp [z₀, zeroBoundedData, zeroPath]
  have hzBall : D.zeroPath T ∈
      Metric.closedBall (heatLinearBUCPath T (z₀ : BUC)) (1 : ℝ) := by
    rw [hcenter]
    exact Metric.mem_closedBall_self (by norm_num)
  have huniq := (Classical.choose_spec
    (exists_semilinearHeatBUCUniformLocalSolution
      (E := E) (F := F) K D.shiftedNonlinearity D.shiftedLocalData z₀)).2.2
  have hz := huniq (D.zeroPath T) hzBall
    (D.zeroPath_isShiftedFixedPt_of_stationary hstationary T)
  exact hz.symm

/-- Pointwise stationary-background zero-solution theorem. -/
theorem shiftedUniformSolution_zero_apply_of_stationary
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (hstationary : D.base.nonlinearity D.background = 0)
    (K : ℝ≥0)
    (t : Set.Icc (0 : ℝ) (D.shiftedUniformLifespan K : ℝ)) :
    D.shiftedUniformSolution K (D.zeroBoundedData K) t = 0 := by
  rw [D.shiftedUniformSolution_zero_eq_zeroPath_of_stationary hstationary K]
  rfl

/-- Compatible compact families for the recentered equation. -/
abbrev CompactFamily
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) :=
  SemilinearHeatBUCCompactFamily Tmax D.nonlinearity D.localData.continuous u₀

/-- Maximal recentered families have unbounded norm. -/
theorem maximalTime_norm_unbounded_of_maximal
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) (fam : D.CompactFamily Tmax u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : SemilinearBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ :=
  semilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (E := E) (F := F) Tmax D.nonlinearity D.localData u₀ fam hmax

/-- Terminal form of maximal-time blow-up for the recentered equation. -/
theorem maximalTime_norm_unbounded_after_of_maximal
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) (fam : D.CompactFamily Tmax u₀)
    (hmax : fam.IsMaximal)
    (S : SemilinearBUCCompactTime Tmax) (K : ℝ≥0) :
    ∃ (T : SemilinearBUCCompactTime Tmax)
      (_hST : (S : ℝ≥0) ≤ (T : ℝ≥0))
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      ((S : ℝ≥0) : ℝ) < (t : ℝ) ∧ (K : ℝ) < ‖fam.path T t‖ :=
  semilinearHeatBUC_maximalTime_norm_unbounded_after_of_maximal
    (E := E) (F := F) Tmax D.nonlinearity D.localData u₀ fam hmax S K

end RecenteredDeTurckShapedBUCRemainderData

end Poincare
