import Poincare.Global.SemilinearHeatBUCLocalDataOperations
import Poincare.Global.SemilinearHeatBUCLocalMaximal

/-!
# Finite polynomial and DeTurck-shaped semilinear heat nonlinearities

Finite coordinate expressions are built from sums, bounded quadratic
contractions, and nested locally Lipschitz operations.  This module supplies
explicit summed bounded-ball moduli, packages a concrete DeTurck-shaped
remainder, and specializes the uniform local and maximal-time theories to it.
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

namespace SemilinearHeatBUCLocalData

/-- A finite sum of locally controlled nonlinearities is locally controlled
with the sums of their growth and Lipschitz moduli. -/
def finsetSum {ι : Type*} (s : Finset ι) (N : ι → BUC → BUC)
    (data : ∀ i, SemilinearHeatBUCLocalData (N i)) :
    SemilinearHeatBUCLocalData (fun x ↦ ∑ i ∈ s, N i x) where
  continuous := continuous_finsetSum s (by
    intro i hi
    exact (data i).continuous)
  growth R := ∑ i ∈ s, (data i).growth R
  lipschitz R := ∑ i ∈ s, (data i).lipschitz R
  norm_le_growth := by
    intro R x hx
    calc
      ‖∑ i ∈ s, N i x‖ ≤ ∑ i ∈ s, ‖N i x‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ((data i).growth R : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (data i).norm_le_growth R x hx
      _ = ((∑ i ∈ s, (data i).growth R : ℝ≥0) : ℝ) := by norm_num
  lipschitzOn_closedBall := by
    intro R
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm, ← Finset.sum_sub_distrib]
    calc
      ‖∑ i ∈ s, (N i x - N i y)‖ ≤
          ∑ i ∈ s, ‖N i x - N i y‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ((data i).lipschitz R : ℝ) * ‖x - y‖ := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [dist_eq_norm] using
          ((data i).lipschitzOn_closedBall R).dist_le_mul x hx y hy
      _ = ((∑ i ∈ s, (data i).lipschitz R : ℝ≥0) : ℝ) * ‖x - y‖ := by
        rw [← Finset.sum_mul]
        norm_num

@[simp]
theorem finsetSum_growth {ι : Type*} (s : Finset ι) (N : ι → BUC → BUC)
    (data : ∀ i, SemilinearHeatBUCLocalData (N i)) (R : ℝ≥0) :
    (finsetSum s N data).growth R = ∑ i ∈ s, (data i).growth R :=
  rfl

@[simp]
theorem finsetSum_lipschitz {ι : Type*} (s : Finset ι) (N : ι → BUC → BUC)
    (data : ∀ i, SemilinearHeatBUCLocalData (N i)) (R : ℝ≥0) :
    (finsetSum s N data).lipschitz R = ∑ i ∈ s, (data i).lipschitz R :=
  rfl

/-- A finite sum of nested nonlinearities, with each outer modulus evaluated
at the corresponding inner growth bound. -/
def finsetCompSum {ι : Type*} (s : Finset ι)
    (outer inner : ι → BUC → BUC)
    (outerData : ∀ i, SemilinearHeatBUCLocalData (outer i))
    (innerData : ∀ i, SemilinearHeatBUCLocalData (inner i)) :
    SemilinearHeatBUCLocalData (fun x ↦ ∑ i ∈ s, outer i (inner i x)) :=
  finsetSum s (fun i x ↦ outer i (inner i x))
    (fun i ↦ comp (outerData i) (innerData i))

@[simp]
theorem finsetCompSum_growth {ι : Type*} (s : Finset ι)
    (outer inner : ι → BUC → BUC)
    (outerData : ∀ i, SemilinearHeatBUCLocalData (outer i))
    (innerData : ∀ i, SemilinearHeatBUCLocalData (inner i)) (R : ℝ≥0) :
    (finsetCompSum s outer inner outerData innerData).growth R =
      ∑ i ∈ s, (outerData i).growth ((innerData i).growth R) :=
  rfl

@[simp]
theorem finsetCompSum_lipschitz {ι : Type*} (s : Finset ι)
    (outer inner : ι → BUC → BUC)
    (outerData : ∀ i, SemilinearHeatBUCLocalData (outer i))
    (innerData : ∀ i, SemilinearHeatBUCLocalData (inner i)) (R : ℝ≥0) :
    (finsetCompSum s outer inner outerData innerData).lipschitz R =
      ∑ i ∈ s,
        (outerData i).lipschitz ((innerData i).growth R) *
          (innerData i).lipschitz R :=
  rfl

/-- A finite sum of bounded bilinear contractions applied to pairs of
separately controlled expressions. -/
def finsetBilinearCompSum {ι : Type*} (s : Finset ι)
    (B : ι → BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ι → ℝ≥0)
    (hB : ∀ i z, ‖B i z‖ ≤ (β i : ℝ) * ‖z‖)
    (left right : ι → BUC → BUC)
    (leftData : ∀ i, SemilinearHeatBUCLocalData (left i))
    (rightData : ∀ i, SemilinearHeatBUCLocalData (right i)) :
    SemilinearHeatBUCLocalData
      (fun x ↦ ∑ i ∈ s, B i (left i x) (right i x)) :=
  finsetSum s (fun i x ↦ B i (left i x) (right i x))
    (fun i ↦ bilinearComp (B i) (β i) (hB i) (leftData i) (rightData i))

@[simp]
theorem finsetBilinearCompSum_growth {ι : Type*} (s : Finset ι)
    (B : ι → BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ι → ℝ≥0)
    (hB : ∀ i z, ‖B i z‖ ≤ (β i : ℝ) * ‖z‖)
    (left right : ι → BUC → BUC)
    (leftData : ∀ i, SemilinearHeatBUCLocalData (left i))
    (rightData : ∀ i, SemilinearHeatBUCLocalData (right i)) (R : ℝ≥0) :
    (finsetBilinearCompSum s B β hB left right leftData rightData).growth R =
      ∑ i ∈ s, β i * (leftData i).growth R * (rightData i).growth R :=
  rfl

@[simp]
theorem finsetBilinearCompSum_lipschitz {ι : Type*} (s : Finset ι)
    (B : ι → BUC →L[ℝ] BUC →L[ℝ] BUC) (β : ι → ℝ≥0)
    (hB : ∀ i z, ‖B i z‖ ≤ (β i : ℝ) * ‖z‖)
    (left right : ι → BUC → BUC)
    (leftData : ∀ i, SemilinearHeatBUCLocalData (left i))
    (rightData : ∀ i, SemilinearHeatBUCLocalData (right i)) (R : ℝ≥0) :
    (finsetBilinearCompSum s B β hB left right leftData rightData).lipschitz R =
      ∑ i ∈ s, β i *
        ((leftData i).lipschitz R * (rightData i).growth R +
          (leftData i).growth R * (rightData i).lipschitz R) :=
  rfl

end SemilinearHeatBUCLocalData

/-- Concrete algebraic data for a DeTurck-shaped coordinate remainder:

* a bounded linear lower-order term;
* finitely many bounded quadratic contractions;
* finitely many nested locally Lipschitz terms.

The principal heat operator is already carried by the semigroup and is not
included here. -/
structure DeTurckShapedBUCRemainderData (ι κ : Type*) where
  linear : BUC →L[ℝ] BUC
  quadraticTerms : Finset ι
  quadratic : ι → BUC →L[ℝ] BUC →L[ℝ] BUC
  quadraticBound : ι → ℝ≥0
  quadratic_bound : ∀ i x,
    ‖quadratic i x‖ ≤ (quadraticBound i : ℝ) * ‖x‖
  compositionTerms : Finset κ
  outer : κ → BUC → BUC
  inner : κ → BUC → BUC
  outerData : ∀ i, SemilinearHeatBUCLocalData (outer i)
  innerData : ∀ i, SemilinearHeatBUCLocalData (inner i)
  bilinearTerms : Finset κ
  bilinear : κ → BUC →L[ℝ] BUC →L[ℝ] BUC
  bilinearBound : κ → ℝ≥0
  bilinear_bound : ∀ i z,
    ‖bilinear i z‖ ≤ (bilinearBound i : ℝ) * ‖z‖
  left : κ → BUC → BUC
  right : κ → BUC → BUC
  leftData : ∀ i, SemilinearHeatBUCLocalData (left i)
  rightData : ∀ i, SemilinearHeatBUCLocalData (right i)

namespace DeTurckShapedBUCRemainderData

variable {ι κ : Type*}

/-- The assembled lower-order coordinate nonlinearity. -/
def nonlinearity (D : DeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) : BUC → BUC :=
  fun x ↦ D.linear x +
    (∑ i ∈ D.quadraticTerms, quadraticOfCLM (D.quadratic i) x) +
    (∑ j ∈ D.compositionTerms, D.outer j (D.inner j x)) +
    ∑ j ∈ D.bilinearTerms,
      D.bilinear j (D.left j x) (D.right j x)

/-- Explicit bounded-ball moduli for the assembled DeTurck-shaped
remainder. -/
def localData (D : DeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) :
    SemilinearHeatBUCLocalData D.nonlinearity := by
  let linearData := SemilinearHeatBUCLocalData.continuousLinear D.linear
  let quadraticData := SemilinearHeatBUCLocalData.finsetSum
    D.quadraticTerms (fun i ↦ quadraticOfCLM (D.quadratic i))
    (fun i ↦ SemilinearHeatBUCLocalData.quadratic
      (D.quadratic i) (D.quadraticBound i) (D.quadratic_bound i))
  let compositionData := SemilinearHeatBUCLocalData.finsetCompSum
    D.compositionTerms D.outer D.inner D.outerData D.innerData
  let bilinearData := SemilinearHeatBUCLocalData.finsetBilinearCompSum
    D.bilinearTerms D.bilinear D.bilinearBound D.bilinear_bound
    D.left D.right D.leftData D.rightData
  simpa only [nonlinearity] using
    SemilinearHeatBUCLocalData.add
      (SemilinearHeatBUCLocalData.add
        (SemilinearHeatBUCLocalData.add linearData quadraticData)
        compositionData)
      bilinearData

/-- The growth modulus is the sum of the linear, quadratic, and nested-term
bounds. -/
theorem localData_growth (D : DeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.growth R =
      ‖D.linear 0‖₊ + ‖D.linear‖₊ * R +
        (∑ i ∈ D.quadraticTerms, D.quadraticBound i * R ^ 2) +
        (∑ j ∈ D.compositionTerms,
          (D.outerData j).growth ((D.innerData j).growth R)) +
        ∑ j ∈ D.bilinearTerms,
          D.bilinearBound j * (D.leftData j).growth R *
            (D.rightData j).growth R := by
  rfl

/-- The Lipschitz modulus is the corresponding finite sum. -/
theorem localData_lipschitz (D : DeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.lipschitz R =
      ‖D.linear‖₊ +
        (∑ i ∈ D.quadraticTerms, 2 * D.quadraticBound i * R) +
        (∑ j ∈ D.compositionTerms,
          (D.outerData j).lipschitz ((D.innerData j).growth R) *
            (D.innerData j).lipschitz R) +
        ∑ j ∈ D.bilinearTerms, D.bilinearBound j *
          ((D.leftData j).lipschitz R * (D.rightData j).growth R +
            (D.leftData j).growth R * (D.rightData j).lipschitz R) := by
  rfl

/-- Explicit common lifespan on the initial-data ball `‖u₀‖ ≤ K`. -/
abbrev uniformLifespan (D : DeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) (K : ℝ≥0) : ℝ≥0 :=
  semilinearHeatBUCUniformLifespan D.localData K

/-- One positive time works for every bounded datum for the assembled
DeTurck-shaped equation. -/
theorem exists_single_time_fixedPoints
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) :
    0 < D.uniformLifespan K ∧
      ∀ u₀ : BUC, ‖u₀‖ ≤ (K : ℝ) →
        ∃ u ∈ Metric.closedBall
            (heatLinearBUCPath (D.uniformLifespan K) u₀) (1 : ℝ),
          semilinearHeatBUCPicard (D.uniformLifespan K) u₀ D.nonlinearity
              D.localData.continuous u = u ∧
          ∀ v ∈ Metric.closedBall
              (heatLinearBUCPath (D.uniformLifespan K) u₀) (1 : ℝ),
            semilinearHeatBUCPicard (D.uniformLifespan K) u₀ D.nonlinearity
                D.localData.continuous v = v → v = u := by
  exact exists_single_time_semilinearHeatBUC_fixedPoints_local
    (E := E) (F := F) K D.nonlinearity D.localData

/-- Canonical common-time solution for the assembled remainder. -/
noncomputable def uniformSolution
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (D.uniformLifespan K) BUC :=
  semilinearHeatBUCUniformLocalSolution K D.nonlinearity D.localData u₀

/-- The selected DeTurck-shaped solution satisfies its corrected mild
equation. -/
theorem uniformSolution_isFixedPt
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCPicard (D.uniformLifespan K) (u₀ : BUC)
        D.nonlinearity D.localData.continuous (D.uniformSolution K u₀) =
      D.uniformSolution K u₀ :=
  semilinearHeatBUCUniformLocalSolution_isFixedPt
    (E := E) (F := F) K D.nonlinearity D.localData u₀

/-- The selected solution stays uniformly in the zero-centered `K + 1`
ball. -/
theorem norm_uniformSolution_le
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    ‖D.uniformSolution K u₀ t‖ ≤ ((K + 1 : ℝ≥0) : ℝ) :=
  norm_semilinearHeatBUCUniformLocalSolution_le
    (E := E) (F := F) K D.nonlinearity D.localData u₀ t

/-- Exact corrected mild identity for the assembled remainder. -/
theorem uniformSolution_mild
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    D.uniformSolution K u₀ t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) (u₀ : BUC) +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (D.nonlinearity (D.uniformSolution K u₀
              (Set.projIcc 0 (D.uniformLifespan K : ℝ)
                (D.uniformLifespan K).property s))) :=
  semilinearHeatBUCUniformLocalSolution_mild
    (E := E) (F := F) K D.nonlinearity D.localData u₀ t

/-- The selected solution starts from the prescribed datum. -/
theorem uniformSolution_zero
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    D.uniformSolution K u₀
        (⟨0, ⟨le_rfl, (D.uniformLifespan K).property⟩⟩ :
          Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) = (u₀ : BUC) :=
  semilinearHeatBUCUniformLocalSolution_zero
    (E := E) (F := F) K D.nonlinearity D.localData u₀

/-- For generator-domain data, the assembled solution has initial right
derivative `A u₀ + D.nonlinearity u₀`. -/
theorem uniformSolution_hasDerivWithinAt_zero
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u₀ : BUC) Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      (Au₀ + D.nonlinearity (u₀ : BUC))
      (Set.Icc 0 (D.uniformLifespan K : ℝ)) 0 :=
  semilinearHeatBUCUniformLocalSolution_hasDerivWithinAt_zero
    (E := E) (F := F) K D.nonlinearity D.localData u₀ Au₀ hu₀

/-- The DeTurck-shaped solution map is Lipschitz on every bounded initial-data
ball. -/
theorem lipschitzWith_uniformSolution
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (K : ℝ≥0) :
    LipschitzWith
      (heatDuhamelBUCIntrinsicStabilityConstant
        (D.uniformLifespan K)
        (semilinearHeatBUCUniformBallLipschitzConstant D.localData K 1)
        (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one D.localData K))
      (fun u₀ : SemilinearBUCBoundedData (E := E) (F := F) K ↦
        D.uniformSolution K u₀) :=
  lipschitzWith_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K D.nonlinearity D.localData

/-- Compatible compact families for the assembled DeTurck-shaped equation. -/
abbrev CompactFamily
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) :=
  SemilinearHeatBUCCompactFamily Tmax D.nonlinearity D.localData.continuous u₀

/-- Finite maximal-time norm blow-up for the assembled remainder. -/
theorem maximalTime_norm_unbounded_of_maximal
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) (fam : D.CompactFamily Tmax u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : SemilinearBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ :=
  semilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (E := E) (F := F) Tmax D.nonlinearity D.localData u₀ fam hmax

/-- Terminal form: every threshold is crossed after every compact time below
the maximal lifespan. -/
theorem maximalTime_norm_unbounded_after_of_maximal
    (D : DeTurckShapedBUCRemainderData (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) (fam : D.CompactFamily Tmax u₀)
    (hmax : fam.IsMaximal)
    (S : SemilinearBUCCompactTime Tmax) (K : ℝ≥0) :
    ∃ (T : SemilinearBUCCompactTime Tmax)
      (_hST : (S : ℝ≥0) ≤ (T : ℝ≥0))
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      ((S : ℝ≥0) : ℝ) < (t : ℝ) ∧ (K : ℝ) < ‖fam.path T t‖ :=
  semilinearHeatBUC_maximalTime_norm_unbounded_after_of_maximal
    (E := E) (F := F) Tmax D.nonlinearity D.localData u₀ fam hmax S K

end DeTurckShapedBUCRemainderData

end Poincare
