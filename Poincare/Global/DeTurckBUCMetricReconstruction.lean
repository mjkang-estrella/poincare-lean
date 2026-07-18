import Poincare.Global.AffineRecenteredDeTurckSemilinearHeatBUC

/-!
# Reconstructing coordinate metric coefficients from the `BUC` DeTurck solver

The semilinear heat theory produces bounded uniformly continuous tensor-valued
perturbations.  This file makes the next geometric step concrete.  We use the
finite-dimensional Riesz-operator representation of continuous bilinear
forms, add the perturbation back to a uniformly positive background
coefficient, and prove:

* an explicit symmetry-preservation hypothesis is exactly what is needed to
  remain in the metric sector;
* a quantitative `BUC` norm bound preserves uniform positive definiteness;
* the reconstructed coefficient starts from background plus initial
  perturbation;
* its exact initial right derivative is the heat generator plus the full
  shifted DeTurck-shaped nonlinearity.

Thus the abstract fixed point now produces an honest positive-definite
coordinate metric coefficient path.  What is not claimed here is a global
`ContMDiffRiemannianMetric`: that requires spatial regularity and chart-overlap
covariance, as well as identification of the assembled coordinate
nonlinearity with the quasilinear Ricci--DeTurck operator.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology Interval NNReal InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Continuous coordinate covariant two-tensors in their Riesz-operator
representation on the finite-dimensional real inner-product model space. -/
abbrev CoordinateTwoTensor (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] :=
  E →L[ℝ] E

/-- Bounded uniformly continuous two-tensor coefficients on the Euclidean
model.  Symmetry is tracked as a theorem because the full continuous-bilinear
space has the normed vector-space instances required by the heat semigroup. -/
abbrev CoordinateBUCTensor (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : Type _ :=
  BoundedUniformContinuousFunction (E := E)
    (F := CoordinateTwoTensor E)

/-- Evaluate a `BUC` two-tensor coefficient on two coordinate vectors. -/
def coordinateMetricValue (g : CoordinateBUCTensor E)
    (x v w : E) : ℝ :=
  ⟪g.1 x v, w⟫_ℝ

/-- Pointwise symmetry of a coordinate two-tensor coefficient. -/
def IsSymmetricCoordinateTensorCoefficient
    (g : CoordinateBUCTensor E) : Prop :=
  ∀ x v w : E, coordinateMetricValue g x v w =
    coordinateMetricValue g x w v

/-- A uniform positive-definiteness certificate with an explicit coercivity
margin. -/
structure IsUniformlyPositiveCoordinateMetric
    (μ : ℝ) (g : CoordinateBUCTensor E) : Prop where
  symmetric : IsSymmetricCoordinateTensorCoefficient g
  margin_pos : 0 < μ
  lower_bound : ∀ x v : E, μ * ‖v‖ ^ 2 ≤ coordinateMetricValue g x v v

/-- Operator norm controls evaluation of a continuous coordinate two-tensor. -/
theorem abs_coordinateTwoTensor_apply_le
    (B : CoordinateTwoTensor E) (v w : E) :
    |⟪B v, w⟫_ℝ| ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
  calc
    |⟪B v, w⟫_ℝ| ≤ ‖B v‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖v‖) * ‖w‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm B v

/-- The global `BUC` norm controls every pointwise bilinear evaluation. -/
theorem abs_coordinateMetricValue_le
    (h : CoordinateBUCTensor E) (x v w : E) :
    |coordinateMetricValue h x v w| ≤ ‖h‖ * ‖v‖ * ‖w‖ := by
  calc
    |coordinateMetricValue h x v w| ≤ ‖h.1 x‖ * ‖v‖ * ‖w‖ := by
      simpa [coordinateMetricValue] using
        abs_coordinateTwoTensor_apply_le (E := E) (h.1 x) v w
    _ ≤ ‖h‖ * ‖v‖ * ‖w‖ := by
      gcongr
      exact BoundedContinuousFunction.norm_coe_le_norm
        h.1 x

/-- Evaluation converts addition of `BUC` operator coefficients into scalar
addition. -/
theorem coordinateMetricValue_add
    (g h : CoordinateBUCTensor E) (x v w : E) :
    coordinateMetricValue (g + h) x v w =
      coordinateMetricValue g x v w + coordinateMetricValue h x v w := by
  change ⟪(g.1 x + h.1 x) v, w⟫_ℝ =
    ⟪g.1 x v, w⟫_ℝ + ⟪h.1 x v, w⟫_ℝ
  rw [ContinuousLinearMap.add_apply, inner_add_left]

/-- Adding a perturbation smaller than the coercivity margin preserves a
uniformly positive coordinate metric, with the sharp reduced margin. -/
theorem IsUniformlyPositiveCoordinateMetric.add_of_norm_lt
    {μ : ℝ} {g : CoordinateBUCTensor E}
    (hg : IsUniformlyPositiveCoordinateMetric μ g)
    (h : CoordinateBUCTensor E)
    (hsymm : IsSymmetricCoordinateTensorCoefficient h)
    (hh : ‖h‖ < μ) :
    IsUniformlyPositiveCoordinateMetric (μ - ‖h‖) (g + h) := by
  refine ⟨?_, sub_pos.mpr hh, ?_⟩
  · intro x v w
    rw [coordinateMetricValue_add, coordinateMetricValue_add]
    rw [hg.symmetric x v w, hsymm x v w]
  intro x v
  have habs :
      |coordinateMetricValue h x v v| ≤ ‖h‖ * ‖v‖ ^ 2 := by
    calc
      |coordinateMetricValue h x v v| ≤ ‖h‖ * ‖v‖ * ‖v‖ :=
        abs_coordinateMetricValue_le (E := E) h x v v
      _ = ‖h‖ * ‖v‖ ^ 2 := by ring
  have hlower :
      -(‖h‖ * ‖v‖ ^ 2) ≤ coordinateMetricValue h x v v :=
    neg_le_of_abs_le habs
  calc
    (μ - ‖h‖) * ‖v‖ ^ 2 =
        μ * ‖v‖ ^ 2 + -(‖h‖ * ‖v‖ ^ 2) := by ring
    _ ≤ coordinateMetricValue g x v v + coordinateMetricValue h x v v :=
      add_le_add (hg.lower_bound x v) hlower
    _ = coordinateMetricValue (g + h) x v v := by
      rw [coordinateMetricValue_add]

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {ι κ : Type*}

local notation "T₂" => CoordinateTwoTensor E
local notation "BUCT₂" => CoordinateBUCTensor E

/-- Add the canonical perturbation back to the background coefficient. -/
def reconstructedMetricCoefficient
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) : BUCT₂ :=
  D.recentered.background + D.uniformSolution K u₀ t

/-- The reconstructed coefficient has its prescribed background-plus-data
initial value. -/
theorem reconstructedMetricCoefficient_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K) :
    D.reconstructedMetricCoefficient K u₀
        (⟨0, ⟨le_rfl, (D.uniformLifespan K).property⟩⟩ :
          Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) =
      D.recentered.background + (u₀ : BUCT₂) := by
  change D.recentered.background +
      D.uniformSolution K u₀
        (⟨0, ⟨le_rfl, (D.uniformLifespan K).property⟩⟩ :
          Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) =
    D.recentered.background + (u₀ : BUCT₂)
  rw [D.uniformSolution_zero K u₀]

/-- The common `K+1` perturbation estimate preserves positive definiteness
whenever the background margin is larger than `K+1`. -/
theorem reconstructedMetricCoefficient_uniformlyPositive
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ
      D.recentered.background)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ))
    (hsolutionSymmetric :
      IsSymmetricCoordinateTensorCoefficient (D.uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ) :
    IsUniformlyPositiveCoordinateMetric
      (μ - ((K + 1 : ℝ≥0) : ℝ))
      (D.reconstructedMetricCoefficient K u₀ t) := by
  have hnorm : ‖D.uniformSolution K u₀ t‖ < μ :=
    lt_of_le_of_lt (D.norm_uniformSolution_le K u₀ t) hsmall
  have hpositive := hbackground.add_of_norm_lt
    (D.uniformSolution K u₀ t) hsolutionSymmetric hnorm
  have hnormle := D.norm_uniformSolution_le K u₀ t
  refine ⟨hpositive.symmetric, sub_pos.mpr hsmall, ?_⟩
  intro x v
  calc
    (μ - ((K + 1 : ℝ≥0) : ℝ)) * ‖v‖ ^ 2 ≤
        (μ - ‖D.uniformSolution K u₀ t‖) * ‖v‖ ^ 2 := by
      gcongr
    _ ≤ coordinateMetricValue
        (D.reconstructedMetricCoefficient K u₀ t) x v v :=
      hpositive.lower_bound x v

/-- Exact initial evolution of the reconstructed coefficient.  Adding the
time-independent background does not change the derivative. -/
theorem reconstructedMetricCoefficient_hasDerivWithinAt_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (Au₀ : BUCT₂)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := T₂) (u₀ : BUCT₂) Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      (Au₀ + D.recentered.nonlinearity (u₀ : BUCT₂) + D.forcing)
      (Set.Icc 0 (D.uniformLifespan K : ℝ)) 0 := by
  have hbackground : HasDerivWithinAt
      (fun _t : ℝ ↦ D.recentered.background) 0
      (Set.Icc 0 (D.uniformLifespan K : ℝ)) 0 :=
    hasDerivWithinAt_const (x := (0 : ℝ))
      (s := Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ))
      (c := D.recentered.background)
  have hsolution := D.uniformSolution_hasDerivWithinAt_zero K u₀ Au₀ hu₀
  simpa only [reconstructedMetricCoefficient, zero_add] using
    hbackground.add hsolution

/-- For the natural residual forcing, the reconstructed metric coefficient
has initial derivative `A u₀ + N(u₀+c)`, the full shifted coordinate
right-hand side. -/
theorem ofShiftedBackground_reconstructedMetricCoefficient_hasDerivWithinAt_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (Au₀ : BUCT₂)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := T₂) (u₀ : BUCT₂) Au₀) :
    let A := ofShiftedBackground D
    HasDerivWithinAt
      (fun t : ℝ ↦ A.reconstructedMetricCoefficient K u₀
        (Set.projIcc 0 (A.uniformLifespan K : ℝ)
          (A.uniformLifespan K).property t))
      (Au₀ + D.base.nonlinearity ((u₀ : BUCT₂) + D.background))
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  let A := ofShiftedBackground D
  have hbackground : HasDerivWithinAt
      (fun _t : ℝ ↦ D.background) 0
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 :=
    hasDerivWithinAt_const (x := (0 : ℝ))
      (s := Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ))
      (c := D.background)
  have hsolution :=
    ofShiftedBackground_uniformSolution_hasDerivWithinAt_zero D K u₀ Au₀ hu₀
  simpa only [reconstructedMetricCoefficient, A, ofShiftedBackground, zero_add]
    using hbackground.add hsolution

/-- The complete theorem-bearing coordinate output of the current BUC
machinery: positive lifespan, correct initial metric coefficient, uniform
positive definiteness, and exact initial Ricci--DeTurck-shaped evolution. -/
theorem exists_positive_reconstructedMetricCoefficient_evolution
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K)
    (Au₀ : BUCT₂)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := T₂) (u₀ : BUCT₂) Au₀)
    (μ : ℝ)
    (hbackground : IsUniformlyPositiveCoordinateMetric μ D.background)
    (hsolutionSymmetric :
      ∀ t : Set.Icc (0 : ℝ)
          ((ofShiftedBackground D).uniformLifespan K : ℝ),
        IsSymmetricCoordinateTensorCoefficient
          ((ofShiftedBackground D).uniformSolution K u₀ t))
    (hsmall : ((K + 1 : ℝ≥0) : ℝ) < μ) :
    let A := ofShiftedBackground D
    0 < A.uniformLifespan K ∧
      A.reconstructedMetricCoefficient K u₀
          (⟨0, ⟨le_rfl, (A.uniformLifespan K).property⟩⟩ :
            Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ)) =
        D.background + (u₀ : BUCT₂) ∧
      (∀ t : Set.Icc (0 : ℝ) (A.uniformLifespan K : ℝ),
        IsUniformlyPositiveCoordinateMetric
          (μ - ((K + 1 : ℝ≥0) : ℝ))
          (A.reconstructedMetricCoefficient K u₀ t)) ∧
      HasDerivWithinAt
        (fun t : ℝ ↦ A.reconstructedMetricCoefficient K u₀
          (Set.projIcc 0 (A.uniformLifespan K : ℝ)
            (A.uniformLifespan K).property t))
        (Au₀ + D.base.nonlinearity ((u₀ : BUCT₂) + D.background))
        (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  let A := ofShiftedBackground D
  refine ⟨A.uniformLifespan_pos K, ?_, ?_, ?_⟩
  · exact A.reconstructedMetricCoefficient_zero K u₀
  · intro t
    exact A.reconstructedMetricCoefficient_uniformlyPositive K u₀ μ
      hbackground t (hsolutionSymmetric t) hsmall
  · exact
      ofShiftedBackground_reconstructedMetricCoefficient_hasDerivWithinAt_zero
        D K u₀ Au₀ hu₀

end AffineRecenteredDeTurckShapedBUCRemainderData

end Poincare
