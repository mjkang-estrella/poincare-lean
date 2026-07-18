import Poincare.Global.DeTurckBUCJointSpacetimeChartCovariance

/-!
# Equivariance of canonical `BUC` fixed-point solutions

This file isolates the exact fixed-point mechanism behind cross-chart
covariance of the uniform-solution summands.  A continuous linear transport
of `BUC` coefficients is lifted pointwise to Duhamel paths.  If it commutes
with the heat semigroup, intertwines the nonlinearities, and is
norm-nonexpanding, then it transports the canonical controlled fixed point
to the canonical controlled fixed point.

For a general nonlinear preferred-chart transition the heat-semigroup
intertwining premise is genuine additional analytic content: the flat
Euclidean heat semigroup is not formally natural under arbitrary coordinate
changes.  The theorems below therefore derive every consequence available
from equivariant semigroup data without disguising that remaining input as a
chart-covariance assumption on the selected solution itself.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology Interval NNReal InnerProductSpace
  BoundedContinuousFunction Manifold ContDiff

namespace Poincare

section PathTransport

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Apply a continuous linear coefficient transport at every time of a
Duhamel path. -/
def mapDuhamelPath (T : ℝ≥0) (L : X →L[ℝ] Y)
    (u : DuhamelPath T X) : DuhamelPath T Y where
  toFun t := L (u t)
  continuous_toFun := L.continuous.comp u.continuous

@[simp]
theorem mapDuhamelPath_apply (T : ℝ≥0) (L : X →L[ℝ] Y)
    (u : DuhamelPath T X) (t : Icc (0 : ℝ) (T : ℝ)) :
    mapDuhamelPath T L u t = L (u t) :=
  rfl

/-- A norm-nonexpanding coefficient transport remains norm-nonexpanding on
compact-time Duhamel paths. -/
theorem dist_mapDuhamelPath_le_of_norm_le_one
    (T : ℝ≥0) (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1)
    (u v : DuhamelPath T X) :
    dist (mapDuhamelPath T L u) (mapDuhamelPath T L v) ≤ dist u v := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖L (u t) - L (v t)‖ = ‖L (u t - v t)‖ := by rw [map_sub]
    _ ≤ ‖L‖ * ‖u t - v t‖ := L.le_opNorm _
    _ ≤ 1 * ‖u - v‖ := by
      exact mul_le_mul hL (ContinuousMap.norm_coe_le_norm (u - v) t)
        (norm_nonneg _) zero_le_one
    _ = ‖u - v‖ := one_mul _

/-- Cast a compact-time path along an equality of time radii. -/
def castDuhamelPath {S T : ℝ≥0} (h : S = T)
    (u : DuhamelPath S X) : DuhamelPath T X := by
  subst T
  exact u

@[simp]
theorem castDuhamelPath_rfl (T : ℝ≥0) (u : DuhamelPath T X) :
    castDuhamelPath (X := X) rfl u = u :=
  rfl

/-- Cast a compact-time point along an equality of time radii. -/
def castDuhamelTime {S T : ℝ≥0} (h : S = T)
    (t : Icc (0 : ℝ) (S : ℝ)) : Icc (0 : ℝ) (T : ℝ) := by
  subst T
  exact t

@[simp]
theorem castDuhamelTime_rfl (T : ℝ≥0)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    castDuhamelTime rfl t = t :=
  rfl

@[simp]
theorem castDuhamelTime_projIcc {S T : ℝ≥0} (h : S = T) (t : ℝ) :
    castDuhamelTime h (Set.projIcc 0 (S : ℝ) S.property t) =
      Set.projIcc 0 (T : ℝ) T.property t := by
  cases h
  rfl

@[simp]
theorem castDuhamelPath_apply_castDuhamelTime {S T : ℝ≥0}
    (h : S = T) (u : DuhamelPath S X)
    (t : Icc (0 : ℝ) (S : ℝ)) :
    castDuhamelPath h u (castDuhamelTime h t) = u t := by
  cases h
  rfl

theorem castDuhamelPath_mem_closedBall_iff {S T : ℝ≥0}
    (h : S = T) (u c : DuhamelPath S X) (r : ℝ) :
    castDuhamelPath h u ∈ Metric.closedBall (castDuhamelPath h c) r ↔
      u ∈ Metric.closedBall c r := by
  cases h
  rfl

end PathTransport

section PicardEquivariance

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

/-- Heat-semigroup and nonlinearity equivariance imply equivariance of the
full corrected semilinear Picard map. -/
theorem mapDuhamelPath_semilinearHeatBUCPicard
    (T : ℝ≥0) (L : BUC →L[ℝ] BUC)
    (u₀₁ u₀₂ : BUC) (N₁ N₂ : BUC → BUC)
    (hN₁ : Continuous N₁) (hN₂ : Continuous N₂)
    (hinit : L u₀₁ = u₀₂)
    (hheat : ∀ r : ℝ, ∀ f : BUC,
      L (vectorHeatSemigroupBUCExtended (E := E) (F := F) r f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) r (L f))
    (hnonlinear : ∀ f : BUC, L (N₁ f) = N₂ (L f))
    (u : DuhamelPath T BUC) :
    mapDuhamelPath T L
        (semilinearHeatBUCPicard T u₀₁ N₁ hN₁ u) =
      semilinearHeatBUCPicard T u₀₂ N₂ hN₂
        (mapDuhamelPath T L u) := by
  apply ContinuousMap.ext
  intro t
  let g : ℝ → BUC := fun s ↦
    vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
      (N₁ (u (Set.projIcc 0 (T : ℝ) T.property s)))
  have hg : Continuous g := by
    apply continuous_vectorHeatSemigroupBUCExtended_apply_comp
      (E := E) (F := F)
    · exact continuous_const.sub continuous_id
    · exact hN₁.comp
        (u.continuous.comp (continuous_projIcc (h := T.property)))
  have hgInt : IntervalIntegrable g volume (0 : ℝ) (t : ℝ) :=
    hg.intervalIntegrable _ _
  simp only [mapDuhamelPath_apply, semilinearHeatBUCPicard_apply]
  rw [map_add, hheat, hinit]
  rw [← L.intervalIntegral_comp_comm hgInt]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _hs
  simp only [g]
  rw [hheat, hnonlinear]

/-- Equivariance of the homogeneous heat orbit follows directly from the
same semigroup and initial-data intertwining laws. -/
theorem mapDuhamelPath_heatLinearBUCPath
    (T : ℝ≥0) (L : BUC →L[ℝ] BUC) (u₀₁ u₀₂ : BUC)
    (hinit : L u₀₁ = u₀₂)
    (hheat : ∀ r : ℝ, ∀ f : BUC,
      L (vectorHeatSemigroupBUCExtended (E := E) (F := F) r f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) r (L f)) :
    mapDuhamelPath T L (heatLinearBUCPath T u₀₁) =
      heatLinearBUCPath T u₀₂ := by
  ext t
  simp only [mapDuhamelPath_apply, heatLinearBUCPath_apply]
  rw [hheat, hinit]

/-- Changing only the displayed compact-time radius commutes with the
homogeneous heat path. -/
theorem castDuhamelPath_heatLinearBUCPath {S T : ℝ≥0} (h : S = T)
    (u₀ : BUC) :
    castDuhamelPath h (heatLinearBUCPath S u₀) =
      heatLinearBUCPath T u₀ := by
  cases h
  rfl

/-- Changing only the displayed compact-time radius commutes with the
corrected semilinear Picard map. -/
theorem castDuhamelPath_semilinearHeatBUCPicard
    {S T : ℝ≥0} (h : S = T) (u₀ : BUC) (N : BUC → BUC)
    (hN : Continuous N) (u : DuhamelPath S BUC) :
    castDuhamelPath h (semilinearHeatBUCPicard S u₀ N hN u) =
      semilinearHeatBUCPicard T u₀ N hN (castDuhamelPath h u) := by
  cases h
  rfl

/-- Export the local uniqueness clause hidden inside the selected canonical
uniform solution.  Any controlled fixed point is the selected one. -/
theorem semilinearHeatBUCUniformLocalSolution_eq_of_mem_orbit_ball_of_isFixedPt
    (K : ℝ≥0) (N : BUC → BUC) (data : SemilinearHeatBUCLocalData N)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (v : DuhamelPath (semilinearHeatBUCUniformLifespan data K) BUC)
    (hvBall : v ∈ Metric.closedBall
      (heatLinearBUCPath (semilinearHeatBUCUniformLifespan data K)
        (u₀ : BUC)) (1 : ℝ))
    (hvFixed : semilinearHeatBUCPicard
      (semilinearHeatBUCUniformLifespan data K) (u₀ : BUC)
        N data.continuous v = v) :
    v = semilinearHeatBUCUniformLocalSolution K N data u₀ := by
  exact (Classical.choose_spec
    (exists_semilinearHeatBUCUniformLocalSolution
      (E := E) (F := F) K N data u₀)).2.2 v hvBall hvFixed

end PicardEquivariance

section AffineUniformSolutionEquivariance

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]

local notation "BUC" =>
  BoundedUniformContinuousFunction (E := E) (F := F)

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/--
Minimal fixed-point transport theorem.  It needs only equivariance of the
homogeneous orbit and of the complete Picard operator; it does not require
the flat heat and nonlinear terms to intertwine separately.  This is the
right interface for nonlinear coordinate changes, where those two summands
need not be natural in isolation even when the full Duhamel operator is.
-/
theorem affineUniformSolutions_cast_map_eq_of_picardEquivariant
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC) (hL : ‖L‖ ≤ 1)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (horbit :
      mapDuhamelPath (D₁.uniformLifespan K₁) L
          (heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₁ : BUC)) =
        heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₂ : BUC))
    (hpicard : ∀ u : DuhamelPath (D₁.uniformLifespan K₁) BUC,
      mapDuhamelPath (D₁.uniformLifespan K₁) L
          (semilinearHeatBUCPicard (D₁.uniformLifespan K₁)
            (u₀₁ : BUC) D₁.nonlinearity D₁.localData.continuous u) =
        semilinearHeatBUCPicard (D₁.uniformLifespan K₁)
          (u₀₂ : BUC) D₂.nonlinearity D₂.localData.continuous
          (mapDuhamelPath (D₁.uniformLifespan K₁) L u)) :
    castDuhamelPath hT
        (mapDuhamelPath (D₁.uniformLifespan K₁) L
          (D₁.uniformSolution K₁ u₀₁)) =
      D₂.uniformSolution K₂ u₀₂ := by
  let S := D₁.uniformLifespan K₁
  let T := D₂.uniformLifespan K₂
  let source := D₁.uniformSolution K₁ u₀₁
  let transported := mapDuhamelPath S L source
  have hsourceBall : source ∈ Metric.closedBall
      (heatLinearBUCPath S (u₀₁ : BUC)) (1 : ℝ) := by
    exact semilinearHeatBUCUniformLocalSolution_mem_orbit_ball
      (E := E) (F := F) K₁ D₁.nonlinearity D₁.localData u₀₁
  have htransportedBall : transported ∈ Metric.closedBall
      (heatLinearBUCPath S (u₀₂ : BUC)) (1 : ℝ) := by
    rw [← horbit]
    exact (dist_mapDuhamelPath_le_of_norm_le_one S L hL source
      (heatLinearBUCPath S (u₀₁ : BUC))).trans
        (by simpa [Metric.mem_closedBall] using hsourceBall)
  have hsourceFixed : semilinearHeatBUCPicard S (u₀₁ : BUC)
      D₁.nonlinearity D₁.localData.continuous source = source := by
    exact D₁.uniformSolution_isFixedPt K₁ u₀₁
  have htransportedFixed : semilinearHeatBUCPicard S (u₀₂ : BUC)
      D₂.nonlinearity D₂.localData.continuous transported =
        transported := by
    rw [← hpicard source]
    rw [hsourceFixed]
  have hcastCenter : castDuhamelPath hT
      (heatLinearBUCPath S (u₀₂ : BUC)) =
        heatLinearBUCPath T (u₀₂ : BUC) :=
    castDuhamelPath_heatLinearBUCPath hT (u₀₂ : BUC)
  have hcastBall : castDuhamelPath hT transported ∈ Metric.closedBall
      (heatLinearBUCPath T (u₀₂ : BUC)) (1 : ℝ) := by
    rw [← hcastCenter]
    exact (castDuhamelPath_mem_closedBall_iff hT transported
      (heatLinearBUCPath S (u₀₂ : BUC)) 1).2 htransportedBall
  have hcastFixed : semilinearHeatBUCPicard T (u₀₂ : BUC)
      D₂.nonlinearity D₂.localData.continuous
        (castDuhamelPath hT transported) = castDuhamelPath hT transported := by
    rw [← castDuhamelPath_semilinearHeatBUCPicard hT
      (u₀₂ : BUC) D₂.nonlinearity D₂.localData.continuous transported]
    rw [htransportedFixed]
  have hunique :=
    semilinearHeatBUCUniformLocalSolution_eq_of_mem_orbit_ball_of_isFixedPt
      (E := E) (F := F) K₂ D₂.nonlinearity D₂.localData u₀₂
      (castDuhamelPath hT transported) hcastBall hcastFixed
  simpa [S, T, source, transported,
    AffineRecenteredDeTurckShapedBUCRemainderData.uniformSolution] using hunique

/-- A norm-nonexpanding transport commuting with the heat semigroup and the
two affine nonlinearities identifies the two canonical uniform solutions.
-/
theorem affineUniformSolutions_cast_map_eq_of_equivariantSemigroup
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := F) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := F) K₂)
    (L : BUC →L[ℝ] BUC) (hL : ‖L‖ ≤ 1)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC) = (u₀₂ : BUC))
    (hheat : ∀ r : ℝ, ∀ f : BUC,
      L (vectorHeatSemigroupBUCExtended (E := E) (F := F) r f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := F) r (L f))
    (hnonlinear : ∀ f : BUC,
      L (D₁.nonlinearity f) = D₂.nonlinearity (L f)) :
    castDuhamelPath hT
        (mapDuhamelPath (D₁.uniformLifespan K₁) L
          (D₁.uniformSolution K₁ u₀₁)) =
      D₂.uniformSolution K₂ u₀₂ := by
  apply affineUniformSolutions_cast_map_eq_of_picardEquivariant
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hL hT
  · exact mapDuhamelPath_heatLinearBUCPath
      (D₁.uniformLifespan K₁) L
      (u₀₁ : BUC) (u₀₂ : BUC) hinit hheat
  · intro u
    exact mapDuhamelPath_semilinearHeatBUCPicard
      (D₁.uniformLifespan K₁) L
      (u₀₁ : BUC) (u₀₂ : BUC)
      D₁.nonlinearity D₂.nonlinearity
      D₁.localData.continuous D₂.localData.continuous
      hinit hheat hnonlinear u

end AffineUniformSolutionEquivariance

section CoordinateMetricEvaluation

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Scalar cross-chart covariance of the fixed-point summands, derived from
equivariant semigroup data and fixed-point uniqueness rather than assumed on
the selected solutions. -/
theorem coordinateMetricValue_uniformSolutions_eq_of_equivariantSemigroup
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂) (hL : ‖L‖ ≤ 1)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (hheat : ∀ r : ℝ, ∀ f : BUC₂,
      L (vectorHeatSemigroupBUCExtended (E := E) (F := T₂) r f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := T₂) r (L f))
    (hnonlinear : ∀ f : BUC₂,
      L (D₁.nonlinearity f) = D₂.nonlinearity (L f))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ),
      coordinateMetricValue
          (D₂.uniformSolution K₂ u₀₂ (castDuhamelTime hT t))
          x₂ v₂ w₂ =
        coordinateMetricValue (D₁.uniformSolution K₁ u₀₁ t)
          x₁ v₁ w₁ := by
  have hpath := affineUniformSolutions_cast_map_eq_of_equivariantSemigroup
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hL hT hinit hheat hnonlinear
  intro t
  have ht := congrArg (fun u ↦ u (castDuhamelTime hT t)) hpath
  simp only [castDuhamelPath_apply_castDuhamelTime, mapDuhamelPath_apply] at ht
  rw [← ht]
  exact heval (D₁.uniformSolution K₁ u₀₁ t)

/--
Projected real-time covariance under the minimal full-Picard transport
interface.  Unlike the semigroup-specialized theorem below, this result is
compatible with nonlinear coordinate transports whose heat and nonlinear
summands are not separately natural.
-/
theorem coordinateMetricValue_projectedUniformSolutions_eq_of_picardEquivariant
    (D₁ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : AffineRecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂) (hL : ‖L‖ ≤ 1)
    (hT : D₁.uniformLifespan K₁ = D₂.uniformLifespan K₂)
    (horbit :
      mapDuhamelPath (D₁.uniformLifespan K₁) L
          (heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₁ : BUC₂)) =
        heatLinearBUCPath (D₁.uniformLifespan K₁) (u₀₂ : BUC₂))
    (hpicard : ∀ u : DuhamelPath (D₁.uniformLifespan K₁) BUC₂,
      mapDuhamelPath (D₁.uniformLifespan K₁) L
          (semilinearHeatBUCPicard (D₁.uniformLifespan K₁)
            (u₀₁ : BUC₂) D₁.nonlinearity D₁.localData.continuous u) =
        semilinearHeatBUCPicard (D₁.uniformLifespan K₁)
          (u₀₂ : BUC₂) D₂.nonlinearity D₂.localData.continuous
          (mapDuhamelPath (D₁.uniformLifespan K₁) L u))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (D₂.uniformSolution K₂ u₀₂
            (Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
              (D₂.uniformLifespan K₂).property t))
          x₂ v₂ w₂ =
        coordinateMetricValue
          (D₁.uniformSolution K₁ u₀₁
            (Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
              (D₁.uniformLifespan K₁).property t))
          x₁ v₁ w₁ := by
  have hpath := affineUniformSolutions_cast_map_eq_of_picardEquivariant
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hL hT horbit hpicard
  intro t
  let t₁ : Icc (0 : ℝ) (D₁.uniformLifespan K₁ : ℝ) :=
    Set.projIcc 0 (D₁.uniformLifespan K₁ : ℝ)
      (D₁.uniformLifespan K₁).property t
  have ht := congrArg (fun u ↦ u (castDuhamelTime hT t₁)) hpath
  simp only [castDuhamelPath_apply_castDuhamelTime, mapDuhamelPath_apply] at ht
  have htcast : castDuhamelTime hT t₁ =
      Set.projIcc 0 (D₂.uniformLifespan K₂ : ℝ)
        (D₂.uniformLifespan K₂).property t := by
    exact castDuhamelTime_projIcc hT t
  rw [← htcast, ← ht]
  exact heval (D₁.uniformSolution K₁ u₀₁ t₁)

/-- The projected, total-real-time solution path used by spacetime metric
reconstruction inherits the same covariance.  This conclusion has exactly
the fixed-point-summand shape consumed by
`chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_and_backgroundSolution`.
-/
theorem coordinateMetricValue_ofShiftedBackground_projectedUniformSolutions_eq_of_equivariantSemigroup
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂) (hL : ‖L‖ ≤ 1)
    (hT :
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁ =
        (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (hheat : ∀ r : ℝ, ∀ f : BUC₂,
      L (vectorHeatSemigroupBUCExtended (E := E) (F := T₂) r f) =
        vectorHeatSemigroupBUCExtended (E := E) (F := T₂) r (L f))
    (hnonlinear : ∀ f : BUC₂,
      L ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).nonlinearity f) =
        (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).nonlinearity (L f))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformSolution
            K₂ u₀₂
            (Set.projIcc 0
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂ : ℝ)
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂).property t))
          x₂ v₂ w₂ =
        coordinateMetricValue
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformSolution
            K₁ u₀₁
            (Set.projIcc 0
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁ : ℝ)
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁).property t))
          x₁ v₁ w₁ := by
  let A₁ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁
  let A₂ :=
    AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂
  have hpath := affineUniformSolutions_cast_map_eq_of_equivariantSemigroup
    A₁ A₂ K₁ K₂ u₀₁ u₀₂ L hL hT hinit hheat hnonlinear
  intro t
  let t₁ : Icc (0 : ℝ) (A₁.uniformLifespan K₁ : ℝ) :=
    Set.projIcc 0 (A₁.uniformLifespan K₁ : ℝ)
      (A₁.uniformLifespan K₁).property t
  have ht := congrArg (fun u ↦ u (castDuhamelTime hT t₁)) hpath
  simp only [castDuhamelPath_apply_castDuhamelTime, mapDuhamelPath_apply] at ht
  have htcast : castDuhamelTime hT t₁ =
      Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
        (A₂.uniformLifespan K₂).property t := by
    exact castDuhamelTime_projIcc hT t
  change coordinateMetricValue
      (A₂.uniformSolution K₂ u₀₂
        (Set.projIcc 0 (A₂.uniformLifespan K₂ : ℝ)
          (A₂.uniformLifespan K₂).property t)) x₂ v₂ w₂ =
    coordinateMetricValue (A₁.uniformSolution K₁ u₀₁ t₁)
      x₁ v₁ w₁
  rw [← htcast, ← ht]
  exact heval (A₁.uniformSolution K₁ u₀₁ t₁)

end CoordinateMetricEvaluation

section ManifoldReconstructedSolutionPath

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Manifold-chart specialization of the projected uniform-solution theorem.
Its conclusion is definitionally the fixed-point summand used by the joint
spacetime chart-covariance assembly. -/
theorem reconstructedCoordinateSolutionPath_value_eq_of_equivariantSemigroup
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (L : BUC₂ →L[ℝ] BUC₂) (hL : ‖L‖ ≤ 1)
    (hT :
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).uniformLifespan K₁ =
        (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).uniformLifespan K₂)
    (hinit : L (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (hheat : ∀ r : ℝ, ∀ f : BUC₂,
      L (vectorHeatSemigroupBUCExtended («E» := E) (F := T₂) r f) =
        vectorHeatSemigroupBUCExtended («E» := E) (F := T₂) r (L f))
    (hnonlinear : ∀ f : BUC₂,
      L ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₁).nonlinearity f) =
        (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D₂).nonlinearity (L f))
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (L f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₂ K₂ u₀₂ t)
          x₂ v₂ w₂ =
        coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₁ K₁ u₀₁ t)
          x₁ v₁ w₁ := by
  simpa only [reconstructedCoordinateSolutionPath] using
    (coordinateMetricValue_ofShiftedBackground_projectedUniformSolutions_eq_of_equivariantSemigroup
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ L hL hT hinit hheat hnonlinear
      x₁ x₂ v₁ w₁ v₂ w₂ heval)

end ManifoldReconstructedSolutionPath

section ChartwiseUniformSolutionTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

/--
The exact global analytic contract needed to transport the canonical local
`BUC` fixed points between preferred charts.  In particular, this structure
does not assume covariance of the selected solution: that conclusion is
derived from full-Picard equivariance and controlled fixed-point uniqueness.

Constructing this contract for nonlinear chart transitions is the remaining
analytic naturality problem.  It is deliberately exposed here rather than
hidden in a hypothesis about the already-selected fixed point.
-/
structure ChartwiseBUCUniformSolutionTransportData
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K) where
  /-- Coefficient transport from the first chart to the second chart. -/
  transport : M → M → BUC₂ →L[ℝ] BUC₂
  norm_transport_le_one : ∀ anchor₁ anchor₂,
    ‖transport anchor₁ anchor₂‖ ≤ 1
  uniformLifespan_eq : ∀ anchor₁ anchor₂,
    (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁)).uniformLifespan K =
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₂)).uniformLifespan K
  orbit_eq : ∀ anchor₁ anchor₂,
    let A₁ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁)
    mapDuhamelPath (A₁.uniformLifespan K)
          (transport anchor₁ anchor₂)
          (heatLinearBUCPath (A₁.uniformLifespan K)
            (u₀ anchor₁ : BUC₂)) =
        heatLinearBUCPath (A₁.uniformLifespan K)
          (u₀ anchor₂ : BUC₂)
  picard_eq : ∀ anchor₁ anchor₂,
    let A₁ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁)
    let A₂ :=
      AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₂)
    ∀ u : DuhamelPath (A₁.uniformLifespan K) BUC₂,
      mapDuhamelPath (A₁.uniformLifespan K)
          (transport anchor₁ anchor₂)
          (semilinearHeatBUCPicard (A₁.uniformLifespan K)
            (u₀ anchor₁ : BUC₂) A₁.nonlinearity
            A₁.localData.continuous u) =
        semilinearHeatBUCPicard (A₁.uniformLifespan K)
          (u₀ anchor₂ : BUC₂) A₂.nonlinearity
          A₂.localData.continuous
          (mapDuhamelPath (A₁.uniformLifespan K)
            (transport anchor₁ anchor₂) u)

/--
Endpoint-map germs, background covariance, and a chartwise semigroup
transport contract imply covariance of the complete reconstructed
inverse-gauge spacetime coefficient.  The fixed-point-summand premise of
`chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_and_backgroundSolution`
is discharged internally by fixed-point uniqueness.
-/
theorem chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_background_and_uniformSolutionTransport
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := T₂) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (H : ChartwiseBUCUniformSolutionTransportData D K u₀)
    (hPhi : ∀ t anchor z,
      HasFDerivAt (Phi anchor t) (DPhi anchor t z) z)
    (hendpointTarget : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      Phi anchor₁ t z ∈ (extChartAt I anchor₁).target)
    (hendpointSource : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      (extChartAt I anchor₁).symm (Phi anchor₁ t z) ∈
        (extChartAt I anchor₂).source)
    (hcompat : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      (Phi anchor₂ t ∘
          GeodesicTransport.chartTransition anchor₁ anchor₂) =ᶠ[nhds z]
        (GeodesicTransport.chartTransition anchor₁ anchor₂ ∘
          Phi anchor₁ t))
    (hbackground : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E,
        coordinateMetricValue (D anchor₂).background
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue (D anchor₁).background
            (Phi anchor₁ t z) a b)
    (htransportEvaluation : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ a b : E, ∀ f : BUC₂,
        coordinateMetricValue (H.transport anchor₁ anchor₂ f)
            (GeodesicTransport.chartTransition anchor₁ anchor₂
              (Phi anchor₁ t z))
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
              (Phi anchor₁ t z) b) =
          coordinateMetricValue f (Phi anchor₁ t z) a b) :
    ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z u v := by
  apply chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_and_backgroundSolution
    D K u₀ Phi DPhi hPhi hendpointTarget hendpointSource hcompat hbackground
  intro t anchor₁ anchor₂ z hz hy a b
  simpa only [reconstructedCoordinateSolutionPath] using
    (coordinateMetricValue_projectedUniformSolutions_eq_of_picardEquivariant
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₁))
      (AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor₂))
      K K (u₀ anchor₁) (u₀ anchor₂)
      (H.transport anchor₁ anchor₂)
      (H.norm_transport_le_one anchor₁ anchor₂)
      (H.uniformLifespan_eq anchor₁ anchor₂)
      (H.orbit_eq anchor₁ anchor₂)
      (H.picard_eq anchor₁ anchor₂)
      (Phi anchor₁ t z)
      (GeodesicTransport.chartTransition anchor₁ anchor₂
        (Phi anchor₁ t z))
      a b
      (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
        (Phi anchor₁ t z) a)
      (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂
        (Phi anchor₁ t z) b)
      (htransportEvaluation t anchor₁ anchor₂ z hz hy a b) t)

end ChartwiseUniformSolutionTransport

end Poincare
