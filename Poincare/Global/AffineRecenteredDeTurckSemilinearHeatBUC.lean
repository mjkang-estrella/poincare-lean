import Poincare.Global.RecenteredDeTurckSemilinearHeatBUC

/-!
# Affine recentered DeTurck semilinear heat equations

Recentring a coordinate remainder `N` about a background `c` separates the
shifted nonlinearity into

`N(x + c) = (N(x + c) - N(c)) + N(c)`.

The first term vanishes at the zero perturbation, while the second is the
constant forcing measuring failure of the background to be stationary.  This
module packages a general constant forcing, proves its uniform local and
maximal-time theories, identifies the exact initial generator derivative, and
shows that the canonical zero-data solution is the zero path exactly when the
forcing vanishes.
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

/-- A recentered DeTurck-shaped remainder together with a constant forcing.
For the actual shifted equation the forcing is the residual `N(c)` of the
background. -/
structure AffineRecenteredDeTurckShapedBUCRemainderData (ι κ : Type*) where
  recentered : RecenteredDeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ
  forcing : BUC

namespace AffineRecenteredDeTurckShapedBUCRemainderData

variable {ι κ : Type*}

/-- Recentered remainder plus constant background forcing. -/
def nonlinearity (D : AffineRecenteredDeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) : BUC → BUC :=
  fun x ↦ D.recentered.nonlinearity x + D.forcing

/-- The affine term at the zero perturbation is exactly the forcing. -/
@[simp]
theorem nonlinearity_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    D.nonlinearity 0 = D.forcing := by
  simp [nonlinearity]

/-- Vanishing of the affine nonlinearity at zero is equivalent to stationarity
of its forcing. -/
@[simp]
theorem nonlinearity_zero_eq_zero_iff
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    D.nonlinearity 0 = 0 ↔ D.forcing = 0 := by
  simp

/-- Explicit local data: constant forcing changes growth but not the
Lipschitz modulus. -/
def localData (D : AffineRecenteredDeTurckShapedBUCRemainderData
    (E := E) (F := F) ι κ) :
    SemilinearHeatBUCLocalData D.nonlinearity := by
  simpa only [nonlinearity] using
    SemilinearHeatBUCLocalData.add D.recentered.localData
      (SemilinearHeatBUCLocalData.const D.forcing)

theorem localData_growth
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.growth R =
      D.recentered.base.localData.lipschitz
          (‖D.recentered.background‖₊ + R) * R + ‖D.forcing‖₊ :=
  rfl

theorem localData_lipschitz
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (R : ℝ≥0) :
    D.localData.lipschitz R =
      D.recentered.base.localData.lipschitz
        (‖D.recentered.background‖₊ + R) := by
  change D.recentered.localData.lipschitz R + 0 = _
  rw [D.recentered.localData_lipschitz, add_zero]

/-- The natural affine package of a shifted background uses its residual
`N(c)` as the constant forcing. -/
def ofShiftedBackground
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ where
  recentered := D
  forcing := D.base.nonlinearity D.background

/-- Recentring plus the background residual reconstructs the original shifted
nonlinearity exactly. -/
theorem ofShiftedBackground_nonlinearity
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (x : BUC) :
    (ofShiftedBackground D).nonlinearity x =
      D.base.nonlinearity (x + D.background) := by
  simp [ofShiftedBackground, nonlinearity,
    RecenteredDeTurckShapedBUCRemainderData.nonlinearity]

/-- In the natural shifted package, zero forcing is precisely the stationary
background equation. -/
@[simp]
theorem ofShiftedBackground_forcing_eq_zero_iff
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) :
    (ofShiftedBackground D).forcing = 0 ↔
      D.base.nonlinearity D.background = 0 :=
  Iff.rfl

/-- Common positive lifespan for all affine initial data of norm at most
`K`. -/
abbrev uniformLifespan
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) : ℝ≥0 :=
  semilinearHeatBUCUniformLifespan D.localData K

theorem uniformLifespan_pos
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    0 < D.uniformLifespan K :=
  semilinearHeatBUCUniformLifespan_pos D.localData K

/-- Uniform local existence and uniqueness for the affine recentered
equation. -/
theorem exists_single_time_fixedPoints
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
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

/-- Canonical common-time affine solution. -/
noncomputable def uniformSolution
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    DuhamelPath (D.uniformLifespan K) BUC :=
  semilinearHeatBUCUniformLocalSolution K D.nonlinearity D.localData u₀

theorem uniformSolution_isFixedPt
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    semilinearHeatBUCPicard (D.uniformLifespan K) (u₀ : BUC)
        D.nonlinearity D.localData.continuous (D.uniformSolution K u₀) =
      D.uniformSolution K u₀ :=
  semilinearHeatBUCUniformLocalSolution_isFixedPt
    (E := E) (F := F) K D.nonlinearity D.localData u₀

theorem norm_uniformSolution_le
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    ‖D.uniformSolution K u₀ t‖ ≤ ((K + 1 : ℝ≥0) : ℝ) :=
  norm_semilinearHeatBUCUniformLocalSolution_le
    (E := E) (F := F) K D.nonlinearity D.localData u₀ t

/-- Exact corrected mild identity with the affine forcing inside the Duhamel
integral. -/
theorem uniformSolution_mild
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (t : Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) :
    D.uniformSolution K u₀ t =
      vectorHeatSemigroupBUCExtended (E := E) (F := F) (t : ℝ) (u₀ : BUC) +
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          vectorHeatSemigroupBUCExtended (E := E) (F := F) ((t : ℝ) - s)
            (D.recentered.nonlinearity (D.uniformSolution K u₀
                (Set.projIcc 0 (D.uniformLifespan K : ℝ)
                  (D.uniformLifespan K).property s)) + D.forcing) := by
  simpa only [nonlinearity] using
    semilinearHeatBUCUniformLocalSolution_mild
      (E := E) (F := F) K D.nonlinearity D.localData u₀ t

theorem uniformSolution_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) :
    D.uniformSolution K u₀
        (⟨0, ⟨le_rfl, (D.uniformLifespan K).property⟩⟩ :
          Set.Icc (0 : ℝ) (D.uniformLifespan K : ℝ)) = (u₀ : BUC) :=
  semilinearHeatBUCUniformLocalSolution_zero
    (E := E) (F := F) K D.nonlinearity D.localData u₀

/-- Exact initial right derivative: heat generator plus recentered remainder
plus constant forcing. -/
theorem uniformSolution_hasDerivWithinAt_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0) (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K)
    (Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u₀ : BUC) Au₀) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.uniformSolution K u₀
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      (Au₀ + D.recentered.nonlinearity (u₀ : BUC) + D.forcing)
      (Set.Icc 0 (D.uniformLifespan K : ℝ)) 0 := by
  simpa only [nonlinearity, add_assoc] using
    semilinearHeatBUCUniformLocalSolution_hasDerivWithinAt_zero
      (E := E) (F := F) K D.nonlinearity D.localData u₀ Au₀ hu₀

/-- The zero datum belongs to the heat-generator domain with generator zero. -/
theorem zero_mem_heatGeneratorDomain :
    IsInBUCHeatGeneratorDomain (E := E) (F := F) (0 : BUC) 0 := by
  simpa [IsInBUCHeatGeneratorDomain] using
    (hasDerivWithinAt_const (x := (0 : ℝ)) (c := (0 : BUC))
      (s := Set.Ici (0 : ℝ)))

/-- Zero initial datum as a point of every bounded ball. -/
def zeroBoundedData
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    SemilinearBUCBoundedData (E := E) (F := F) K :=
  ⟨0, by simp⟩

/-- The zero perturbation path on an arbitrary interval. -/
def zeroPath
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (T : ℝ≥0) : DuhamelPath T BUC :=
  constantDuhamelPathGeneric T (0 : BUC)

@[simp]
theorem zeroPath_apply
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (T : ℝ≥0)
    (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    D.zeroPath T t = 0 :=
  rfl

/-- At zero data, the exact initial derivative is the forcing itself. -/
theorem uniformSolution_zeroData_hasDerivWithinAt_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    HasDerivWithinAt
      (fun t : ℝ ↦ D.uniformSolution K (D.zeroBoundedData K)
        (Set.projIcc 0 (D.uniformLifespan K : ℝ)
          (D.uniformLifespan K).property t))
      D.forcing (Set.Icc 0 (D.uniformLifespan K : ℝ)) 0 := by
  simpa [zeroBoundedData] using D.uniformSolution_hasDerivWithinAt_zero K
    (D.zeroBoundedData K) 0
    (zero_mem_heatGeneratorDomain (E := E) (F := F))

/-- If the forcing vanishes, the zero path is a fixed point on every time
interval. -/
theorem zeroPath_isFixedPt_of_forcing_eq_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (hforcing : D.forcing = 0) (T : ℝ≥0) :
    semilinearHeatBUCPicard T (0 : BUC) D.nonlinearity
        D.localData.continuous (D.zeroPath T) = D.zeroPath T := by
  apply ContinuousMap.ext
  intro t
  simp [semilinearHeatBUCPicard_apply, zeroPath, nonlinearity, hforcing]

/-- On the positive canonical lifespan, a zero-path fixed point forces the
constant affine term to vanish. -/
theorem forcing_eq_zero_of_zeroPath_isFixedPt
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0)
    (hfixed :
      semilinearHeatBUCPicard (D.uniformLifespan K) (0 : BUC) D.nonlinearity
          D.localData.continuous (D.zeroPath (D.uniformLifespan K)) =
        D.zeroPath (D.uniformLifespan K)) :
    D.forcing = 0 := by
  let T := D.uniformLifespan K
  have hTreal : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast D.uniformLifespan_pos K
  have hderiv : HasDerivWithinAt
      (fun t : ℝ ↦ D.zeroPath T (Set.projIcc 0 (T : ℝ) T.property t))
      (0 + D.nonlinearity 0) (Set.Icc 0 (T : ℝ)) 0 :=
    semilinearHeatBUCFixedPoint_hasDerivWithinAt_zero
      (E := E) (F := F) T (0 : BUC) (0 : BUC) D.nonlinearity
      D.localData.continuous (D.zeroPath T) hfixed
      (zero_mem_heatGeneratorDomain (E := E) (F := F))
  have hconst : HasDerivWithinAt
      (fun t : ℝ ↦ D.zeroPath T (Set.projIcc 0 (T : ℝ) T.property t))
      0 (Set.Icc 0 (T : ℝ)) 0 := by
    simpa [zeroPath] using
      (hasDerivWithinAt_const (x := (0 : ℝ)) (c := (0 : BUC))
        (s := Set.Icc (0 : ℝ) (T : ℝ)))
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨le_rfl, hTreal.le⟩
  have huniq : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (T : ℝ)) 0 :=
    (uniqueDiffOn_Icc hTreal).uniqueDiffWithinAt hzero
  have hslope : (0 : BUC) + D.nonlinearity 0 = 0 :=
    (hderiv.derivWithin huniq).symm.trans (hconst.derivWithin huniq)
  simpa using hslope

/-- Exact fixed-point characterization of stationary forcing on the canonical
positive lifespan. -/
theorem zeroPath_isFixedPt_iff_forcing_eq_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    (semilinearHeatBUCPicard (D.uniformLifespan K) (0 : BUC) D.nonlinearity
        D.localData.continuous (D.zeroPath (D.uniformLifespan K)) =
      D.zeroPath (D.uniformLifespan K)) ↔ D.forcing = 0 := by
  constructor
  · exact D.forcing_eq_zero_of_zeroPath_isFixedPt K
  · intro h
    exact D.zeroPath_isFixedPt_of_forcing_eq_zero h (D.uniformLifespan K)

/-- The selected zero-data solution is identically zero exactly for stationary
forcing. -/
theorem uniformSolution_zero_eq_zeroPath_iff_forcing_eq_zero
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    D.uniformSolution K (D.zeroBoundedData K) =
        D.zeroPath (D.uniformLifespan K) ↔ D.forcing = 0 := by
  constructor
  · intro hzero
    apply D.forcing_eq_zero_of_zeroPath_isFixedPt K
    rw [← hzero]
    exact D.uniformSolution_isFixedPt K (D.zeroBoundedData K)
  · intro hforcing
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
    have hz := huniq (D.zeroPath T) hzBall
      (D.zeroPath_isFixedPt_of_forcing_eq_zero hforcing T)
    exact hz.symm

/-- For the natural shifted-background package, the canonical zero solution
is the zero path exactly when the background residual vanishes. -/
theorem ofShiftedBackground_uniformSolution_zero_iff_stationary
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    let A := ofShiftedBackground D
    A.uniformSolution K (A.zeroBoundedData K) =
        A.zeroPath (A.uniformLifespan K) ↔
      D.base.nonlinearity D.background = 0 := by
  exact (ofShiftedBackground D).uniformSolution_zero_eq_zeroPath_iff_forcing_eq_zero K

/-- The natural shifted equation has initial derivative
`A u₀ + N(u₀ + c)`. -/
theorem ofShiftedBackground_uniformSolution_hasDerivWithinAt_zero
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := F) K) (Au₀ : BUC)
    (hu₀ : IsInBUCHeatGeneratorDomain (E := E) (F := F) (u₀ : BUC) Au₀) :
    let A := ofShiftedBackground D
    HasDerivWithinAt
      (fun t : ℝ ↦ A.uniformSolution K u₀
        (Set.projIcc 0 (A.uniformLifespan K : ℝ)
          (A.uniformLifespan K).property t))
      (Au₀ + D.base.nonlinearity ((u₀ : BUC) + D.background))
      (Set.Icc 0 (A.uniformLifespan K : ℝ)) 0 := by
  have h :=
    (ofShiftedBackground D).uniformSolution_hasDerivWithinAt_zero K u₀ Au₀ hu₀
  convert h using 1
  simp only [ofShiftedBackground,
    RecenteredDeTurckShapedBUCRemainderData.nonlinearity]
  abel

/-- Quantitative stability of the affine local solution with respect to its
initial datum. -/
theorem lipschitzWith_uniformSolution
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    LipschitzWith
      (heatDuhamelBUCIntrinsicStabilityConstant
        (D.uniformLifespan K)
        (semilinearHeatBUCUniformBallLipschitzConstant D.localData K 1)
        (semilinearHeatBUCUniformLifespan_mul_lipschitz_lt_one D.localData K))
      (fun u₀ : SemilinearBUCBoundedData (E := E) (F := F) K ↦
        D.uniformSolution K u₀) :=
  lipschitzWith_semilinearHeatBUCUniformLocalSolution
    (E := E) (F := F) K D.nonlinearity D.localData

theorem continuous_uniformSolution
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ) (K : ℝ≥0) :
    Continuous
      (fun u₀ : SemilinearBUCBoundedData (E := E) (F := F) K ↦
        D.uniformSolution K u₀) :=
  (D.lipschitzWith_uniformSolution K).continuous

/-- An endpoint norm bound gives the explicit common continuation length for
the affine equation. -/
theorem has_localContinuation_of_end_norm_le
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (T K : ℝ≥0) (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T D.nonlinearity
      D.localData.continuous u₀ u)
    (hend : ‖u (compactDuhamelEndTime T)‖ ≤ (K : ℝ)) :
    HasSemilinearHeatBUCLocalContinuation T (D.uniformLifespan K)
      D.nonlinearity D.localData.continuous u :=
  has_semilinearHeatBUCLocalContinuation_of_end_norm_le
    (E := E) (F := F) T K D.nonlinearity D.localData u₀ u hu hend

/-- Every closed affine mild path admits some positive continuation. -/
theorem exists_positive_localContinuation
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (T : ℝ≥0) (u₀ : BUC) (u : DuhamelPath T BUC)
    (hu : IsSemilinearHeatBUCMildPath T D.nonlinearity
      D.localData.continuous u₀ u) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      HasSemilinearHeatBUCLocalContinuation T δ D.nonlinearity
        D.localData.continuous u :=
  exists_positive_semilinearHeatBUCLocalContinuation
    (E := E) (F := F) T D.nonlinearity D.localData u₀ u hu

/-- Compatible compact solution families for the affine equation. -/
abbrev CompactFamily
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) :=
  SemilinearHeatBUCCompactFamily Tmax D.nonlinearity D.localData.continuous u₀

/-- Every maximal affine solution family has unbounded norm. -/
theorem maximalTime_norm_unbounded_of_maximal
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := F) ι κ)
    (Tmax : ℝ≥0) (u₀ : BUC) (fam : D.CompactFamily Tmax u₀)
    (hmax : fam.IsMaximal) :
    ∀ K : ℝ≥0, ∃ (T : SemilinearBUCCompactTime Tmax)
      (t : Set.Icc (0 : ℝ) ((T : ℝ≥0) : ℝ)),
      (K : ℝ) < ‖fam.path T t‖ :=
  semilinearHeatBUC_maximalTime_norm_unbounded_of_maximal
    (E := E) (F := F) Tmax D.nonlinearity D.localData u₀ fam hmax

/-- Terminal form: each norm threshold is crossed after every compact time
strictly below the maximal lifespan. -/
theorem maximalTime_norm_unbounded_after_of_maximal
    (D : AffineRecenteredDeTurckShapedBUCRemainderData
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

end AffineRecenteredDeTurckShapedBUCRemainderData

end Poincare
