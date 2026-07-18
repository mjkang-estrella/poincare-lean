import Poincare.Global.DeTurckBUCFlatHilbertSchmidtEnergy

/-!
# Flat Hilbert--Schmidt energy closes reconstructed chart uniqueness

This file composes the concrete quasilinear rate split, the finite-entry flat
Bochner estimate, and the compact parabolic maximum principle.  It keeps the
two genuinely global inputs visible:

* `CompactFlatChartBoundarySupportData` says that a compact spatial carrier
  detects the coefficient, carries the energy maximum principle, and realizes
  its scalar Laplacian by the local flat chart Laplacian;
* `CorrectedLowerLinearizationData` says that all analytic, connection, and
  localization corrections left after the proved flat principal split form a
  continuous linear action on the finite entry difference.

From these two records the compact energy certificate is automatic.  The
last sections specialize it to shifted reconstructed solutions, build the
chart-indexed overlap-energy package, prove chart covariance, and invoke the
global metric-family assembly theorem.
-/

noncomputable section

open Bornology Bundle FiberBundle Filter Function Set InnerProductSpace
open scoped BoundedContinuousFunction ContDiff InnerProductSpace Interval
  Laplacian Manifold NNReal Topology

namespace Poincare

set_option maxHeartbeats 800000

section FiniteEntryEvaluation

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

local notation "P" => CoordinateTensorEntryIndex E
local notation "H²" => EuclideanSpace ℝ P
local notation "BUC₂" => CoordinateBUCTensor E

/-- Simultaneous continuous evaluation of every standard-basis tensor entry. -/
def coordinateTensorEntryEvaluationCLM (z : E) : BUC₂ →L[ℝ] H² :=
  (EuclideanSpace.equiv P ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun p : P ↦
      coordinateMetricEvaluationCLM z
        ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2))

@[simp] theorem coordinateTensorEntryEvaluationCLM_apply_entry
    (z : E) (f : BUC₂) (p : P) :
    coordinateTensorEntryEvaluationCLM z f p =
      coordinateMetricValue f z
        ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2) := by
  simp only [coordinateTensorEntryEvaluationCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply,
    ContinuousLinearMap.pi_apply, coordinateMetricEvaluationCLM_apply]

/-- Finite evaluation agrees exactly with the Hilbert--Schmidt entry vector. -/
theorem coordinateTensorEntryEvaluationCLM_apply
    (z : E) (f : BUC₂) :
    coordinateTensorEntryEvaluationCLM z f =
      coordinateTensorEntryVector (coordinateBilinearFormAt f z) := by
  ext p
  simp only [coordinateTensorEntryEvaluationCLM_apply_entry,
    coordinateTensorEntryVector_apply, coordinateBilinearFormAt_apply]

end FiniteEntryEvaluation

section AbstractFlatChartComparison

universe u v

variable {E : Type u} {Q : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q]

local notation "P" => CoordinateTensorEntryIndex E
local notation "H²" => EuclideanSpace ℝ P
local notation "BUC₂" => CoordinateBUCTensor E

/-- The full coordinate bilinear-form difference of two compact-time paths. -/
def flatChartDuhamelDifferenceCoefficient
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) (t : ℝ) (z : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  coordinateBilinearFormAt (extendedDuhamelPathDifference T u v t) z

/-- The finite componentwise flat-Laplacian principal vector. -/
def flatChartDuhamelDifferencePrincipal
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂)
    (coordinate : Q → E) (t : ℝ) (q : Q) : H² :=
  coordinateTensorFlatLaplacianEntryVector
    (flatChartDuhamelDifferenceCoefficient T u v t) (coordinate q)

omit [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q] in
/-- Evaluation on the compact carrier is the finite entry vector of the
actual `BUC` difference coefficient. -/
theorem pointwiseDuhamelDifferenceTensor_entryEvaluation_eq
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂)
    (coordinate : Q → E) (t : ℝ) (q : Q) :
    pointwiseDuhamelDifferenceTensor T
        (fun q ↦ coordinateTensorEntryEvaluationCLM (coordinate q))
        u v t q =
      coordinateTensorEntryVector
        (flatChartDuhamelDifferenceCoefficient T u v t (coordinate q)) := by
  exact coordinateTensorEntryEvaluationCLM_apply _ _

/--
The honest global boundary/support obligation for a flat-chart maximum
principle.  The Euclidean chart model is not compact, so compactness,
coefficient detection, and compatibility between the chosen compact scalar
Laplacian and the local flat Laplacian are recorded explicitly here.
-/
structure CompactFlatChartBoundarySupportData
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) where
  coordinate : Q → E
  pointwiseContinuous : Continuous
    (Function.uncurry
      (pointwiseDuhamelDifferenceTensor T
        (fun q ↦ coordinateTensorEntryEvaluationCLM (coordinate q)) u v))
  support_separates : ∀ f : BUC₂,
    (∀ q : Q, coordinateTensorEntryEvaluationCLM (coordinate q) f = 0) →
      f = 0
  energyLaplacian : CompactParabolicPointwiseDifferenceEnergyLaplacianData
    T (fun q ↦ coordinateTensorEntryEvaluationCLM (coordinate q)) u v
  entry_contDiff_two : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ p : P,
    ContDiff ℝ 2 (fun z ↦
      flatChartDuhamelDifferenceCoefficient T u v t z
        ((stdOrthonormalBasis ℝ E) p.1)
        ((stdOrthonormalBasis ℝ E) p.2))
  laplacian_energy_eq_flat :
    ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ q : Q,
      energyLaplacian.lap t
          (fun r ↦
            ‖pointwiseDuhamelDifferenceTensor T
              (fun q ↦ coordinateTensorEntryEvaluationCLM (coordinate q))
              u v t r‖ ^ 2) q =
        (Δ fun z ↦ coordinateTensorHilbertSchmidtEnergy
          (flatChartDuhamelDifferenceCoefficient T u v t z)) (coordinate q)

/--
The separate lower-order linearization obligation.  `exact_rate_split` is
the finite-entry assembly of
`reconstructedInteriorSlope_difference_eq_flatPrincipal_add_lowerOrder`;
`correctedLower` includes all chart-connection and localization corrections.
The second field is the mean-value/linearization statement needed to make
that corrected lower term a reaction coefficient.
-/
structure CorrectedLowerLinearizationData
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) (pathRate : ℝ → BUC₂)
    (B : CompactFlatChartBoundarySupportData (Q := Q) T u v) where
  correctedLower : ℝ → Q → H²
  correctedLowerOperator : ℝ → Q → H² →L[ℝ] H²
  exact_rate_split : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ q : Q,
    coordinateTensorEntryEvaluationCLM (B.coordinate q) (pathRate t) =
      flatChartDuhamelDifferencePrincipal T u v B.coordinate t q +
        correctedLower t q
  correctedLower_eq_operator :
    ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ q : Q,
      correctedLower t q =
        correctedLowerOperator t q
          (pointwiseDuhamelDifferenceTensor T
            (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
            u v t q)
  correctedLowerOperator_continuousOn :
    ContinuousOn (Function.uncurry correctedLowerOperator)
      (Set.Icc (0 : ℝ) (T : ℝ) ×ˢ (Set.univ : Set Q))

/-- Scalar coefficient identities assemble into the exact finite-entry rate
identity.  This is the direct adapter from the scalar conclusion of
`reconstructedInteriorSlope_difference_eq_flatPrincipal_add_lowerOrder` to
the Hilbert--Schmidt comparison space. -/
theorem coordinateTensorEntryEvaluation_eq_add_of_entries
    (z : E) (rate : BUC₂) (principal lower : H²)
    (hentries : ∀ p : P,
      coordinateMetricValue rate z
          ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2) =
        principal p + lower p) :
    coordinateTensorEntryEvaluationCLM z rate = principal + lower := by
  ext p
  simpa only [coordinateTensorEntryEvaluationCLM_apply_entry,
    Pi.add_apply] using hentries p

/-- Entrywise exact quasilinear splits and one corrected-lower operator build
the entire lower-linearization record. -/
noncomputable def CorrectedLowerLinearizationData.of_entrywise
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) (pathRate : ℝ → BUC₂)
    (B : CompactFlatChartBoundarySupportData (Q := Q) T u v)
    (correctedLower : ℝ → Q → H²)
    (correctedLowerOperator : ℝ → Q → H² →L[ℝ] H²)
    (hentries : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ q : Q, ∀ p : P,
      coordinateMetricValue (pathRate t) (B.coordinate q)
          ((stdOrthonormalBasis ℝ E) p.1)
          ((stdOrthonormalBasis ℝ E) p.2) =
        flatChartDuhamelDifferencePrincipal T u v B.coordinate t q p +
          correctedLower t q p)
    (hoperator : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ), ∀ q : Q,
      correctedLower t q =
        correctedLowerOperator t q
          (pointwiseDuhamelDifferenceTensor T
            (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
            u v t q))
    (hcontinuous : ContinuousOn (Function.uncurry correctedLowerOperator)
      (Set.Icc (0 : ℝ) (T : ℝ) ×ˢ (Set.univ : Set Q))) :
    CorrectedLowerLinearizationData T u v pathRate B where
  correctedLower := correctedLower
  correctedLowerOperator := correctedLowerOperator
  exact_rate_split := by
    intro t ht q
    exact coordinateTensorEntryEvaluation_eq_add_of_entries
      (B.coordinate q) (pathRate t)
      (flatChartDuhamelDifferencePrincipal T u v B.coordinate t q)
      (correctedLower t q) (hentries t ht q)
  correctedLower_eq_operator := hoperator
  correctedLowerOperator_continuousOn := hcontinuous

omit [CompactSpace Q] [Nonempty Q] in
/-- The flat Hilbert--Schmidt principal term satisfies the exact scalar
energy inequality required by the compact comparison Laplacian. -/
theorem flatChartDuhamelDifference_principalEnergy
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂)
    (B : CompactFlatChartBoundarySupportData (Q := Q) T u v)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T : ℝ)) (q : Q) :
    2 * ⟪pointwiseDuhamelDifferenceTensor T
          (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
          u v t q,
        flatChartDuhamelDifferencePrincipal T u v B.coordinate t q⟫_ℝ ≤
      B.energyLaplacian.lap t
        (fun r ↦ ‖pointwiseDuhamelDifferenceTensor T
          (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
          u v t r‖ ^ 2) q := by
  rw [B.laplacian_energy_eq_flat t ht q]
  simpa only [flatChartDuhamelDifferencePrincipal,
    pointwiseDuhamelDifferenceTensor_entryEvaluation_eq] using
    (two_mul_coordinateTensor_flatPrincipalPairing_le_laplacian_energy
      (flatChartDuhamelDifferenceCoefficient T u v t)
      (B.entry_contDiff_two t ht) (B.coordinate q))

/-- The two named obligations automatically produce the complete compact
parabolic difference-energy certificate. -/
noncomputable def compactParabolicDuhamelDifferenceEnergyData_of_flatHS
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) (pathRate : ℝ → BUC₂)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)))
    (B : CompactFlatChartBoundarySupportData (Q := Q) T u v)
    (A : CorrectedLowerLinearizationData T u v pathRate B) :
    CompactParabolicDuhamelDifferenceEnergyData (M := Q) T u v := by
  let hbound :=
    exists_uniform_chartConnectionCorrectedLowerOperator_bound
      (T : ℝ) A.correctedLowerOperator
        A.correctedLowerOperator_continuousOn
  let C := Classical.choose hbound
  have hC := (Classical.choose_spec hbound).2
  exact
    compactParabolicDuhamelDifferenceEnergyData_of_pointwiseTensor_energyLaplacian_jointContinuous
      T u v
      (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
      B.pointwiseContinuous B.support_separates pathRate hpathRate
      B.energyLaplacian (fun _ _ ↦ 2 * C) (2 * C)
      (by intro t ht q; exact le_rfl)
      (by
        intro t ht q
        rw [A.exact_rate_split t ht q, inner_add_right]
        have hprincipal :=
          flatChartDuhamelDifference_principalEnergy T u v B t ht q
        have htIcc : t ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
          ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hlower := two_mul_inner_linearLower_le_reaction_energy
          (A.correctedLowerOperator t q)
          (pointwiseDuhamelDifferenceTensor T
            (fun q ↦ coordinateTensorEntryEvaluationCLM (B.coordinate q))
            u v t q)
          (hC t htIcc q)
        rw [← A.correctedLower_eq_operator t ht q] at hlower
        linarith)
      hzero

/-- Consequently the two compact-time coefficient paths are equal. -/
theorem duhamelPaths_eq_of_flatHSEnergy
    (T : ℝ≥0) (u v : DuhamelPath T BUC₂) (pathRate : ℝ → BUC₂)
    (hpathRate : ∀ t ∈ Set.Ioo (0 : ℝ) (T : ℝ),
      HasDerivAt (extendedDuhamelPathDifference T u v) (pathRate t) t)
    (hzero :
      u (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)) =
        v (⟨0, ⟨le_rfl, T.property⟩⟩ : Set.Icc (0 : ℝ) (T : ℝ)))
    (B : CompactFlatChartBoundarySupportData (Q := Q) T u v)
    (A : CorrectedLowerLinearizationData T u v pathRate B) :
    u = v :=
  duhamelPaths_eq_of_compactParabolicDifferenceEnergy T u v
    (compactParabolicDuhamelDifferenceEnergyData_of_flatHS
      T u v pathRate hpathRate hzero B A)

end AbstractFlatChartComparison

section ReconstructedAffineComparison

universe u v

variable {E : Type u} {Q : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q]

local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Short name for the natural affine package of a shifted background. -/
abbrev shiftedReconstructedAffineData
    {iota kappa : Type*}
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa) :=
  AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground D

/-- The transported source solution on the target reconstructed lifespan. -/
abbrev transportedShiftedReconstructedUniformSolution
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := T₂) K₁)
    (transport : BUC₂ →L[ℝ] BUC₂)
    (hT : (shiftedReconstructedAffineData D₁).uniformLifespan K₁ =
      (shiftedReconstructedAffineData D₂).uniformLifespan K₂) :
    DuhamelPath
      ((shiftedReconstructedAffineData D₂).uniformLifespan K₂) BUC₂ :=
  castMapAffineUniformSolution (shiftedReconstructedAffineData D₁)
    K₁ u₀₁ transport
    ((shiftedReconstructedAffineData D₂).uniformLifespan K₂) hT

/-- The target shifted reconstructed solution. -/
abbrev shiftedReconstructedUniformSolution
    {iota kappa : Type*}
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData (E := E) (F := T₂) K) :
    DuhamelPath ((shiftedReconstructedAffineData D).uniformLifespan K) BUC₂ :=
  (shiftedReconstructedAffineData D).uniformSolution K u₀

/-- The automatic positive-time rate of the transported reconstructed pair. -/
abbrev shiftedReconstructedInteriorRateDifference
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (transport : BUC₂ →L[ℝ] BUC₂) : ℝ → BUC₂ :=
  affineUniformSolutionsInteriorRateDifference
    (shiftedReconstructedAffineData D₁)
    (shiftedReconstructedAffineData D₂)
    K₁ K₂ u₀₁ u₀₂ transport

/-- Zero in the compact target lifespan of a shifted reconstruction. -/
def shiftedReconstructedZeroTime
    {iota kappa : Type*}
    (D : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota kappa)
    (K : ℝ≥0) :
    Set.Icc (0 : ℝ)
      ((shiftedReconstructedAffineData D).uniformLifespan K : ℝ) :=
  ⟨0, ⟨le_rfl,
    ((shiftedReconstructedAffineData D).uniformLifespan K).property⟩⟩

set_option maxHeartbeats 2000000 in
/-- One reconstructed pair's two named analytic obligations together with
the literal zero-time path equality consumed by the energy constructor. -/
structure ReconstructedFlatHSComparisonData
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := T₂) K₂)
    (transport : BUC₂ →L[ℝ] BUC₂)
    (hT : (shiftedReconstructedAffineData D₁).uniformLifespan K₁ =
      (shiftedReconstructedAffineData D₂).uniformLifespan K₂) where
  boundarySupport : CompactFlatChartBoundarySupportData (Q := Q)
    ((shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (transportedShiftedReconstructedUniformSolution
      D₁ D₂ K₁ K₂ u₀₁ transport hT)
    (shiftedReconstructedUniformSolution D₂ K₂ u₀₂)
  correctedLowerLinearization : CorrectedLowerLinearizationData
    ((shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (transportedShiftedReconstructedUniformSolution
      D₁ D₂ K₁ K₂ u₀₁ transport hT)
    (shiftedReconstructedUniformSolution D₂ K₂ u₀₂)
    (shiftedReconstructedInteriorRateDifference
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport)
    boundarySupport
  zero_path_eq :
    transportedShiftedReconstructedUniformSolution
        D₁ D₂ K₁ K₂ u₀₁ transport hT
        (⟨0, ⟨le_rfl,
          ((shiftedReconstructedAffineData D₂).uniformLifespan K₂).property⟩⟩ :
          Set.Icc (0 : ℝ)
            ((shiftedReconstructedAffineData D₂).uniformLifespan K₂ : ℝ)) =
      shiftedReconstructedUniformSolution D₂ K₂ u₀₂
        (⟨0, ⟨le_rfl,
          ((shiftedReconstructedAffineData D₂).uniformLifespan K₂).property⟩⟩ :
          Set.Icc (0 : ℝ)
            ((shiftedReconstructedAffineData D₂).uniformLifespan K₂ : ℝ))

set_option maxHeartbeats 2000000 in
/-- The exact flat-HS package instantiates the compact energy certificate for
two reconstructed shifted solutions. -/
noncomputable def compactParabolicDifferenceEnergyData_of_reconstructedFlatHS
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := T₂) K₂)
    (transport : BUC₂ →L[ℝ] BUC₂)
    (hT : (shiftedReconstructedAffineData D₁).uniformLifespan K₁ =
      (shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (C : ReconstructedFlatHSComparisonData (Q := Q)
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT) :
    CompactParabolicDuhamelDifferenceEnergyData (M := Q)
      ((shiftedReconstructedAffineData D₂).uniformLifespan K₂)
      (transportedShiftedReconstructedUniformSolution
        D₁ D₂ K₁ K₂ u₀₁ transport hT)
      (shiftedReconstructedUniformSolution D₂ K₂ u₀₂) :=
  compactParabolicDuhamelDifferenceEnergyData_of_flatHS
    ((shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (transportedShiftedReconstructedUniformSolution
      D₁ D₂ K₁ K₂ u₀₁ transport hT)
    (shiftedReconstructedUniformSolution D₂ K₂ u₀₂)
    (shiftedReconstructedInteriorRateDifference
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport)
    (fun _ ht ↦
      extended_castMapAffineUniformSolutions_hasDerivAt_interior_automatic
        (shiftedReconstructedAffineData D₁)
        (shiftedReconstructedAffineData D₂)
        K₁ K₂ u₀₁ u₀₂ transport hT ht)
    C.zero_path_eq
    C.boundarySupport C.correctedLowerLinearization

/-- Zero initial difference plus the two flat-HS obligations identifies the
transported and target reconstructed coefficient paths. -/
theorem transportedShiftedReconstructedUniformSolution_eq_of_flatHS
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      (E := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData (E := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData (E := E) (F := T₂) K₂)
    (transport : BUC₂ →L[ℝ] BUC₂)
    (hT : (shiftedReconstructedAffineData D₁).uniformLifespan K₁ =
      (shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (C : ReconstructedFlatHSComparisonData (Q := Q)
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT) :
    transportedShiftedReconstructedUniformSolution
        D₁ D₂ K₁ K₂ u₀₁ transport hT =
      shiftedReconstructedUniformSolution D₂ K₂ u₀₂ :=
  duhamelPaths_eq_of_compactParabolicDifferenceEnergy _ _ _
    (compactParabolicDifferenceEnergyData_of_reconstructedFlatHS
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT C)

end ReconstructedAffineComparison

section ReconstructedChartEntryEquality

universe u v

variable {n : ℕ} {M : Type u} {Q : Type v}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]
variable [TopologicalSpace Q] [CompactSpace Q] [Nonempty Q]

local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

variable {iota₁ kappa₁ iota₂ kappa₂ : Type*}

/-- Flat-HS energy gives equality of every reconstructed scalar chart entry
on the common positive-time interior (indeed the projected equality holds for
all real time parameters). -/
theorem reconstructedCoordinateSolutionPath_entries_eq_of_flatHS
    (D₁ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₁ kappa₁)
    (D₂ : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota₂ kappa₂)
    (K₁ K₂ : ℝ≥0)
    (u₀₁ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₁)
    (u₀₂ : SemilinearBUCBoundedData («E» := E) (F := T₂) K₂)
    (transport : BUC₂ →L[ℝ] BUC₂)
    (hT : (shiftedReconstructedAffineData D₁).uniformLifespan K₁ =
      (shiftedReconstructedAffineData D₂).uniformLifespan K₂)
    (hinit : transport (u₀₁ : BUC₂) = (u₀₂ : BUC₂))
    (C : ReconstructedFlatHSComparisonData (Q := Q)
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT)
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (transport f) x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₂ K₂ u₀₂ t)
          x₂ v₂ w₂ =
        coordinateMetricValue
          (reconstructedCoordinateSolutionPath D₁ K₁ u₀₁ t)
          x₁ v₁ w₁ := by
  let energy :=
    compactParabolicDifferenceEnergyData_of_reconstructedFlatHS
      D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT C
  have hslope :=
    hasTransportedParabolicDuhamelDifferenceSlopeBound_of_compactEnergy
      hT 0 transport
      ((shiftedReconstructedAffineData D₁).uniformSolution K₁ u₀₁)
      ((shiftedReconstructedAffineData D₂).uniformSolution K₂ u₀₂)
      energy
  exact reconstructedCoordinateSolutionPath_value_eq_of_parabolicDifferenceSlopeBound
    D₁ D₂ K₁ K₂ u₀₁ u₀₂ transport hT hinit 0 hslope
    x₁ x₂ v₁ w₁ v₂ w₂ heval

end ReconstructedChartEntryEquality

section ChartwiseFlatHSEnergy

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [CompactSpace M] [Nonempty M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

/-- Chart-indexed flat-HS data.  The boundary/support and corrected-lower
obligations remain visibly separate for every ordered pair of anchors. -/
structure ChartwiseBUCFlatHSEnergyData
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K) where
  transport : M → M → BUC₂ →L[ℝ] BUC₂
  uniformLifespan_eq : ∀ anchor₁ anchor₂,
    chartwiseShiftedBUCUniformLifespan D K anchor₁ =
      chartwiseShiftedBUCUniformLifespan D K anchor₂
  initial_eq : ∀ anchor₁ anchor₂,
    transport anchor₁ anchor₂ (u₀ anchor₁ : BUC₂) =
      (u₀ anchor₂ : BUC₂)
  comparison : ∀ anchor₁ anchor₂,
    ReconstructedFlatHSComparisonData (Q := M)
      (D anchor₁) (D anchor₂) K K
      (u₀ anchor₁) (u₀ anchor₂)
      (transport anchor₁ anchor₂)
      (uniformLifespan_eq anchor₁ anchor₂)

/-- Every chartwise flat-HS comparison supplies the exact overlap energy
package consumed by the established covariance pipeline. -/
noncomputable def ChartwiseBUCFlatHSEnergyData.toOverlapEnergyData
    {iota kappa : Type*}
    {D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa}
    {K : ℝ≥0}
    {u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K}
    (H : ChartwiseBUCFlatHSEnergyData D K u₀) :
    ChartwiseBUCOverlapParabolicEnergyData D K u₀ where
  transport := H.transport
  uniformLifespan_eq := H.uniformLifespan_eq
  initial_eq := H.initial_eq
  difference_energy := by
    intro anchor₁ anchor₂
    refine ⟨?_⟩
    exact compactParabolicDifferenceEnergyData_of_reconstructedFlatHS
      (D anchor₁) (D anchor₂) K K
      (u₀ anchor₁) (u₀ anchor₂)
      (H.transport anchor₁ anchor₂)
      (H.uniformLifespan_eq anchor₁ anchor₂)
      (H.comparison anchor₁ anchor₂)

/-- Flat-HS chartwise data therefore also supply the slope interface used by
the pre-existing reconstructed-coordinate covariance theorem. -/
noncomputable def ChartwiseBUCFlatHSEnergyData.toOverlapSlopeData
    {iota kappa : Type*}
    {D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa}
    {K : ℝ≥0}
    {u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K}
    (H : ChartwiseBUCFlatHSEnergyData D K u₀) :
    ChartwiseBUCOverlapParabolicUniquenessData D K u₀ :=
  H.toOverlapEnergyData.toSlopeData

omit [ChartedSpace E M] [IsManifold I ∞ M] in
/-- Pairwise flat-HS data identify every transported reconstructed chart
entry on the common positive-time interior (and, by projection, at all real
time parameters). -/
theorem chartwiseReconstructedCoordinateSolutionPath_entries_eq_of_flatHS
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K)
    (H : ChartwiseBUCFlatHSEnergyData D K u₀)
    (anchor₁ anchor₂ : M)
    (x₁ x₂ v₁ w₁ v₂ w₂ : E)
    (heval : ∀ f : BUC₂,
      coordinateMetricValue (H.transport anchor₁ anchor₂ f)
          x₂ v₂ w₂ =
        coordinateMetricValue f x₁ v₁ w₁) :
    ∀ t : ℝ,
      coordinateMetricValue
          (reconstructedCoordinateSolutionPath
            (D anchor₂) K (u₀ anchor₂) t) x₂ v₂ w₂ =
        coordinateMetricValue
          (reconstructedCoordinateSolutionPath
            (D anchor₁) K (u₀ anchor₁) t) x₁ v₁ w₁ :=
  reconstructedCoordinateSolutionPath_entries_eq_of_flatHS
    (D anchor₁) (D anchor₂) K K
    (u₀ anchor₁) (u₀ anchor₂)
    (H.transport anchor₁ anchor₂)
    (H.uniformLifespan_eq anchor₁ anchor₂)
    (H.initial_eq anchor₁ anchor₂)
    (H.comparison anchor₁ anchor₂)
    x₁ x₂ v₁ w₁ v₂ w₂ heval

/-- The flat-HS energy construction feeds the established endpoint-germ and
background assembly to give full inverse-gauge chart covariance. -/
theorem chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_flatHSEnergy
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (H : ChartwiseBUCFlatHSEnergyData D K u₀)
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
      ∀ a b : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z a)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z b) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z a b :=
  chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_endpointGerms_background_and_parabolicDifferenceSlope
    D K u₀ Phi DPhi H.toOverlapSlopeData hPhi hendpointTarget
    hendpointSource hcompat hbackground htransportEvaluation

end ChartwiseFlatHSEnergy

section GlobalMetricFamilyAssembly

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [CompactSpace M] [Nonempty M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => CoordinateTwoTensor E
local notation "BUC₂" => CoordinateBUCTensor E

/--
End-to-end assembly: flat Hilbert--Schmidt overlap energy proves chartwise
coefficient equality, endpoint germs turn it into inverse-gauge covariance,
and the self-chart construction returns one global closed smooth metric
family realizing every preferred-chart reconstruction.
-/
theorem exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction_of_flatHSEnergy
    {iota kappa : Type*}
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := T₂) iota kappa)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData («E» := E) (F := T₂) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (H : ChartwiseBUCFlatHSEnergyData D K u₀)
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
          coordinateMetricValue f (Phi anchor₁ t z) a b)
    (hsymm : ∀ t x u v,
      chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi t x (extChartAt I x x) u v =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < chartwiseReconstructedInverseGaugeMetricSpacetime
        D K u₀ Phi DPhi t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E |
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, chartwiseReconstructedInverseGaugeMetricSpacetime
              D K u₀ Phi DPhi t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ)))) :
    ∃ rt : ℝ → ClosedSmoothRiemannianMetric n M,
      ∀ t anchor z,
        z ∈ (extChartAt I anchor).target →
        CovariantDerivative.chartMetric (rt t).inner anchor z =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor z := by
  have hcov :=
    chartwiseReconstructedInverseGaugeMetricSpacetime_covariant_of_flatHSEnergy
      D K u₀ Phi DPhi H hPhi hendpointTarget hendpointSource hcompat
      hbackground htransportEvaluation
  exact exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction
    D K u₀ Phi DPhi hsymm hpos hbounded hsmooth hcov

end GlobalMetricFamilyAssembly

end Poincare
