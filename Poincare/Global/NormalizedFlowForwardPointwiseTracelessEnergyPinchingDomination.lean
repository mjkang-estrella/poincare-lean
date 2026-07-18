import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching

/-!
# Geometric domination of the normalized traceless-Ricci reaction

The exact normalized evolution leaves one honest algebraic obstruction:
Hamilton's cubic traceless-Ricci reaction must be dominated by the
normalization term.  There is no universal coercive sign.  This file derives
the sharp bound available from the repository's improved eigenvalue-pinching
lemma and then records the additional quotient and scalar/mean comparison
needed for a positive decay rate.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3
local notation "TM" => (TangentSpace I : M → Type _)

/-!
## Pointwise cubic and normalized-reaction bounds
-/

/-- Hamilton's improved eigenvalue-pinching sign is equivalently an upper
bound for the raw cubic traceless reaction.  The factor
`2 (2 - delta) |Ric|^2 / R` is exact; no sign or size estimate is discarded.
-/
theorem
    pinchingTracelessRicciReactionTrace3At_le_two_mul_two_sub_delta_mul_ricciNorm_div_scalar_mul_traceless
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) {epsilon delta : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hScalarPos : 0 < g.scalarAt x)
    (hEigenFloor :
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (mu : Fin 3 → ℝ),
        (∀ i : Fin 3, g.ricciEndoAt x (b i) = mu i • b i) →
          ∀ i : Fin 3, epsilon * g.scalarAt x ≤ mu i) :
    g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
      (2 * (2 - delta) * g.ricciNormSqAt x / g.scalarAt x) *
        g.tracelessRicciNormSqAt x := by
  let R : ℝ := g.scalarAt x
  let N : ℝ := g.ricciNormSqAt x
  let U : ℝ := g.tracelessRicciNormSqAt x
  let T : ℝ :=
    g.pinchingTracelessRicciReactionTrace3At x
      (g.pinchingRicciNormReactionMotionTraceCubicAt x)
  let p : ℝ := 2 - delta
  have hTerm :
      g.tracelessPinchingReactionTermAt x delta
          (g.pinchingTracelessRicciReactionTrace3At x
            (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ≤ 0 :=
    g.tracelessPinchingReactionTermAt_nonpos_of_eigenvalue_pinched
      rfl hepsilonPos hepsilonLe hdeltaNonneg hdeltaAdm hScalarPos hEigenFloor
  have hRpos : 0 < R := by simpa [R] using hScalarPos
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hRpPos : 0 < R ^ p := Real.rpow_pos_of_pos hRpos p
  have hRpNe : R ^ p ≠ 0 := ne_of_gt hRpPos
  have hpow : R ^ (3 - delta) = R ^ p * R := by
    have h := Real.rpow_add_one hRne p
    simpa [p, show 2 - delta + 1 = 3 - delta by ring] using h
  unfold ClosedSmoothRiemannianMetric.tracelessPinchingReactionTermAt
    ClosedSmoothRiemannianMetric.pinchingScalarReactionAt at hTerm
  change T / R ^ p - p * U * (2 * N) / R ^ (3 - delta) ≤ 0 at hTerm
  rw [hpow] at hTerm
  have hcombine :
      T / R ^ p - p * U * (2 * N) / (R ^ p * R) =
        (T * R - 2 * p * N * U) / (R ^ p * R) := by
    field_simp [hRne, hRpNe]
  rw [hcombine] at hTerm
  have hDenPos : 0 < R ^ p * R := mul_pos hRpPos hRpos
  have hNumerator : T * R - 2 * p * N * U ≤ 0 := by
    have h := (div_le_iff₀ hDenPos).mp hTerm
    simpa using h
  have hDiv : T ≤ (2 * p * N * U) / R := by
    apply (le_div_iff₀ hRpos).2
    linarith
  dsimp [T, R, N, U, p] at hDiv ⊢
  calc
    _ ≤ (2 * (2 - delta) * g.ricciNormSqAt x *
          g.tracelessRicciNormSqAt x) / g.scalarAt x := hDiv
    _ = _ := by ring

/-- The weakest direct coercivity bridge after eigenvalue pinching: the
normalization coefficient must dominate the exact cubic coefficient by the
requested rate. -/
theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) {epsilon delta rate : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hScalarPos : 0 < g.scalarAt x)
    (hEigenFloor :
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (mu : Fin 3 → ℝ),
        (∀ i : Fin 3, g.ricciEndoAt x (b i) = mu i • b i) →
          ∀ i : Fin 3, epsilon * g.scalarAt x ≤ mu i)
    (hNormalizationGap :
      2 * (2 - delta) * g.ricciNormSqAt x / g.scalarAt x + rate ≤
        (4 / 3 : ℝ) * meanScalar g) :
    normalizedTracelessRicciEvolutionReactionAt g x ≤
      -rate * g.tracelessRicciNormSqAt x := by
  have hCubic :=
    pinchingTracelessRicciReactionTrace3At_le_two_mul_two_sub_delta_mul_ricciNorm_div_scalar_mul_traceless
      g x hepsilonPos hepsilonLe hdeltaNonneg hdeltaAdm hScalarPos hEigenFloor
  apply
    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
  have hCoefficient :
      2 * (2 - delta) * g.ricciNormSqAt x / g.scalarAt x ≤
        (4 / 3 : ℝ) * meanScalar g - rate := by
    linarith
  exact hCubic.trans
    (mul_le_mul_of_nonneg_right hCoefficient
      (g.tracelessRicciNormSqAt_nonneg x (by norm_num)))

/-- A geometric sufficient condition for the normalization gap.  Besides
Hamilton eigenvalue pinching, it uses a scalar-normalized Ricci quotient bound
and an explicit comparison between pointwise scalar curvature and its mean.
The coefficient condition is sharp for this chain of inequalities. -/
theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_quotient_scalar_mean
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) {epsilon delta kappa C rate : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta) (hdeltaLeTwo : delta ≤ 2)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hkappaNonneg : 0 ≤ kappa)
    (hScalarPos : 0 < g.scalarAt x)
    (hEigenFloor :
      ∀ (b : Module.Basis (Fin 3) ℝ (TM x)) (mu : Fin 3 → ℝ),
        (∀ i : Fin 3, g.ricciEndoAt x (b i) = mu i • b i) →
          ∀ i : Fin 3, epsilon * g.scalarAt x ≤ mu i)
    (hQuotient : g.pinchingQuotientAt x ≤ kappa)
    (hScalarMean : g.scalarAt x ≤ C * meanScalar g)
    (hRate :
      rate ≤
        ((4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C) * meanScalar g) :
    normalizedTracelessRicciEvolutionReactionAt g x ≤
      -rate * g.tracelessRicciNormSqAt x := by
  apply
    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
      g x hepsilonPos hepsilonLe hdeltaNonneg hdeltaAdm hScalarPos hEigenFloor
  have hRpos := hScalarPos
  have hRsqPos : 0 < (g.scalarAt x) ^ 2 := sq_pos_of_pos hRpos
  have hNormLe :
      g.ricciNormSqAt x ≤ kappa * (g.scalarAt x) ^ 2 := by
    apply (div_le_iff₀ hRsqPos).mp
    simpa [ClosedSmoothRiemannianMetric.pinchingQuotientAt] using hQuotient
  have hNormDivLe :
      g.ricciNormSqAt x / g.scalarAt x ≤ kappa * g.scalarAt x := by
    apply (div_le_iff₀ hRpos).2
    nlinarith
  have hpNonneg : 0 ≤ 2 * (2 - delta) := by
    nlinarith
  have hFirst :
      2 * (2 - delta) * (g.ricciNormSqAt x / g.scalarAt x) ≤
        2 * (2 - delta) * (kappa * g.scalarAt x) :=
    mul_le_mul_of_nonneg_left hNormDivLe hpNonneg
  have hScaleNonneg : 0 ≤ 2 * (2 - delta) * kappa :=
    mul_nonneg hpNonneg hkappaNonneg
  have hSecond :
      2 * (2 - delta) * kappa * g.scalarAt x ≤
        2 * (2 - delta) * kappa * (C * meanScalar g) :=
    mul_le_mul_of_nonneg_left hScalarMean hScaleNonneg
  calc
    2 * (2 - delta) * g.ricciNormSqAt x / g.scalarAt x + rate
        = 2 * (2 - delta) *
            (g.ricciNormSqAt x / g.scalarAt x) + rate := by ring
    _ ≤ 2 * (2 - delta) * (kappa * g.scalarAt x) + rate := by
      linarith
    _ ≤ 2 * (2 - delta) * kappa * (C * meanScalar g) + rate := by
      linarith
    _ ≤ (4 / 3 : ℝ) * meanScalar g := by
      nlinarith

/-!
## Global slice and forward-flow consumers
-/

/-- Global Hamilton pinching, quotient, and scalar/mean comparison data imply
the explicit reaction domination on an entire time slice. -/
theorem normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
    (g : ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    {epsilon delta kappa C rate : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta) (hdeltaLeTwo : delta ≤ 2)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hkappaNonneg : 0 ≤ kappa)
    (hScalarPos : ∀ x : M, 0 < g.scalarAt x)
    (hEigenFloor : GlobalRicciEigenvalueFloor3 g epsilon)
    (hQuotient : GlobalPinchingQuotientBound3 g kappa)
    (hScalarMean : ∀ x : M, g.scalarAt x ≤ C * meanScalar g)
    (hRate :
      rate ≤
        ((4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C) * meanScalar g) :
    ∀ x : M,
      normalizedTracelessRicciEvolutionReactionAt g x ≤
        -rate * g.tracelessRicciNormSqAt x := by
  intro x
  exact
    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_quotient_scalar_mean
      g x hepsilonPos hepsilonLe hdeltaNonneg hdeltaLeTwo hdeltaAdm
      hkappaNonneg (hScalarPos x) (hEigenFloor x) (hQuotient x)
      (hScalarMean x) hRate

/-- The geometric pinching package discharges the final reaction premise in
the fully automatic global-joint pointwise decay theorem. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_pinching_domination_of_normalizedFlow_global_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {epsilon delta kappa C rate : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta) (hdeltaLeTwo : delta ≤ 2)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hkappaNonneg : 0 ≤ kappa)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hScalarPos : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt t).scalarAt x)
    (hEigenFloor : ∀ t ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt t) epsilon)
    (hQuotient : ∀ t ∈ Ici (0 : ℝ),
      GlobalPinchingQuotientBound3 (gt t) kappa)
    (hScalarMean : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      (gt t).scalarAt x ≤ C * meanScalar (gt t))
    (hRate : ∀ t ∈ Ici (0 : ℝ),
      rate ≤
        ((4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C) *
          meanScalar (gt t)) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) * Real.exp ((-rate) * t.1) := by
  apply
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
      gt hFlow hJointMetricEntries
  intro t ht x
  exact
    normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
      (gt t) hepsilonPos hepsilonLe hdeltaNonneg hdeltaLeTwo hdeltaAdm
      hkappaNonneg (hScalarPos t ht) (hEigenFloor t ht) (hQuotient t ht)
      (hScalarMean t ht) (hRate t ht) x

/-- Under the same geometric pinching package and the pre-existing volume and
measurability inputs, the forward traceless-Ricci energy is integrable. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pinching_domination_of_normalizedFlow_global_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {epsilon delta kappa C rate : ℝ}
    (hepsilonPos : 0 < epsilon) (hepsilonLe : epsilon ≤ 1 / 3)
    (hdeltaNonneg : 0 ≤ delta) (hdeltaLeTwo : delta ≤ 2)
    (hdeltaAdm :
      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hkappaNonneg : 0 ≤ kappa) (hrate : 0 < rate)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hJointMetricEntries : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (hScalarPos : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (gt t).scalarAt x)
    (hEigenFloor : ∀ t ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt t) epsilon)
    (hQuotient : ∀ t ∈ Ici (0 : ℝ),
      GlobalPinchingQuotientBound3 (gt t) kappa)
    (hScalarMean : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      (gt t).scalarAt x ≤ C * meanScalar (gt t))
    (hRate : ∀ t ∈ Ici (0 : ℝ),
      rate ≤
        ((4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C) *
          meanScalar (gt t)) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_actualNormalizedReaction_domination_of_normalizedFlow_global_jointMetricEntries_Ici
      gt hFlow hVolumeVariation hMeasurable hJointMetricEntries hrate
  intro t ht x
  exact
    normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
      (gt t) hepsilonPos hepsilonLe hdeltaNonneg hdeltaLeTwo hdeltaAdm
      hkappaNonneg (hScalarPos t ht) (hEigenFloor t ht) (hQuotient t ht)
      (hScalarMean t ht) (hRate t ht) x

end Poincare
