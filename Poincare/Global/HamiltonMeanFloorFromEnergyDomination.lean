import Poincare.Global.HamiltonChartDensityLocalDomination
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination

/-!
# Mean scalar floor from energy domination

Moving integral differentiation follows from joint C³ metric entries and
explicit closed Laplacian Stokes. The integrated energy inequality then
makes the forward mean scalar nondecreasing. Core existence, Stokes, and
the energy inequality remain explicit inputs.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonMeanFloorFromEnergyDomination
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The moving volume and total-scalar identities, retaining Stokes explicitly. -/
theorem movingDerivatives
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t) := by
  obtain ⟨D⟩ := HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
    gt hjoint (HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint)
  let V := D.toChartFrameDensityVariation
  constructor
  · intro t ht
    exact V.hasDerivAt_totalVolume_of_normalizedFlowAt t (hflow t ht)
  · intro t ht
    exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
      V hjoint (scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three hjoint)
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
      t (hflow t ht) (hstokes t ht)

/-- The exact survey mean-floor theorem from pointwise initial positivity. -/
theorem meanFloorFromEnergy
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
  obtain ⟨rho, hrho, hlower⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  exact ⟨meanScalar_pos_of_forall_scalarAt_ge (gt 0) hrho hlower,
    fun t ↦ hm (by simp) t.2 t.2⟩

/-- Positive initial mean suffices for the same uniform floor. -/
theorem meanFloorFromEnergy_of_initialMeanPos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : 0 < meanScalar (gt 0))
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
  exact ⟨hinit, fun t ↦ hm (by simp) t.2 t.2⟩

/-- The final reaction core with positive initial mean, energy domination,
and scalar Stokes replacing the positive floor. Every analytic input is explicit. -/
def HamiltonReactionCore3Energy (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (rate : ℝ),
      Continuous parameter ∧
      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
      0 < meanScalar (gt 0) ∧
      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
      (∀ t ∈ Ici (0 : ℝ),
        ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
      0 < rate ∧
      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
          -rate * (gt t).tracelessRicciNormSqAt x) ∧
      (∀ slot : MetricEntryThirdJetSlot 3 M,
        Continuous (fun p : K × ClosedSmoothModel 3 ↦
          metricEntryThirdJetProfile (metric p.1) slot p.2))

/-- Energy domination supplies the floor in the unchanged final core. -/
theorem hamiltonReactionCore3Final_of_energy
    (h : HamiltonReactionCore3Energy.{u, v} M) :
    HamiltonReactionCore3Final.{u, v} M := by
  rcases h with ⟨K, topK, compactK, gt, metric, parameter, rate,
    hparam, hreal, hinit, henergy, hstokes, hflow, hjoint, hrate, hreaction, hjet⟩
  letI : TopologicalSpace K := topK
  haveI : CompactSpace K := compactK
  have hfloor := meanFloorFromEnergy_of_initialMeanPos gt hjoint hflow hstokes hinit henergy
  exact ⟨K, topK, compactK, gt, metric, parameter, meanScalar (gt 0), rate,
    hparam, hreal, hfloor.1, hfloor.2, hflow, hjoint, hrate, hreaction, hjet⟩

/-- The energy core reaches the Hamilton pinched-limit endpoint. -/
theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy
    (h : HamiltonReactionCore3Energy.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
    (hamiltonReactionCore3Final_of_energy h)

/-- Open existence obligation for the energy core on every compatible Borel manifold. -/
def UniversalHamiltonReactionCoreEnergyStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      HamiltonReactionCore3Energy.{u, v} N

/-- Universal energy cores supply the unchanged universal final cores. -/
theorem universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy
    (h : UniversalHamiltonReactionCoreEnergyStatement.{u, v}) :
    UniversalHamiltonReactionCoreFinalStatement.{u, v} := by
  intro N _ _ _ _ _ _ _ _ _ _
  exact hamiltonReactionCore3Final_of_energy (h N)

/-- Universal energy cores yield universal Hamilton convergence. -/
theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEnergy
    (h : UniversalHamiltonReactionCoreEnergyStatement.{u, v}) :
    UniversalHamiltonConvergenceStatement.{u} :=
  universalHamiltonConvergence_of_universalHamiltonReactionCoreFinal
    (universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy h)

end Poincare.HamiltonMeanFloorFromEnergyDomination
