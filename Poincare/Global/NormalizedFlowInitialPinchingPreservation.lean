import Poincare.Global.NormalizedFlowPinchingEvolutionAutomatic
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor

/-!
# Forward normalized-flow pinching from initial data

Positive initial scalar curvature stays positive at every finite forward time.
The initial Ricci quotient bound is preserved, giving the eigenvalue floor
with coefficient `2 * ε₀ - 1/3`.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.NormalizedFlowInitialPinchingPreservation

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

local notation "I" => closedSmoothModelWithCorners 3

/-- The exponential scalar comparison gives positivity on every forward slice. -/
theorem scalarAt_pos_of_initial_scalar_pos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x := by
  obtain ⟨P, hP, _, hd⟩ := exists_normalizationPrimitive_of_normalizedRicciFlow gt hflow hjoint
  obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
    continuous_iff_continuousAt.mpr fun p ↦
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
  have hp := normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
    (gt := gt) (t0 := 0) hrho (by simpa only [zero_add] using hs)
    (fun t ht x ↦ by
      simpa only [zero_add] using
        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
          (x := x) (hflow t ht) hL)
    (fun t ht x ↦ by
      simpa only [zero_add] using scalarAt_contMDiffAt_two_of_normalizedRicciFlow
        (hflow t ht) (hL.timeVariationEntries t) x)
    P hP (by simpa only [zero_add] using hd) hlow
  intro t ht x
  have hpos : 0 < (rho / 2) * Real.exp (-(P t - P 0)) :=
    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _)
  exact hpos.trans (by simpa only [zero_add] using hp t ht x)

omit [SecondCountableTopology M] [SimplyConnectedSpace M] in
/-- Joint `C³` regularity and the normalized equation give spatial `C²`
regularity of the ordinary Ricci quotient on a positive-scalar slice. -/
theorem contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ}
    (hjoint : ∀ x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hpos : ∀ x, 0 < (gt t).scalarAt x) (x : M) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t).pinchingQuotientAt y) x := by
  have hEntries : ∀ y : M, TimeVariationExtContMDiffAt gt t y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three (hjoint y)
  have hRic := ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
    hflow hEntries x
  exact contMDiffAt_two_pinchingQuotientAt (gt t) x
    (contMDiffAt_two_ricciNormSqAt_of_ricci_entries (gt t) x hRic)
    (scalarAt_contMDiffAt_two_of_normalizedRicciFlow hflow hEntries x) (hpos x).ne'

/-- Initial eigenvalue pinching preserves its Ricci quotient bound on the whole
forward ray and yields the explicit degraded eigenvalue floor. -/
theorem initial_pinching_preserved
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (ε₀ : ℝ)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hinit : ∀ x, 0 < (gt 0).scalarAt x) (hεle : ε₀ ≤ 1 / 3)
    (hfloor : GlobalRicciEigenvalueFloor3 (gt 0) ε₀) :
    ∀ t ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (gt t) (2 * ε₀ - 1 / 3) ∧
      GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2) := by
  have hpos := scalarAt_pos_of_initial_scalar_pos gt hjoint hflow hinit
  have hQ₂ : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t).pinchingQuotientAt y) x :=
    fun t ht x ↦ contMDiffAt_two_pinchingQuotientAt_of_normalizedFlow
      (hjoint t) (hflow t ht) (hpos t ht) x
  have hmax0 : pinchingMaximumTrack gt 0 0 ≤ 1 - 4 * ε₀ + 6 * ε₀ ^ 2 := by
    obtain ⟨x, hx⟩ := exists_pinchingQuotientAt_isMaxOn (gt 0) (hQ₂ 0 (by simp))
    have hbound := (gt 0).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
      hinit hfloor x
    simpa only [pinchingMaximumTrack, zero_add,
      pinchingMaximumAt_eq_of_isMaxOn (gt 0) hx] using hbound
  intro t ht
  have hcont : ContinuousOn
      (↿fun τ (x : M) ↦ (gt (0 + τ)).pinchingQuotientAt x)
      (Icc (0 : ℝ) t ×ˢ (Set.univ : Set M)) :=
    continuousOn_pinchingQuotientAt_timeShift_of_metricEntriesJointContDiffAt_three
      (fun τ _ x ↦ hjoint (0 + τ) x)
      (fun τ hτ x ↦ by simpa only [zero_add] using (hpos τ hτ.1 x).ne')
  have hpres := hamilton_pinching_preserved_continuousOn
    (gt := gt) (t₀ := 0) (T := t) rfl ht hcont
    (fun τ hτ x ↦ by simpa only [zero_add] using hQ₂ τ hτ.1 x)
    (fun τ hτ x ↦ by
      simpa only [zero_add] using
        NormalizedFlowPinchingEvolutionAutomatic.satisfiesPinchingQuotientEvolutionAt
          hjoint (hflow τ hτ.1) (hpos τ hτ.1) x)
  have hbound : GlobalPinchingQuotientBound3 (gt t) (1 - 4 * ε₀ + 6 * ε₀ ^ 2) := by
    intro x
    have hpoint : (gt t).pinchingQuotientAt x ≤ pinchingMaximumTrack gt 0 t := by
      simpa only [pinchingMaximumTrack, zero_add] using
        pinchingQuotientAt_le_pinchingMaximumAt (gt t) (hQ₂ t ht) x
    exact hpoint.trans ((hpres t ⟨ht, le_rfl⟩).trans hmax0)
  refine ⟨?_, hbound⟩
  intro x b μ hEig
  exact (gt t).eigenvalue_pinched_of_pinchingQuotientAt_le
    hεle (hpos t ht x) (hbound x) b μ hEig

end Poincare.NormalizedFlowInitialPinchingPreservation
