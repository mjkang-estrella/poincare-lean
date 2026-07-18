import Poincare.Global.NormalizedFlowHausdorffLichnerowiczEndpoint

/-!
# Scalar regularity from a smooth normalized Ricci-flow slice

For normalized Ricci flow,

`∂ₜg = -2 Ric + (2 / n) meanScalar(g) g`.

At a fixed time the mean scalar is a spatial constant.  Consequently spatial
`C²` regularity of the metric-variation entries, together with the already
smooth metric entries, gives spatial `C²` regularity of the Ricci entries.
Taking the inverse-metric trace then proves `C²` regularity of scalar
curvature.  The final theorem uses this fact to remove the independent
all-time scalar-regularity premise from the Hausdorff/Lichnerowicz/LSC
Hamilton endpoint.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section NormalizedFlowSlice

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The normalized-flow equation expresses the Ricci tensor as a spatially
constant linear combination of the metric time variation and the metric.
Thus `C²` time-variation entries give `C²` Ricci entries. -/
theorem ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hEntries : ∀ y : M, TimeVariationExtContMDiffAt gt t₀ y 2)
    (x : M) :
    CovTensor2ExtContMDiffAt (ricciVariationField (gt t₀)) x 2 := by
  intro p q
  let H : M → ℝ := fun y ↦
    timeDerivAt gt t₀ y (extend E p y) (extend E q y)
  let G : M → ℝ := fun y ↦
    (gt t₀).inner y (extend E p y) (extend E q y)
  let R : M → ℝ := fun y ↦
    (gt t₀).ricciAt y (extend E p y) (extend E q y)
  let c : ℝ := (1 / (n : ℝ)) * meanScalar (gt t₀)
  have hH : ContMDiffAt I 𝓘(ℝ) 2 H x := by
    simpa [H, TimeVariationExtContMDiffAt,
      CovTensor2ExtContMDiffAt] using hEntries x p q
  have hG : ContMDiffAt I 𝓘(ℝ) 2 G x := by
    simpa [G, MetricExtContMDiffAt] using
      metricExtContMDiffAt_two (gt t₀) x p q
  have hNegHalfH : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (-1 / 2 : ℝ) * H y) x := by
    simpa [smul_eq_mul] using
      (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ) 2
        (fun _ : M ↦ (-1 / 2 : ℝ)) x).smul hH
  have hcG : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ c * G y) x := by
    simpa [smul_eq_mul] using
      (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ) 2
        (fun _ : M ↦ c) x).smul hG
  have heq : R = fun y : M ↦ (-1 / 2 : ℝ) * H y + c * G y := by
    funext y
    have hEq :=
      isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_eq_normalizedRicciFlowRHSAt
        (gt := gt) (t₀ := t₀) (x := y) (hFlow y)
        (extend E p y) (extend E q y)
    change H y =
      -2 * R y + (2 / (n : ℝ)) * meanScalar (gt t₀) * G y at hEq
    rw [hEq]
    dsimp [c]
    ring
  change ContMDiffAt I _ 2 R x
  rw [heq]
  exact hNegHalfH.add hcG

/-- The inverse-metric trace of the preceding `C²` Ricci tensor is the actual
scalar curvature, so scalar curvature is `C²` on a normalized-flow slice. -/
theorem scalarAt_contMDiffAt_two_of_normalizedRicciFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hEntries : ∀ y : M, TimeVariationExtContMDiffAt gt t₀ y 2)
    (x : M) :
    ContMDiffAt I 𝓘(ℝ) 2 (fun y : M ↦ (gt t₀).scalarAt y) x := by
  have hTraceEntries :
      TraceMetricVariationEntriesExtContMDiffAt
        (gt t₀) (ricciVariationField (gt t₀)) x 2 :=
    ⟨ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
        hFlow hEntries x,
      metricExtContMDiffAt_two (gt t₀) x⟩
  have hTrace : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦
        traceMetricVariationAt (gt t₀) (ricciVariationField (gt t₀)) y) x :=
    traceMetricVariationAt_contMDiffAt_two_of_entries
      (g := gt t₀) (h := ricciVariationField (gt t₀)) (x := x)
      hTraceEntries (ricciVariationBilinForm (gt t₀))
      (by intro y p q; rfl)
  have hfun :
      (fun y : M ↦
        traceMetricVariationAt (gt t₀) (ricciVariationField (gt t₀)) y) =
      fun y : M ↦ (gt t₀).scalarAt y := by
    funext y
    exact traceMetricVariationAt_ricci (gt t₀) y
  simpa [hfun] using hTrace

end NormalizedFlowSlice

section DimensionThreeEndpoint

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Actual Hausdorff moving integrals, automatic Lichnerowicz assemblies, and
the normalized-flow equation now also discharge the scalar `C²` premise in
the lower-semicontinuous absolute-dissipation Hamilton endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffLichnerowiczRegularity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartScalarVariation_of_globalLichnerowiczRegularity_of_lscCompactness
      hFlow hHausdorff hLichnerowicz
      (fun t ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
        (hFlow t) (hLichnerowicz.timeVariationEntries t))
      hStokes hFiniteDissipation hCompact hc hScalarLower

end DimensionThreeEndpoint

end Poincare
