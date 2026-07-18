import Poincare.Global.HausdorffTotalScalarFirstVariation
import Poincare.Global.NormalizedFlowLowerSemicontinuousCompactness
import Poincare.Global.MetricRaiseTimeDerivative
import Poincare.Global.DeltaGammaFieldRegularity

/-!
# Hausdorff normalized-flow endpoint from automatic Lichnerowicz assemblies

The Hausdorff chart package differentiates the actual moving total-scalar
integral, but its normalized-flow endpoint still accepted the pointwise scalar
variation formula as an independent hypothesis.  This file removes that free
formula.

The remaining regularity package records only the inputs not yet constructed
by the repository: time differentiability of metric entries, neighborhood
regularity for commuting time and spatial derivatives of the connection, and
spatial `C²` regularity of the metric-variation entries.  Existing theorems
then automatically build

* the derivative of the inverse metric,
* the scalar `δΓ` entry bridge,
* both traced `δΓ` Hessian assemblies, and
* the Lichnerowicz scalar-variation formula.

The final theorem combines this construction with the moving Hausdorff volume
and total-scalar derivatives, finite absolute dissipation, and only lower
semicontinuity of the limiting traceless-Ricci energy.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

section AutomaticLichnerowiczAssemblies

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The pointwise outputs needed by the closed Lichnerowicz scalar-variation
formula.  The inverse-metric derivative is deliberately absent: it follows
from `timeDifferentiable` by `hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt`.
-/
structure LichnerowiczDeltaGammaAssembliesAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t : ℝ) (x : M) : Prop where
  metricFlowRegular : MetricFlowRegularAt gt t x
  timeDifferentiable : TimeDifferentiableAt gt t x
  divergenceTrace : DeltaGammaDivergenceTraceAssemblyAt gt t x
  contractionTrace : DeltaGammaContractionTraceAssemblyAt gt t x

/-- Global raw regularity from which both traced `δΓ` assemblies can be
constructed automatically at every spacetime point.

The neighborhood field is the genuine mixed time/spatial derivative boundary
still used by the Koszul and curvature-variation chain.  The `C²` entry field
supplies all older first- and second-covariant differentiability predicates.
-/
structure GlobalLichnerowiczAssemblyRegularity
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) : Prop where
  timeDifferentiable : ∀ t : ℝ, ∀ y : M, TimeDifferentiableAt gt t y
  nearMetricFlowRegularity : ∀ t : ℝ, ∀ x : M,
    ∀ᶠ y in nhds x,
      MetricFlowRegularAt gt t y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun s ↦
              extDerivFun
                (fun z : M ↦ (gt s).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦ timeDerivAt gt t z (extend E b z) (extend E c z))
              y a) t)
  timeVariationEntries : ∀ t : ℝ, ∀ y : M,
    TimeVariationExtContMDiffAt gt t y 2

/-- Add the automatically smooth metric entries to the recorded `C²`
variation entries. -/
theorem GlobalLichnerowiczAssemblyRegularity.traceEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (H : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ) (x : M) :
    TimeVariationTraceEntriesExtContMDiffAt gt t x 2 :=
  ⟨H.timeVariationEntries t x, metricExtContMDiffAt_two (gt t) x⟩

/-- The raw global package constructs the complete pointwise pair of traced
`δΓ` assemblies.

This is the automatic portion of the strongest scalar-evolution assembly
route currently present in the repository, separated from the unnormalized
Ricci-flow-specific algebraic tail.
-/
theorem GlobalLichnerowiczAssemblyRegularity.assembliesAt
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (H : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ) (x : M) :
    LichnerowiczDeltaGammaAssembliesAt gt t x := by
  have hgt : ∀ y : M, TimeDifferentiableAt gt t y :=
    H.timeDifferentiable t
  have hNear := H.nearMetricFlowRegularity t x
  have hreg : MetricFlowRegularAt gt t x := (hNear.self_of_nhds).1
  have hExt :
      ∀ a b c : TM x,
        HasDerivAt
          (fun s ↦
            extDerivFun
              (fun y : M ↦ (gt s).inner y (extend E b y) (extend E c y)) x a)
          (extDerivFun
            (fun y : M ↦ timeDerivAt gt t y (extend E b y) (extend E c y))
            x a) t :=
    (hNear.self_of_nhds).2
  have hEntries : ∀ y : M,
      TimeVariationTraceEntriesExtContMDiffAt gt t y 2 :=
    H.traceEntries t
  have hCovDiff : ∀ y : M,
      CovTensor2ExtDifferentiableAt (timeDerivAt gt t) y := fun y ↦
    (timeVariationTraceEntriesExtContMDiffAt_two_old_regularities
      (hEntries y)).1
  have hSecond :
      CovTensor2DerivExtDifferentiableAt (gt t) (timeDerivAt gt t) x :=
    covTensor2DerivExtDifferentiableAt_timeDeriv_of_global_entries
      hgt hEntries
  have hBridge : DeltaGammaEntryDerivativeBridgeAt gt t x :=
    deltaGammaEntryDerivativeBridgeAt_of_koszul_regular hgt hNear hSecond
  have hTraceGradient :
      let g : ClosedSmoothRiemannianMetric n M := gt t
      let V : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t
      let f : M → ℝ := fun y ↦ traceMetricVariationAt g V y
      MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% (g.gradient f)) x := by
    let g : ClosedSmoothRiemannianMetric n M := gt t
    let V : ∀ y : M, TM y → TM y → ℝ := timeDerivAt gt t
    let f : M → ℝ := fun y ↦ traceMetricVariationAt g V y
    have hTrace₂ : ContMDiffAt I 𝓘(ℝ) 2 f x := by
      simpa [g, V, f] using
        traceMetricVariationAt_contMDiffAt_two_of_entries
          (g := gt t) (h := timeDerivAt gt t) (x := x)
          (hEntries x)
          (fun y ↦ timeDerivBilinAt gt t y (hgt y))
          (by intro y p q; rfl)
    simpa [g, V, f] using (gt t).mdifferentiableAt_gradient hTrace₂
  have hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t x :=
    deltaGammaDivergenceTraceAssemblyAt_of_hessianAssembly
      (deltaGammaDivergenceTraceHessianAssemblyAt_of_covTensor2Regular
        (gt := gt) (t₀ := t) (x := x)
        hreg hgt hExt hNear hBridge hSecond hCovDiff hTraceGradient)
  have hNearCon :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t y ∧
          CovTensor2ExtDifferentiableAt (timeDerivAt gt t) y ∧
          (∀ a b c : TM y,
            HasDerivAt
              (fun s ↦
                extDerivFun
                  (fun z : M ↦ (gt s).inner z (extend E b z) (extend E c z))
                  y a)
              (extDerivFun
                (fun z : M ↦ timeDerivAt gt t z (extend E b z) (extend E c z))
                y a) t) := by
    filter_upwards [hNear] with y hy
    exact ⟨hy.1, hCovDiff y, hy.2⟩
  have hCon : DeltaGammaContractionTraceAssemblyAt gt t x :=
    deltaGammaContractionTraceAssemblyAt_of_hessianAssembly
      (deltaGammaContractionTraceHessianAssemblyAt_of_traceHessianDerivative
        (deltaGammaContractionTraceHessianDerivativeAt_of_entryBridge_entries_contMDiffAt
          (gt := gt) (t₀ := t) (x := x)
          hBridge hreg hgt hExt hNearCon (hEntries x) hTraceGradient))
  exact ⟨hreg, hgt x, hDiv, hCon⟩

/-- The assembled pointwise package proves actual scalar differentiability
with the inverse-metric derivative supplied automatically. -/
theorem LichnerowiczDeltaGammaAssembliesAt.hasDerivAt_scalar_stokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t : ℝ} {x : M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (A : LichnerowiczDeltaGammaAssembliesAt gt t x) :
    HasDerivAt (fun s ↦ (gt s).scalarAt x)
      (scalarVariationStokesBoundaryAt gt t x -
        metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x) t := by
  simpa [scalarVariationStokesBoundaryAt] using
    hasDerivAt_scalarAt_lichnerowicz
    (raise' := metricRaiseDerivAt gt t x A.timeDifferentiable)
    A.metricFlowRegular A.timeDifferentiable
    (hasDerivAt_metricRaiseContinuousAt_of_timeDifferentiableAt
      A.timeDifferentiable)
    A.divergenceTrace A.contractionTrace

/-- `deriv` form of the assembled scalar-variation statement. -/
theorem LichnerowiczDeltaGammaAssembliesAt.scalarVariation_stokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t : ℝ} {x : M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (A : LichnerowiczDeltaGammaAssembliesAt gt t x) :
    deriv (fun s ↦ (gt s).scalarAt x) t =
      scalarVariationStokesBoundaryAt gt t x -
        metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x :=
  A.hasDerivAt_scalar_stokes.deriv

/-- Global automatic Lichnerowicz regularity therefore supplies the scalar
variation formula at every spacetime point, with no formula-valued premise. -/
theorem GlobalLichnerowiczAssemblyRegularity.scalarVariation_stokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (H : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ) (x : M) :
    deriv (fun s ↦ (gt s).scalarAt x) t =
      scalarVariationStokesBoundaryAt gt t x -
        metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x :=
  (H.assembliesAt t x).scalarVariation_stokes

/-- Global actual scalar differentiability supplied by the automatic
Lichnerowicz assembly. -/
theorem GlobalLichnerowiczAssemblyRegularity.hasDerivAt_scalar_stokes
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (H : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ) (x : M) :
    HasDerivAt (fun s ↦ (gt s).scalarAt x)
      (scalarVariationStokesBoundaryAt gt t x -
        metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x) t :=
  (H.assembliesAt t x).hasDerivAt_scalar_stokes

end AutomaticLichnerowiczAssemblies

section DimensionThreeEndpoint

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The strongest assembled endpoint of this route: actual Hausdorff moving
volume and total-scalar differentiation, automatically assembled
Lichnerowicz scalar variation, finite absolute dissipation, and only lower
semicontinuity of the limiting traceless-Ricci energy. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartScalarVariation_of_globalLichnerowiczRegularity_of_lscCompactness
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hScalar₂ : ∀ t : ℝ, ∀ y : M,
      ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
        (fun z : M ↦ (gt t).scalarAt z) y)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hCompact : NormalizedFlowScalarEnergyLscSequentialCompactness gt)
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartDensity_of_lscCompactness
      gt hFlow
      (fun t ↦ hHausdorff.hasDerivAt_totalScalar_energyNumerator
        hFlow (by norm_num) hScalar₂
          (fun s x ↦ hLichnerowicz.scalarVariation_stokes s x)
          hStokes t)
      hHausdorff.volumeVariation hFiniteDissipation hCompact hc hScalarLower

end DimensionThreeEndpoint

end Poincare
