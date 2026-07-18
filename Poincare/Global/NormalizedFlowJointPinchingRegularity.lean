import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowScalarRegularity

/-!
# Spatial pinching regularity on normalized Ricci-flow slices

Joint `C³` metric entries determine `C²` spatial time-variation entries.
On a normalized Ricci-flow slice, the flow equation then determines `C²`
Ricci entries, while the inverse-metric trace determines `C²` scalar
curvature. Combining these facts with the finite Gram formulas removes the
standalone spatial `C²` premise for both the traceless-Ricci energy and the
traceless pinching quotient.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n

/-- Joint `C³` metric entries on a normalized Ricci-flow slice automatically
give spatial `C²` regularity of the squared traceless-Ricci norm.  Unlike the
quotient theorem below, this statement needs no scalar-curvature sign. -/
theorem contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).tracelessRicciNormSqAt y) x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hRicC2 : ∀ y : M,
      CovTensor2ExtContMDiffAt (ricciVariationField g) y 2 := fun y ↦
    ricciVariationField_extContMDiffAt_two_of_normalizedRicciFlow
      hFlow hEntries y
  have hNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.ricciNormSqAt y) x :=
    contMDiffAt_two_ricciNormSqAt_of_ricci_entries g x (hRicC2 x)
  have hScalar2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries x
  exact contMDiffAt_two_tracelessRicciNormSqAt g x hNorm2 hScalar2

/-- A globally joint `C³` normalized Ricci flow has spatially `C¹` squared
traceless-Ricci energy on every time slice.  This is the raw proposition
underlying `UniformTracelessRicciEnergyCOne`, stated here without importing
the later energy-concentration module that gives that proposition its name. -/
theorem contMDiff_one_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    ∀ t : ℝ, ContMDiff I 𝓘(ℝ) 1
      (fun x : M ↦ (gt t).tracelessRicciNormSqAt x) := by
  intro t x
  exact
    (contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
      x (hFlow t) (hJoint t)).of_le (by norm_num)

/-- Joint `C³` metric entries on a positive-scalar normalized Ricci-flow
slice automatically give spatial `C²` regularity of Hamilton's improved
traceless pinching quotient. -/
theorem contMDiffAt_two_tracelessPinchingAt_of_normalizedRicciFlow_joint_metric_entries_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
    (x : M) (δ : ℝ)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ y : M, IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
    (hJoint : ∀ y : M, MetricEntriesJointContDiffAt gt t₀ y 3)
    (hRpos : ∀ y : M, 0 < (gt t₀).scalarAt y) :
    ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ (gt t₀).tracelessPinchingAt y δ) x := by
  let g : ClosedSmoothRiemannianMetric n M := gt t₀
  have hEntries : ∀ y : M,
      TimeVariationExtContMDiffAt gt t₀ y 2 := fun y ↦
    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
      (hJoint y)
  have hScalar2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.scalarAt y) x :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries x
  have hTraceNorm2 : ContMDiffAt I 𝓘(ℝ) 2
      (fun y : M ↦ g.tracelessRicciNormSqAt y) x :=
    contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
      x hFlow hJoint
  exact contMDiffAt_two_tracelessPinchingAt
    g x δ hTraceNorm2 hScalar2 (hRpos x)

end Poincare
