import Poincare.Global.DeTurckBUCInverseGaugeEvolution
import Poincare.Global.ScalarEvolution

/-!
# From reconstructed coordinate metrics to scalar-evolution regularity

The reconstructed `BUC` solver canonically supplies only a forward derivative
at the initial endpoint.  Hamilton's scalar-evolution interface instead uses
ordinary two-sided time differentiability and `C²` spatial entries of the
metric time-variation tensor.  This file records the exact honest bridges for
interior positive times, where a two-sided coordinate metric germ and a smooth
tensor-field representative have been assembled.

Nothing here promotes a nonzero forward derivative at time zero to a
two-sided derivative.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

section TemporalChartBridge

omit [T2Space M] in
/-- A two-sided differentiable coordinate metric germ representing an honest
manifold metric germ gives pointwise time differentiability of that metric.
This is intended for interior positive times of the reconstructed lifespan;
the explicit `DifferentiableAt` premise prevents its use as an endpoint
upgrade for the merely forward `BUC` derivative. -/
theorem timeDifferentiableAt_of_coordinateMetric_eventuallyEq_chartMetric
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (t₀ : ℝ) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hdiff : ∀ p q : E, DifferentiableAt ℝ (fun t ↦ g t p q) t₀)
    (hmetric : ∀ p q : E,
      (fun t : ℝ ↦ g t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt gt t₀ y := by
  intro v w
  let p : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v
  let q : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w
  have hchart : DifferentiableAt ℝ
      (fun t : ℝ ↦ CovariantDerivative.chartMetric
        (gt t).inner anchor (extChartAt I anchor y) p q) t₀ :=
    (hdiff p q).congr_of_eventuallyEq (hmetric p q).symm
  have heq :
      (fun t : ℝ ↦ CovariantDerivative.chartMetric
        (gt t).inner anchor (extChartAt I anchor y) p q) =
      fun t : ℝ ↦ (gt t).inner y v w := by
    funext t
    exact CovariantDerivative.chartMetric_apply_chart
      (gt t).inner anchor hy v w
  rw [heq] at hchart
  exact hchart

omit [T2Space M] in
/-- A two-sided coordinate Ricci-flow predicate supplies the differentiability
premise of the preceding chart bridge.  A forward predicate is deliberately
insufficient: callers must first work at an interior time where the coordinate
metric path has an ordinary derivative. -/
theorem timeDifferentiableAt_of_isCoordinateRicciFlowAt_chartMetric_germ
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : E → E → (E →ₗ[ℝ] E))
    (t₀ : ℝ) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hflow : IsCoordinateRicciFlowAt g curv t₀)
    (hmetric : ∀ p q : E,
      (fun t : ℝ ↦ g t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt gt t₀ y := by
  exact timeDifferentiableAt_of_coordinateMetric_eventuallyEq_chartMetric
    gt g t₀ anchor hy (fun p q ↦ (hflow p q).differentiableAt) hmetric

omit [T2Space M] in
/-- A coordinate metric derivative whose rate is the chart expression of an
intrinsic tensor field identifies both the intrinsic time derivative and the
pointwise time-differentiability witness.  This is the direct temporal bridge
from a positive-interior reconstructed coordinate evolution to the two scalar
evolution inputs associated with one manifold point. -/
theorem timeDerivAt_eq_tensorField_of_coordinateMetric_hasDerivAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (t₀ : ℝ) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hderiv : ∀ p q : E, HasDerivAt (fun t ↦ g t p q)
      (CovariantDerivative.chartMetric H anchor
        (extChartAt I anchor y) p q) t₀)
    (hmetric : ∀ p q : E,
      (fun t : ℝ ↦ g t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt gt t₀ y ∧
      ∀ v w : TM y, timeDerivAt gt t₀ y v w = H y v w := by
  have hhas : ∀ v w : TM y,
      HasDerivAt (fun t : ℝ ↦ (gt t).inner y v w) (H y v w) t₀ := by
    intro v w
    let p : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y v
    let q : E := mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) y w
    have hchart :=
      (hderiv p q).congr_of_eventuallyEq (hmetric p q).symm
    have hpath :
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (extChartAt I anchor y) p q) =
        fun t : ℝ ↦ (gt t).inner y v w := by
      funext t
      exact CovariantDerivative.chartMetric_apply_chart
        (gt t).inner anchor hy v w
    have hrate :
        CovariantDerivative.chartMetric H anchor
            (extChartAt I anchor y) p q =
          H y v w :=
      CovariantDerivative.chartMetric_apply_chart H anchor hy v w
    rw [hpath, hrate] at hchart
    exact hchart
  constructor
  · intro v w
    exact (hhas v w).differentiableAt
  · intro v w
    exact (hhas v w).deriv

omit [T2Space M] in
/-- Specialization of the preceding tensor-rate bridge to an ordinary
coordinate Ricci-flow predicate.  The rate comparison is the sole geometric
input: it identifies the coordinate curvature trace with the chart pullback
of the chosen intrinsic tensor representative. -/
theorem timeDerivAt_eq_tensorField_of_isCoordinateRicciFlowAt_chartMetric_germ
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (curv : E → E → (E →ₗ[ℝ] E))
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (t₀ : ℝ) (anchor : M) {y : M}
    (hy : y ∈ (extChartAt I anchor).source)
    (hflow : IsCoordinateRicciFlowAt g curv t₀)
    (hrate : ∀ p q : E,
      (-2 : ℝ) * LinearMap.trace ℝ E (curv p q) =
        CovariantDerivative.chartMetric H anchor
          (extChartAt I anchor y) p q)
    (hmetric : ∀ p q : E,
      (fun t : ℝ ↦ g t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt gt t₀ y ∧
      ∀ v w : TM y, timeDerivAt gt t₀ y v w = H y v w := by
  apply timeDerivAt_eq_tensorField_of_coordinateMetric_hasDerivAt
    gt g H t₀ anchor hy
  · intro p q
    exact (hflow p q).congr_deriv (hrate p q)
  · exact hmetric

end TemporalChartBridge

section IntrinsicRicciFlowBridge

/-- A pointwise bilinear Ricci equation for `timeDerivAt` reconstructs the
section-tested closed Ricci-flow predicate.  Tensoriality of the Ricci trace
is the only conversion needed: an admissible test field has the same Ricci
contraction as its value in the tangent fiber. -/
theorem isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    (hRicci : ∀ v w : TM x,
      timeDerivAt gt t₀ x v w = -2 * (gt t₀).ricciAt x v w) :
    IsClosedRicciFlowSolutionAt gt t₀ x := by
  apply isClosedRicciFlowSolutionAt_of_metric gt
  intro Z hZ hreg w
  have htrace₀ :=
    CovariantDerivative.ricciTraceAt_eq_ricciBilinearAt
      (cov := (gt t₀).leviCivita) (Z := Z) (x := x) (hZ x) hreg w
  have htrace :
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w =
        (gt t₀).ricciAt x (Z x) w := by
    calc
      CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w =
          (gt t₀).ricciAt x w (Z x) := by
            simpa [ClosedSmoothRiemannianMetric.ricciAt] using htrace₀
      _ = (gt t₀).ricciAt x (Z x) w :=
        (gt t₀).ricciAt_symm x w (Z x)
  calc
    deriv (fun t ↦ (gt t).inner x (Z x) w) t₀ =
        timeDerivAt gt t₀ x (Z x) w := rfl
    _ = -2 * (gt t₀).ricciAt x (Z x) w := hRicci (Z x) w
    _ = -2 * CovariantDerivative.ricciTraceAt
        (gt t₀).leviCivita hreg w := by rw [htrace]

end IntrinsicRicciFlowBridge

section SpatialVariationBridge

omit [T2Space M] in
/-- A `C²` tensor-field representative of the metric time variation, equal
as a germ on all canonical extension entries, gives exactly the spatial
regularity premise retained by the minimal scalar-evolution interface. -/
theorem timeVariationExtContMDiffAt_of_tensorField_eventuallyEq
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (H : ∀ y : M, TM y → TM y → ℝ) (x : M)
    (hH : CovTensor2ExtContMDiffAt H x 2)
    (hgerm : ∀ p q : TM x,
      (fun y : M ↦
        timeDerivAt gt t₀ y (extend E p y) (extend E q y)) =ᶠ[nhds x]
      (fun y : M ↦ H y (extend E p y) (extend E q y))) :
    TimeVariationExtContMDiffAt gt t₀ x 2 := by
  intro p q
  exact (hH p q).congr_of_eventuallyEq (hgerm p q)

omit [T2Space M] in
/-- Pointwise tensor equality is a convenient sufficient form of the same
representative bridge. -/
theorem timeVariationExtContMDiffAt_of_tensorField_eq
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (H : ∀ y : M, TM y → TM y → ℝ)
    (hH : ∀ x : M, CovTensor2ExtContMDiffAt H x 2)
    (heq : ∀ y : M, ∀ p q : TM y,
      timeDerivAt gt t₀ y p q = H y p q) :
    ∀ x : M, TimeVariationExtContMDiffAt gt t₀ x 2 := by
  intro x
  apply timeVariationExtContMDiffAt_of_tensorField_eventuallyEq
    gt t₀ H x (hH x)
  intro p q
  filter_upwards with y
  exact heq y (extend E p y) (extend E q y)

/-- Global assembly of the two regularity outputs retained by the minimal
scalar-evolution interface.  Each point may use its own preferred chart and
coordinate metric path.  The coordinate derivative must already be two-sided,
so in the reconstructed setting this theorem applies at interior positive
times, not at the initial forward endpoint. -/
theorem scalarEvolution_regularities_of_coordinateMetric_tensorField_charts
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hderiv : ∀ y : M, ∀ p q : E,
      HasDerivAt (fun t ↦ g y t p q)
        (CovariantDerivative.chartMetric H (anchor y)
          (extChartAt I (anchor y) y) p q) t₀)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hH : ∀ x : M,
      CovTensor2ExtContMDiffAt (fun y p q ↦ H y p q) x 2) :
    (∀ y : M, TimeDifferentiableAt gt t₀ y) ∧
      ∀ x : M, TimeVariationExtContMDiffAt gt t₀ x 2 := by
  have hlocal (y : M) :
      TimeDifferentiableAt gt t₀ y ∧
        ∀ v w : TM y, timeDerivAt gt t₀ y v w = H y v w :=
    timeDerivAt_eq_tensorField_of_coordinateMetric_hasDerivAt
      gt (g y) H t₀ (anchor y) (hsource y) (hderiv y) (hmetric y)
  refine ⟨fun y ↦ (hlocal y).1, ?_⟩
  apply timeVariationExtContMDiffAt_of_tensorField_eq
    gt t₀ (fun y p q ↦ H y p q) hH
  intro y p q
  exact (hlocal y).2 p q

/-- If the intrinsic tensor representative is `-2 Ric`, the chartwise
derivative assembly also supplies the global closed Ricci-flow predicate.
Together with the two regularity conclusions, this is the complete output
needed from the reconstructed coordinate evolution before the genuinely mixed
time-space connection regularity step. -/
theorem ricciFlow_scalarEvolution_regularities_of_coordinateMetric_tensorField_charts
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ)
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hderiv : ∀ y : M, ∀ p q : E,
      HasDerivAt (fun t ↦ g y t p q)
        (CovariantDerivative.chartMetric H (anchor y)
          (extChartAt I (anchor y) y) p q) t₀)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hH : ∀ x : M,
      CovTensor2ExtContMDiffAt (fun y p q ↦ H y p q) x 2)
    (hRicci : ∀ y : M, ∀ v w : TM y,
      H y v w = -2 * (gt t₀).ricciAt y v w) :
    (∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y) ∧
      (∀ y : M, TimeDifferentiableAt gt t₀ y) ∧
      ∀ x : M, TimeVariationExtContMDiffAt gt t₀ x 2 := by
  have hlocal (y : M) :
      TimeDifferentiableAt gt t₀ y ∧
        ∀ v w : TM y, timeDerivAt gt t₀ y v w = H y v w :=
    timeDerivAt_eq_tensorField_of_coordinateMetric_hasDerivAt
      gt (g y) H t₀ (anchor y) (hsource y) (hderiv y) (hmetric y)
  have hFlow : ∀ y : M, IsClosedRicciFlowSolutionAt gt t₀ y := by
    intro y
    apply isClosedRicciFlowSolutionAt_of_timeDerivAt_eq_neg_two_ricciAt
    intro v w
    exact ((hlocal y).2 v w).trans (hRicci y v w)
  refine ⟨hFlow, (fun y ↦ (hlocal y).1), ?_⟩
  apply timeVariationExtContMDiffAt_of_tensorField_eq
    gt t₀ (fun y p q ↦ H y p q) hH
  intro y p q
  exact (hlocal y).2 p q

/-- End-to-end scalar-evolution capstone for a globally assembled chartwise
metric evolution.  The coordinate derivative, its Ricci identification, and
the spatial `C²` representative discharge the flow and variation inputs of
Hamilton's theorem.  The remaining `hNearRegExt` premise is exactly the mixed
time-space connection differentiability that cannot follow from abstract
`BUC` regularity alone. -/
theorem satisfiesHamiltonScalarEvolutionAt_of_coordinateMetric_tensorField_charts
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (H : ∀ y : M, TM y →L[ℝ] TM y →L[ℝ] ℝ)
    (anchor : M → M)
    (g : M → ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hsource : ∀ y : M, y ∈ (extChartAt I (anchor y)).source)
    (hderiv : ∀ y : M, ∀ p q : E,
      HasDerivAt (fun t ↦ g y t p q)
        (CovariantDerivative.chartMetric H (anchor y)
          (extChartAt I (anchor y) y) p q) t₀)
    (hmetric : ∀ y : M, ∀ p q : E,
      (fun t : ℝ ↦ g y t p q) =ᶠ[nhds t₀]
        (fun t : ℝ ↦ CovariantDerivative.chartMetric
          (gt t).inner (anchor y) (extChartAt I (anchor y) y) p q))
    (hH : ∀ y : M,
      CovTensor2ExtContMDiffAt (fun z p q ↦ H z p q) y 2)
    (hRicci : ∀ y : M, ∀ v w : TM y,
      H y v w = -2 * (gt t₀).ricciAt y v w)
    (hNearRegExt :
      ∀ᶠ y in nhds x,
        MetricFlowRegularAt gt t₀ y ∧
        (∀ a b c : TM y,
          HasDerivAt
            (fun t ↦
              extDerivFun
                (fun z : M ↦ (gt t).inner z (extend E b z) (extend E c z))
                y a)
            (extDerivFun
              (fun z : M ↦
                timeDerivAt gt t₀ z (extend E b z) (extend E c z))
              y a) t₀)) :
    SatisfiesHamiltonScalarEvolutionAt gt t₀ x := by
  rcases
      ricciFlow_scalarEvolution_regularities_of_coordinateMetric_tensorField_charts
        gt t₀ H anchor g hsource hderiv hmetric hH hRicci with
    ⟨hFlow, hgt, hEntries⟩
  exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_no_raise_hypothesis
    hFlow hNearRegExt hgt hEntries

end SpatialVariationBridge

end Poincare
