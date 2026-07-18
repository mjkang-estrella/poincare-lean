import Poincare.Global.DeTurckBUCInteriorInverseGaugeEvolution

/-!
# Interior inverse-gauge time-germ assembly

The interior inverse-gauge construction gives a genuine two-sided coordinate
Ricci-flow equation for its reconstructed pullback path.  An independently
assembled smooth metric family inherits that equation as soon as its fixed
chart coefficients agree with the reconstructed path as an ordinary time
germ.  This file records that transfer and the resulting intrinsic time
differentiability.

The germ hypotheses below are intentionally not manufactured from the
fixed-time spatial metric germ used by the reconstruction theorem.  The
remaining geometric assembly boundary is a joint spacetime germ identifying
the pullback of the reconstructed coefficient by a local endpoint family with
the chart metric of the assembled family.  Restricting such a joint germ to a
fixed chart point would supply the hypotheses here, but construction of that
endpoint family and spacetime metric germ remains separate.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

omit [T2Space M] in
/--
An ordinary pointwise time germ transfers the reconstructed inverse-gauge
Ricci equation to the fixed chart coefficients of an assembled metric family.

The target family `rt` is kept distinct from the DeTurck metric family used to
construct the inverse gauge: identifying those two families is not implicit in
the pullback calculation.
-/
theorem isCoordinateRicciFlowAt_chartMetric_of_reconstructedInverseGaugeMetric_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hmetric : ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        D K u₀ phi J s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y) p q)) :
    IsCoordinateRicciFlowAt
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y)) curv t := by
  apply hflow.congr_of_eventuallyEq
  intro p q
  exact (hmetric p q).symm

omit [T2Space M] in
/--
The same time-germ assembly supplies intrinsic time differentiability of the
assembled metric at the represented manifold point.
-/
theorem timeDifferentiableAt_of_reconstructedInverseGaugeMetric_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (hy : y ∈ (extChartAt I anchor).source)
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hmetric : ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        D K u₀ phi J s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y) p q)) :
    TimeDifferentiableAt rt t y := by
  have hchart :=
    isCoordinateRicciFlowAt_chartMetric_of_reconstructedInverseGaugeMetric_germ
      D K u₀ phi J rt anchor curv hflow hmetric
  exact IsCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric
    rt anchor hy curv hchart

omit [T2Space M] in
/--
A bilinear-form-valued time germ is a convenient uniform version of the
pointwise germ: one eventual equality supplies every pair of tangent slots.
-/
theorem isCoordinateRicciFlowAt_chartMetric_of_reconstructedInverseGaugeMetric_form_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hmetric :
      (reconstructedInverseGaugeMetric D K u₀ phi J) =ᶠ[nhds t]
        (fun s : ℝ ↦ CovariantDerivative.chartMetric
          (rt s).inner anchor (extChartAt I anchor y))) :
    IsCoordinateRicciFlowAt
      (fun s : ℝ ↦ CovariantDerivative.chartMetric
        (rt s).inner anchor (extChartAt I anchor y)) curv t := by
  apply
    isCoordinateRicciFlowAt_chartMetric_of_reconstructedInverseGaugeMetric_germ
      D K u₀ phi J rt anchor curv hflow
  intro p q
  filter_upwards [hmetric] with s hs
  exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B p q) hs

omit [T2Space M] in
/--
Form-valued time-germ assembly also yields intrinsic time differentiability.
-/
theorem timeDifferentiableAt_of_reconstructedInverseGaugeMetric_form_germ
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y : M} {t : ℝ}
    (hy : y ∈ (extChartAt I anchor).source)
    (curv : E → E → (E →ₗ[ℝ] E))
    (hflow : IsCoordinateRicciFlowAt
      (reconstructedInverseGaugeMetric D K u₀ phi J) curv t)
    (hmetric :
      (reconstructedInverseGaugeMetric D K u₀ phi J) =ᶠ[nhds t]
        (fun s : ℝ ↦ CovariantDerivative.chartMetric
          (rt s).inner anchor (extChartAt I anchor y))) :
    TimeDifferentiableAt rt t y := by
  have hchart :=
    isCoordinateRicciFlowAt_chartMetric_of_reconstructedInverseGaugeMetric_form_germ
      D K u₀ phi J rt anchor curv hflow hmetric
  exact IsCoordinateRicciFlowAt.timeDifferentiableAt_of_chartMetric
    rt anchor hy curv hchart

end Poincare
