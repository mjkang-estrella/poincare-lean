import Poincare.Global.DeTurckBUCJointSpacetimeGermRestriction
import Poincare.Global.DeTurckFlowSymmetricPhysicalTime

/-!
# Joint-spacetime germ restriction for the symmetric point flow

The physical-time point-flow theorem identifies the spatial `fderiv` of its
endpoint family with the translated variational path throughout a symmetric
interval.  Consequently, when that endpoint family is used in the
reconstructed spacetime coefficient, the endpoint and derivative time germs
required by the general restriction theorem are automatic.  The only
remaining premise here is the genuine joint pulled-metric/chart-metric germ.
-/

noncomputable section

open Bundle FiberBundle Filter Metric Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

/--
Restrict a joint spacetime metric germ along the base trajectory of a
symmetric physical-time point flow.  The endpoint germ is definitional and
the derivative germ follows from the interval-wide `fderiv` identification.
-/
theorem reconstructedInverseGaugeMetric_form_germ_of_symmetricPhysicalTime
    (R : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (t₀ T : ℝ) (hT : 0 < T)
    (Phi : ℝ → E → E) (J : ℝ → E →L[ℝ] E) (z₀ : E)
    (hDPhi : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      fderiv ℝ (Phi s) z₀ = J s)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M)
    (hjoint :
      reconstructedInverseGaugeMetricSpacetime R K u₀ Phi
          (fun s z ↦ fderiv ℝ (Phi s) z) =ᶠ[nhds (t₀, z₀)]
        (fun q : ℝ × E ↦
          CovariantDerivative.chartMetric (rt q.1).inner anchor q.2)) :
    reconstructedInverseGaugeMetric R K u₀
        (fun s ↦ Phi s z₀) J =ᶠ[nhds t₀]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀) := by
  apply reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm
    R K u₀ Phi (fun s z ↦ fderiv ℝ (Phi s) z)
      (fun s ↦ Phi s z₀) J rt anchor z₀ hjoint
  · exact Filter.Eventually.of_forall fun _ ↦ rfl
  · filter_upwards [Icc_mem_nhds
        (a := t₀ - T) (b := t₀ + T)
        (by linarith [hT]) (by linarith [hT])] with s hs
    exact hDPhi s hs

/--
Slotwise form of
`reconstructedInverseGaugeMetric_form_germ_of_symmetricPhysicalTime`, in the
quantifier order used by the coordinate Ricci-flow assembly interface.
-/
theorem reconstructedInverseGaugeMetric_germ_of_symmetricPhysicalTime
    (R : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (t₀ T : ℝ) (hT : 0 < T)
    (Phi : ℝ → E → E) (J : ℝ → E →L[ℝ] E) (z₀ : E)
    (hDPhi : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      fderiv ℝ (Phi s) z₀ = J s)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M)
    (hjoint :
      reconstructedInverseGaugeMetricSpacetime R K u₀ Phi
          (fun s z ↦ fderiv ℝ (Phi s) z) =ᶠ[nhds (t₀, z₀)]
        (fun q : ℝ × E ↦
          CovariantDerivative.chartMetric (rt q.1).inner anchor q.2)) :
    ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric R K u₀
        (fun tau ↦ Phi tau z₀) J s p q) =ᶠ[nhds t₀]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀ p q) := by
  have hform :=
    reconstructedInverseGaugeMetric_form_germ_of_symmetricPhysicalTime
      R K u₀ t₀ T hT Phi J z₀ hDPhi rt anchor hjoint
  intro p q
  filter_upwards [hform] with s hs
  exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B p q) hs

end Poincare
