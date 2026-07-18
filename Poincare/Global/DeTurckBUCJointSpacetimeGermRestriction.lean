import Poincare.Global.DeTurckBUCInteriorTimeGermAssembly

/-!
# Restricting a joint inverse-gauge spacetime germ to one time germ

A local endpoint family `Phi` and its spatial derivative family `DPhi` turn
the reconstructed coordinate coefficient into a bilinear field over
`time × initial-coordinate-point`.  If that pulled field agrees jointly near
`(t, z₀)` with the chart metric of an assembled family, then restriction along
the continuous map `s ↦ (s, z₀)` gives exactly the ordinary time germ used
by the interior assembly theorems.

This module only performs that restriction.  The endpoint family, its
derivative identification, and the joint spacetime metric germ remain explicit
premises; no such germ is constructed here.
-/

noncomputable section

open Bundle FiberBundle Filter
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
The reconstructed coefficient pulled back by a time-dependent endpoint family
and its spatial derivative, viewed as a field on time × initial point.
-/
def reconstructedInverseGaugeMetricSpacetime
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : ℝ → E → E)
    (DPhi : ℝ → E → E →L[ℝ] E)
    (q : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  pullbackBilinearForm
    (coordinateBilinearFormAt
      (reconstructedCoordinateMetricPath D K u₀ q.1)
      (Phi q.1 q.2))
    (DPhi q.1 q.2)

/--
Restrict a joint pulled-metric/chart-metric germ along the fixed initial point
`z₀`.  The only filter map used is the automatic continuity of
`s ↦ (s, z₀)`.  Endpoint and derivative agreement at the base point are
needed only as ordinary time germs.
-/
theorem reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : ℝ → E → E)
    (DPhi : ℝ → E → E →L[ℝ] E)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (z₀ : E) {t : ℝ}
    (hjoint :
      (reconstructedInverseGaugeMetricSpacetime D K u₀ Phi DPhi) =ᶠ[
          nhds (t, z₀)]
        (fun q : ℝ × E ↦
          CovariantDerivative.chartMetric (rt q.1).inner anchor q.2))
    (hPhi : (fun s : ℝ ↦ Phi s z₀) =ᶠ[nhds t] phi)
    (hDPhi : (fun s : ℝ ↦ DPhi s z₀) =ᶠ[nhds t] J) :
    (reconstructedInverseGaugeMetric D K u₀ phi J) =ᶠ[nhds t]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀) := by
  have hbase : Tendsto (fun s : ℝ ↦ (s, z₀)) (nhds t) (nhds (t, z₀)) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hjointBase := hjoint.comp_tendsto hbase
  filter_upwards [hjointBase, hPhi, hDPhi] with s hs hPhiS hDPhiS
  simpa only [reconstructedInverseGaugeMetricSpacetime,
    reconstructedInverseGaugeMetric, Function.comp_apply, hPhiS, hDPhiS] using hs

/--
Slotwise form of the joint-to-time restriction, in exactly the quantifier
order consumed by the coordinate Ricci-flow and Hamilton assembly bridges.
-/
theorem reconstructedInverseGaugeMetric_germ_of_jointSpacetimeGerm
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : ℝ → E → E)
    (DPhi : ℝ → E → E →L[ℝ] E)
    (phi : ℝ → E) (J : ℝ → E →L[ℝ] E)
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (anchor : M) (z₀ : E) {t : ℝ}
    (hjoint :
      (reconstructedInverseGaugeMetricSpacetime D K u₀ Phi DPhi) =ᶠ[
          nhds (t, z₀)]
        (fun q : ℝ × E ↦
          CovariantDerivative.chartMetric (rt q.1).inner anchor q.2))
    (hPhi : (fun s : ℝ ↦ Phi s z₀) =ᶠ[nhds t] phi)
    (hDPhi : (fun s : ℝ ↦ DPhi s z₀) =ᶠ[nhds t] J) :
    ∀ p q : E,
      (fun s : ℝ ↦ reconstructedInverseGaugeMetric
        D K u₀ phi J s p q) =ᶠ[nhds t]
      (fun s : ℝ ↦
        CovariantDerivative.chartMetric (rt s).inner anchor z₀ p q) := by
  have hform :=
    reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm
      D K u₀ Phi DPhi phi J rt anchor z₀ hjoint hPhi hDPhi
  intro p q
  filter_upwards [hform] with s hs
  exact congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ ↦ B p q) hs

end Poincare
