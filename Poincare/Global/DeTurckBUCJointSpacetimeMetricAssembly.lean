import Poincare.Global.DeTurckBUCJointSpacetimeGermRestriction
import Poincare.Global.DeTurckChartIndependentPullback

/-!
# Assembling a closed metric family from covariant chart coefficients

The inverse-gauge construction naturally produces bilinear coefficients in
preferred charts.  This file isolates the exact global tensor-assembly step.
A coefficient family indexed by every preferred-chart anchor determines an
intrinsic tensor by taking its self-chart value.  If the chart coefficients
obey the honest preferred-chart transition law, every chart metric of that
intrinsic tensor is the original coefficient family.

Thus the joint spacetime germ needed by the Ricci-flow assembly follows from
two concrete inputs: a chartwise covariant smooth positive coefficient family
and a local germ identifying the reconstructed inverse-gauge coefficient with
the chosen anchor's member of that family.
-/

noncomputable section

open Bornology Bundle FiberBundle Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

variable {ι κ : Type*}

/--
Assemble an intrinsic smooth Riemannian metric from the self-chart members of
a chartwise coefficient family.  Compatibility with the non-self charts is
not needed to define the tensor; it is used by the realization theorem below.
-/
noncomputable def closedSmoothRiemannianMetricOfChartwiseSelf
    (G : ℝ → M → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ t x u v,
      G t x (extChartAt I x x) u v = G t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < G t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E | G t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, G t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))))
    (t : ℝ) : ClosedSmoothRiemannianMetric n M where
  inner := fun x ↦ G t x (extChartAt I x x)
  symm := hsymm t
  pos := hpos t
  isVonNBounded := hbounded t
  contMDiff := hsmooth t

@[simp] theorem closedSmoothRiemannianMetricOfChartwiseSelf_inner
    (G : ℝ → M → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ t x u v,
      G t x (extChartAt I x x) u v = G t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < G t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E | G t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, G t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))))
    (t : ℝ) (x : M) :
    (closedSmoothRiemannianMetricOfChartwiseSelf
      G hsymm hpos hbounded hsmooth t).inner x =
      G t x (extChartAt I x x) :=
  rfl

/-- The inverse-gauge spacetime coefficient when the analytic data, endpoint
family, and variational differential are supplied in every preferred chart. -/
def chartwiseReconstructedInverseGaugeMetricSpacetime
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (s : ℝ) (anchor : M) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  reconstructedInverseGaugeMetricSpacetime
    (D anchor) K (u₀ anchor) (Phi anchor) (DPhi anchor) (s, z)

/--
The metric assembled from self-chart coefficients realizes the entire
chartwise family, provided the latter obeys the actual preferred-chart
transition law.  This is an equality of continuous bilinear forms, not merely
of their values at the chart center.
-/
theorem chartMetric_closedSmoothRiemannianMetricOfChartwiseSelf_eq
    (G : ℝ → M → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ t x u v,
      G t x (extChartAt I x x) u v = G t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < G t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E | G t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, G t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))))
    (hcov : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        G t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          G t anchor₁ z u v)
    (t : ℝ) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) :
    CovariantDerivative.chartMetric
        (closedSmoothRiemannianMetricOfChartwiseSelf
          G hsymm hpos hbounded hsmooth t).inner anchor z =
      G t anchor z := by
  let y : M := (extChartAt I anchor).symm z
  have hy : y ∈ (extChartAt I y).source := mem_extChartAt_source y
  have htrans := hcov t anchor y z hz hy
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have huv := htrans u v
  rw [GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    anchor y hz hy] at huv
  simp only [GeodesicTransport.chartTransition,
    GeodesicTransport.chartTransitionMFDeriv] at huv
  dsimp only [y] at huv
  rw [mfderiv_extChartAt_self] at huv
  simpa only [CovariantDerivative.chartMetric_apply,
    closedSmoothRiemannianMetricOfChartwiseSelf_inner, y] using huv

/--
Global exact assembly of a chart-indexed inverse-gauge reconstruction.  Once
the reconstructed coefficients are smooth positive self-chart tensors and
obey the honest preferred-chart transition law, this theorem constructs one
closed smooth metric family whose chart coefficients are those reconstructed
coefficients at every genuine chart point.  In particular no independent
metric family and no joint-germ hypothesis remain in the conclusion.
-/
theorem exists_closedSmoothRiemannianMetricFamily_realizing_chartwiseReconstruction
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (DPhi : M → ℝ → E → E →L[ℝ] E)
    (hsymm : ∀ t x u v,
      chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi t x (extChartAt I x x) u v =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi DPhi t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < chartwiseReconstructedInverseGaugeMetricSpacetime
        D K u₀ Phi DPhi t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E |
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, chartwiseReconstructedInverseGaugeMetricSpacetime
              D K u₀ Phi DPhi t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))))
    (hcov : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₂
              (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
              (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
              (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor₁ z u v) :
    ∃ rt : ℝ → ClosedSmoothRiemannianMetric n M,
      ∀ t anchor z,
        z ∈ (extChartAt I anchor).target →
        CovariantDerivative.chartMetric (rt t).inner anchor z =
          chartwiseReconstructedInverseGaugeMetricSpacetime
            D K u₀ Phi DPhi t anchor z := by
  let G : ℝ → M → E → E →L[ℝ] E →L[ℝ] ℝ :=
    chartwiseReconstructedInverseGaugeMetricSpacetime D K u₀ Phi DPhi
  let rt : ℝ → ClosedSmoothRiemannianMetric n M := fun t ↦
    closedSmoothRiemannianMetricOfChartwiseSelf
      G hsymm hpos hbounded hsmooth t
  refine ⟨rt, ?_⟩
  intro t anchor z hz
  exact chartMetric_closedSmoothRiemannianMetricOfChartwiseSelf_eq
    G hsymm hpos hbounded hsmooth hcov t anchor hz

/--
Construct the assembled metric family and discharge the joint spacetime germ
from a local identification with one member of a globally covariant chartwise
coefficient family.
-/
theorem exists_closedSmoothRiemannianMetricFamily_with_jointSpacetimeGerm
    (D : RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : ℝ → E → E)
    (DPhi : ℝ → E → E →L[ℝ] E)
    (G : ℝ → M → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ t x u v,
      G t x (extChartAt I x x) u v = G t x (extChartAt I x x) v u)
    (hpos : ∀ t x (v : E), v ≠ 0 →
      0 < G t x (extChartAt I x x) v v)
    (hbounded : ∀ t x,
      IsVonNBounded ℝ
        {v : E | G t x (extChartAt I x x) v v < 1})
    (hsmooth : ∀ t,
      ContMDiff I
        ((I).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x : M ↦
          (⟨x, G t x (extChartAt I x x)⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun y : M ↦ TM y →L[ℝ] TM y →L[ℝ] ℝ))))
    (hcov : ∀ t anchor₁ anchor₂ z,
      z ∈ (extChartAt I anchor₁).target →
      (extChartAt I anchor₁).symm z ∈
        (extChartAt I anchor₂).source →
      ∀ u v : E,
        G t anchor₂
            (GeodesicTransport.chartTransition anchor₁ anchor₂ z)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z u)
            (GeodesicTransport.chartTransitionDeriv anchor₁ anchor₂ z v) =
          G t anchor₁ z u v)
    (anchor : M) {t : ℝ} {z₀ : E}
    (hz₀ : z₀ ∈ (extChartAt I anchor).target)
    (hlocal :
      reconstructedInverseGaugeMetricSpacetime D K u₀ Phi DPhi =ᶠ[
          nhds (t, z₀)]
        (fun q : ℝ × E ↦ G q.1 anchor q.2)) :
    ∃ rt : ℝ → ClosedSmoothRiemannianMetric n M,
      reconstructedInverseGaugeMetricSpacetime D K u₀ Phi DPhi =ᶠ[
          nhds (t, z₀)]
        (fun q : ℝ × E ↦
          CovariantDerivative.chartMetric (rt q.1).inner anchor q.2) := by
  let rt : ℝ → ClosedSmoothRiemannianMetric n M := fun s ↦
    closedSmoothRiemannianMetricOfChartwiseSelf
      G hsymm hpos hbounded hsmooth s
  refine ⟨rt, ?_⟩
  have htarget :
      (fun q : ℝ × E ↦ q.2) ⁻¹' (extChartAt I anchor).target ∈
        nhds (t, z₀) := by
    exact continuousAt_snd
      ((isOpen_extChartAt_target anchor).mem_nhds hz₀)
  filter_upwards [hlocal, htarget] with q hq hqtarget
  rw [hq]
  simpa only [rt] using
    (chartMetric_closedSmoothRiemannianMetricOfChartwiseSelf_eq
      G hsymm hpos hbounded hsmooth hcov q.1 anchor hqtarget).symm

end Poincare
