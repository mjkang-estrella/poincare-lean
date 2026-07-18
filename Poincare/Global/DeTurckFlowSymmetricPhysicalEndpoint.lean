import Poincare.Global.DeTurckFlowSymmetricPhysicalTime

/-!
# Endpoint germs from the symmetric physical-time inverse DeTurck flow

`DeTurckFlowSymmetricPhysicalTime` already translates the single symmetric
offset-time Picard--Lindelof family to physical time and proves its point and
variational ODEs.  This module adds only the endpoint data needed by
`reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm`:

* the spatial derivative family `DPhi s z = fderiv ℝ (Phi s) z`,
* the base trajectory `s ↦ Phi s z₀`, and
* the endpoint and derivative identities as ordinary time germs at `t₀`.

The joint pulled-metric/chart-metric spacetime germ remains a separate
geometric input and is neither assumed nor constructed here.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace Poincare

section PhysicalEndpoint

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial derivative of a physical-time endpoint family. -/
def inverseGaugePhysicalPointFlowDeriv
    (Phi : ℝ → E → E) : ℝ → E → E →L[ℝ] E :=
  fun s z => fderiv ℝ (Phi s) z

/-- The physical-time endpoint trajectory through a fixed base point. -/
def inverseGaugePhysicalBaseTrajectory
    (Phi : ℝ → E → E) (z₀ : E) : ℝ → E :=
  fun s => Phi s z₀

@[simp] theorem inverseGaugePhysicalPointFlowDeriv_apply
    (Phi : ℝ → E → E) (s : ℝ) (z : E) :
    inverseGaugePhysicalPointFlowDeriv Phi s z = fderiv ℝ (Phi s) z :=
  rfl

@[simp] theorem inverseGaugePhysicalBaseTrajectory_apply
    (Phi : ℝ → E → E) (z₀ : E) (s : ℝ) :
    inverseGaugePhysicalBaseTrajectory Phi z₀ s = Phi s z₀ :=
  rfl

/-- The endpoint at the base point and the named base trajectory agree at
every time, hence in particular as a germ at any restart time. -/
theorem inverseGaugePhysicalPointFlow_base_eventuallyEq
    (Phi : ℝ → E → E) (z₀ : E) (t₀ : ℝ) :
    (fun s : ℝ => Phi s z₀) =ᶠ[nhds t₀]
      inverseGaugePhysicalBaseTrajectory Phi z₀ :=
  Filter.Eventually.of_forall fun _ => rfl

/-- A Frechet-derivative identification for one physical endpoint gives the
corresponding value of the named spatial derivative family. -/
theorem inverseGaugePhysicalPointFlowDeriv_base_eq_of_hasFDerivAt
    (Phi : ℝ → E → E) (J : ℝ → E →L[ℝ] E) (z₀ : E) {s : ℝ}
    (h : HasFDerivAt (Phi s) (J s) z₀) :
    inverseGaugePhysicalPointFlowDeriv Phi s z₀ = J s := by
  simpa [inverseGaugePhysicalPointFlowDeriv] using h.fderiv

/-- Endpoint differentiability on a positive closed interval around `t₀`
gives exactly the derivative time germ consumed by the joint-spacetime
restriction theorem. -/
theorem inverseGaugePhysicalPointFlowDeriv_base_eventuallyEq
    (Phi : ℝ → E → E) (J : ℝ → E →L[ℝ] E)
    (z₀ : E) (t₀ T : ℝ) (hT : 0 < T)
    (hendpoint : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasFDerivAt (Phi s) (J s) z₀) :
    (fun s : ℝ => inverseGaugePhysicalPointFlowDeriv Phi s z₀) =ᶠ[nhds t₀] J := by
  filter_upwards [Icc_mem_nhds (a := t₀ - T) (b := t₀ + T)
      (by linarith [hT]) (by linarith [hT])] with s hs
  exact inverseGaugePhysicalPointFlowDeriv_base_eq_of_hasFDerivAt
    Phi J z₀ (hendpoint s hs)

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Construct the target-compatible endpoint package around a restart time.

The returned `Phi` and `J` are the already-proved physical-time point and
variational flows from
`exists_local_inverseGaugePointFlow_variationalIdentification_physicalTime`.
This theorem adds `DPhi := inverseGaugePhysicalPointFlowDeriv Phi`, the fixed
base trajectory, and the two ordinary time-germ identities needed by
`reconstructedInverseGaugeMetric_form_germ_of_jointSpacetimeGerm`.
-/
theorem exists_local_inverseGaugePhysicalEndpoint_variationalIdentification
    (W : ℝ → E → E) (DW : ℝ → E → E →L[ℝ] E)
    (hW : ContDiff ℝ 1 (Function.uncurry W))
    (hDWcont : ContDiff ℝ 1 (Function.uncurry DW))
    (hDW : ∀ t x, HasFDerivAt (W t) (DW t x) x)
    (t₀ : ℝ) (z₀ : E) :
    ∃ T > (0 : ℝ), ∃ r > (0 : ℝ),
      ∃ Phi : ℝ → E → E, ∃ J : ℝ → E →L[ℝ] E,
        (∀ z ∈ closedBall z₀ r,
          Phi t₀ z = z ∧
            ∀ s ∈ Icc (t₀ - T) (t₀ + T),
              HasDerivWithinAt (fun q : ℝ => Phi q z)
                (-W s (Phi s z)) (Icc (t₀ - T) (t₀ + T)) s) ∧
        J t₀ = ContinuousLinearMap.id ℝ E ∧
        (∀ s ∈ Icc (t₀ - T) (t₀ + T),
          HasDerivWithinAt J
            (-((DW s (Phi s z₀)).comp (J s)))
            (Icc (t₀ - T) (t₀ + T)) s) ∧
        (∀ s ∈ Icc (t₀ - T) (t₀ + T),
          HasFDerivAt (Phi s) (J s) z₀) ∧
        (∀ s ∈ Icc (t₀ - T) (t₀ + T),
          inverseGaugePhysicalPointFlowDeriv Phi s z₀ = J s) ∧
        (fun s : ℝ => Phi s z₀) =ᶠ[nhds t₀]
          inverseGaugePhysicalBaseTrajectory Phi z₀ ∧
        (fun s : ℝ => inverseGaugePhysicalPointFlowDeriv Phi s z₀) =ᶠ[nhds t₀] J ∧
        HasDerivAt (inverseGaugePhysicalBaseTrajectory Phi z₀)
          (-W t₀ z₀) t₀ ∧
        HasDerivAt J
          (-((DW t₀ z₀).comp (ContinuousLinearMap.id ℝ E))) t₀ := by
  rcases exists_local_inverseGaugePointFlow_variationalIdentification_physicalTime
      W DW hW hDWcont hDW t₀ z₀ with
    ⟨T, hT, r, hr, Phi, J, hPhi, hJ₀, hJ, hendpointFull⟩
  have hendpoint : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasFDerivAt (Phi s) (J s) z₀ :=
    fun s hs => (hendpointFull s hs).1
  have hDPhiOn : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      inverseGaugePhysicalPointFlowDeriv Phi s z₀ = J s := by
    intro s hs
    exact inverseGaugePhysicalPointFlowDeriv_base_eq_of_hasFDerivAt
      Phi J z₀ (hendpoint s hs)
  have hPhiGerm : (fun s : ℝ => Phi s z₀) =ᶠ[nhds t₀]
      inverseGaugePhysicalBaseTrajectory Phi z₀ :=
    inverseGaugePhysicalPointFlow_base_eventuallyEq Phi z₀ t₀
  have hDPhiGerm :
      (fun s : ℝ => inverseGaugePhysicalPointFlowDeriv Phi s z₀) =ᶠ[nhds t₀] J :=
    inverseGaugePhysicalPointFlowDeriv_base_eventuallyEq
      Phi J z₀ t₀ T hT hendpoint
  have ht₀ : t₀ ∈ Icc (t₀ - T) (t₀ + T) := by
    constructor <;> linarith [hT]
  have hnhds : Icc (t₀ - T) (t₀ + T) ∈ nhds t₀ :=
    Icc_mem_nhds (by linarith [hT]) (by linarith [hT])
  have hz₀ : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
  have hbaseAt : HasDerivAt (inverseGaugePhysicalBaseTrajectory Phi z₀)
      (-W t₀ z₀) t₀ := by
    have h := ((hPhi z₀ hz₀).2 t₀ ht₀).hasDerivAt hnhds
    simpa [inverseGaugePhysicalBaseTrajectory, (hPhi z₀ hz₀).1] using h
  have hvarAt : HasDerivAt J
      (-((DW t₀ z₀).comp (ContinuousLinearMap.id ℝ E))) t₀ := by
    have h := (hJ t₀ ht₀).hasDerivAt hnhds
    simpa [(hPhi z₀ hz₀).1, hJ₀] using h
  exact ⟨T, hT, r, hr, Phi, J, hPhi, hJ₀, hJ, hendpoint,
    hDPhiOn, hPhiGerm, hDPhiGerm, hbaseAt, hvarAt⟩

end PhysicalEndpoint

end Poincare
