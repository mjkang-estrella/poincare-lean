import Poincare.Global.FTransition

/-!
# Cartan-map derivative germ on the punctured normal ball

This module discharges the neighborhood-level pullback germ available from the
pointwise Cartan differential field.  The remaining second-derivative
regularity of the derivative field is intentionally not asserted here.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace GermAndField

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

/--
The pointwise Cartan differential field is a genuine local derivative germ on
the open punctured normal ball.  Around each nonzero endpoint `eM v`, the
selected field evaluated at the local inverse coordinate `eM.symm q` is the
derivative of the Cartan chart map at nearby `q`, and the pointwise metric
pullback identity therefore becomes an eventual germ for `fderiv F`.
-/
theorem exists_cartanChartMap_fderiv_eventual_pullback_germ_on_punctured_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    (p₀ : RoundSphere3) (L : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ),
      ∃ Afield Bfield : E3 → E3 ≃L[ℝ] E3,
      ∃ DF : E3 → E3 →L[ℝ] E3,
        (∀ v : E3,
          DF v =
            CartanLocalIsometry.cartanChartDifferential L (Afield v) (Bfield v)) ∧
        ∀ v : E3, ‖v‖ < ρ → v ≠ 0 →
          let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
          let F := CartanDifferential.cartanChartMap g x₀ p₀ L
          let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric g.inner x₀ z
          let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
            fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
          v ∈ eM.source →
            (∀ᶠ q in 𝓝 (eM v),
              HasFDerivAt F (DF (eM.symm q)) q) ∧
            ∀ a b : E3,
              (fun q : E3 =>
                  G₁ (F q) ((fderiv ℝ F q) a) ((fderiv ℝ F q) b))
                =ᶠ[𝓝 (eM v)]
              (fun q : E3 => G₀ q a b) := by
  rcases
      DifferentialField.exists_cartanChartDifferential_field_on_punctured_ball
        (g := g) hcurv (x₀ := x₀) (p₀ := p₀) L with
    ⟨ρ, hρ_pos, Afield, Bfield, DF, hDF_def, hfield⟩
  use ρ, hρ_pos, Afield, Bfield, DF
  constructor
  · exact hDF_def
  intro v hv hvne
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀
  let F := CartanDifferential.cartanChartMap g x₀ p₀ L
  let G₀ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric g.inner x₀ z
  let G₁ : E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun z => CovariantDerivative.chartMetric roundSphereMetric3.inner p₀ z
  intro hvsrc
  let U : Set E3 := {w | ‖w‖ < ρ ∧ w ≠ 0}
  have hU_open : IsOpen U := by
    have hball_open : IsOpen {w : E3 | ‖w‖ < ρ} := by
      simpa [Metric.ball, dist_eq_norm] using
        (Metric.isOpen_ball (x := (0 : E3)) (ε := ρ))
    have hne_open : IsOpen {w : E3 | w ≠ 0} := isOpen_ne
    exact hball_open.inter hne_open
  have hvU : v ∈ U := ⟨hv, hvne⟩
  have hvU_symm : eM.symm (eM v) ∈ U := by
    simpa [eM.left_inv hvsrc] using hvU
  have htarget_nhds : eM.target ∈ 𝓝 (eM v) :=
    eM.open_target.mem_nhds (eM.map_source hvsrc)
  have hsymm_preimage : {q : E3 | eM.symm q ∈ U} ∈ 𝓝 (eM v) :=
    (eM.continuousAt_symm (eM.map_source hvsrc)).preimage_mem_nhds
      (hU_open.mem_nhds hvU_symm)
  have hnear :
      ∀ᶠ q in 𝓝 (eM v), q ∈ eM.target ∧ eM.symm q ∈ U := by
    filter_upwards [htarget_nhds, hsymm_preimage] with q hqtarget hqU
    exact ⟨hqtarget, hqU⟩
  constructor
  · filter_upwards [hnear] with q hq
    rcases hfield (eM.symm q) hq.2.1 hq.2.2 with
      ⟨_, _, _, hstrict, _⟩
    have hq_eq : eM (eM.symm q) = q := eM.right_inv hq.1
    have hderiv : HasFDerivAt F (DF (eM.symm q)) (eM (eM.symm q)) := by
      simpa [F] using hstrict.hasFDerivAt
    rwa [hq_eq] at hderiv
  · intro a b
    filter_upwards [hnear] with q hq
    rcases hfield (eM.symm q) hq.2.1 hq.2.2 with
      ⟨_, _, _, hstrict, hpull⟩
    have hq_eq : eM (eM.symm q) = q := eM.right_inv hq.1
    have hderiv : HasFDerivAt F (DF (eM.symm q)) q := by
      have hderiv' :
          HasFDerivAt F (DF (eM.symm q)) (eM (eM.symm q)) := by
        simpa [F] using hstrict.hasFDerivAt
      rwa [hq_eq] at hderiv'
    have hfderiv : fderiv ℝ F q = DF (eM.symm q) := hderiv.fderiv
    calc
      G₁ (F q) ((fderiv ℝ F q) a) ((fderiv ℝ F q) b)
          =
        G₁
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) p₀) (L (eM.symm q)))
          (DF (eM.symm q) a) (DF (eM.symm q) b) := by
            simp [F, CartanDifferential.cartanChartMap, eM, G₁, hfderiv]
      _ = G₀ (eM (eM.symm q)) a b := by
            simpa [G₀, G₁, eM] using hpull a b
      _ = G₀ q a b := by
            rw [hq_eq]

end GermAndField
end Poincare
