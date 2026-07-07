import Poincare.Global.JacobiOscillator
import Poincare.Global.TangentAlignmentExists

/-!
# Cartan metric-preservation strict partial

This module starts the Cartan local-isometry assembly at the first required
non-vacuous interface: the fixed-time derivative of the charted exponential in
an initial-velocity direction is the position component of the linearized
geodesic-flow solution.  Combining that with the already-proved harmonic
Jacobi uniqueness theorem gives the `sin t` transverse factor, under the
explicit hypotheses that identify the linearized state with the harmonic
Jacobi state on the interval.
-/

noncomputable section

open Bundle Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanIsometry

universe u

section General

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Fixed-time initial-velocity derivative of the charted exponential.

Precisely, for a common PL chart geodesic flow `α`, if `Ψ` solves the
linearized geodesic equation along the base velocity `v` with initial state
`(0,w)`, then the derivative at `s = 0` of

`s ↦ extChartAt I x₀ (expAt g x₀ (t • (v + s • w)))`

is `(Ψ t).1`.  Thus this is `D(expAt)_{t • v}(t • w)` in chart coordinates,
with the homogeneity reparametrization carried by the fixed time `t`.
-/
theorem expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {δ τ : ℝ} {a : ℝ≥0}
    {α : E × E → ℝ → E × E}
    {v w : E} {Ψ : ℝ → E × E} {t : ℝ}
    (hτ : 0 < τ) (hv : ‖v‖ < δ)
    (hα0 : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀))
    (hαder : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v₀) r))
        (Icc (-τ) τ) r)
    (hαmem : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      α (extChartAt I x₀ x₀, v₀) r ∈
        closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ))
    (hαtarget : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      (α (extChartAt I x₀ x₀, v₀) r).1 ∈ (extChartAt I x₀).target)
    (hexp : ∀ v₀ : E, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      GeodesicTransport.expAt g x₀ (r • v₀) =
        (extChartAt I x₀).symm (α (extChartAt I x₀ x₀, v₀) r).1)
    (hΨ0 : Ψ 0 = ((0 : E), w))
    (hΨder : ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I x₀ x₀, v)) r (Ψ r))
        (Icc (-τ) τ) r)
    (ht : t ∈ Icc (0 : ℝ) τ) :
    HasDerivAt
      (fun s : ℝ =>
        extChartAt I x₀
          (GeodesicTransport.expAt g x₀ (t • (v + s • w))))
      (Ψ t).1 0 := by
  have hαflow : ∀ v₀ : E, ‖v₀‖ < δ →
      α (extChartAt I x₀ x₀, v₀) 0 = (extChartAt I x₀ x₀, v₀) ∧
        (∀ r ∈ Icc (-τ) τ,
          HasDerivWithinAt (α (extChartAt I x₀ x₀, v₀))
            (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
              (α (extChartAt I x₀ x₀, v₀) r))
            (Icc (-τ) τ) r) ∧
          ∀ r ∈ Icc (-τ) τ,
            α (extChartAt I x₀ x₀, v₀) r ∈
              closedBall (extChartAt I x₀ x₀, (0 : E)) (a : ℝ) := by
    intro v₀ hv₀
    exact ⟨hα0 v₀ hv₀, hαder v₀ hv₀, hαmem v₀ hv₀⟩
  have hflow_pair :
      HasDerivAt
        (fun s : ℝ => α (extChartAt I x₀ x₀, v + s • w) t)
        (Ψ t) 0 :=
    GeodesicTransport.chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (ε := τ) (a := a)
      (α := α) (v := v) (w := w) (Ψ := Ψ) (t := t)
      hτ hv hαflow hΨ0 hΨder ht
  have hflow_pos :
      HasDerivAt
        (fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).1)
        (Ψ t).1 0 := by
    have hF := hflow_pair.hasFDerivAt.fst
    simpa using hF.hasDerivAt
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), ‖v + s • w‖ < δ :=
    eventually_norm_add_smul_lt (v := v) (w := w) hv
  have htfull : t ∈ Icc (-τ) τ := ⟨by linarith [hτ, ht.1], ht.2⟩
  have hEq :
      (fun s : ℝ =>
        extChartAt I x₀
          (GeodesicTransport.expAt g x₀ (t • (v + s • w)))) =ᶠ[𝓝 (0 : ℝ)]
        fun s : ℝ => (α (extChartAt I x₀ x₀, v + s • w) t).1 := by
    filter_upwards [hsmall] with s hs
    have htarget := hαtarget (v + s • w) hs t htfull
    have hexps := hexp (v + s • w) hs t ht
    calc
      extChartAt I x₀
          (GeodesicTransport.expAt g x₀ (t • (v + s • w))) =
          extChartAt I x₀ ((extChartAt I x₀).symm
            (α (extChartAt I x₀ x₀, v + s • w) t).1) := by
            rw [hexps]
      _ = (α (extChartAt I x₀ x₀, v + s • w) t).1 :=
          (extChartAt I x₀).right_inv htarget
  exact hflow_pos.congr_of_eventuallyEq hEq

end General

section DimensionThree

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "E3" => ClosedSmoothModel 3

/--
The same fixed-time derivative after substituting the constant-curvature
Jacobi formula.  Under the explicit interval hypotheses that make `Ψ` the
harmonic Jacobi state with initial data `(0,w)`, the charted derivative is the
classical transverse value `sin t • w`.
-/
theorem expAt_chart_initialVelocity_hasDerivAt_eq_sin_smul
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {δ τ : ℝ} {a : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {v w : E3} {Ψ : ℝ → E3 × E3} {t : ℝ}
    (hτ : 0 < τ) (hv : ‖v‖ < δ)
    (hα0 : ∀ v₀ : E3, ‖v₀‖ < δ →
      α (extChartAt I3 x₀ x₀, v₀) 0 = (extChartAt I3 x₀ x₀, v₀))
    (hαder : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt (α (extChartAt I3 x₀ x₀, v₀))
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v₀) r))
        (Icc (-τ) τ) r)
    (hαmem : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      α (extChartAt I3 x₀ x₀, v₀) r ∈
        closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (a : ℝ))
    (hαtarget : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ r ∈ Icc (-τ) τ,
      (α (extChartAt I3 x₀ x₀, v₀) r).1 ∈ (extChartAt I3 x₀).target)
    (hexp : ∀ v₀ : E3, ‖v₀‖ < δ → ∀ r ∈ Icc (0 : ℝ) τ,
      GeodesicTransport.expAt g x₀ (r • v₀) =
        (extChartAt I3 x₀).symm (α (extChartAt I3 x₀ x₀, v₀) r).1)
    (hΨ0 : Ψ 0 = ((0 : E3), w))
    (hΨlin : ∀ r ∈ Icc (-τ) τ,
      HasDerivWithinAt Ψ
        (linearizedGeodesicFlowFieldAlong
          (GeodesicTransport.chartChristoffelField g x₀)
          (α (extChartAt I3 x₀ x₀, v)) r (Ψ r))
        (Icc (-τ) τ) r)
    {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {A R L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun _ : ℝ => fun ψ : E3 × E3 => harmonicJacobiOperator ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩ ((0 : E3), w) A R L K)
    (hΨharmonic : ∀ r ∈ Icc tmin tmax,
      HasDerivWithinAt Ψ (harmonicJacobiOperator (Ψ r)) (Icc tmin tmax) r)
    (hΨmem : ∀ r ∈ Icc tmin tmax, Ψ r ∈ closedBall ((0 : E3), w) A)
    (hsinmem : ∀ r ∈ Icc tmin tmax, jacobiSinState w r ∈ closedBall ((0 : E3), w) A)
    (ht : t ∈ Icc (0 : ℝ) τ) (htJacobi : t ∈ Icc tmin tmax) :
    HasDerivAt
      (fun s : ℝ =>
        extChartAt I3 x₀
          (GeodesicTransport.expAt g x₀ (t • (v + s • w))))
      (Real.sin t • w) 0 := by
  have hder :=
    expAt_chart_initialVelocity_hasDerivAt_of_uniform_geodesicFlow
      (g := g) (x₀ := x₀) (δ := δ) (τ := τ) (a := a)
      (α := α) (v := v) (w := w) (Ψ := Ψ) (t := t)
      hτ hv hα0 hαder hαmem hαtarget hexp hΨ0 hΨlin ht
  have hsin :
      (Ψ t).1 = Real.sin t • w :=
    jacobi_position_eq_sin_smul_on_Icc
      (w := w) hzero (hpl := hpl) (Ψ := Ψ)
      hΨharmonic hΨmem hsinmem hΨ0 htJacobi
  simpa [hsin] using hder

end DimensionThree

end CartanIsometry
end Poincare
