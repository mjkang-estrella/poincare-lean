import Poincare.Global.GeodesicFlowDerivative

/-!
# Continuous-linear endpoint map for linearized geodesic solutions

This module packages the fixed-time position endpoint of a chosen family of
linearized chart-geodesic solutions as a continuous linear map.  The linearity
inputs are isolated as standalone uniqueness lemmas for the linearized ODE:
the sum and scalar multiple of solutions solve the same linear system with the
corresponding initial data, so Picard-Lindelöf uniqueness identifies them on
the interval.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/--
Additivity of linearized geodesic solutions on a Picard-Lindelöf interval.

If `Ψw`, `Ψw'`, and `Ψadd` solve the same time-dependent linearized equation
with initial velocities `w`, `w'`, and `w + w'`, and both `Ψadd` and
`Ψw + Ψw'` remain in the PL ball for the summed initial datum, then uniqueness
gives `Ψadd = Ψw + Ψw'` on the whole interval.
-/
theorem linearizedGeodesicFlow_solution_add_uniqueOn_Icc
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ Ψw Ψw' Ψadd : ℝ → E × E}
    {w w' : E} {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E × E => linearizedGeodesicFlowOperator Γ (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E), w + w') a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨw' : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw'
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw' s))
        (Icc tmin tmax) s)
    (hΨadd : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψadd s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ s ∈ Icc tmin tmax,
      Ψadd s ∈ closedBall ((0 : E), w + w') a)
    (hmem_sum : ∀ s ∈ Icc tmin tmax,
      Ψw s + Ψw' s ∈ closedBall ((0 : E), w + w') a)
    (hΨw0 : Ψw 0 = ((0 : E), w))
    (hΨw'0 : Ψw' 0 = ((0 : E), w'))
    (hΨadd0 : Ψadd 0 = ((0 : E), w + w')) :
    EqOn Ψadd (fun s : ℝ => Ψw s + Ψw' s) (Icc tmin tmax) := by
  let A : ℝ → (E × E) →L[ℝ] (E × E) :=
    fun s => linearizedGeodesicFlowOperator Γ (γ s)
  have hder_add : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd (A s (Ψadd s)) (Icc tmin tmax) s := by
    intro s hs
    simpa [A, linearizedGeodesicFlowFieldAlong] using hΨadd s hs
  have hder_sum : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => Ψw τ + Ψw' τ)
        (A s ((fun τ : ℝ => Ψw τ + Ψw' τ) s)) (Icc tmin tmax) s := by
    intro s hs
    have hder := (hΨw s hs).add (hΨw' s hs)
    simpa [A, linearizedGeodesicFlowFieldAlong] using hder
  have hinitial :
      Ψadd (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
        (fun s : ℝ => Ψw s + Ψw' s)
          (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
    change Ψadd 0 = Ψw 0 + Ψw' 0
    rw [hΨadd0, hΨw0, hΨw'0]
    simp
  exact
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : E), w + w')) (a := a) (r := r) (L := L) (K := K)
      hpl hder_add hmem_add hder_sum hmem_sum hinitial

/-- Fixed-time endpoint form of `linearizedGeodesicFlow_solution_add_uniqueOn_Icc`. -/
theorem linearizedGeodesicFlow_endpoint_add_of_uniqueOn_Icc
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ Ψw Ψw' Ψadd : ℝ → E × E}
    {w w' : E} {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E × E => linearizedGeodesicFlowOperator Γ (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E), w + w') a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨw' : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw'
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw' s))
        (Icc tmin tmax) s)
    (hΨadd : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψadd
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψadd s))
        (Icc tmin tmax) s)
    (hmem_add : ∀ s ∈ Icc tmin tmax,
      Ψadd s ∈ closedBall ((0 : E), w + w') a)
    (hmem_sum : ∀ s ∈ Icc tmin tmax,
      Ψw s + Ψw' s ∈ closedBall ((0 : E), w + w') a)
    (hΨw0 : Ψw 0 = ((0 : E), w))
    (hΨw'0 : Ψw' 0 = ((0 : E), w'))
    (hΨadd0 : Ψadd 0 = ((0 : E), w + w')) (hT : T ∈ Icc tmin tmax) :
    (Ψadd T).1 = (Ψw T).1 + (Ψw' T).1 := by
  have hEq :=
    linearizedGeodesicFlow_solution_add_uniqueOn_Icc
      (Γ := Γ) (γ := γ) (Ψw := Ψw) (Ψw' := Ψw') (Ψadd := Ψadd)
      (w := w) (w' := w') hzero hpl hΨw hΨw' hΨadd
      hmem_add hmem_sum hΨw0 hΨw'0 hΨadd0
  exact congrArg Prod.fst (hEq hT)

/--
Scalar homogeneity of linearized geodesic solutions on a Picard-Lindelöf
interval.

If `Ψw` and `Ψsmul` solve the same time-dependent linearized equation with
initial velocities `w` and `c • w`, and both `Ψsmul` and `c • Ψw` remain in
the PL ball for the scaled initial datum, uniqueness gives
`Ψsmul = c • Ψw` on the whole interval.
-/
theorem linearizedGeodesicFlow_solution_smul_uniqueOn_Icc
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ Ψw Ψsmul : ℝ → E × E}
    {w : E} {c : ℝ} {tmin tmax : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E × E => linearizedGeodesicFlowOperator Γ (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E), c • w) a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨsmul : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψsmul
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψsmul s))
        (Icc tmin tmax) s)
    (hmem_smul : ∀ s ∈ Icc tmin tmax,
      Ψsmul s ∈ closedBall ((0 : E), c • w) a)
    (hmem_scaled : ∀ s ∈ Icc tmin tmax,
      c • Ψw s ∈ closedBall ((0 : E), c • w) a)
    (hΨw0 : Ψw 0 = ((0 : E), w))
    (hΨsmul0 : Ψsmul 0 = ((0 : E), c • w)) :
    EqOn Ψsmul (fun s : ℝ => c • Ψw s) (Icc tmin tmax) := by
  let A : ℝ → (E × E) →L[ℝ] (E × E) :=
    fun s => linearizedGeodesicFlowOperator Γ (γ s)
  have hder_smul : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψsmul (A s (Ψsmul s)) (Icc tmin tmax) s := by
    intro s hs
    simpa [A, linearizedGeodesicFlowFieldAlong] using hΨsmul s hs
  have hder_scaled : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt (fun τ : ℝ => c • Ψw τ)
        (A s ((fun τ : ℝ => c • Ψw τ) s)) (Icc tmin tmax) s := by
    intro s hs
    have hder := (hΨw s hs).const_smul c
    simpa [A, linearizedGeodesicFlowFieldAlong] using hder
  have hinitial :
      Ψsmul (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) =
        (fun s : ℝ => c • Ψw s) (⟨(0 : ℝ), hzero⟩ : Icc tmin tmax) := by
    change Ψsmul 0 = c • Ψw 0
    rw [hΨsmul0, hΨw0]
    simp
  exact
    linearODE_solution_uniqueOn_Icc
      (A := A) (t₀ := ⟨(0 : ℝ), hzero⟩)
      (x₀ := ((0 : E), c • w)) (a := a) (r := r) (L := L) (K := K)
      hpl hder_smul hmem_smul hder_scaled hmem_scaled hinitial

/-- Fixed-time endpoint form of `linearizedGeodesicFlow_solution_smul_uniqueOn_Icc`. -/
theorem linearizedGeodesicFlow_endpoint_smul_of_uniqueOn_Icc
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {γ Ψw Ψsmul : ℝ → E × E}
    {w : E} {c : ℝ} {tmin tmax T : ℝ} (hzero : (0 : ℝ) ∈ Icc tmin tmax)
    {a r L K : ℝ≥0}
    (hpl : IsPicardLindelof
      (fun s : ℝ => fun ψ : E × E => linearizedGeodesicFlowOperator Γ (γ s) ψ)
      (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
      ((0 : E), c • w) a r L K)
    (hΨw : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψw
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψw s))
        (Icc tmin tmax) s)
    (hΨsmul : ∀ s ∈ Icc tmin tmax,
      HasDerivWithinAt Ψsmul
        (linearizedGeodesicFlowFieldAlong Γ γ s (Ψsmul s))
        (Icc tmin tmax) s)
    (hmem_smul : ∀ s ∈ Icc tmin tmax,
      Ψsmul s ∈ closedBall ((0 : E), c • w) a)
    (hmem_scaled : ∀ s ∈ Icc tmin tmax,
      c • Ψw s ∈ closedBall ((0 : E), c • w) a)
    (hΨw0 : Ψw 0 = ((0 : E), w))
    (hΨsmul0 : Ψsmul 0 = ((0 : E), c • w)) (hT : T ∈ Icc tmin tmax) :
    (Ψsmul T).1 = c • (Ψw T).1 := by
  have hEq :=
    linearizedGeodesicFlow_solution_smul_uniqueOn_Icc
      (Γ := Γ) (γ := γ) (Ψw := Ψw) (Ψsmul := Ψsmul)
      (w := w) (c := c) hzero hpl hΨw hΨsmul hmem_smul hmem_scaled
      hΨw0 hΨsmul0
  exact congrArg Prod.fst (hEq hT)

/--
The linear map sending an initial linearized velocity `w` to the position
component of the chosen linearized solution at time `T`.
-/
def linearizedEndpointLinearMap
    (Ψ : E → ℝ → E × E) (T : ℝ)
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1) :
    E →ₗ[ℝ] E where
  toFun w := (Ψ w T).1
  map_add' w w' := hadd w w'
  map_smul' c w := hsmul c w

/--
The fixed-time linearized endpoint position map as a continuous linear map.

Continuity is supplied by finite dimensionality of the domain through
`LinearMap.toContinuousLinearMap`.
-/
def linearizedEndpointCLM
    [FiniteDimensional ℝ E]
    (Ψ : E → ℝ → E × E) (T : ℝ)
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1) :
    E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (linearizedEndpointLinearMap (Ψ := Ψ) (T := T) hadd hsmul)

@[simp]
theorem linearizedEndpointCLM_apply
    [FiniteDimensional ℝ E]
    (Ψ : E → ℝ → E × E) (T : ℝ)
    (hadd : ∀ w w' : E,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hsmul : ∀ (c : ℝ) (w : E),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (w : E) :
    linearizedEndpointCLM (Ψ := Ψ) T hadd hsmul w = (Ψ w T).1 :=
  rfl

end Poincare
