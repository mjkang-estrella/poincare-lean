import Poincare.Global.CoefficientEvolution

/-!
# Jacobi norm scalar system

This file isolates the classical scalar ODE behind the transverse Jacobi norm
calculation.  The geometric input is expressed in chart form: metric
compatibility converts coordinate derivatives of the endpoint pairing into
pairings of covariant time derivatives.  Once the covariant second derivative
is `-J`, the three quadratic scalars close as `a' = 2b`, `b' = c - a`,
`c' = -2b`.

The final section pins the closed system against the model sine/cosine solution
and records the polarization algebra used to pass from quadratic norms to
bilinear pairings.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

open Filter Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

namespace JacobiNormSystem

section Compatibility

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

open GeodesicTransport

/-- The covariant time derivative in chart coordinates along a curve with velocity `v`. -/
def covariantTimeDerivative
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z v X Xdot : E) : E :=
  Xdot + (chartChristoffelField g x₀ z) v X

/-- The quadratic Jacobi norm scalar `a(t) = G(z(t))(J(t),J(t))`. -/
def normA
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z J : ℝ → E) (t : ℝ) : ℝ :=
  chartGeodesicMetric g x₀ (z t) (J t) (J t)

/-- The mixed Jacobi norm scalar `b(t) = G(z(t))(J(t),D_t J(t))`. -/
def normB
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z J D : ℝ → E) (t : ℝ) : ℝ :=
  chartGeodesicMetric g x₀ (z t) (J t) (D t)

/-- The derivative-norm scalar `c(t) = G(z(t))(D_t J(t),D_t J(t))`. -/
def normC
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    (z D : ℝ → E) (t : ℝ) : ℝ :=
  chartGeodesicMetric g x₀ (z t) (D t) (D t)

omit [T2Space M] in
/--
Metric compatibility for time-varying fields in chart form.

If `Xcov` and `Ycov` are the covariant time derivatives of the two chart fields
at `t`, the derivative of their metric pairing is the expected sum of endpoint
pairings with `Xcov` and `Ycov`.
-/
theorem chart_metric_pairing_hasDerivAt_covariant
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {zcurve X Y : ℝ → E} {t : ℝ} {zdot Xcov Ycov : E}
    (hz : HasDerivAt zcurve zdot t)
    (hX : HasDerivAt X
      (Xcov - (chartChristoffelField g x₀ (zcurve t)) zdot (X t)) t)
    (hY : HasDerivAt Y
      (Ycov - (chartChristoffelField g x₀ (zcurve t)) zdot (Y t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (zcurve t)) :
    HasDerivAt
      (fun τ : ℝ => chartGeodesicMetric g x₀ (zcurve τ) (X τ) (Y τ))
      (chartGeodesicMetric g x₀ (zcurve t) Xcov (Y t) +
        chartGeodesicMetric g x₀ (zcurve t) (X t) Ycov) t := by
  set G : E → E →L[ℝ] E →L[ℝ] ℝ := chartGeodesicMetric g x₀
  set Γ : E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀ (zcurve t)
  have hGpath :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ))
        ((fderiv ℝ G (zcurve t)) zdot) t := by
    have hcomp :
        HasDerivAt (G ∘ zcurve) ((fderiv ℝ G (zcurve t)) zdot) t :=
      HasFDerivAt.comp_hasDerivAt
        (𝕜 := ℝ) (F := E)
        (f := zcurve) (f' := zdot) (x := t)
        (l := G) (l' := fderiv ℝ G (zcurve t))
        hGd.hasFDerivAt hz
    simpa [Function.comp_def] using hcomp
  have hGX :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ) (X τ))
        (((fderiv ℝ G (zcurve t)) zdot) (X t) +
          G (zcurve t) (Xcov - Γ zdot (X t))) t := by
    simpa [G, Γ] using hGpath.clm_apply hX
  have hraw :
      HasDerivAt
        (fun τ : ℝ => G (zcurve τ) (X τ) (Y τ))
        (((((fderiv ℝ G (zcurve t)) zdot) (X t) +
              G (zcurve t) (Xcov - Γ zdot (X t))) (Y t)) +
          G (zcurve t) (X t) (Ycov - Γ zdot (Y t))) t := by
    simpa [G, Γ] using hGX.clm_apply hY
  have hcompat :
      G (zcurve t) (Γ zdot (X t)) (Y t) +
          G (zcurve t) (X t) (Γ zdot (Y t)) =
        ((fderiv ℝ G (zcurve t)) zdot) (X t) (Y t) := by
    simpa [G, Γ] using
      chartChristoffelField_fixed_pairing_eq_fderiv_metric
        (g := g) (x₀ := x₀) (z := zcurve t) hGd
        (v := zdot) (w := X t) (w' := Y t)
  convert hraw using 1
  simp only [G, Γ, ContinuousLinearMap.add_apply, map_sub,
    ContinuousLinearMap.sub_apply]
  rw [← hcompat]
  abel

omit [T2Space M] in
/-- The first scalar equation: `a' = 2b`. -/
theorem normA_hasDerivAt
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z J D : ℝ → E} {t : ℝ} {zdot : E}
    (hz : HasDerivAt z zdot t)
    (hJ : HasDerivAt J
      (D t - (chartChristoffelField g x₀ (z t)) zdot (J t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt (normA g x₀ z J) (2 * normB g x₀ z J D t) t := by
  have h :=
    chart_metric_pairing_hasDerivAt_covariant
      (g := g) (x₀ := x₀) (zcurve := z) (X := J) (Y := J)
      (t := t) (zdot := zdot) (Xcov := D t) (Ycov := D t)
      hz hJ hJ hGd
  have h' :
      HasDerivAt (normA g x₀ z J)
        (chartGeodesicMetric g x₀ (z t) (D t) (J t) +
          chartGeodesicMetric g x₀ (z t) (J t) (D t)) t := by
    simpa [normA] using h
  convert h' using 1
  dsimp [normB]
  rw [chartGeodesicMetric_symm (g := g) (x₀ := x₀) (z t) (D t) (J t)]
  ring

omit [T2Space M] in
/-- The second scalar equation under the oscillator hypothesis: `b' = c - a`. -/
theorem normB_hasDerivAt_of_oscillator
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z J D : ℝ → E} {t : ℝ} {zdot : E}
    (hz : HasDerivAt z zdot t)
    (hJ : HasDerivAt J
      (D t - (chartChristoffelField g x₀ (z t)) zdot (J t)) t)
    (hD : HasDerivAt D
      ((-J t) - (chartChristoffelField g x₀ (z t)) zdot (D t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt (normB g x₀ z J D) (normC g x₀ z D t - normA g x₀ z J t) t := by
  have h :=
    chart_metric_pairing_hasDerivAt_covariant
      (g := g) (x₀ := x₀) (zcurve := z) (X := J) (Y := D)
      (t := t) (zdot := zdot) (Xcov := D t) (Ycov := -J t)
      hz hJ hD hGd
  have h' :
      HasDerivAt (normB g x₀ z J D)
        (chartGeodesicMetric g x₀ (z t) (D t) (D t) +
          chartGeodesicMetric g x₀ (z t) (J t) (-J t)) t := by
    simpa [normB] using h
  convert h' using 1
  dsimp [normA, normC]
  simp only [map_neg]
  ring

omit [T2Space M] in
/-- The third scalar equation under the oscillator hypothesis: `c' = -2b`. -/
theorem normC_hasDerivAt_of_oscillator
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {z J D : ℝ → E} {t : ℝ} {zdot : E}
    (hz : HasDerivAt z zdot t)
    (hD : HasDerivAt D
      ((-J t) - (chartChristoffelField g x₀ (z t)) zdot (D t)) t)
    (hGd : DifferentiableAt ℝ (chartGeodesicMetric g x₀) (z t)) :
    HasDerivAt (normC g x₀ z D) (-2 * normB g x₀ z J D t) t := by
  have h :=
    chart_metric_pairing_hasDerivAt_covariant
      (g := g) (x₀ := x₀) (zcurve := z) (X := D) (Y := D)
      (t := t) (zdot := zdot) (Xcov := -J t) (Ycov := -J t)
      hz hD hD hGd
  have h' :
      HasDerivAt (normC g x₀ z D)
        (chartGeodesicMetric g x₀ (z t) (-J t) (D t) +
          chartGeodesicMetric g x₀ (z t) (D t) (-J t)) t := by
    simpa [normC] using h
  convert h' using 1
  dsimp [normB]
  simp only [map_neg, ContinuousLinearMap.neg_apply]
  rw [chartGeodesicMetric_symm (g := g) (x₀ := x₀) (z t) (D t) (J t)]
  ring

end Compatibility

section PinnedSolution

/-- The pinned model solution `a(t) = sin²(t) q`. -/
def pinnedA (q t : ℝ) : ℝ :=
  Real.sin t ^ 2 * q

/-- The pinned model solution `b(t) = sin(t) cos(t) q`. -/
def pinnedB (q t : ℝ) : ℝ :=
  (Real.sin t * Real.cos t) * q

/-- The pinned model solution `c(t) = cos²(t) q`. -/
def pinnedC (q t : ℝ) : ℝ :=
  Real.cos t ^ 2 * q

@[simp]
theorem pinnedA_zero (q : ℝ) : pinnedA q 0 = 0 := by
  simp [pinnedA]

@[simp]
theorem pinnedB_zero (q : ℝ) : pinnedB q 0 = 0 := by
  simp [pinnedB]

@[simp]
theorem pinnedC_zero (q : ℝ) : pinnedC q 0 = q := by
  simp [pinnedC]

/-- Pinning check: `a = sin² q` satisfies `a' = 2b`. -/
theorem pinnedA_hasDerivAt (q t : ℝ) :
    HasDerivAt (pinnedA q) (2 * pinnedB q t) t := by
  have hsin := Real.hasDerivAt_sin t
  have hprod := (hsin.mul hsin).mul_const q
  convert hprod using 1
  · ext y
    simp [pinnedA, pow_two]
  · dsimp [pinnedB]
    ring_nf

/-- Pinning check: `b = sin cos q` satisfies `b' = c - a`. -/
theorem pinnedB_hasDerivAt (q t : ℝ) :
    HasDerivAt (pinnedB q) (pinnedC q t - pinnedA q t) t := by
  have hsin := Real.hasDerivAt_sin t
  have hcos := Real.hasDerivAt_cos t
  have hprod := (hsin.mul hcos).mul_const q
  convert hprod using 1
  dsimp [pinnedA, pinnedC]
  ring_nf

/-- Pinning check: `c = cos² q` satisfies `c' = -2b`. -/
theorem pinnedC_hasDerivAt (q t : ℝ) :
    HasDerivAt (pinnedC q) (-2 * pinnedB q t) t := by
  have hcos := Real.hasDerivAt_cos t
  have hprod := (hcos.mul hcos).mul_const q
  convert hprod using 1
  · ext y
    simp [pinnedC, pow_two]
  · dsimp [pinnedB]
    ring_nf

end PinnedSolution

section Polarization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Polarization for a symmetric continuous bilinear form. -/
theorem symmetric_bilinear_polarization
    (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ u v : E, B u v = B v u) (u v : E) :
    B u v =
      (1 / 2 : ℝ) * (B (u + v) (u + v) - B u u - B v v) := by
  have hquad :
      B (u + v) (u + v) = B u u + B u v + B v u + B v v := by
    simp [ContinuousLinearMap.add_apply, add_left_comm, add_comm]
  rw [hquad, hsymm v u]
  ring

/--
Quadratic norm identities plus linearity of the Jacobi field in the initial
direction polarize to the bilinear endpoint pairing.
-/
theorem polarize_endpoint_pairing_of_quadratic
    (B A : E →L[ℝ] E →L[ℝ] ℝ)
    (hBsymm : ∀ u v : E, B u v = B v u)
    (hAsymm : ∀ u v : E, A u v = A v u)
    (S : ℝ) {w w' Jw Jw' Jadd : E}
    (hJadd : Jadd = Jw + Jw')
    (hww : B Jw Jw = S * A w w)
    (hww' : B Jw' Jw' = S * A w' w')
    (hadd : B Jadd Jadd = S * A (w + w') (w + w')) :
    B Jw Jw' = S * A w w' := by
  have hBpol := symmetric_bilinear_polarization B hBsymm Jw Jw'
  have hApol := symmetric_bilinear_polarization A hAsymm w w'
  have hAquad : A (w + w') (w + w') - A w w - A w' w' = 2 * A w w' := by
    linarith
  calc
    B Jw Jw' =
        (1 / 2 : ℝ) * (B (Jw + Jw') (Jw + Jw') - B Jw Jw - B Jw' Jw') := hBpol
    _ = (1 / 2 : ℝ) *
        (S * A (w + w') (w + w') - S * A w w - S * A w' w') := by
          rw [← hJadd, hadd, hww, hww']
    _ = S * A w w' := by
      rw [← mul_sub, ← mul_sub, hAquad]
      ring

end Polarization

end JacobiNormSystem

end Poincare
