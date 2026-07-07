import Poincare.Global.ConformalCurvature

/-!
# Collapse pin on a radial sphere state

This module records the requested sphere pin before any downstream Cartan
composition: the raw coordinate collapse still fails at a unit radial
stereographic sphere state with the harmonic sine/cosine transverse values.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare
namespace CollapseOnRay

theorem sphereChristoffel_refutes_haccCollapse_at_unit_radial_harmonic_state :
    (let e0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ);
     let e1 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (1 : Fin 3) (1 : ℝ);
     let z : EuclideanSpace ℝ (Fin 3) := e0;
     let V : EuclideanSpace ℝ (Fin 3) := (5 / 4 : ℝ) • e0;
     let J : EuclideanSpace ℝ (Fin 3) := (4 / 5 : ℝ) • e1;
     let K : EuclideanSpace ℝ (Fin 3) := (3 / 5 : ℝ) • e1;
     let speed : ℝ := 1;
     V = (5 / 4 : ℝ) • z ∧
      conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : EuclideanSpace ℝ (Fin 3) → ℝ)
          z V V = 1 ∧
      conformalChartMetricForm
          (stereoInvFunAuxConformalFactor : EuclideanSpace ℝ (Fin 3) → ℝ)
          z J V = 0 ∧
      -J -
          (((fderiv ℝ (sphereChristoffel (E := EuclideanSpace ℝ (Fin 3))) z) V) V) J +
          (sphereChristoffel (E := EuclideanSpace ℝ (Fin 3)) z)
            ((sphereChristoffel (E := EuclideanSpace ℝ (Fin 3)) z) V V) J -
          (sphereChristoffel (E := EuclideanSpace ℝ (Fin 3)) z) V (speed • K) -
          (sphereChristoffel (E := EuclideanSpace ℝ (Fin 3)) z) V
            ((speed • K) +
              (sphereChristoffel (E := EuclideanSpace ℝ (Fin 3)) z) V J) ≠
        (speed * speed) • (-J)) := by
  dsimp
  constructor
  · rfl
  constructor
  · simp [conformalChartMetricForm, stereoInvFunAuxConformalFactor]
    rw [norm_smul, PiLp.norm_single]
    norm_num
  constructor
  · unfold conformalChartMetricForm
    rw [inner_smul_left, inner_smul_right]
    simp [EuclideanSpace.inner_single_left]
  · intro h
    have hc := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x (1 : Fin 3)) h
    simp [fderiv_sphereChristoffel, sphereChristoffelFDeriv_apply,
      sphereChristoffel_apply, sphereChristoffelCoeff, sphereChristoffelCoeffFDeriv,
      sphereChristoffelCoreFormula, EuclideanSpace.inner_single_left] at hc
    norm_num at hc

end CollapseOnRay
end Poincare
