import Poincare.Global.ConformalCurvature

/-!
# Christoffel collapse obstruction

This module records the explicit round-sphere chart obstruction to the proposed
`haccCollapse`: even at a unit-speed transverse state, the Christoffel
correction expression is not the rescaled harmonic acceleration for arbitrary
hosted speed.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare
namespace ChristoffelCollapse

theorem sphereChristoffel_refutes_haccCollapse_at_unit_transverse_state :
    (let z : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ);
     let V : EuclideanSpace ℝ (Fin 3) :=
      (5 / 4 : ℝ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ);
     let J : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : ℝ);
     let K : EuclideanSpace ℝ (Fin 3) := 0;
     let speed : ℝ := 2;
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
  · simp [conformalChartMetricForm, stereoInvFunAuxConformalFactor]
    rw [norm_smul, PiLp.norm_single]
    norm_num
  constructor
  · simp [conformalChartMetricForm, stereoInvFunAuxConformalFactor,
      EuclideanSpace.inner_single_left]
  · intro h
    have hc := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x (2 : Fin 3)) h
    simp [fderiv_sphereChristoffel, sphereChristoffelFDeriv_apply,
      sphereChristoffel_apply, sphereChristoffelCoeff, sphereChristoffelCoeffFDeriv,
      sphereChristoffelCoreFormula, EuclideanSpace.inner_single_left] at hc
    norm_num at hc

end ChristoffelCollapse
end Poincare
