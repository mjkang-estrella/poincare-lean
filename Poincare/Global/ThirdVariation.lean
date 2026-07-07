import Poincare.Global.FlowSmoothness

/-!
# Third variation opener for chart geodesic flows

This module starts the next replay one system above `SecondVariation.lean`.
The doubly-augmented state is an augmented geodesic/first-variation state
together with its first variation.  Its vector field is `(F z, D F z ξ)`,
where `F` is the augmented geodesic flow field.
-/

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "X" => ClosedSmoothModel n

omit [T2Space M] in
/--
Picard-Lindelöf package for the third-variation linear ODE along a continuous
doubly-augmented curve.

The proof uses the exported `C²` regularity of the augmented
geodesic/first-variation vector field.  Therefore the doubly-augmented field
`(z, ξ) ↦ (F z, D F z ξ)` is `C¹`, and composing its derivative with a
continuous hosted curve gives the continuous linear coefficient required by
the generic linear-ODE PL package.
-/
theorem exists_isPicardLindelof_chartChristoffel_thirdVariation_linearODE
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {ζ : ℝ → (((X × X) × (X × X)) × ((X × X) × (X × X)))}
    (hζ : Continuous ζ)
    (ξ₀ : (((X × X) × (X × X)) × ((X × X) × (X × X)))) :
    ∃ (ε : ℝ) (_ : 0 < ε), ∃ a r L K : ℝ≥0, 0 < r ∧
      IsPicardLindelof
        (fun t ξ ↦
          fderiv ℝ
            (fun y :
                (((X × X) × (X × X)) × ((X × X) × (X × X))) =>
              let F :
                  ((X × X) × (X × X)) → ((X × X) × (X × X)) :=
                augmentedGeodesicFlowField (chartChristoffelField g x₀)
              (F y.1, (fderiv ℝ F y.1) y.2))
            (ζ t) ξ)
        (tmin := -ε) (tmax := ε)
        ⟨(0 : ℝ), by constructor <;> linarith⟩ ξ₀ a r L K := by
  let Γ : X → X →L[ℝ] X →L[ℝ] X := chartChristoffelField g x₀
  let A : Type := (X × X) × (X × X)
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y => (F y.1, (fderiv ℝ F y.1) y.2)
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
        (g := g) (x₀ := x₀) (p := (0 : A)) (a := 0) with
    ⟨hF_two, _hLip⟩
  have hbase : ContDiff ℝ 1 (fun y : A × A => F y.1) :=
    (hF_two.of_le (by norm_num)).comp contDiff_fst
  have hlin :
      ContDiff ℝ 1
        (fun y : A × A => (fderiv ℝ F y.1 : A →L[ℝ] A) y.2) := by
    simpa [F, Γ, A] using
      (hF_two.contDiff_fderiv_apply (m := 1) (by norm_num))
  have hdouble : ContDiff ℝ 1 doubleF := by
    simpa [doubleF] using hbase.prodMk hlin
  simpa [doubleF, F, Γ, A] using
    exists_isPicardLindelof_continuous_linearODE
      (A := fun t : ℝ => fderiv ℝ doubleF (ζ t))
      (by
        simpa [doubleF] using
          (hdouble.continuous_fderiv (by norm_num)).comp hζ)
      ξ₀

end GeodesicTransport
end Poincare
