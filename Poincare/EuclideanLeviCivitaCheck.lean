/-
The Levi-Civita construction computes correctly on the model space: for the
Euclidean metric it coincides with the flat connection.
-/

import Poincare.KoszulExistence

noncomputable section

open Bundle CovariantDerivative
open scoped Manifold ContDiff RealInnerProductSpace

namespace CovariantDerivative

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

theorem euclideanBundleMetric_symm (y : F)
    (v w : TangentSpace 𝓘(ℝ, F) y) :
    euclideanBundleMetric y v w = euclideanBundleMetric y w v :=
  @real_inner_comm F _ _ w v

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
theorem euclideanBundleMetric_nondegenerate (y : F)
    (v : TangentSpace 𝓘(ℝ, F) y)
    (hv : ∀ w, euclideanBundleMetric y v w = 0) : v = 0 := by
  have h := hv v
  exact (inner_self_eq_zero (𝕜 := ℝ) (E := F)).mp h

theorem euclideanBundleMetric_pairing_mdiff (x : F)
    (A B : Π y : F, TangentSpace 𝓘(ℝ, F) y)
    (hA : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% A) x)
    (hB : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% B) x) :
    MDiffAt (fun y ↦ euclideanBundleMetric y (A y) (B y)) x := by
  have hA' := mdiffAt_vectorSpace_iff_differentiableAt.mp hA
  have hB' := mdiffAt_vectorSpace_iff_differentiableAt.mp hB
  exact mdifferentiableAt_iff_differentiableAt.mpr (hA'.inner ℝ hB')

/--
**The construction computes correctly on the model**: the constructed
Levi-Civita connection of the Euclidean metric coincides with the flat
connection on differentiable fields.
-/
theorem leviCivitaConnection_euclidean_eq_flat
    {Y : Π y : F, TangentSpace 𝓘(ℝ, F) y} {x : F}
    (hY : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% Y) x) :
    leviCivitaConnection euclideanBundleMetric
        euclideanBundleMetric_symm euclideanBundleMetric_nondegenerate
        euclideanBundleMetric_pairing_mdiff Y x =
      flatCovariantDerivative ℝ F Y x :=
  leviCivitaConnection_eq_of_isLeviCivita euclideanBundleMetric
    euclideanBundleMetric_symm euclideanBundleMetric_nondegenerate
    euclideanBundleMetric_pairing_mdiff (flatCovariantDerivative ℝ F)
    (fun y ↦ flat_metricCompatibleAt y) (fun y ↦ flat_torsionFreeAt y) hY

end CovariantDerivative
