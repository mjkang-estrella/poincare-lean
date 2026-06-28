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

/--
**The constructed connection on Euclidean space is flat**: its curvature
operator vanishes on `C²` fields, via the coincidence with the flat
connection and the model flatness theorem.
-/
theorem curvatureOp_leviCivitaConnection_euclidean
    {X Y Z : Π y : F, TangentSpace 𝓘(ℝ, F) y} {x : F}
    (hX : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% X) x)
    (hY : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% Y) x)
    (hZcd : ContDiff ℝ 2 (Z : F → F)) :
    curvatureOp (leviCivitaConnection (euclideanBundleMetric (F := F))
        euclideanBundleMetric_symm euclideanBundleMetric_nondegenerate
        euclideanBundleMetric_pairing_mdiff) X Y Z x = 0 := by
  set LC := leviCivitaConnection (euclideanBundleMetric (F := F))
    euclideanBundleMetric_symm euclideanBundleMetric_nondegenerate
    euclideanBundleMetric_pairing_mdiff with hLC
  have hZdiff : ∀ y : F, MDifferentiableAt 𝓘(ℝ, F)
      (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (T% Z) y := fun y ↦
    mdiffAt_vectorSpace_iff_differentiableAt.mpr
      (hZcd.differentiable (by norm_num) y)
  have hcovZ : LC Z = flatCovariantDerivative ℝ F Z :=
    funext fun y ↦ leviCivitaConnection_euclidean_eq_flat (hZdiff y)
  have hDZY : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
      (T% (fun y ↦ flatCovariantDerivative ℝ F Z y (Y y))) x := by
    apply mdiffAt_vectorSpace_iff_differentiableAt.mpr
    apply DifferentiableAt.clm_apply
    · exact ((hZcd.contDiffAt (x := x)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp hY
  have hDZX : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
      (T% (fun y ↦ flatCovariantDerivative ℝ F Z y (X y))) x := by
    apply mdiffAt_vectorSpace_iff_differentiableAt.mpr
    apply DifferentiableAt.clm_apply
    · exact ((hZcd.contDiffAt (x := x)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp hX
  rw [curvatureOp_apply]
  rw [show (fun y ↦ LC Z y (Y y)) =
    fun y ↦ flatCovariantDerivative ℝ F Z y (Y y) from by rw [hcovZ]]
  rw [show (fun y ↦ LC Z y (X y)) =
    fun y ↦ flatCovariantDerivative ℝ F Z y (X y) from by rw [hcovZ]]
  rw [leviCivitaConnection_euclidean_eq_flat hDZY,
    leviCivitaConnection_euclidean_eq_flat hDZX, hcovZ]
  have h := flatCovariantDerivative_curvatureOp_eq_zero
    (V := X) (W := Y) (Z := Z) (x := x)
    (mdiffAt_vectorSpace_iff_differentiableAt.mp hX)
    (mdiffAt_vectorSpace_iff_differentiableAt.mp hY)
    (((hZcd.contDiffAt (x := x)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt one_ne_zero)
    ((hZcd.contDiffAt (x := x)).isSymmSndFDerivAt (by simp))
  rw [curvatureOp_apply] at h
  exact h


/--
**Euclidean space has zero sectional curvature**: the sectional numerator
of the flat connection vanishes on all planes, for any fibrewise metric.
-/
theorem flat_sectionalNumeratorAt_eq_zero (x : F)
    (g : Π y : F, TangentSpace 𝓘(ℝ, F) y →L[ℝ] TangentSpace 𝓘(ℝ, F) y
      →L[ℝ] ℝ)
    (u v : TangentSpace 𝓘(ℝ, F) x) :
    sectionalNumeratorAt (flatCovariantDerivative ℝ F) x g u v = 0 := by
  unfold sectionalNumeratorAt
  have hcurv : curvatureOp (flatCovariantDerivative ℝ F)
      (FiberBundle.extend F u) (FiberBundle.extend F v)
      (FiberBundle.extend F v) x = 0 := by
    set Z : Π y : F, TangentSpace 𝓘(ℝ, F) y := FiberBundle.extend F v
      with hZdef
    have hZcd : ContDiff ℝ 2 (Z : F → F) := by
      rw [hZdef, extend_model_space v]
      exact contDiff_const
    apply flatCovariantDerivative_curvatureOp_eq_zero
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp
        (FiberBundle.mdifferentiableAt_extend ..)
    · exact mdiffAt_vectorSpace_iff_differentiableAt.mp
        (FiberBundle.mdifferentiableAt_extend ..)
    · exact ((hZcd.contDiffAt.fderiv_right (m := 1)
        (by norm_num)).differentiableAt one_ne_zero)
    · exact (hZcd.contDiffAt).isSymmSndFDerivAt (by simp)
  rw [hcurv]
  simp

end CovariantDerivative
