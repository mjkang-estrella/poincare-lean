import Poincare.Global.TowerClosed

/-!
# Projection and currying adapters for endpoint derivatives

The doubly-augmented endpoint theorem produces derivatives with product source
and product target.  This file records the functional-analytic adapters needed
to extract a fixed-input derivative and, when the resulting derivatives depend
continuously linearly on the fixed input, curry them into an operator-valued
derivative.

The final theorem is the finite-dimensional converse to differentiation after
evaluation: pointwise derivative identities on a basis determine a derivative
with values in a space of continuous linear maps, in the operator norm.
-/

noncomputable section

open scoped Topology

namespace Poincare
namespace EndpointCurry

/-- Postcompose and precompose an operator, bundled as a continuous linear map
on the corresponding operator spaces. -/
def projectedOperatorCLM
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X) :
    (X →L[ℝ] Y) →L[ℝ] E →L[ℝ] Z :=
  ((ContinuousLinearMap.compL ℝ E X Z).flip pre).comp
    (ContinuousLinearMap.compL ℝ X Y Z post)

@[simp]
theorem projectedOperatorCLM_apply
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X)
    (D : X →L[ℝ] Y) (h : E) :
    projectedOperatorCLM post pre D h = post (D (pre h)) :=
  rfl

/-- Operator-norm control for simultaneous fixed pre- and postcomposition. -/
theorem norm_projectedOperatorCLM_le
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X) :
    ‖projectedOperatorCLM post pre‖ ≤ ‖post‖ * ‖pre‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro D
  change ‖(post.comp D).comp pre‖ ≤ (‖post‖ * ‖pre‖) * ‖D‖
  calc
    ‖(post.comp D).comp pre‖ ≤ ‖post.comp D‖ * ‖pre‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖post‖ * ‖D‖) * ‖pre‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = (‖post‖ * ‖pre‖) * ‖D‖ := by ring

/-- A continuously-linear family of full endpoint derivatives can be projected
and curried.  The outer variable is the base perturbation and the inner
variable is the fixed endpoint input. -/
def curryProjectedEndpoint
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X)
    (D₃ : F →L[ℝ] X →L[ℝ] Y) :
    E →L[ℝ] F →L[ℝ] Z :=
  ((projectedOperatorCLM post pre).comp D₃).flip

@[simp]
theorem curryProjectedEndpoint_apply
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X)
    (D₃ : F →L[ℝ] X →L[ℝ] Y) (h : E) (w : F) :
    curryProjectedEndpoint post pre D₃ h w = post (D₃ w (pre h)) :=
  rfl

/-- Currying does not lose the standard product of the precomposition,
endpoint-family, and postcomposition norm bounds. -/
theorem norm_curryProjectedEndpoint_le
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X)
    (D₃ : F →L[ℝ] X →L[ℝ] Y) :
    ‖curryProjectedEndpoint post pre D₃‖ ≤ ‖post‖ * ‖D₃‖ * ‖pre‖ := by
  rw [curryProjectedEndpoint, ContinuousLinearMap.opNorm_flip]
  calc
    ‖(projectedOperatorCLM post pre).comp D₃‖ ≤
        ‖projectedOperatorCLM post pre‖ * ‖D₃‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖post‖ * ‖pre‖) * ‖D₃‖ :=
      mul_le_mul_of_nonneg_right (norm_projectedOperatorCLM_le post pre) (norm_nonneg D₃)
    _ = ‖post‖ * ‖D₃‖ * ‖pre‖ := by ring

/-- A derivative with product source gives the derivative in the first input
after fixing the second input and applying a fixed output projection. -/
theorem HasFDerivAt.project_fixed_second
    {E F Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E × F → Y} {D : (E × F) →L[ℝ] Y}
    {x : E} {w : F} (post : Y →L[ℝ] Z)
    (hf : HasFDerivAt f D (x, w)) :
    HasFDerivAt
      (fun x' : E => post (f (x', w)))
      ((post.comp D).comp (ContinuousLinearMap.inl ℝ E F)) x := by
  have hpair : HasFDerivAt (fun x' : E => (x', w))
      (ContinuousLinearMap.inl ℝ E F) x :=
    hasFDerivAt_prodMk_left x w
  exact post.hasFDerivAt.comp x (hf.comp x hpair)

/-- A derivative with product source gives the derivative in the second input
after fixing the first input and applying a fixed output projection. -/
theorem HasFDerivAt.project_fixed_first
    {E F Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E × F → Y} {D : (E × F) →L[ℝ] Y}
    {x : E} {w : F} (post : Y →L[ℝ] Z)
    (hf : HasFDerivAt f D (x, w)) :
    HasFDerivAt
      (fun w' : F => post (f (x, w')))
      ((post.comp D).comp (ContinuousLinearMap.inr ℝ E F)) w := by
  have hpair : HasFDerivAt (fun w' : F => (x, w'))
      (ContinuousLinearMap.inr ℝ E F) w :=
    hasFDerivAt_prodMk_right x w
  exact post.hasFDerivAt.comp w (hf.comp w hpair)

/-- Differentiation of an operator-valued field implies differentiation after
evaluation at any fixed vector. -/
theorem HasFDerivAt.apply_fixed
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F →L[ℝ] G} {D : E →L[ℝ] F →L[ℝ] G}
    {x : E} (hf : HasFDerivAt f D x) (w : F) :
    HasFDerivAt (fun x' => f x' w)
      ((ContinuousLinearMap.apply ℝ G w).comp D) x :=
  (ContinuousLinearMap.apply ℝ G w).hasFDerivAt.comp x hf

/-- In finite dimension, compatible pointwise derivatives on a basis lift to
an operator-norm derivative of a continuous-linear-map-valued field.

This is the converse of `HasFDerivAt.apply_fixed` needed for endpoint
currying.  It is important that the inner domain `F` is finite-dimensional;
without that hypothesis, pointwise differentiability need not control the
operator norm. -/
theorem hasFDerivAt_clm_of_apply_finBasis
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {D : E →L[ℝ] F →L[ℝ] G} {x : E}
    (hpoint : ∀ i : Fin (Module.finrank ℝ F),
      HasFDerivAt
        (fun x' => f x' ((Module.finBasis ℝ F) i))
        ((ContinuousLinearMap.apply ℝ G ((Module.finBasis ℝ F) i)).comp D) x) :
    HasFDerivAt f D x := by
  let b := Module.finBasis ℝ F
  let coord : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hterm : ∀ i : Fin (Module.finrank ℝ F),
      HasFDerivAt
        (fun x' => ContinuousLinearMap.smulRight (coord i) (f x' (b i)))
        ((ContinuousLinearMap.smulRightL ℝ F G (coord i)).comp
          ((ContinuousLinearMap.apply ℝ G (b i)).comp D)) x := by
    intro i
    exact (ContinuousLinearMap.smulRightL ℝ F G (coord i)).hasFDerivAt.comp x
      (by simpa [b] using hpoint i)
  have hsum := HasFDerivAt.fun_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  have hfun : (fun x' => ∑ i, ContinuousLinearMap.smulRight (coord i) (f x' (b i))) = f := by
    funext x'
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply]
    calc
      (∑ i, coord i w • f x' (b i)) =
          ∑ i, f x' (b.coord i w • b i) := by
        simp [coord]
      _ = f x' (∑ i, b.coord i w • b i) := by rw [map_sum]
      _ = f x' w := by
        exact congrArg (f x') (by
          simpa only [b.coord_apply] using b.sum_repr w)
  have hD :
      (∑ i, (ContinuousLinearMap.smulRightL ℝ F G (coord i)).comp
        ((ContinuousLinearMap.apply ℝ G (b i)).comp D)) = D := by
    apply ContinuousLinearMap.ext
    intro h
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      ContinuousLinearMap.apply_apply]
    rw [ContinuousLinearMap.sum_apply]
    calc
      (∑ i, coord i w • D h (b i)) =
          ∑ i, D h (b.coord i w • b i) := by
        simp [coord]
      _ = D h (∑ i, b.coord i w • b i) := by rw [map_sum]
      _ = D h w := by
        exact congrArg (D h) (by
          simpa only [b.coord_apply] using b.sum_repr w)
  simpa only [hfun, hD] using hsum

/-- Endpoint-specialized assembly: a continuous-linear family of full
product derivatives, together with its fixed-input pointwise derivative
identities on the canonical finite basis, yields the curried projected
operator-valued derivative. -/
theorem hasFDerivAt_curryProjectedEndpoint_of_finBasis
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ F]
    (post : Y →L[ℝ] Z) (pre : E →L[ℝ] X)
    (D₃ : F →L[ℝ] X →L[ℝ] Y)
    {f : E → F →L[ℝ] Z} {x : E}
    (hpoint : ∀ i : Fin (Module.finrank ℝ F),
      HasFDerivAt
        (fun x' => f x' ((Module.finBasis ℝ F) i))
        ((projectedOperatorCLM post pre).comp D₃
          ((Module.finBasis ℝ F) i)) x) :
    HasFDerivAt f (curryProjectedEndpoint post pre D₃) x := by
  apply hasFDerivAt_clm_of_apply_finBasis
  intro i
  simpa only [curryProjectedEndpoint_apply, projectedOperatorCLM_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hpoint i

/-- Direct paired-endpoint adapter.

For each basis input `w`, a full derivative of `paired` at `(x, w)` is
projected to the first-variable derivative.  If those full derivatives are the
values of one continuous-linear family `D₃`, the finite-dimensional basis
assembly upgrades the pointwise statements to an operator-norm derivative of
the curried field. -/
theorem hasFDerivAt_clm_of_paired_finBasis
    {E F Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ F]
    (post : Y →L[ℝ] Z)
    (D₃ : F →L[ℝ] (E × F) →L[ℝ] Y)
    {paired : E × F → Y} {f : E → F →L[ℝ] Z} {x : E}
    (hfield : ∀ x' w, f x' w = post (paired (x', w)))
    (hpaired : ∀ i : Fin (Module.finrank ℝ F),
      HasFDerivAt paired (D₃ ((Module.finBasis ℝ F) i))
        (x, (Module.finBasis ℝ F) i)) :
    HasFDerivAt f
      (curryProjectedEndpoint post (ContinuousLinearMap.inl ℝ E F) D₃) x := by
  apply hasFDerivAt_curryProjectedEndpoint_of_finBasis
  intro i
  have hi := HasFDerivAt.project_fixed_second post (hpaired i)
  simpa only [hfield] using hi

end EndpointCurry
end Poincare
