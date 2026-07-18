import Poincare.Global.EndpointCurry
import Poincare.Global.ContinuityPackages

/-!
# Finite-basis endpoint derivative assembly

Pointwise full endpoint derivatives at the vectors of a finite basis can
always be interpolated by a continuous-linear family.  This removes the
apparently extra compatibility hypothesis from the endpoint-currying bridge:
the compatibility is needed only on basis values, where it is automatic by
linear interpolation.
-/

noncomputable section

open scoped Topology NNReal

namespace Poincare
namespace EndpointCurry

/-- Any values prescribed on the canonical finite basis extend to a
continuous-linear map. -/
theorem exists_clm_family_of_finBasis_values
    {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    (v : Fin (Module.finrank ℝ F) → G) :
    ∃ L : F →L[ℝ] G,
      ∀ i : Fin (Module.finrank ℝ F),
        L ((Module.finBasis ℝ F) i) = v i := by
  let b := Module.finBasis ℝ F
  let coord : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i)
  let L : F →L[ℝ] G :=
    ∑ i, ContinuousLinearMap.smulRight (coord i) (v i)
  refine ⟨L, ?_⟩
  intro j
  change
    (∑ i, ContinuousLinearMap.smulRight (coord i) (v i))
        ((Module.finBasis ℝ F) j) = v j
  rw [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [coord, b]
  · intro i _hi hij
    simp [coord, b, hij]
  · simp

/--
Basiswise derivatives of the evaluations of an operator-valued field assemble
into an operator-norm Frechet derivative.  The individual derivatives need no
compatibility hypothesis: finite-basis interpolation constructs the required
continuous-linear family automatically.
-/
theorem exists_hasFDerivAt_clm_of_apply_finBasis
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {x : E}
    (hpoint : ∀ i : Fin (Module.finrank ℝ F),
      ∃ D : E →L[ℝ] G,
        HasFDerivAt
          (fun x' => f x' ((Module.finBasis ℝ F) i)) D x) :
    ∃ D : E →L[ℝ] F →L[ℝ] G, HasFDerivAt f D x := by
  choose Di hDi using hpoint
  rcases
      exists_clm_family_of_finBasis_values
        (F := F) (G := E →L[ℝ] G) Di with
    ⟨L, hL⟩
  let D : E →L[ℝ] F →L[ℝ] G := L.flip
  refine ⟨D, hasFDerivAt_clm_of_apply_finBasis ?_⟩
  intro i
  have hder := hDi i
  convert hder using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [D, hL i]

/-- Scaled canonical-basis evaluation derivatives also assemble into an
operator-valued derivative. -/
theorem exists_hasFDerivAt_clm_of_smul_finBasis
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {x : E}
    (c : ℝ) (hc : c ≠ 0)
    (hpoint : ∀ i : Fin (Module.finrank ℝ F),
      ∃ D : E →L[ℝ] G,
        HasFDerivAt
          (fun x' => f x' (c • (Module.finBasis ℝ F) i)) D x) :
    ∃ D : E →L[ℝ] F →L[ℝ] G, HasFDerivAt f D x := by
  apply exists_hasFDerivAt_clm_of_apply_finBasis
  intro i
  rcases hpoint i with ⟨D, hD⟩
  refine ⟨c⁻¹ • D, ?_⟩
  have hscaled := hD.const_smul c⁻¹
  convert hscaled using 1
  funext x'
  simp [smul_smul, hc]

/--
Continuous basiswise derivative fields imply `C¹` regularity of a
continuous-linear-map-valued field.  Finite dimensionality is used only to
reconstruct evaluation at an arbitrary vector from the canonical basis.
-/
theorem contDiffAt_one_clm_of_finBasis_derivative_fields
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U)
    (D : Fin (Module.finrank ℝ F) → E → E →L[ℝ] G)
    (hDcont : ∀ i, ContinuousOn (D i) U)
    (hDderiv : ∀ i q, q ∈ U →
      HasFDerivAt
        (fun q' => f q' ((Module.finBasis ℝ F) i)) (D i q) q) :
    ContDiffAt ℝ 1 f x := by
  let b := Module.finBasis ℝ F
  have hbasis : ∀ i : Fin (Module.finrank ℝ F),
      ContDiffOn ℝ 1 (fun q => f q (b i)) U := by
    intro i
    rw [hU.contDiffOn_iff]
    intro q hq
    rw [contDiffAt_one_iff]
    exact ⟨D i, U, hU.mem_nhds hq, hDcont i,
      fun y hy => by simpa [b] using hDderiv i y hy⟩
  have hall : ∀ w : F, ContDiffOn ℝ 1 (fun q => f q w) U := by
    intro w
    have hsum :
        ContDiffOn ℝ 1
          (fun q => ∑ i, (b.coord i w) • f q (b i)) U := by
      exact ContDiffOn.sum fun i _hi => (hbasis i).const_smul (b.coord i w)
    have heq :
        (fun q => ∑ i, (b.coord i w) • f q (b i)) =
          (fun q => f q w) := by
      funext q
      calc
        (∑ i, (b.coord i w) • f q (b i)) =
            ∑ i, f q ((b.coord i w) • b i) := by simp
        _ = f q (∑ i, (b.coord i w) • b i) := by rw [map_sum]
        _ = f q w := by
          exact congrArg (f q) (by
            simpa only [b.coord_apply] using b.sum_repr w)
    rw [← heq]
    exact hsum
  exact (contDiffOn_clm_apply.mpr hall).contDiffAt (hU.mem_nhds hx)

/--
Scaled basis evaluations suffice for the same `C¹` assembly.  This variant is
useful for short-time flow arguments: choosing the scale equal to the endpoint
time keeps the rescaled initial variation uniformly bounded.
-/
theorem contDiffAt_one_clm_of_smul_finBasis_derivative_fields
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {U : Set E} {x : E}
    (c : ℝ) (hc : c ≠ 0)
    (hU : IsOpen U) (hx : x ∈ U)
    (D : Fin (Module.finrank ℝ F) → E → E →L[ℝ] G)
    (hDcont : ∀ i, ContinuousOn (D i) U)
    (hDderiv : ∀ i q, q ∈ U →
      HasFDerivAt
        (fun q' => f q' (c • (Module.finBasis ℝ F) i)) (D i q) q) :
    ContDiffAt ℝ 1 f x := by
  let D' : Fin (Module.finrank ℝ F) → E → E →L[ℝ] G :=
    fun i q => c⁻¹ • D i q
  apply contDiffAt_one_clm_of_finBasis_derivative_fields hU hx D'
  · intro i
    exact (hDcont i).const_smul c⁻¹
  · intro i q hq
    have hscaled := (hDderiv i q hq).const_smul c⁻¹
    convert hscaled using 1
    · funext q'
      simp [smul_smul, hc]

/--
Pairwise Gronwall bounds for derivatives of the canonical-basis evaluations
give `C¹` regularity of an operator-valued field.  Frechet-derivative
uniqueness makes the pairwise witnesses coherent, so no global choice of
endpoint derivatives is required.
-/
theorem contDiffAt_one_clm_of_finBasis_pairwise_fderiv_gronwall
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U)
    (K : Fin (Module.finrank ℝ F) → ℝ≥0)
    (hpairs : ∀ i, ∀ q ∈ U, ∀ q' ∈ U,
      ∃ D D' : E →L[ℝ] G,
        HasFDerivAt
            (fun y => f y ((Module.finBasis ℝ F) i)) D q ∧
          HasFDerivAt
            (fun y => f y ((Module.finBasis ℝ F) i)) D' q' ∧
          ‖D' - D‖ ≤ (K i : ℝ) * dist q' q) :
    ContDiffAt ℝ 1 f x := by
  let D : Fin (Module.finrank ℝ F) → E → E →L[ℝ] G :=
    fun i q => fderiv ℝ (fun y => f y ((Module.finBasis ℝ F) i)) q
  apply contDiffAt_one_clm_of_finBasis_derivative_fields hU hx D
  · intro i
    apply ContinuityPackages.normedField_continuousOn_of_norm_sub_le (K := K i)
    intro q hq q' hq'
    rcases hpairs i q hq q' hq' with ⟨Dq, Dq', hDq, hDq', hbound⟩
    change ‖D i q' - D i q‖ ≤ (K i : ℝ) * dist q' q
    rw [show D i q' = Dq' by exact hDq'.fderiv,
      show D i q = Dq by exact hDq.fderiv]
    exact hbound
  · intro i q hq
    rcases hpairs i q hq q hq with ⟨Dq, _Dq', hDq, _hDq', _hbound⟩
    change HasFDerivAt
      (fun y => f y ((Module.finBasis ℝ F) i)) (D i q) q
    rw [show D i q = Dq by exact hDq.fderiv]
    exact hDq

/--
Scaled canonical-basis version of
`contDiffAt_one_clm_of_finBasis_pairwise_fderiv_gronwall`.  This is the form
used by short-time second-variation constructions, where scaling by the common
endpoint time keeps all initial variations in one compact tube.
-/
theorem contDiffAt_one_clm_of_smul_finBasis_pairwise_fderiv_gronwall
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]
    {f : E → F →L[ℝ] G} {U : Set E} {x : E}
    (c : ℝ) (hc : c ≠ 0)
    (hU : IsOpen U) (hx : x ∈ U)
    (K : Fin (Module.finrank ℝ F) → ℝ≥0)
    (hpairs : ∀ i, ∀ q ∈ U, ∀ q' ∈ U,
      ∃ D D' : E →L[ℝ] G,
        HasFDerivAt
            (fun y => f y (c • (Module.finBasis ℝ F) i)) D q ∧
          HasFDerivAt
            (fun y => f y (c • (Module.finBasis ℝ F) i)) D' q' ∧
          ‖D' - D‖ ≤ (K i : ℝ) * dist q' q) :
    ContDiffAt ℝ 1 f x := by
  let D : Fin (Module.finrank ℝ F) → E → E →L[ℝ] G :=
    fun i q =>
      fderiv ℝ (fun y => f y (c • (Module.finBasis ℝ F) i)) q
  apply contDiffAt_one_clm_of_smul_finBasis_derivative_fields c hc hU hx D
  · intro i
    apply ContinuityPackages.normedField_continuousOn_of_norm_sub_le (K := K i)
    intro q hq q' hq'
    rcases hpairs i q hq q' hq' with ⟨Dq, Dq', hDq, hDq', hbound⟩
    change ‖D i q' - D i q‖ ≤ (K i : ℝ) * dist q' q
    rw [show D i q' = Dq' by exact hDq'.fderiv,
      show D i q = Dq by exact hDq.fderiv]
    exact hbound
  · intro i q hq
    rcases hpairs i q hq q hq with ⟨Dq, _Dq', hDq, _hDq', _hbound⟩
    change HasFDerivAt
      (fun y => f y (c • (Module.finBasis ℝ F) i)) (D i q) q
    rw [show D i q = Dq by exact hDq.fderiv]
    exact hDq

/--
Finite-basis paired endpoint derivatives directly yield an operator-valued
Frechet derivative.  No pre-existing continuous-linear family of the chosen
full derivatives is required: it is constructed by interpolation on the
basis.
-/
theorem exists_hasFDerivAt_clm_of_paired_finBasis
    {E F Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ F]
    (post : Y →L[ℝ] Z)
    {paired : E × F → Y} {f : E → F →L[ℝ] Z} {x : E}
    (hfield : ∀ x' w, f x' w = post (paired (x', w)))
    (hpaired : ∀ i : Fin (Module.finrank ℝ F),
      ∃ D : (E × F) →L[ℝ] Y,
        HasFDerivAt paired D
          (x, (Module.finBasis ℝ F) i)) :
    ∃ D : E →L[ℝ] F →L[ℝ] Z, HasFDerivAt f D x := by
  choose D hD using hpaired
  rcases
      exists_clm_family_of_finBasis_values
        (F := F) (G := (E × F) →L[ℝ] Y) D with
    ⟨D₃, hD₃⟩
  let Dcurried : E →L[ℝ] F →L[ℝ] Z :=
    curryProjectedEndpoint post (ContinuousLinearMap.inl ℝ E F) D₃
  refine ⟨Dcurried, ?_⟩
  apply hasFDerivAt_clm_of_paired_finBasis
    (post := post) (D₃ := D₃) hfield
  intro i
  rw [hD₃ i]
  exact hD i

/--
Endpoint-flow form of the finite-basis assembly.

The full endpoint derivative may naturally be stated on a larger state space
`X`.  A fixed differentiable initialization map embeds `(base,input)` into
that state space; derivatives of the full endpoint at the finitely many basis
initializations then suffice to differentiate the projected operator field.
-/
theorem exists_hasFDerivAt_clm_of_endpoint_finBasis
    {E F X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ F]
    (post : Y →L[ℝ] Z) (pre : (E × F) →L[ℝ] X)
    {endpoint : X → Y} {initMap : E × F → X}
    {f : E → F →L[ℝ] Z} {x : E}
    (hinit : ∀ z : E × F, HasFDerivAt initMap pre z)
    (hfield : ∀ x' w, f x' w = post (endpoint (initMap (x', w))))
    (hendpoint : ∀ i : Fin (Module.finrank ℝ F),
      ∃ D : X →L[ℝ] Y,
        HasFDerivAt endpoint D
          (initMap (x, (Module.finBasis ℝ F) i))) :
    ∃ D : E →L[ℝ] F →L[ℝ] Z, HasFDerivAt f D x := by
  let paired : E × F → Y := fun z => endpoint (initMap z)
  have hpaired : ∀ i : Fin (Module.finrank ℝ F),
      ∃ D : (E × F) →L[ℝ] Y,
        HasFDerivAt paired D (x, (Module.finBasis ℝ F) i) := by
    intro i
    rcases hendpoint i with ⟨D, hD⟩
    exact ⟨D.comp pre, hD.comp _ (hinit _)⟩
  apply exists_hasFDerivAt_clm_of_paired_finBasis post
    (paired := paired) hfield
  exact hpaired

end EndpointCurry
end Poincare
