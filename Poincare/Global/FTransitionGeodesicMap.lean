import Poincare.Global.UniformAnchoredFTransition
import Poincare.Global.GeodesicGerm

/-!
# Christoffel F-transition maps geodesic ODE solutions

This module is the analytic consumer missing between the Cartan-map
Christoffel transition law and exponential naturality.  A `C²` coordinate map
whose first and second derivatives satisfy the signed Christoffel transition
law sends a source chart-geodesic state to a target chart-geodesic state.
The proof is the ordinary second-order chain rule, followed by local ODE
uniqueness.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace FTransitionGeodesicMap

universe u

local notation "E" => ClosedSmoothModel 3

/-- The first-order state obtained by applying `F` to the position and its
Fréchet derivative to the velocity. -/
def mappedState (F : E → E) (gamma : ℝ → E × E) : ℝ → E × E :=
  fun t => (F (gamma t).1, (fderiv ℝ F (gamma t).1) (gamma t).2)

@[simp]
theorem mappedState_fst (F : E → E) (gamma : ℝ → E × E) (t : ℝ) :
    (mappedState F gamma t).1 = F (gamma t).1 := rfl

@[simp]
theorem mappedState_snd (F : E → E) (gamma : ℝ → E × E) (t : ℝ) :
    (mappedState F gamma t).2 =
      (fderiv ℝ F (gamma t).1) (gamma t).2 := rfl

/-- On a cutoff-one germ, the globally blended chart Christoffel field agrees
on the diagonal with the raw Christoffel corrector of the transported metric.

The raw corrector may use any bilinear-form representation of the metric at
the point.  Nondegeneracy makes the representation and proof witnesses
irrelevant.  This is the coefficient bridge needed to feed the raw
`christoffelAt` transition exported by `UniformAnchoredFTransition` into the
geodesic ODE, whose coefficient is `chartChristoffelField`. -/
theorem chartChristoffelField_self_eq_christoffelAt_of_cutoff_eventuallyEq_one
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M) {z : E}
    (hcut : ∀ᶠ q in nhds z,
      GeodesicTransport.cutoff (n := 3) x0 q = 1)
    (b : LinearMap.BilinForm ℝ E) (hb : b.Nondegenerate)
    (hbG : ∀ a w : E,
      b a w = CovariantDerivative.chartMetric g.inner x0 z a w)
    (v : E) :
    GeodesicTransport.chartChristoffelField g x0 z v v =
      CovariantDerivative.christoffelAt
        (fun q : E => CovariantDerivative.chartMetric g.inner x0 q)
        z b hb v v := by
  apply sub_eq_zero.mp
  apply hb.1
  intro w
  simp only [map_sub, LinearMap.sub_apply]
  nth_rewrite 1 [hbG]
  rw [GeodesicTransport.chartChristoffelField_pairing_eq_chartMetric_of_cutoff_eventuallyEq_one
    (g := g) (x₀ := x0) hcut]
  rw [CovariantDerivative.b_christoffelAt]
  have hG :
      (fun q : E => CovariantDerivative.chartMetric g.inner x0 q) =
        CovariantDerivative.chartMetric g.inner x0 := by
    funext q
    rfl
  rw [hG]
  ring

/-- Convert a raw diagonal `christoffelAt` F-transition into the diagonal
transition law for the globally defined chart geodesic coefficients. -/
theorem chartChristoffelField_self_F_transition_of_christoffelAt
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g : ClosedSmoothRiemannianMetric 3 M) (x0 : M)
    (p0 : RoundSphere3) (F : E → E) {z : E}
    (D : E →L[ℝ] E) (hD : D = fderiv ℝ F z)
    (hcut0 : ∀ᶠ q in nhds z,
      GeodesicTransport.cutoff (n := 3) x0 q = 1)
    (hcut1 : ∀ᶠ q in nhds (F z),
      GeodesicTransport.cutoff (n := 3) p0 q = 1)
    (b0 b1 : LinearMap.BilinForm ℝ E)
    (hb0 : b0.Nondegenerate) (hb1 : b1.Nondegenerate)
    (hb0G : ∀ a w : E,
      b0 a w = CovariantDerivative.chartMetric g.inner x0 z a w)
    (hb1G : ∀ a w : E,
      b1 a w =
        CovariantDerivative.chartMetric roundSphereMetric3.inner p0 (F z) a w)
    (v : E)
    (hraw :
      CovariantDerivative.christoffelAt
          (fun q : E =>
            CovariantDerivative.chartMetric roundSphereMetric3.inner p0 q)
          (F z) b1 hb1 (D v) (D v) =
        D (CovariantDerivative.christoffelAt
            (fun q : E => CovariantDerivative.chartMetric g.inner x0 q)
            z b0 hb0 v v) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) z) v) v) :
    GeodesicTransport.chartChristoffelField roundSphereMetric3 p0 (F z)
        ((fderiv ℝ F z) v) ((fderiv ℝ F z) v) =
      (fderiv ℝ F z)
          (GeodesicTransport.chartChristoffelField g x0 z v v) -
        ((fderiv ℝ (fun q : E => fderiv ℝ F q) z) v) v := by
  rw [chartChristoffelField_self_eq_christoffelAt_of_cutoff_eventuallyEq_one
    (g := roundSphereMetric3) (x0 := p0) hcut1 b1 hb1 hb1G]
  rw [chartChristoffelField_self_eq_christoffelAt_of_cutoff_eventuallyEq_one
    (g := g) (x0 := x0) hcut0 b0 hb0 hb0G]
  simpa [hD] using hraw

/-- Pointwise second-order chain rule for a map satisfying the signed
Christoffel transition identity. -/
theorem mappedState_hasDerivAt_of_F_transition
    (F : E → E)
    (Gamma0 Gamma1 : E → E →L[ℝ] E →L[ℝ] E)
    {gamma : ℝ → E × E} {t : ℝ}
    (hgamma : HasDerivAt gamma
      (geodesicFlowField Gamma0 (gamma t)) t)
    (hF2 : ContDiffAt ℝ 2 F (gamma t).1)
    (htransition :
      Gamma1 (F (gamma t).1)
          ((fderiv ℝ F (gamma t).1) (gamma t).2)
          ((fderiv ℝ F (gamma t).1) (gamma t).2) =
        (fderiv ℝ F (gamma t).1)
            (Gamma0 (gamma t).1 (gamma t).2 (gamma t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
            (gamma t).2) (gamma t).2) :
    HasDerivAt (mappedState F gamma)
      (geodesicFlowField Gamma1 (mappedState F gamma t)) t := by
  have hpos : HasDerivAt (fun s : ℝ => (gamma s).1) (gamma t).2 t :=
    geodesic_position_hasDerivAt hgamma
  have hvel : HasDerivAt (fun s : ℝ => (gamma s).2)
      (-(Gamma0 (gamma t).1) (gamma t).2 (gamma t).2) t :=
    geodesic_velocity_hasDerivAt hgamma
  have hF : HasFDerivAt F (fderiv ℝ F (gamma t).1) (gamma t).1 :=
    (hF2.differentiableAt (by norm_num)).hasFDerivAt
  have hmappedPos : HasDerivAt
      (fun s : ℝ => F (gamma s).1)
      ((fderiv ℝ F (gamma t).1) (gamma t).2) t := by
    simpa [Function.comp_def] using hF.comp_hasDerivAt t hpos
  have hDcont : ContDiffAt ℝ 1 (fun q : E => fderiv ℝ F q) (gamma t).1 := by
    simpa using (hF2.fderiv_right (m := 1) (by norm_num))
  have hD : HasFDerivAt (fun q : E => fderiv ℝ F q)
      (fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
      (gamma t).1 :=
    (hDcont.hasStrictFDerivAt (by norm_num)).hasFDerivAt
  have hDalong : HasDerivAt
      (fun s : ℝ => fderiv ℝ F (gamma s).1)
      ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
        (gamma t).2) t := by
    simpa [Function.comp_def] using hD.comp_hasDerivAt t hpos
  have hmappedVelRaw := hDalong.clm_apply hvel
  have hmappedVel : HasDerivAt
      (fun s : ℝ => (fderiv ℝ F (gamma s).1) (gamma s).2)
      (-(Gamma1 (F (gamma t).1)
        ((fderiv ℝ F (gamma t).1) (gamma t).2)
        ((fderiv ℝ F (gamma t).1) (gamma t).2))) t := by
    convert hmappedVelRaw using 1
    rw [htransition]
    simp only [map_neg]
    abel
  exact
    GeodesicTransport.geodesicFlowField_hasDerivAt_of_components
      hmappedPos hmappedVel

/-- Eventual form of the F-transition geodesic-map calculation. -/
theorem mappedState_eventually_solves_of_F_transition
    (F : E → E)
    (Gamma0 Gamma1 : E → E →L[ℝ] E →L[ℝ] E)
    {gamma : ℝ → E × E}
    (hgamma : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt gamma
      (geodesicFlowField Gamma0 (gamma t)) t)
    (hF2 : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 F (gamma t).1)
    (htransition : ∀ᶠ t in 𝓝 (0 : ℝ),
      Gamma1 (F (gamma t).1)
          ((fderiv ℝ F (gamma t).1) (gamma t).2)
          ((fderiv ℝ F (gamma t).1) (gamma t).2) =
        (fderiv ℝ F (gamma t).1)
            (Gamma0 (gamma t).1 (gamma t).2 (gamma t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
            (gamma t).2) (gamma t).2) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (mappedState F gamma)
      (geodesicFlowField Gamma1 (mappedState F gamma t)) t := by
  filter_upwards [hgamma, hF2, htransition] with t ht hFt htrans
  exact mappedState_hasDerivAt_of_F_transition F Gamma0 Gamma1 ht hFt htrans

/-- Local ODE uniqueness turns the F-transition calculation into equality
with any target solution having the same initial state. -/
theorem mappedState_eventuallyEq_target_of_F_transition
    (F : E → E)
    (Gamma0 Gamma1 : E → E →L[ℝ] E →L[ℝ] E)
    {gamma eta : ℝ → E × E} {p0 : E × E}
    (hGamma1 : ContDiffAt ℝ 1
      (geodesicFlowField Gamma1) p0)
    (hmap0 : mappedState F gamma 0 = p0)
    (heta0 : eta 0 = p0)
    (hgamma : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt gamma
      (geodesicFlowField Gamma0 (gamma t)) t)
    (hF2 : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 F (gamma t).1)
    (htransition : ∀ᶠ t in 𝓝 (0 : ℝ),
      Gamma1 (F (gamma t).1)
          ((fderiv ℝ F (gamma t).1) (gamma t).2)
          ((fderiv ℝ F (gamma t).1) (gamma t).2) =
        (fderiv ℝ F (gamma t).1)
            (Gamma0 (gamma t).1 (gamma t).2 (gamma t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
            (gamma t).2) (gamma t).2)
    (heta : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt eta
      (geodesicFlowField Gamma1 (eta t)) t) :
    mappedState F gamma =ᶠ[𝓝 (0 : ℝ)] eta := by
  exact geodesicFlowField_eventuallyEq_of_contDiffAt
    hGamma1 hmap0 heta0
    (mappedState_eventually_solves_of_F_transition
      F Gamma0 Gamma1 hgamma hF2 htransition)
    heta

/-- Interval form of the F-transition geodesic-map calculation.

If the mapped source state and a target geodesic remain in one set on which
the target geodesic vector field is Lipschitz, equality of their initial
states propagates across the whole closed interval.  This is the endpoint
version needed for exponential naturality at time `1`; no uniform-in-velocity
ODE choice is hidden in the statement. -/
theorem mappedState_eqOn_Icc_target_of_F_transition
    (F : E → E)
    (Gamma0 Gamma1 : E → E →L[ℝ] E →L[ℝ] E)
    {gamma eta : ℝ → E × E} {a b : ℝ}
    {K : ℝ≥0} {S : Set (E × E)}
    (hLip : LipschitzOnWith K (geodesicFlowField Gamma1) S)
    (hinitial : mappedState F gamma a = eta a)
    (hgamma : ∀ t ∈ Set.Icc a b, HasDerivAt gamma
      (geodesicFlowField Gamma0 (gamma t)) t)
    (hF2 : ∀ t ∈ Set.Icc a b, ContDiffAt ℝ 2 F (gamma t).1)
    (htransition : ∀ t ∈ Set.Icc a b,
      Gamma1 (F (gamma t).1)
          ((fderiv ℝ F (gamma t).1) (gamma t).2)
          ((fderiv ℝ F (gamma t).1) (gamma t).2) =
        (fderiv ℝ F (gamma t).1)
            (Gamma0 (gamma t).1 (gamma t).2 (gamma t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gamma t).1)
            (gamma t).2) (gamma t).2)
    (heta : ∀ t ∈ Set.Icc a b, HasDerivAt eta
      (geodesicFlowField Gamma1 (eta t)) t)
    (hmapped_mem : ∀ t ∈ Set.Ico a b, mappedState F gamma t ∈ S)
    (heta_mem : ∀ t ∈ Set.Ico a b, eta t ∈ S) :
    Set.EqOn (mappedState F gamma) eta (Set.Icc a b) := by
  have hmapped : ∀ t ∈ Set.Icc a b, HasDerivAt (mappedState F gamma)
      (geodesicFlowField Gamma1 (mappedState F gamma t)) t := by
    intro t ht
    exact mappedState_hasDerivAt_of_F_transition F Gamma0 Gamma1
      (hgamma t ht) (hF2 t ht) (htransition t ht)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ : ℝ => geodesicFlowField Gamma1)
    (s := fun _ : ℝ => S) (K := K)
    (fun _ _ => hLip)
    (HasDerivAt.continuousOn hmapped)
    (fun t ht => (hmapped t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hmapped_mem
    (HasDerivAt.continuousOn heta)
    (fun t ht => (heta t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt)
    heta_mem hinitial

end FTransitionGeodesicMap
end Poincare
