import Poincare.Global.DeTurckFlowVariationalIdentification
import Poincare.Global.GeodesicOverlap

/-!
# Chart-overlap covariance for inverse-gauge flows

The coordinate inverse-gauge construction must be independent of the chosen
chart.  This file proves the exact mechanism: a coordinate transition pushes
one ODE solution to a solution of the transitioned vector field, and local
ODE uniqueness identifies it with the solution chosen in the second chart.
It also records the corresponding conjugacy identity for endpoint Frechet
derivatives.
-/

noncomputable section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace Poincare

section AbstractCovariance

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Chain-rule transport of one ODE derivative through a coordinate map. -/
theorem hasDerivAt_coordinateChange_of_vectorField_covariant
    {V₁ V₂ : X → X} {e : X → X} {De : X →L[ℝ] X}
    {gamma : ℝ → X} {s : ℝ}
    (hgamma : HasDerivAt gamma (V₁ (gamma s)) s)
    (he : HasFDerivAt e De (gamma s))
    (hcov : De (V₁ (gamma s)) = V₂ (e (gamma s))) :
    HasDerivAt (e ∘ gamma) (V₂ ((e ∘ gamma) s)) s := by
  have h := he.comp_hasDerivAt s hgamma
  simpa [Function.comp_def, hcov] using h

/-- Eventual chain-rule transport of an autonomous ODE solution germ. -/
theorem coordinateChange_eventually_solves_of_vectorField_covariant
    {V₁ V₂ : X → X} {e : X → X} {De : X → X →L[ℝ] X}
    {gamma : ℝ → X} {s₀ : ℝ}
    (hgamma : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma (V₁ (gamma s)) s)
    (he : ∀ᶠ s in 𝓝 s₀,
      HasFDerivAt e (De (gamma s)) (gamma s))
    (hcov : ∀ᶠ s in 𝓝 s₀,
      De (gamma s) (V₁ (gamma s)) = V₂ (e (gamma s))) :
    ∀ᶠ s in 𝓝 s₀,
      HasDerivAt (e ∘ gamma) (V₂ ((e ∘ gamma) s)) s := by
  filter_upwards [hgamma, he, hcov] with s hs hse hscov
  exact hasDerivAt_coordinateChange_of_vectorField_covariant
    hs hse hscov

/--
Chart-overlap uniqueness for autonomous coordinate flows.

The target field only needs to be `C¹` at the common initial value.  This
provides a local Lipschitz neighborhood; continuity of the two solution germs
places them in that neighborhood, and Gronwall uniqueness identifies them.
-/
theorem coordinateChangedFlow_eventuallyEq_of_covariant
    {V₁ V₂ : X → X} {e : X → X} {De : X → X →L[ℝ] X}
    {gamma₁ gamma₂ : ℝ → X} {s₀ : ℝ}
    (hV₂ : ContDiffAt ℝ 1 V₂ (e (gamma₁ s₀)))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁ (V₁ (gamma₁ s)) s)
    (he : ∀ᶠ s in 𝓝 s₀,
      HasFDerivAt e (De (gamma₁ s)) (gamma₁ s))
    (hcov : ∀ᶠ s in 𝓝 s₀,
      De (gamma₁ s) (V₁ (gamma₁ s)) = V₂ (e (gamma₁ s)))
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂ (V₂ (gamma₂ s)) s)
    (hinit : e (gamma₁ s₀) = gamma₂ s₀) :
    (e ∘ gamma₁) =ᶠ[𝓝 s₀] gamma₂ := by
  have htrans := coordinateChange_eventually_solves_of_vectorField_covariant
    (s₀ := s₀) hgamma₁ he hcov
  rcases hV₂.exists_lipschitzOnWith with ⟨K, U, hU, hLip⟩
  have htransAt := htrans.self_of_nhds
  have hgamma₂At := hgamma₂.self_of_nhds
  have hmem₁ : ∀ᶠ s in 𝓝 s₀, (e ∘ gamma₁) s ∈ U :=
    htransAt.continuousAt.preimage_mem_nhds hU
  have hU₂ : U ∈ 𝓝 (gamma₂ s₀) := by
    simpa [Function.comp_def, hinit] using hU
  have hmem₂ : ∀ᶠ s in 𝓝 s₀, gamma₂ s ∈ U :=
    hgamma₂At.continuousAt.preimage_mem_nhds hU₂
  exact ODE_solution_unique_of_eventually
    (v := fun _ : ℝ => V₂) (s := fun _ : ℝ => U) (K := K)
    (.of_forall fun _ => hLip)
    (htrans.and hmem₁) (hgamma₂.and hmem₂)
    (by simpa [Function.comp_def] using hinit)

/-- Endpoint derivative conjugacy forced by a coordinate-flow germ equality.
This is the variational chart-overlap law

`D Phi₂(e x) ∘ De(x) = De(Phi₁ x) ∘ D Phi₁(x)`.
-/
theorem coordinateFlow_fderiv_conjugacy
    {e Phi₁ Phi₂ : X → X} {x : X}
    {De₀ De₁ D₁ D₂ : X →L[ℝ] X}
    (he₀ : HasFDerivAt e De₀ x)
    (hPhi₁ : HasFDerivAt Phi₁ D₁ x)
    (hPhi₂ : HasFDerivAt Phi₂ D₂ (e x))
    (he₁ : HasFDerivAt e De₁ (Phi₁ x))
    (hcompat : (Phi₂ ∘ e) =ᶠ[𝓝 x] (e ∘ Phi₁)) :
    D₂.comp De₀ = De₁.comp D₁ := by
  have hleft : HasFDerivAt (Phi₂ ∘ e) (D₂.comp De₀) x :=
    hPhi₂.comp x he₀
  have hright : HasFDerivAt (e ∘ Phi₁) (De₁.comp D₁) x :=
    he₁.comp x hPhi₁
  exact hleft.unique (hright.congr_of_eventuallyEq hcompat)

end AbstractCovariance

section TimeExtension

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lift a spatial coordinate change without changing time. -/
def timeLiftCoordinateChange (e : E → E) : ℝ × E → ℝ × E :=
  fun q => (q.1, e q.2)

/-- Differential of the time-lifted coordinate change. -/
def timeLiftCoordinateChangeDeriv (De : E →L[ℝ] E) :
    (ℝ × E) →L[ℝ] (ℝ × E) :=
  (ContinuousLinearMap.fst ℝ ℝ E).prod
    (De.comp (ContinuousLinearMap.snd ℝ ℝ E))

@[simp] theorem timeLiftCoordinateChangeDeriv_apply
    (De : E →L[ℝ] E) (q : ℝ × E) :
    timeLiftCoordinateChangeDeriv De q = (q.1, De q.2) :=
  rfl

/-- A spatial derivative lifts to the derivative of the time-preserving map. -/
theorem hasFDerivAt_timeLiftCoordinateChange
    {e : E → E} {De : E →L[ℝ] E} {q : ℝ × E}
    (he : HasFDerivAt e De q.2) :
    HasFDerivAt (timeLiftCoordinateChange e)
      (timeLiftCoordinateChangeDeriv De) q := by
  have hsnd : HasFDerivAt (fun p : ℝ × E => e p.2)
      (De.comp (ContinuousLinearMap.snd ℝ ℝ E)) q :=
    he.comp q hasFDerivAt_snd
  simpa [timeLiftCoordinateChange, timeLiftCoordinateChangeDeriv] using
    hasFDerivAt_fst.prodMk hsnd

/-- Autonomous extension of a time-dependent vector field. -/
def timeDependentExtendedField (V : ℝ → E → E) : ℝ × E → ℝ × E :=
  fun q => (1, V q.1 q.2)

/-- A jointly `C¹` time-dependent field has a `C¹` autonomous extension. -/
theorem contDiff_one_timeDependentExtendedField
    (V : ℝ → E → E) (hV : ContDiff ℝ 1 (Function.uncurry V)) :
    ContDiff ℝ 1 (timeDependentExtendedField V) := by
  have hvq : ContDiff ℝ 1 (fun q : ℝ × E => V q.1 q.2) := by
    simpa [Function.uncurry] using hV.comp (contDiff_fst.prodMk contDiff_snd)
  simpa [timeDependentExtendedField] using contDiff_const.prodMk hvq

/-- Spatial vector-field covariance is exactly covariance of the autonomous
time extensions through the time-lifted transition. -/
theorem timeLiftCoordinateChangeDeriv_extendedField
    (V₁ V₂ : ℝ → E → E) (e : E → E) (De : E →L[ℝ] E)
    (q : ℝ × E)
    (hcov : De (V₁ q.1 q.2) = V₂ q.1 (e q.2)) :
    timeLiftCoordinateChangeDeriv De (timeDependentExtendedField V₁ q) =
      timeDependentExtendedField V₂ (timeLiftCoordinateChange e q) := by
  simp [timeDependentExtendedField, timeLiftCoordinateChange, hcov]

/--
Time-dependent chart-overlap uniqueness.

This is the form used by the inverse DeTurck gauge: once the spatial fields
obey the transition differential law, the two coordinate solution germs are
forced to represent the same time-dependent curve.
-/
theorem timeDependentCoordinateChangedFlow_eventuallyEq_of_covariant
    {V₁ V₂ : ℝ → E → E} {e : E → E} {De : E → E →L[ℝ] E}
    {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1 (Function.uncurry V₂))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁ (timeDependentExtendedField V₁ (gamma₁ s)) s)
    (he : ∀ᶠ s in 𝓝 s₀,
      HasFDerivAt e (De (gamma₁ s).2) (gamma₁ s).2)
    (hcov : ∀ᶠ s in 𝓝 s₀,
      De (gamma₁ s).2 (V₁ (gamma₁ s).1 (gamma₁ s).2) =
        V₂ (gamma₁ s).1 (e (gamma₁ s).2))
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂ (timeDependentExtendedField V₂ (gamma₂ s)) s)
    (hinit : timeLiftCoordinateChange e (gamma₁ s₀) = gamma₂ s₀) :
    (timeLiftCoordinateChange e ∘ gamma₁) =ᶠ[𝓝 s₀] gamma₂ := by
  let eT := timeLiftCoordinateChange e
  let DeT : (ℝ × E) → (ℝ × E) →L[ℝ] (ℝ × E) := fun q =>
    timeLiftCoordinateChangeDeriv (De q.2)
  have heT : ∀ᶠ s in 𝓝 s₀,
      HasFDerivAt eT (DeT (gamma₁ s)) (gamma₁ s) := by
    filter_upwards [he] with s hs
    exact hasFDerivAt_timeLiftCoordinateChange hs
  have hcovT : ∀ᶠ s in 𝓝 s₀,
      DeT (gamma₁ s) (timeDependentExtendedField V₁ (gamma₁ s)) =
        timeDependentExtendedField V₂ (eT (gamma₁ s)) := by
    filter_upwards [hcov] with s hs
    exact timeLiftCoordinateChangeDeriv_extendedField V₁ V₂ e
      (De (gamma₁ s).2) (gamma₁ s) hs
  apply coordinateChangedFlow_eventuallyEq_of_covariant
    (V₁ := timeDependentExtendedField V₁)
    (V₂ := timeDependentExtendedField V₂)
    (e := eT) (De := DeT) (s₀ := s₀)
    ((contDiff_one_timeDependentExtendedField V₂ hV₂).contDiffAt)
    hgamma₁ heT hcovT hgamma₂
  exact hinit

end TimeExtension

section ManifoldChartTransition

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "𝓘" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/-- On the genuine overlap source, the total preferred-chart transition is
differentiable.  Outside this open source the extended charts are deliberately
arbitrary, so the membership hypothesis is essential. -/
theorem chartTransition_differentiableAt_of_mem_source
    (x₀ y₀ : M) {z : E}
    (hz : z ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    DifferentiableAt ℝ (GeodesicTransport.chartTransition x₀ y₀) z := by
  have hcd := contDiffWithinAt_ext_coord_change
    (I := 𝓘) (n := 1) y₀ x₀ hz
  have hcdAt : ContDiffAt ℝ 1
      ((extChartAt 𝓘 y₀) ∘ (extChartAt 𝓘 x₀).symm) z := by
    simpa [ModelWithCorners.range_eq_univ] using hcd
  simpa [GeodesicTransport.chartTransition] using
    (hcdAt.differentiableAt one_ne_zero)

/-- Coordinate representative, in the preferred chart anchored at `x₀`, of
an intrinsic tangent field.  The input point is a model-space coordinate; the
field value is transported from the preferred chart at the represented point
to the chart at `x₀`. -/
noncomputable def chartCoordinateTangentField
    (x₀ : M) (W : ∀ x : M, TangentSpace 𝓘 x) : E → E :=
  fun z =>
    let x := (extChartAt 𝓘 x₀).symm z
    tangentCoordChange 𝓘 x x₀ x (W x)

/-- Coordinate representatives of an intrinsic tangent field obey the exact
preferred-chart transition law on every genuine chart overlap. -/
theorem chartCoordinateTangentField_covariant
    (x₀ y₀ : M) (W : ∀ x : M, TangentSpace 𝓘 x) {z : E}
    (hz : z ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    GeodesicTransport.chartTransitionDeriv x₀ y₀ z
        (chartCoordinateTangentField x₀ W z) =
      chartCoordinateTangentField y₀ W
        (GeodesicTransport.chartTransition x₀ y₀ z) := by
  let x := (extChartAt 𝓘 x₀).symm z
  have hz' :
      z ∈ (extChartAt 𝓘 x₀).target ∧ x ∈ (extChartAt 𝓘 y₀).source := by
    simpa [x, PartialEquiv.trans_source'', PartialEquiv.symm_target] using hz
  have hx₀ : x ∈ (extChartAt 𝓘 x₀).source :=
    (extChartAt 𝓘 x₀).symm.map_source hz'.1
  have hzx : extChartAt 𝓘 x₀ x = z :=
    (extChartAt 𝓘 x₀).right_inv hz'.1
  have hderWithin := hasFDerivWithinAt_tangentCoordChange
    (I := 𝓘) (x := x₀) (y := y₀) (z := x) ⟨hx₀, hz'.2⟩
  have hderAt : HasFDerivAt
      ((extChartAt 𝓘 y₀) ∘ (extChartAt 𝓘 x₀).symm)
      (tangentCoordChange 𝓘 x₀ y₀ x) z := by
    rw [hzx] at hderWithin
    simpa [ModelWithCorners.range_eq_univ] using hderWithin
  have htransitionDeriv :
      GeodesicTransport.chartTransitionDeriv x₀ y₀ z =
        tangentCoordChange 𝓘 x₀ y₀ x := by
    simpa [GeodesicTransport.chartTransition,
      GeodesicTransport.chartTransitionDeriv] using hderAt.fderiv
  rw [htransitionDeriv]
  have hcomp := tangentCoordChange_comp (I := 𝓘)
    (w := x) (x := x₀) (y := y₀) (z := x) (v := W x)
    ⟨⟨mem_extChartAt_source x, hx₀⟩, hz'.2⟩
  have hcoord₀ : chartCoordinateTangentField x₀ W z =
      tangentCoordChange 𝓘 x x₀ x (W x) := by
    rfl
  have htransition : GeodesicTransport.chartTransition x₀ y₀ z =
      extChartAt 𝓘 y₀ x := by
    rfl
  have hcoord₁ :
      chartCoordinateTangentField y₀ W (extChartAt 𝓘 y₀ x) =
        tangentCoordChange 𝓘 x y₀ x (W x) := by
    simp only [chartCoordinateTangentField]
    rw [(extChartAt 𝓘 y₀).left_inv hz'.2]
  rw [hcoord₀, htransition, hcoord₁]
  exact hcomp

/-- The concrete intrinsic DeTurck vector field therefore has compatible
preferred-chart coordinate representatives.  No Christoffel-symbol
transformation calculation is needed: tensoriality is already encoded by the
intrinsic tangent field and `tangentCoordChange`'s cocycle law. -/
theorem deTurckChartCoordinateField_covariant
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (x₀ y₀ : M) {z : E}
    (hz : z ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    GeodesicTransport.chartTransitionDeriv x₀ y₀ z
        (chartCoordinateTangentField x₀ (deTurckVectorField gt bg t) z) =
      chartCoordinateTangentField y₀ (deTurckVectorField gt bg t)
        (GeodesicTransport.chartTransition x₀ y₀ z) :=
  chartCoordinateTangentField_covariant x₀ y₀
    (deTurckVectorField gt bg t) hz

/-- Coordinate velocity field for the inverse DeTurck gauge equation
`phi' = -W(t, phi)`. -/
noncomputable def inverseDeTurckChartCoordinateField
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ : M) : ℝ → E → E :=
  fun t z ↦ -chartCoordinateTangentField x₀ (deTurckVectorField gt bg t) z

/-- The inverse-gauge sign preserves preferred-chart covariance. -/
theorem inverseDeTurckChartCoordinateField_covariant
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (t : ℝ)
    (x₀ y₀ : M) {z : E}
    (hz : z ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    GeodesicTransport.chartTransitionDeriv x₀ y₀ z
        (inverseDeTurckChartCoordinateField gt bg x₀ t z) =
      inverseDeTurckChartCoordinateField gt bg y₀ t
        (GeodesicTransport.chartTransition x₀ y₀ z) := by
  simp only [inverseDeTurckChartCoordinateField, map_neg]
  rw [deTurckChartCoordinateField_covariant gt bg t x₀ y₀ hz]

/-- Read a time-parameterized coordinate curve as a manifold-valued curve
through the inverse of the preferred chart at `x₀`. -/
noncomputable def manifoldCurveOfChart
    (x₀ : M) (gamma : ℝ → ℝ × E) : ℝ → M :=
  fun s ↦ (extChartAt 𝓘 x₀).symm (gamma s).2

omit [IsManifold 𝓘 ∞ M] in
/-- Coordinate map germs related by an honest chart transition decode to the
same manifold-valued map germ.  This is the spatial analogue of
`manifoldCurveOfChart_eventuallyEq_of_transition`. -/
theorem manifoldMapGerm_eventuallyEq_of_chartTransition
    (x₀ y₀ : M) {Phi₁ Phi₂ : E → E} {z : E}
    (hcompat :
      (Phi₂ ∘ GeodesicTransport.chartTransition x₀ y₀) =ᶠ[𝓝 z]
        (GeodesicTransport.chartTransition x₀ y₀ ∘ Phi₁))
    (hoverlap : ∀ᶠ a in 𝓝 z,
      Phi₁ a ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    (fun a ↦ (extChartAt 𝓘 x₀).symm (Phi₁ a)) =ᶠ[𝓝 z]
      (fun a ↦ (extChartAt 𝓘 y₀).symm
        (Phi₂ (GeodesicTransport.chartTransition x₀ y₀ a))) := by
  filter_upwards [hcompat, hoverlap] with a ha hsource
  have hsource' :
      Phi₁ a ∈ (extChartAt 𝓘 x₀).target ∧
        (extChartAt 𝓘 x₀).symm (Phi₁ a) ∈
          (extChartAt 𝓘 y₀).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using hsource
  change (extChartAt 𝓘 x₀).symm (Phi₁ a) =
    (extChartAt 𝓘 y₀).symm
      (Phi₂ (GeodesicTransport.chartTransition x₀ y₀ a))
  change Phi₂ (GeodesicTransport.chartTransition x₀ y₀ a) =
    GeodesicTransport.chartTransition x₀ y₀ (Phi₁ a) at ha
  rw [ha]
  exact ((extChartAt 𝓘 y₀).left_inv hsource'.2).symm

omit [IsManifold 𝓘 ∞ M] in
/-- Compatible coordinate curves determine the same manifold curve germ.
The overlap hypothesis ensures that both total extended-chart inverses are
being used on their genuine targets. -/
theorem manifoldCurveOfChart_eventuallyEq_of_transition
    (x₀ y₀ : M) {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hcompat :
      (timeLiftCoordinateChange (GeodesicTransport.chartTransition x₀ y₀) ∘
        gamma₁) =ᶠ[𝓝 s₀] gamma₂)
    (hoverlap : ∀ᶠ s in 𝓝 s₀,
      (gamma₁ s).2 ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source) :
    manifoldCurveOfChart x₀ gamma₁ =ᶠ[𝓝 s₀]
      manifoldCurveOfChart y₀ gamma₂ := by
  filter_upwards [hcompat, hoverlap] with s hs hsource
  have hsource' :
      (gamma₁ s).2 ∈ (extChartAt 𝓘 x₀).target ∧
        (extChartAt 𝓘 x₀).symm (gamma₁ s).2 ∈
          (extChartAt 𝓘 y₀).source := by
    simpa [PartialEquiv.trans_source'', PartialEquiv.symm_target] using hsource
  have hsnd := congrArg Prod.snd hs
  change GeodesicTransport.chartTransition x₀ y₀ (gamma₁ s).2 =
    (gamma₂ s).2 at hsnd
  change (extChartAt 𝓘 x₀).symm (gamma₁ s).2 =
    (extChartAt 𝓘 y₀).symm (gamma₂ s).2
  rw [← hsnd]
  exact ((extChartAt 𝓘 y₀).left_inv hsource'.2).symm

omit [IsManifold 𝓘 ∞ M] in
/--
Actual preferred-chart overlap theorem for time-dependent coordinate flows.

The former chart-compatibility obligation is replaced by the geometric input
that the two coordinate vector fields transform through
`chartTransitionDeriv`.  ODE uniqueness then proves compatibility.
-/
theorem chartTransition_timeDependentFlow_eventuallyEq_of_covariant
    (x₀ y₀ : M)
    {V₁ V₂ : ℝ → E → E}
    {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1 (Function.uncurry V₂))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁ (timeDependentExtendedField V₁ (gamma₁ s)) s)
    (htransition : ∀ᶠ s in 𝓝 s₀,
      DifferentiableAt ℝ (GeodesicTransport.chartTransition x₀ y₀)
        (gamma₁ s).2)
    (hcov : ∀ᶠ s in 𝓝 s₀,
      GeodesicTransport.chartTransitionDeriv x₀ y₀ (gamma₁ s).2
          (V₁ (gamma₁ s).1 (gamma₁ s).2) =
        V₂ (gamma₁ s).1
          (GeodesicTransport.chartTransition x₀ y₀ (gamma₁ s).2))
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂ (timeDependentExtendedField V₂ (gamma₂ s)) s)
    (hinit :
      timeLiftCoordinateChange
          (GeodesicTransport.chartTransition x₀ y₀) (gamma₁ s₀) =
        gamma₂ s₀) :
    (timeLiftCoordinateChange (GeodesicTransport.chartTransition x₀ y₀) ∘
        gamma₁) =ᶠ[𝓝 s₀] gamma₂ := by
  have he : ∀ᶠ s in 𝓝 s₀,
      HasFDerivAt (GeodesicTransport.chartTransition x₀ y₀)
        (GeodesicTransport.chartTransitionDeriv x₀ y₀ (gamma₁ s).2)
        (gamma₁ s).2 := by
    filter_upwards [htransition] with s hs
    simpa [GeodesicTransport.chartTransitionDeriv] using hs.hasFDerivAt
  exact timeDependentCoordinateChangedFlow_eventuallyEq_of_covariant
    (V₁ := V₁) (V₂ := V₂)
    (e := GeodesicTransport.chartTransition x₀ y₀)
    (De := GeodesicTransport.chartTransitionDeriv x₀ y₀)
    (gamma₁ := gamma₁) (gamma₂ := gamma₂) (s₀ := s₀)
    hV₂ hgamma₁ he hcov hgamma₂ hinit

/-- Preferred-chart overlap compatibility with transition differentiability
discharged from eventual membership in the actual open overlap source. -/
theorem chartTransition_timeDependentFlow_eventuallyEq_of_overlap_covariant
    (x₀ y₀ : M)
    {V₁ V₂ : ℝ → E → E}
    {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1 (Function.uncurry V₂))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁ (timeDependentExtendedField V₁ (gamma₁ s)) s)
    (hoverlap : ∀ᶠ s in 𝓝 s₀,
      (gamma₁ s).2 ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source)
    (hcov : ∀ᶠ s in 𝓝 s₀,
      GeodesicTransport.chartTransitionDeriv x₀ y₀ (gamma₁ s).2
          (V₁ (gamma₁ s).1 (gamma₁ s).2) =
        V₂ (gamma₁ s).1
          (GeodesicTransport.chartTransition x₀ y₀ (gamma₁ s).2))
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂ (timeDependentExtendedField V₂ (gamma₂ s)) s)
    (hinit :
      timeLiftCoordinateChange
          (GeodesicTransport.chartTransition x₀ y₀) (gamma₁ s₀) =
        gamma₂ s₀) :
    (timeLiftCoordinateChange (GeodesicTransport.chartTransition x₀ y₀) ∘
        gamma₁) =ᶠ[𝓝 s₀] gamma₂ := by
  have htransition : ∀ᶠ s in 𝓝 s₀,
      DifferentiableAt ℝ (GeodesicTransport.chartTransition x₀ y₀)
        (gamma₁ s).2 := by
    filter_upwards [hoverlap] with s hs
    exact chartTransition_differentiableAt_of_mem_source x₀ y₀ hs
  exact chartTransition_timeDependentFlow_eventuallyEq_of_covariant
    (x₀ := x₀) (y₀ := y₀) hV₂ hgamma₁ htransition hcov
    hgamma₂ hinit

/-- Coordinate inverse-gauge solutions built in two preferred charts agree on
their genuine overlap.  The DeTurck covariance premise is fully discharged by
the intrinsic tangent-field construction; only coordinate regularity, the ODE
equations, overlap membership, and common initial data remain. -/
theorem inverseDeTurckChartFlow_eventuallyEq_of_overlap
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg x₀) (gamma₁ s)) s)
    (hoverlap : ∀ᶠ s in 𝓝 s₀,
      (gamma₁ s).2 ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source)
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg y₀) (gamma₂ s)) s)
    (hinit :
      timeLiftCoordinateChange
          (GeodesicTransport.chartTransition x₀ y₀) (gamma₁ s₀) =
        gamma₂ s₀) :
    (timeLiftCoordinateChange (GeodesicTransport.chartTransition x₀ y₀) ∘
        gamma₁) =ᶠ[𝓝 s₀] gamma₂ := by
  have hcov : ∀ᶠ s in 𝓝 s₀,
      GeodesicTransport.chartTransitionDeriv x₀ y₀ (gamma₁ s).2
          (inverseDeTurckChartCoordinateField gt bg x₀
            (gamma₁ s).1 (gamma₁ s).2) =
        inverseDeTurckChartCoordinateField gt bg y₀ (gamma₁ s).1
          (GeodesicTransport.chartTransition x₀ y₀ (gamma₁ s).2) := by
    filter_upwards [hoverlap] with s hs
    exact inverseDeTurckChartCoordinateField_covariant
      gt bg (gamma₁ s).1 x₀ y₀ hs
  exact chartTransition_timeDependentFlow_eventuallyEq_of_overlap_covariant
    (x₀ := x₀) (y₀ := y₀)
    (V₁ := inverseDeTurckChartCoordinateField gt bg x₀)
    (V₂ := inverseDeTurckChartCoordinateField gt bg y₀)
    hV₂ hgamma₁ hoverlap hcov hgamma₂ hinit

/-- Chart-independent manifold trajectory germ for the concrete inverse
DeTurck gauge.  Any two preferred-chart ODE constructions satisfying the
honest overlap conditions decode to the same manifold-valued curve germ. -/
theorem inverseDeTurckManifoldCurve_eventuallyEq_of_overlap
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {gamma₁ gamma₂ : ℝ → ℝ × E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg x₀) (gamma₁ s)) s)
    (hoverlap : ∀ᶠ s in 𝓝 s₀,
      (gamma₁ s).2 ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source)
    (hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg y₀) (gamma₂ s)) s)
    (hinit :
      timeLiftCoordinateChange
          (GeodesicTransport.chartTransition x₀ y₀) (gamma₁ s₀) =
        gamma₂ s₀) :
    manifoldCurveOfChart x₀ gamma₁ =ᶠ[𝓝 s₀]
      manifoldCurveOfChart y₀ gamma₂ := by
  apply manifoldCurveOfChart_eventuallyEq_of_transition x₀ y₀
    (hoverlap := hoverlap)
  exact inverseDeTurckChartFlow_eventuallyEq_of_overlap
    gt bg x₀ y₀ hV₂ hgamma₁ hoverlap hgamma₂ hinit

/-- Spatial-path form of chart-independent inverse DeTurck trajectories.
This is the direct consumer shape for coordinate Picard--Lindelof output:
each chart path solves `phi' = -W`, begins at transitioned initial data, and
stays in the genuine overlap; their manifold decodings agree as germs. -/
theorem inverseDeTurckCoordinateTrajectories_eventuallyEq_on_manifold
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {phi₁ phi₂ : ℝ → E} {s₀ : ℝ}
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (hphi₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt phi₁
        (inverseDeTurckChartCoordinateField gt bg x₀ s (phi₁ s)) s)
    (hoverlap : ∀ᶠ s in 𝓝 s₀,
      phi₁ s ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source)
    (hphi₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt phi₂
        (inverseDeTurckChartCoordinateField gt bg y₀ s (phi₂ s)) s)
    (hinit : GeodesicTransport.chartTransition x₀ y₀ (phi₁ s₀) =
      phi₂ s₀) :
    (fun s ↦ (extChartAt 𝓘 x₀).symm (phi₁ s)) =ᶠ[𝓝 s₀]
      (fun s ↦ (extChartAt 𝓘 y₀).symm (phi₂ s)) := by
  let gamma₁ : ℝ → ℝ × E := fun s ↦ (s, phi₁ s)
  let gamma₂ : ℝ → ℝ × E := fun s ↦ (s, phi₂ s)
  have hgamma₁ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₁
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg x₀) (gamma₁ s)) s := by
    filter_upwards [hphi₁] with s hs
    simpa [gamma₁, timeDependentExtendedField] using
      (hasDerivAt_id s).prodMk hs
  have hgamma₂ : ∀ᶠ s in 𝓝 s₀,
      HasDerivAt gamma₂
        (timeDependentExtendedField
          (inverseDeTurckChartCoordinateField gt bg y₀) (gamma₂ s)) s := by
    filter_upwards [hphi₂] with s hs
    simpa [gamma₂, timeDependentExtendedField] using
      (hasDerivAt_id s).prodMk hs
  have hoverlap' : ∀ᶠ s in 𝓝 s₀,
      (gamma₁ s).2 ∈ ((extChartAt 𝓘 x₀).symm ≫ extChartAt 𝓘 y₀).source := by
    simpa [gamma₁] using hoverlap
  have hinit' :
      timeLiftCoordinateChange
          (GeodesicTransport.chartTransition x₀ y₀) (gamma₁ s₀) =
        gamma₂ s₀ := by
    apply Prod.ext
    · rfl
    · exact hinit
  have hcurves := inverseDeTurckManifoldCurve_eventuallyEq_of_overlap
    gt bg x₀ y₀ hV₂ hgamma₁ hoverlap' hgamma₂ hinit'
  simpa [manifoldCurveOfChart, gamma₁, gamma₂] using hcurves

omit [IsManifold 𝓘 ∞ M] in
/-- Variational conjugacy for actual preferred-chart transitions. -/
theorem chartTransition_flow_fderiv_conjugacy
    (x₀ y₀ : M) {Phi₁ Phi₂ : E → E} {z : E}
    {D₁ D₂ : E →L[ℝ] E}
    (htransition₀ :
      DifferentiableAt ℝ (GeodesicTransport.chartTransition x₀ y₀) z)
    (hPhi₁ : HasFDerivAt Phi₁ D₁ z)
    (hPhi₂ : HasFDerivAt Phi₂ D₂
      (GeodesicTransport.chartTransition x₀ y₀ z))
    (htransition₁ :
      DifferentiableAt ℝ (GeodesicTransport.chartTransition x₀ y₀) (Phi₁ z))
    (hcompat :
      (Phi₂ ∘ GeodesicTransport.chartTransition x₀ y₀) =ᶠ[𝓝 z]
        (GeodesicTransport.chartTransition x₀ y₀ ∘ Phi₁)) :
    D₂.comp (GeodesicTransport.chartTransitionDeriv x₀ y₀ z) =
      (GeodesicTransport.chartTransitionDeriv x₀ y₀ (Phi₁ z)).comp D₁ := by
  exact coordinateFlow_fderiv_conjugacy
    (he₀ := by
      simpa [GeodesicTransport.chartTransitionDeriv] using
        htransition₀.hasFDerivAt)
    hPhi₁ hPhi₂
    (he₁ := by
      simpa [GeodesicTransport.chartTransitionDeriv] using
        htransition₁.hasFDerivAt)
    hcompat

end ManifoldChartTransition

end Poincare
