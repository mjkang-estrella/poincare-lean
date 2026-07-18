import Poincare.Global.DeTurckChartOverlapCovariance

/-!
# Spatial endpoint-map germs for inverse DeTurck chart flows

The chart-overlap theorem for a single inverse-gauge trajectory gives a germ
in the time variable.  Pullback assembly instead needs a germ in the initial
point variable at a fixed time.  This file supplies that missing bridge.

The main abstract theorem works trajectory by trajectory but concludes an
identity of endpoint maps on an entire set of initial points.  No continuity
of the flow in the initial point is needed for this identity.  Joint `C¹`
regularity of the target vector field is enough for uniqueness on the whole
compact time interval: the two trajectory images lie in a common closed ball,
and `C¹` regularity gives a single Lipschitz constant on the compact convex
time--space cylinder over that ball.
-/

noncomputable section

open Filter Function Metric Set
open scoped Manifold Topology ContDiff

namespace Poincare

section AbstractEndpointMaps

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]

/--
Whole-interval covariance of parameterized endpoint maps.

For every initial point in `U`, the source trajectory is transported through
`e` to a solution of the target ODE.  Joint `C¹` regularity of the target
field gives uniqueness on the entire compact interval, hence equality of the
two endpoint maps on all of `U` at every time in the interval.

The hypotheses deliberately impose no regularity on `Phi₁` or `Phi₂` in
their initial-point argument.  Only the time trajectories are used.
-/
theorem timeDependentCoordinateEndpointMaps_eqOn_of_covariant
    {V₁ V₂ : ℝ → X → X} {e : X → X}
    {De : X → X →L[ℝ] X}
    {Phi₁ Phi₂ : ℝ → X → X} {U : Set X}
    {a b t₀ : ℝ}
    (hV₂ : ContDiff ℝ 1 (Function.uncurry V₂))
    (ht₀ : t₀ ∈ Ioo a b)
    (hPhi₁ : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₁ tau x)
        (V₁ t (Phi₁ t x)) (Icc a b) t)
    (he : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasFDerivAt e (De (Phi₁ t x)) (Phi₁ t x))
    (hcov : ∀ x ∈ U, ∀ t ∈ Icc a b,
      De (Phi₁ t x) (V₁ t (Phi₁ t x)) =
        V₂ t (e (Phi₁ t x)))
    (hPhi₂ : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₂ tau (e x))
        (V₂ t (Phi₂ t (e x))) (Icc a b) t)
    (hinit : ∀ x ∈ U,
      e (Phi₁ t₀ x) = Phi₂ t₀ (e x)) :
    ∀ t ∈ Icc a b, EqOn (Phi₂ t ∘ e) (e ∘ Phi₁ t) U := by
  intro t ht x hx
  let source : ℝ → X := fun tau ↦ e (Phi₁ tau x)
  let target : ℝ → X := fun tau ↦ Phi₂ tau (e x)
  have hsourceDer : ∀ tau ∈ Icc a b,
      HasDerivWithinAt source (V₂ tau (source tau)) (Icc a b) tau := by
    intro tau htau
    have hcomp := (he x hx tau htau).comp_hasDerivWithinAt tau
      (hPhi₁ x hx tau htau)
    simpa [source, hcov x hx tau htau] using hcomp
  have htargetDer : ∀ tau ∈ Icc a b,
      HasDerivWithinAt target (V₂ tau (target tau)) (Icc a b) tau := by
    intro tau htau
    simpa [target] using hPhi₂ x hx tau htau
  have hsourceCont : ContinuousOn source (Icc a b) :=
    HasDerivWithinAt.continuousOn hsourceDer
  have htargetCont : ContinuousOn target (Icc a b) :=
    HasDerivWithinAt.continuousOn htargetDer
  have hcompact : IsCompact
      (source '' Icc a b ∪ target '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hsourceCont).union
      (isCompact_Icc.image_of_continuousOn htargetCont)
  rcases hcompact.isBounded.subset_closedBall (0 : X) with ⟨R, hR⟩
  let cylinder : Set (ℝ × X) := Icc a b ×ˢ closedBall (0 : X) R
  have hcylinderConvex : Convex ℝ cylinder := by
    exact (convex_Icc a b).prod (convex_closedBall (0 : X) R)
  have hcylinderCompact : IsCompact cylinder := by
    exact isCompact_Icc.prod (isCompact_closedBall (0 : X) R)
  rcases hV₂.contDiffOn.exists_lipschitzOnWith one_ne_zero
      hcylinderConvex hcylinderCompact with ⟨K, hKLip⟩
  have hLip : ∀ tau ∈ Ioo a b,
      LipschitzOnWith K (V₂ tau) (closedBall (0 : X) R) := by
    intro tau htau
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    have hpairY : (tau, y) ∈ cylinder :=
      ⟨Ioo_subset_Icc_self htau, hy⟩
    have hpairZ : (tau, z) ∈ cylinder :=
      ⟨Ioo_subset_Icc_self htau, hz⟩
    have hdist := hKLip.dist_le_mul (tau, y) hpairY (tau, z) hpairZ
    simpa [Function.uncurry] using hdist
  have hsourceMem : ∀ tau ∈ Ioo a b,
      source tau ∈ closedBall (0 : X) R := by
    intro tau htau
    exact hR (Or.inl ⟨tau, Ioo_subset_Icc_self htau, rfl⟩)
  have htargetMem : ∀ tau ∈ Ioo a b,
      target tau ∈ closedBall (0 : X) R := by
    intro tau htau
    exact hR (Or.inr ⟨tau, Ioo_subset_Icc_self htau, rfl⟩)
  have heq : EqOn source target (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc
      (v := V₂) (s := fun _ : ℝ ↦ closedBall (0 : X) R)
      (K := K) hLip ht₀ hsourceCont
    · intro tau htau
      exact (hsourceDer tau (Ioo_subset_Icc_self htau)).hasDerivAt
        (Icc_mem_nhds htau.1 htau.2)
    · exact hsourceMem
    · exact htargetCont
    · intro tau htau
      exact (htargetDer tau (Ioo_subset_Icc_self htau)).hasDerivAt
        (Icc_mem_nhds htau.1 htau.2)
    · exact htargetMem
    · simpa [source, target] using hinit x hx
  exact (heq ht).symm

/--
Fixed-time spatial germ form of
`timeDependentCoordinateEndpointMaps_eqOn_of_covariant`.
-/
theorem timeDependentCoordinateEndpointMaps_eventuallyEq_of_covariant
    {V₁ V₂ : ℝ → X → X} {e : X → X}
    {De : X → X →L[ℝ] X}
    {Phi₁ Phi₂ : ℝ → X → X} {U : Set X}
    {a b t₀ : ℝ} {x₀ : X}
    (hU : U ∈ nhds x₀)
    (hV₂ : ContDiff ℝ 1 (Function.uncurry V₂))
    (ht₀ : t₀ ∈ Ioo a b)
    (hPhi₁ : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₁ tau x)
        (V₁ t (Phi₁ t x)) (Icc a b) t)
    (he : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasFDerivAt e (De (Phi₁ t x)) (Phi₁ t x))
    (hcov : ∀ x ∈ U, ∀ t ∈ Icc a b,
      De (Phi₁ t x) (V₁ t (Phi₁ t x)) =
        V₂ t (e (Phi₁ t x)))
    (hPhi₂ : ∀ x ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₂ tau (e x))
        (V₂ t (Phi₂ t (e x))) (Icc a b) t)
    (hinit : ∀ x ∈ U,
      e (Phi₁ t₀ x) = Phi₂ t₀ (e x)) :
    ∀ t ∈ Icc a b,
      (Phi₂ t ∘ e) =ᶠ[nhds x₀] (e ∘ Phi₁ t) := by
  intro t ht
  have heq := timeDependentCoordinateEndpointMaps_eqOn_of_covariant
    hV₂ ht₀ hPhi₁ he hcov hPhi₂ hinit t ht
  filter_upwards [hU] with x hx
  exact heq hx

end AbstractEndpointMaps

section InverseDeTurckEndpointMaps

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "𝑐" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

/--
Endpoint-map covariance for inverse DeTurck coordinate flows on an honest
preferred-chart overlap.

The overlap hypothesis discharges both differentiability of the total chart
transition and covariance of the inverse DeTurck coordinate vector field.
The conclusion is uniform over the whole initial-point set `U` and the whole
closed time interval.
-/
theorem inverseDeTurckChartEndpointMaps_eqOn_of_interval_overlap
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {Phi₁ Phi₂ : ℝ → E → E} {U : Set E}
    {a b t₀ : ℝ}
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (ht₀ : t₀ ∈ Ioo a b)
    (hPhi₁ : ∀ z ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₁ tau z)
        (inverseDeTurckChartCoordinateField gt bg x₀ t (Phi₁ t z))
        (Icc a b) t)
    (hoverlap : ∀ z ∈ U, ∀ t ∈ Icc a b,
      Phi₁ t z ∈
        ((extChartAt 𝑐 x₀).symm ≫ extChartAt 𝑐 y₀).source)
    (hPhi₂ : ∀ z ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt
        (fun tau : ℝ ↦ Phi₂ tau
          (GeodesicTransport.chartTransition x₀ y₀ z))
        (inverseDeTurckChartCoordinateField gt bg y₀ t
          (Phi₂ t (GeodesicTransport.chartTransition x₀ y₀ z)))
        (Icc a b) t)
    (hinit : ∀ z ∈ U,
      GeodesicTransport.chartTransition x₀ y₀ (Phi₁ t₀ z) =
        Phi₂ t₀ (GeodesicTransport.chartTransition x₀ y₀ z)) :
    ∀ t ∈ Icc a b,
      EqOn
        (Phi₂ t ∘ GeodesicTransport.chartTransition x₀ y₀)
        (GeodesicTransport.chartTransition x₀ y₀ ∘ Phi₁ t) U := by
  apply timeDependentCoordinateEndpointMaps_eqOn_of_covariant
    (V₁ := inverseDeTurckChartCoordinateField gt bg x₀)
    (V₂ := inverseDeTurckChartCoordinateField gt bg y₀)
    (e := GeodesicTransport.chartTransition x₀ y₀)
    (De := GeodesicTransport.chartTransitionDeriv x₀ y₀)
    hV₂ ht₀ hPhi₁
  · intro z hz t ht
    have hd := chartTransition_differentiableAt_of_mem_source
      x₀ y₀ (hoverlap z hz t ht)
    simpa [GeodesicTransport.chartTransitionDeriv] using hd.hasFDerivAt
  · intro z hz t ht
    exact inverseDeTurckChartCoordinateField_covariant
      gt bg t x₀ y₀ (hoverlap z hz t ht)
  · exact hPhi₂
  · exact hinit

/--
The exact fixed-time initial-point germ required by chartwise inverse-gauge
metric reconstruction.
-/
theorem inverseDeTurckChartEndpointMaps_eventuallyEq_of_interval_overlap
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {Phi₁ Phi₂ : ℝ → E → E} {U : Set E}
    {a b t₀ : ℝ} {z₀ : E}
    (hU : U ∈ nhds z₀)
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (ht₀ : t₀ ∈ Ioo a b)
    (hPhi₁ : ∀ z ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun tau : ℝ ↦ Phi₁ tau z)
        (inverseDeTurckChartCoordinateField gt bg x₀ t (Phi₁ t z))
        (Icc a b) t)
    (hoverlap : ∀ z ∈ U, ∀ t ∈ Icc a b,
      Phi₁ t z ∈
        ((extChartAt 𝑐 x₀).symm ≫ extChartAt 𝑐 y₀).source)
    (hPhi₂ : ∀ z ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt
        (fun tau : ℝ ↦ Phi₂ tau
          (GeodesicTransport.chartTransition x₀ y₀ z))
        (inverseDeTurckChartCoordinateField gt bg y₀ t
          (Phi₂ t (GeodesicTransport.chartTransition x₀ y₀ z)))
        (Icc a b) t)
    (hinit : ∀ z ∈ U,
      GeodesicTransport.chartTransition x₀ y₀ (Phi₁ t₀ z) =
        Phi₂ t₀ (GeodesicTransport.chartTransition x₀ y₀ z)) :
    ∀ t ∈ Icc a b,
      (Phi₂ t ∘ GeodesicTransport.chartTransition x₀ y₀) =ᶠ[nhds z₀]
        (GeodesicTransport.chartTransition x₀ y₀ ∘ Phi₁ t) := by
  intro t ht
  have heq := inverseDeTurckChartEndpointMaps_eqOn_of_interval_overlap
    gt bg x₀ y₀ hV₂ ht₀ hPhi₁ hoverlap hPhi₂ hinit t ht
  filter_upwards [hU] with z hz
  exact heq hz

/--
Consumer form for the local point-flow existence API.  Each flow package
starts from the identity and supplies all time derivatives on the common
closed interval; these identity clauses discharge the remaining common
initial-data premise automatically.
-/
theorem inverseDeTurckChartEndpointMaps_eventuallyEq_of_localPointFlows
    [T2Space M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {Phi₁ Phi₂ : ℝ → E → E} {U : Set E}
    {a b t₀ : ℝ} {z₀ : E}
    (hU : U ∈ nhds z₀)
    (hV₂ : ContDiff ℝ 1
      (Function.uncurry (inverseDeTurckChartCoordinateField gt bg y₀)))
    (ht₀ : t₀ ∈ Ioo a b)
    (hPhi₁ : ∀ z ∈ U,
      Phi₁ t₀ z = z ∧
        ∀ t ∈ Icc a b,
          HasDerivWithinAt (fun tau : ℝ ↦ Phi₁ tau z)
            (inverseDeTurckChartCoordinateField gt bg x₀ t (Phi₁ t z))
            (Icc a b) t)
    (hoverlap : ∀ z ∈ U, ∀ t ∈ Icc a b,
      Phi₁ t z ∈
        ((extChartAt 𝑐 x₀).symm ≫ extChartAt 𝑐 y₀).source)
    (hPhi₂ : ∀ z ∈ U,
      Phi₂ t₀ (GeodesicTransport.chartTransition x₀ y₀ z) =
          GeodesicTransport.chartTransition x₀ y₀ z ∧
        ∀ t ∈ Icc a b,
          HasDerivWithinAt
            (fun tau : ℝ ↦ Phi₂ tau
              (GeodesicTransport.chartTransition x₀ y₀ z))
            (inverseDeTurckChartCoordinateField gt bg y₀ t
              (Phi₂ t (GeodesicTransport.chartTransition x₀ y₀ z)))
            (Icc a b) t) :
    ∀ t ∈ Icc a b,
      (Phi₂ t ∘ GeodesicTransport.chartTransition x₀ y₀) =ᶠ[nhds z₀]
        (GeodesicTransport.chartTransition x₀ y₀ ∘ Phi₁ t) := by
  apply inverseDeTurckChartEndpointMaps_eventuallyEq_of_interval_overlap
    gt bg x₀ y₀ hU hV₂ ht₀
    (fun z hz ↦ (hPhi₁ z hz).2) hoverlap (fun z hz ↦ (hPhi₂ z hz).2)
  intro z hz
  rw [(hPhi₁ z hz).1, (hPhi₂ z hz).1]

end InverseDeTurckEndpointMaps

end Poincare
