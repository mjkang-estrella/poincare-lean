import Poincare.Global.DifferentialInducedSuccessor

/-!
# The zero-vector differential successor

The punctured estimates used for nontrivial re-anchoring exclude the stored
normal vector `0`.  That case is algebraic: the new anchor is the old anchor,
the reanchored chart map has the old tangent alignment as its derivative, and
the differential-induced successor is the original Cartan germ.
-/

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorZero

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

private theorem tangentAlignment_heq_of_target_eq_of_clm_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    (L₁ : CartanMap.TangentAlignment g x p₁)
    (L₂ : CartanMap.TangentAlignment g x p₂)
    (hp : p₁ = p₂)
    (hclm : (L₁.toContinuousLinearEquiv : E →L[ℝ] E) =
      (L₂.toContinuousLinearEquiv : E →L[ℝ] E)) :
    HEq L₁ L₂ := by
  subst p₂
  apply heq_of_eq
  apply DFunLike.coe_injective
  funext v
  exact DFunLike.congr_fun hclm v

private theorem chainState_eq_of_target_eq_of_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    {L₁ : CartanMap.TangentAlignment g x p₁}
    {L₂ : CartanMap.TangentAlignment g x p₂}
    (hp : p₁ = p₂) (hL : HEq L₁ L₂) :
    (CartanChain.ChainState.mk x p₁ L₁ : CartanChain.ChainState g) =
      CartanChain.ChainState.mk x p₂ L₂ := by
  subst p₂
  cases hL
  rfl

/-- Canonical differential-successor data at the predecessor anchor.  Both
exponential-chart derivatives are the identity at zero, while the Cartan
chart derivative is the stored tangent alignment. -/
def anchorData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) :
    DifferentialInducedSuccessor.Data s s.anchor where
  v := 0
  A := ContinuousLinearEquiv.refl ℝ E
  B := ContinuousLinearEquiv.refl ℝ E
  source_vector_mem :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) s.anchor
  target_vector_mem := by
    simpa using
      GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
        (g := roundSphereMetric3) s.target
  source_mem_oldChart := mem_extChartAt_source s.anchor
  target_mem_oldChart := by
    rw [CartanChain.ChainState.map,
      CartanMap.cartanMap_anchor g s.anchor s.target s.alignment]
    exact mem_extChartAt_source s.target
  source_coordinate := by
    simpa [extChartAt_coe] using
      (CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
        g s.anchor).symm
  target_coordinate := by
    rw [CartanChain.ChainState.map,
      CartanMap.cartanMap_anchor g s.anchor s.target s.alignment]
    simpa [extChartAt_coe] using
      (CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
        roundSphereMetric3 s.target).symm
  source_exp_derivative := by
    simpa [GeodesicTransport.expAtChartOpenPartialHomeomorph] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := g) (x₀ := s.anchor)
  target_exp_derivative := by
    simpa [GeodesicTransport.expAtChartOpenPartialHomeomorph] using
      GeodesicTransport.expAt_chart_hasStrictFDerivAt_zero
        (g := roundSphereMetric3) (x₀ := s.target)
  cartan_chart_derivative := by
    simpa [CartanLocalIsometry.cartanChartDifferential] using
      CartanDifferential.cartanChartMap_hasStrictFDerivAt_anchor
        g s.anchor s.target s.alignment
  metric_pullback := by
    intro u u'
    simpa [CartanLocalIsometry.cartanChartDifferential,
      CartanMap.sourceAnchorChartMetric, CartanMap.targetAnchorChartMetric,
      CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor] using
      CartanMap.TangentAlignment.map_app s.alignment u u'

@[simp]
theorem anchorData_vector
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) : (anchorData s).v = 0 :=
  rfl

/-- Differential data are therefore inhabited at the anchor without any
punctured-ball or curvature hypothesis. -/
theorem data_nonempty_at_anchor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) :
    Nonempty (DifferentialInducedSuccessor.Data s s.anchor) :=
  ⟨anchorData s⟩

/-- Inside the predecessor's strict Cartan source, zero old normal coordinate
characterizes the predecessor anchor. -/
theorem eq_anchor_of_source_normal_coordinate_eq_zero
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {x : M}
    (hx : x ∈ s.germ.source)
    (hv :
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor).symm ((chartAt E s.anchor) x) = 0) :
    x = s.anchor := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) s.target
  let v : E := eM.symm ((chartAt E s.anchor) x)
  have hsource :
      x ∈ (chartAt E s.anchor).source ∧
        (chartAt E s.anchor) x ∈ eM.target ∧
          v ∈ (CartanMap.tangentAlignmentOpenPartialHomeomorph
            s.alignment).source ∧
            s.alignment v ∈ eS.source ∧
              (chartAt E s.target)
                (GeodesicTransport.expAt roundSphereMetric3 s.target
                  (s.alignment v)) ∈ (chartAt E s.target).target := by
    simpa [CartanChain.ChainState.germ, eM, eS, v,
      CartanMap.openPartialHomeomorph] using hx
  have hxcoord : (chartAt E s.anchor) x = eM v :=
    (eM.right_inv hsource.2.1).symm
  have hv' : v = 0 := by simpa [v, eM] using hv
  rw [hv'] at hxcoord
  apply (chartAt E s.anchor).injOn hsource.1 (mem_chart_source E s.anchor)
  exact hxcoord.trans
    (CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
      g s.anchor)

/-- Constant curvature supplies differential-induced data on a whole small
normal ball, including its center.  The nonzero part is the existing
punctured-ball construction and the center is `anchorData`. -/
theorem exists_data_on_ball
    [T2Space M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ ρ > (0 : ℝ),
      ∀ x : M, x ∈ s.germ.source →
        let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor
        let v := eM.symm ((chartAt E s.anchor) x)
        ‖v‖ < ρ → Nonempty (DifferentialInducedSuccessor.Data s x) := by
  rcases DifferentialInducedSuccessor.exists_data_on_punctured_ball
      g hcurv s with
    ⟨ρ, hρ, hdata⟩
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  dsimp only
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let v : E := eM.symm ((chartAt E s.anchor) x)
  change ‖v‖ < ρ → Nonempty (DifferentialInducedSuccessor.Data s x)
  intro hv
  by_cases hvzero : v = 0
  · have hxanchor : x = s.anchor :=
      eq_anchor_of_source_normal_coordinate_eq_zero s hx (by
        simpa [v, eM] using hvzero)
    subst x
    exact data_nonempty_at_anchor s
  · exact hdata x hx
      (by simpa [v, eM] using hv)
      (by simpa [v, eM] using hvzero)

/-- Zero stored normal vector forces the re-anchor point to be the original
anchor, by injectivity of the old preferred chart. -/
theorem data_anchor_eq_of_vector_eq_zero
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) (hd : d.v = 0) :
    x₁ = s.anchor := by
  apply (extChartAt I s.anchor).injOn
    d.source_mem_oldChart (mem_extChartAt_source s.anchor)
  calc
    extChartAt I s.anchor x₁ =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor d.v := d.source_coordinate
    _ = GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor (0 : E) := by rw [hd]
    _ = extChartAt I s.anchor s.anchor := by
      simpa [extChartAt_coe] using
        CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
          g s.anchor

/-- Conversely, differential data based at the predecessor anchor necessarily
store the zero old normal coordinate. -/
theorem data_vector_eq_zero_of_anchor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁)
    (hx : x₁ = s.anchor) : d.v = 0 := by
  subst x₁
  simpa using d.vector_eq (anchorData s)

/-- The stored normal vector is zero exactly when the data point is the
predecessor anchor. -/
theorem data_vector_eq_zero_iff_anchor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) :
    d.v = 0 ↔ x₁ = s.anchor := by
  exact ⟨data_anchor_eq_of_vector_eq_zero d,
    data_vector_eq_zero_of_anchor_eq d⟩

/-- At the original anchor, the reanchored coordinate map is germ-equal to
the original Cartan chart map. -/
theorem reanchoredChartMap_anchor_eventuallyEq_cartanChartMap
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) :
    DifferentialInducedSuccessor.reanchoredChartMap s s.anchor
        =ᶠ[nhds (extChartAt I s.anchor s.anchor)]
      CartanDifferential.cartanChartMap
        g s.anchor s.target s.alignment := by
  let zS : E := extChartAt I s.anchor s.anchor
  let zT : E := extChartAt I s.target s.target
  let F : E → E := CartanDifferential.cartanChartMap
    g s.anchor s.target s.alignment
  have hp : s.map s.anchor = s.target := by
    exact CartanMap.cartanMap_anchor g s.anchor s.target s.alignment
  have hzS : zS ∈ (extChartAt I s.anchor).target :=
    (extChartAt I s.anchor).map_source (mem_extChartAt_source s.anchor)
  have hinner : ∀ᶠ z in nhds zS,
      GeodesicTransport.chartTransition s.anchor s.anchor z = z := by
    filter_upwards [(isOpen_extChartAt_target s.anchor).mem_nhds hzS] with z hz
    exact (extChartAt I s.anchor).right_inv hz
  have heMzero :
      GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) s.anchor (0 : E) = zS := by
    simpa [zS, extChartAt_coe] using
      CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
        g s.anchor
  have hFcont : ContinuousAt F zS := by
    have h :=
      (CartanDifferential.cartanChartMap_hasStrictFDerivAt_anchor
        g s.anchor s.target s.alignment).continuousAt
    rw [heMzero] at h
    simpa [F] using h
  have hFzS : F zS = zT := by
    change
      GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) s.target
          (s.alignment
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) s.anchor).symm zS)) = zT
    rw [← heMzero,
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) s.anchor).left_inv
          (GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
            (g := g) s.anchor)]
    simp only [map_zero]
    simpa [zT, extChartAt_coe] using
      CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
        roundSphereMetric3 s.target
  have hzT : zT ∈ (extChartAt I s.target).target :=
    (extChartAt I s.target).map_source (mem_extChartAt_source s.target)
  have hFtarget : ∀ᶠ z in nhds zS, F z ∈ (extChartAt I s.target).target := by
    have htargetN : (extChartAt I s.target).target ∈ nhds (F zS) := by
      rw [hFzS]
      exact (isOpen_extChartAt_target s.target).mem_nhds hzT
    exact hFcont.preimage_mem_nhds htargetN
  change
    (fun z : E =>
      GeodesicTransport.chartTransition s.target (s.map s.anchor)
        (F (GeodesicTransport.chartTransition s.anchor s.anchor z)))
      =ᶠ[nhds zS] F
  rw [hp]
  filter_upwards [hinner, hFtarget] with z hzin hzout
  rw [hzin]
  exact (extChartAt I s.target).right_inv hzout

/-- Under a zero stored vector, the differential-induced alignment is the old
alignment, after identifying their target indices. -/
theorem data_alignment_heq_of_vector_eq_zero
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) (hd : d.v = 0) :
    HEq d.alignment s.alignment := by
  have hx : x₁ = s.anchor := data_anchor_eq_of_vector_eq_zero d hd
  subst x₁
  let zS : E := extChartAt I s.anchor s.anchor
  have hmap := reanchoredChartMap_anchor_eventuallyEq_cartanChartMap s
  have hclm :
      (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
        (s.alignment.toContinuousLinearEquiv : E →L[ℝ] E) := by
    calc
      (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
          fderiv ℝ
            (DifferentialInducedSuccessor.reanchoredChartMap s s.anchor) zS :=
        d.hasFDerivAt_reanchoredChartMap.fderiv.symm
      _ = fderiv ℝ
          (CartanDifferential.cartanChartMap
            g s.anchor s.target s.alignment) zS := hmap.fderiv_eq
      _ = (s.alignment.toContinuousLinearEquiv : E →L[ℝ] E) := by
        have h :=
          (CartanDifferential.cartanChartMap_hasStrictFDerivAt_anchor
            g s.anchor s.target s.alignment).hasFDerivAt.fderiv
        have heMzero :
            GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) s.anchor (0 : E) = zS := by
          simpa [zS, extChartAt_coe] using
            CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor
              g s.anchor
        rw [heMzero] at h
        exact h
  have hp : s.map s.anchor = s.target :=
    CartanMap.cartanMap_anchor g s.anchor s.target s.alignment
  exact tangentAlignment_heq_of_target_eq_of_clm_eq
    d.alignment s.alignment hp hclm

/-- A zero-vector differential successor is the predecessor state itself, not
only an equal germ on a restricted source. -/
theorem successor_eq_of_vector_eq_zero
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) (hd : d.v = 0) :
    d.successor = s := by
  have hx : x₁ = s.anchor := data_anchor_eq_of_vector_eq_zero d hd
  have hL : HEq d.alignment s.alignment :=
    data_alignment_heq_of_vector_eq_zero d hd
  subst x₁
  have hp : s.map s.anchor = s.target :=
    CartanMap.cartanMap_anchor g s.anchor s.target s.alignment
  change
    CartanChain.ChainState.mk s.anchor (s.map s.anchor) d.alignment =
      CartanChain.ChainState.mk s.anchor s.target s.alignment
  exact chainState_eq_of_target_eq_of_alignment_heq hp hL

@[simp]
theorem anchorData_successor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) : (anchorData s).successor = s :=
  successor_eq_of_vector_eq_zero (anchorData s) rfl

/-- The zero-vector differential successor carries exactly the predecessor
Cartan germ, hence is rigid-compatible on its full strict common source. -/
theorem rigidStepCompatibleWith_of_vector_eq_zero
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) (hd : d.v = 0) :
    InducedAlignment.CompatibleStep.RigidStepCompatibleWith
      s x₁ d.alignment := by
  have hstate : d.successor = s :=
    successor_eq_of_vector_eq_zero d hd
  intro x _hxcommon
  change s.germ x = d.successor.germ x
  rw [hstate]

end DifferentialSuccessorZero
end Poincare
