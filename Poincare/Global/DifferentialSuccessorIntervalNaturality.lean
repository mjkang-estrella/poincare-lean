import Poincare.Global.DifferentialSuccessorNaturality
import Poincare.Global.DifferentialSuccessorZero
import Poincare.Global.GeodesicLengthFinal
import Poincare.Global.RayCoverInputs
import Poincare.Global.UniformTangentAlignmentGeodesicTransition

/-!
# Closed-interval naturality for differential-induced successors

The germ theorem in `DifferentialSuccessorNaturality` is upgraded here using
the uniform Picard--Lindelof chart flows.  A common short time keeps the whole
source family inside the open chart/F-transition side-condition locus.  The
transported source flow and the target flow then agree on the full closed
interval by Gronwall uniqueness, giving a uniform normal-ball identity rather
than one velocity-dependent time germ.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace DifferentialSuccessorIntervalNaturality

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

omit [T2Space M] in
/-- Re-expressing the carried total Cartan map in the charts centered at `x₁`
and `s.map x₁` is the concrete `reanchoredChartMap`. -/
theorem reanchoredChartMap_chart_eq_target_chart_map_of_mem
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (x₁ : M) {x : M}
    (hxNew : x ∈ (extChartAt I x₁).source) :
    DifferentialInducedSuccessor.reanchoredChartMap s x₁
        (extChartAt I x₁ x) =
      extChartAt I (s.map x₁) (s.map x) := by
  change
    extChartAt I (s.map x₁)
        ((extChartAt I s.target).symm
          (CartanDifferential.cartanChartMap
            g s.anchor s.target s.alignment
            (extChartAt I s.anchor
              ((extChartAt I x₁).symm (extChartAt I x₁ x))))) =
      extChartAt I (s.map x₁) (s.map x)
  rw [(extChartAt I x₁).left_inv hxNew]
  change extChartAt I (s.map x₁) (s.map x) =
    extChartAt I (s.map x₁) (s.map x)
  rfl

omit [T2Space M] in
/-- A normal-ball identity for the reanchored coordinate map gives equality
of the predecessor and differential successor at every strict common-source
point whose new normal coordinate lies in that ball and whose predecessor
value remains in the new target chart. -/
theorem predecessor_germ_eq_successor_germ_of_expAtChart_norm_lt
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁)
    {r : ℝ}
    (hball : ∀ v : E, ‖v‖ < r →
      DifferentialInducedSuccessor.reanchoredChartMap s x₁
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₁ v) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map x₁) (d.alignment v))
    {x : M}
    (hx : x ∈ s.germ.source ∩ d.successor.germ.source)
    (hmapNew : s.map x ∈ (extChartAt I (s.map x₁)).source)
    (hnorm :
      ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) x₁).symm ((chartAt E x₁) x)‖ < r) :
    s.germ x = d.successor.germ x := by
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) (s.map x₁)
  let v : E := eM.symm ((chartAt E x₁) x)
  have hxCompat :
      x ∈ s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment
          s x₁ d.alignment).germ.source := by
    simpa [DifferentialInducedSuccessor.Data.successor] using hx
  have hxNext :
      x ∈ (CartanMap.openPartialHomeomorph
        g x₁ (s.map x₁) d.alignment).source := by
    simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ] using hxCompat.2
  have hsource :
      x ∈ (chartAt E x₁).source ∧
        (chartAt E x₁) x ∈ eM.target ∧
          eM.symm ((chartAt E x₁) x) ∈
              (CartanMap.tangentAlignmentOpenPartialHomeomorph
                d.alignment).source ∧
            d.alignment (eM.symm ((chartAt E x₁) x)) ∈ eS.source ∧
              (chartAt E (s.map x₁))
                  (GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
                    (d.alignment (eM.symm ((chartAt E x₁) x)))) ∈
                (chartAt E (s.map x₁)).target := by
    simpa [eM, eS, CartanMap.openPartialHomeomorph] using hxNext
  have hxNew : x ∈ (extChartAt I x₁).source := by
    simpa [extChartAt_source] using hsource.1
  have hcoords :=
    RayCoverInputs.common_source_expAt_inverse_and_reanchored_target_chart_coordinates
      (s := s) (x₁ := x₁) (L₁ := d.alignment) x hxCompat
  have hball' := hball v (by simpa [v, eM] using hnorm)
  rw [show eM v = (chartAt E x₁) x by simpa [eM, v] using hcoords.1]
      at hball'
  have hreanchored :
      DifferentialInducedSuccessor.reanchoredChartMap s x₁
          ((chartAt E x₁) x) =
        (chartAt E (s.map x₁)) (s.map x) := by
    simpa [extChartAt_coe] using
      reanchoredChartMap_chart_eq_target_chart_map_of_mem s x₁ hxNew
  have hchartEq :
      (chartAt E (s.map x₁)) (s.map x) =
        (chartAt E (s.map x₁)) (d.successor.map x) := by
    calc
      (chartAt E (s.map x₁)) (s.map x) =
          DifferentialInducedSuccessor.reanchoredChartMap s x₁
            ((chartAt E x₁) x) := hreanchored.symm
      _ = eS (d.alignment v) := by simpa [eS] using hball'
      _ = (chartAt E (s.map x₁)) (d.successor.map x) := by
        simpa [v, eM, eS, DifferentialInducedSuccessor.Data.successor,
          InducedAlignment.CompatibleStep.nextWithAlignment,
          CartanChain.ChainState.map] using hcoords.2
  have hnewMapSource :
      d.successor.map x ∈ (chartAt E (s.map x₁)).source := by
    change
      (chartAt E (s.map x₁)).symm
          (eS (d.alignment (eM.symm ((chartAt E x₁) x)))) ∈
        (chartAt E (s.map x₁)).source
    exact (chartAt E (s.map x₁)).symm.map_source (by
      simpa [eS, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
        hsource.2.2.2.2)
  change s.map x = d.successor.map x
  exact (chartAt E (s.map x₁)).injOn
    (by simpa [extChartAt_source] using hmapNew) hnewMapSource hchartEq

omit [T2Space M] in
/-- If the strict common source is covered by one of the normal balls supplied
by interval naturality, the local coordinate identity is exactly the staged
`RigidStepCompatibleWith` conclusion.  The two cover hypotheses expose the
only global step not implied by the local ODE argument. -/
theorem rigidStepCompatibleWith_of_expAtChart_ball_cover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁)
    {r : ℝ}
    (hball : ∀ v : E, ‖v‖ < r →
      DifferentialInducedSuccessor.reanchoredChartMap s x₁
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₁ v) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map x₁) (d.alignment v))
    (hmapNew : ∀ x ∈ s.germ.source ∩ d.successor.germ.source,
      s.map x ∈ (extChartAt I (s.map x₁)).source)
    (hnorm : ∀ x ∈ s.germ.source ∩ d.successor.germ.source,
      ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) x₁).symm ((chartAt E x₁) x)‖ < r) :
    InducedAlignment.CompatibleStep.RigidStepCompatibleWith
      s x₁ d.alignment := by
  intro x hx
  exact predecessor_germ_eq_successor_germ_of_expAtChart_norm_lt
    s d hball (by
      simpa [DifferentialInducedSuccessor.Data.successor] using hx)
      (hmapNew x (by
        simpa [DifferentialInducedSuccessor.Data.successor] using hx))
      (hnorm x (by
        simpa [DifferentialInducedSuccessor.Data.successor] using hx))

omit [T2Space M] in
/-- The closed-interval ODE argument underlying exponential naturality,
parameterized only by the local geodesic-transition package it consumes. -/
private theorem reanchoredChartMap_expAtChart_naturality_ball_of_transition
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) (rho : ℝ)
    (DF : E → E →L[ℝ] E)
    (htransition :
      ∀ v : E, ‖v‖ < rho → v ≠ 0 →
        let eM :=
          GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) s.anchor
        let eS :=
          GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) s.target
        let F := CartanDifferential.cartanChartMap
          g s.anchor s.target s.alignment
        v ∈ eM.source ∧
          s.alignment v ∈ eS.source ∧
          ContDiffAt ℝ 2 F (eM v) ∧
          HasStrictFDerivAt F (DF v) (eM v) ∧
          (∀ᶠ q in nhds (eM v),
            GeodesicTransport.cutoff (n := 3) s.anchor q = 1) ∧
          (∀ᶠ q in nhds (F (eM v)),
            GeodesicTransport.cutoff (n := 3) s.target q = 1) ∧
          ∀ w : E,
            GeodesicTransport.chartChristoffelField
                roundSphereMetric3 s.target (F (eM v))
                ((fderiv ℝ F (eM v)) w)
                ((fderiv ℝ F (eM v)) w) =
              (fderiv ℝ F (eM v))
                  (GeodesicTransport.chartChristoffelField
                    g s.anchor (eM v) w w) -
                ((fderiv ℝ (fun q : E => fderiv ℝ F q) (eM v)) w) w) :
    ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
      ‖d.v‖ < rho → d.v ≠ 0 →
        ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
          DifferentialInducedSuccessor.reanchoredChartMap s x₁
              (GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁ v) =
            GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (s.map x₁) (d.alignment v) := by
  intro x₁ d hd hdne
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) s.target
  let F := CartanDifferential.cartanChartMap
    g s.anchor s.target s.alignment
  let inner : E → E := GeodesicTransport.chartTransition x₁ s.anchor
  let outer : E → E :=
    GeodesicTransport.chartTransition s.target (s.map x₁)
  rcases htransition d.v hd hdne with
    ⟨hdvsrc, hLdsrc, hF₂d, hFstrictd, hcutS, hcutT, htransd⟩
  let zS : E := extChartAt I x₁ x₁
  let qT : E := extChartAt I s.target (s.map x₁)
  let zT : E := extChartAt I (s.map x₁) (s.map x₁)
  have hzS_target : zS ∈ (extChartAt I x₁).target := by
    change extChartAt I x₁ x₁ ∈ (extChartAt I x₁).target
    exact (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsymmS : (extChartAt I x₁).symm zS = x₁ := by
    change (extChartAt I x₁).symm (extChartAt I x₁ x₁) = x₁
    exact (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hinnerPoint : inner zS = eM d.v := by
    change extChartAt I s.anchor ((extChartAt I x₁).symm zS) = eM d.v
    rw [hsymmS]
    simpa [eM] using d.source_coordinate
  have hnewTargetN : (extChartAt I x₁).target ∈ nhds zS :=
    (isOpen_extChartAt_target x₁).mem_nhds hzS_target
  have holdSourceN :
      {q : E | (extChartAt I x₁).symm q ∈
        (extChartAt I s.anchor).source} ∈ nhds zS := by
    have hold : (extChartAt I s.anchor).source ∈
        nhds ((extChartAt I x₁).symm zS) := by
      rw [hsymmS]
      exact (isOpen_extChartAt_source s.anchor).mem_nhds
        d.source_mem_oldChart
    exact (continuousAt_extChartAt_symm x₁).preimage_mem_nhds hold
  have hsourceNewCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) x₁ q = 1} ∈ nhds zS := by
    simpa [zS] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) x₁)
  have hinnerDeriv :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      x₁ s.anchor hzS_target (by
        rw [hsymmS]
        exact d.source_mem_oldChart)
  have holdCutAt :
      {q : E | GeodesicTransport.cutoff (n := 3) s.anchor q = 1} ∈
        nhds (inner zS) := by
    rw [hinnerPoint]
    exact hcutS
  have holdCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) s.anchor (inner q) = 1} ∈
        nhds zS := by
    exact hinnerDeriv.continuousAt.preimage_mem_nhds holdCutAt
  have heMdvTarget : eM d.v ∈ eM.target := eM.map_source hdvsrc
  have hinnerTarget : ∀ᶠ q in nhds zS, inner q ∈ eM.target := by
    have htargetN : eM.target ∈ nhds (inner zS) := by
      rw [hinnerPoint]
      exact eM.open_target.mem_nhds heMdvTarget
    exact hinnerDeriv.continuousAt.preimage_mem_nhds htargetN
  have hwTendsto :
      Tendsto (fun q : E => eM.symm (inner q)) (nhds zS) (nhds d.v) := by
    have hinnerT : Tendsto inner (nhds zS) (nhds (inner zS)) := by
      simpa [inner] using hinnerDeriv.continuousAt
    rw [hinnerPoint] at hinnerT
    have hcomp := (eM.continuousAt_symm heMdvTarget).tendsto.comp hinnerT
    simpa [Function.comp_def, eM.left_inv hdvsrc] using hcomp
  have hdBall : d.v ∈ ball (0 : E) rho := by
    simpa [mem_ball, dist_eq_norm] using hd
  have hwNorm : ∀ᶠ q in nhds zS, ‖eM.symm (inner q)‖ < rho := by
    have hmem := hwTendsto.eventually (isOpen_ball.mem_nhds hdBall)
    simpa [mem_ball, dist_eq_norm] using hmem
  have hdCompl : d.v ∈ ({0} : Set E)ᶜ := by simpa using hdne
  have hwNe : ∀ᶠ q in nhds zS, eM.symm (inner q) ≠ 0 := by
    have hmem := hwTendsto.eventually
      (isClosed_singleton.isOpen_compl.mem_nhds hdCompl)
    simpa using hmem
  have hFendpoint : F (eM d.v) = eS (s.alignment d.v) := by
    change eS (s.alignment (eM.symm (eM d.v))) = eS (s.alignment d.v)
    rw [eM.left_inv hdvsrc]
  have hFpoint : F (eM d.v) = qT := by
    rw [hFendpoint]
    simpa [qT, eS] using d.target_coordinate.symm
  have hmiddleTendsto :
      Tendsto (fun q : E => F (inner q)) (nhds zS) (nhds qT) := by
    have hFcont : ContinuousAt F (eM d.v) := by
      simpa [F, eM] using hF₂d.continuousAt
    have hinnerT : Tendsto inner (nhds zS) (nhds (inner zS)) := by
      simpa [inner] using hinnerDeriv.continuousAt
    rw [hinnerPoint] at hinnerT
    have hcomp := hFcont.tendsto.comp hinnerT
    simpa [Function.comp_def, hFpoint] using hcomp
  have hqTtarget : qT ∈ (extChartAt I s.target).target := by
    simpa [qT] using
      (extChartAt I s.target).map_source d.target_mem_oldChart
  have hsymmT : (extChartAt I s.target).symm qT = s.map x₁ := by
    simpa [qT] using
      (extChartAt I s.target).left_inv d.target_mem_oldChart
  have houterPoint : outer qT = zT := by
    change extChartAt I (s.map x₁) ((extChartAt I s.target).symm qT) = zT
    rw [hsymmT]
  have holdTargetN : (extChartAt I s.target).target ∈ nhds qT :=
    (isOpen_extChartAt_target s.target).mem_nhds hqTtarget
  have hnewSourceN :
      {q : E | (extChartAt I s.target).symm q ∈
        (extChartAt I (s.map x₁)).source} ∈ nhds qT := by
    have hsource : (extChartAt I (s.map x₁)).source ∈
        nhds ((extChartAt I s.target).symm qT) := by
      rw [hsymmT]
      exact (isOpen_extChartAt_source (s.map x₁)).mem_nhds
        (mem_extChartAt_source (s.map x₁))
    exact (continuousAt_extChartAt_symm'' hqTtarget).preimage_mem_nhds hsource
  have holdTargetCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) s.target q = 1} ∈
        nhds qT := by
    rw [← hFpoint]
    exact hcutT
  have houterDeriv :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      s.target (s.map x₁) hqTtarget (by
        rw [hsymmT]
        exact mem_extChartAt_source (s.map x₁))
  have hnewCutAt :
      {q : E | GeodesicTransport.cutoff (n := 3) (s.map x₁) q = 1} ∈
        nhds (outer qT) := by
    rw [houterPoint]
    simpa [zT] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) (s.map x₁))
  have htargetNewCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) (s.map x₁) (outer q) = 1} ∈
        nhds qT :=
    houterDeriv.continuousAt.preimage_mem_nhds hnewCutAt
  have hnewTargetNN : ∀ᶠ q in nhds zS,
      (extChartAt I x₁).target ∈ nhds q :=
    eventually_eventually_nhds.2 hnewTargetN
  have holdSourceNN : ∀ᶠ q in nhds zS,
      {p : E | (extChartAt I x₁).symm p ∈
        (extChartAt I s.anchor).source} ∈ nhds q :=
    eventually_eventually_nhds.2 holdSourceN
  have hnewCutNN : ∀ᶠ q in nhds zS,
      {p : E | GeodesicTransport.cutoff (n := 3) x₁ p = 1} ∈ nhds q :=
    eventually_eventually_nhds.2 hsourceNewCutN
  have holdCutNN : ∀ᶠ q in nhds zS,
      {p : E | GeodesicTransport.cutoff (n := 3) s.anchor (inner p) = 1} ∈
        nhds q :=
    eventually_eventually_nhds.2 holdCutN
  have holdTargetNN : ∀ᶠ q in nhds zS,
      (extChartAt I s.target).target ∈ nhds (F (inner q)) :=
    hmiddleTendsto.eventually (eventually_eventually_nhds.2 holdTargetN)
  have hnewSourceNN : ∀ᶠ q in nhds zS,
      {p : E | (extChartAt I s.target).symm p ∈
        (extChartAt I (s.map x₁)).source} ∈ nhds (F (inner q)) :=
    hmiddleTendsto.eventually (eventually_eventually_nhds.2 hnewSourceN)
  have holdTargetCutNN : ∀ᶠ q in nhds zS,
      {p : E | GeodesicTransport.cutoff (n := 3) s.target p = 1} ∈
        nhds (F (inner q)) :=
    hmiddleTendsto.eventually (eventually_eventually_nhds.2 holdTargetCutN)
  have hnewCutNN' : ∀ᶠ q in nhds zS,
      {p : E | GeodesicTransport.cutoff (n := 3) (s.map x₁) (outer p) = 1} ∈
        nhds (F (inner q)) :=
    hmiddleTendsto.eventually (eventually_eventually_nhds.2 htargetNewCutN)
  let Good : E → Prop := fun q =>
    (extChartAt I x₁).target ∈ nhds q ∧
    {p : E | (extChartAt I x₁).symm p ∈
      (extChartAt I s.anchor).source} ∈ nhds q ∧
    {p : E | GeodesicTransport.cutoff (n := 3) x₁ p = 1} ∈ nhds q ∧
    {p : E | GeodesicTransport.cutoff (n := 3) s.anchor (inner p) = 1} ∈
      nhds q ∧
    inner q ∈ eM.target ∧
    ‖eM.symm (inner q)‖ < rho ∧
    eM.symm (inner q) ≠ 0 ∧
    (extChartAt I s.target).target ∈ nhds (F (inner q)) ∧
    {p : E | (extChartAt I s.target).symm p ∈
      (extChartAt I (s.map x₁)).source} ∈ nhds (F (inner q)) ∧
    {p : E | GeodesicTransport.cutoff (n := 3) s.target p = 1} ∈
      nhds (F (inner q)) ∧
    {p : E | GeodesicTransport.cutoff (n := 3) (s.map x₁) (outer p) = 1} ∈
      nhds (F (inner q))
  have hgood : ∀ᶠ q in nhds zS, Good q := by
    filter_upwards [hnewTargetNN, holdSourceNN, hnewCutNN, holdCutNN,
      hinnerTarget, hwNorm, hwNe, holdTargetNN, hnewSourceNN,
      holdTargetCutNN, hnewCutNN'] with q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  rcases Metric.mem_nhds_iff.mp hgood with ⟨rGood, hrGood, hrGoodSub⟩
  rcases GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc g x₁ with
    ⟨tauS, htauS, deltaS, hdeltaS, epsS, hepsS, aS, alphaS, hAlphaS, hExpS⟩
  rcases GeodesicTransport.expAt_uniform_pl_flow_eq_on_Icc
      roundSphereMetric3 (s.map x₁) with
    ⟨tauT, htauT, deltaT, hdeltaT, epsT, hepsT, aT, alphaT, hAlphaT, hExpT⟩
  let D : E →L[ℝ] E := d.alignment.toContinuousLinearEquiv
  let delta : ℝ := min deltaS (deltaT / (‖D‖ + 1))
  have hdenD : 0 < ‖D‖ + 1 := by positivity
  have hdeltaTquot : 0 < deltaT / (‖D‖ + 1) :=
    div_pos hdeltaT hdenD
  have hdelta : 0 < delta := lt_min hdeltaS hdeltaTquot
  let timeCap : ℝ :=
    min tauS (min tauT (min epsS (min epsT (rGood / ((aS : ℝ) + 1)))))
  have htimeCap : 0 < timeCap := by
    dsimp [timeCap]
    exact lt_min htauS (lt_min htauT (lt_min hepsS
      (lt_min hepsT (div_pos hrGood (by positivity)))))
  let T : ℝ := timeCap / 2
  have hT : 0 < T := half_pos htimeCap
  have hTlt : T < timeCap := half_lt_self htimeCap
  have hTtauS : T < tauS := hTlt.trans_le (by
    dsimp [timeCap]
    exact min_le_left _ _)
  have hTtauT : T < tauT := hTlt.trans_le (by
    dsimp [timeCap]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hTepsS : T < epsS := hTlt.trans_le (by
    dsimp [timeCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hTepsT : T < epsT := hTlt.trans_le (by
    dsimp [timeCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))
  have hTrGood : T < rGood / ((aS : ℝ) + 1) := hTlt.trans_le (by
    dsimp [timeCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
  let r : ℝ := T * delta
  have hr : 0 < r := mul_pos hT hdelta
  refine ⟨r, hr, ?_⟩
  intro v hv
  let u : E := T⁻¹ • v
  have hTu : T • u = v := by
    simp [u, smul_smul, ne_of_gt hT]
  have hu : ‖u‖ < delta := by
    change ‖T⁻¹ • v‖ < delta
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT)]
    have hvin : ‖v‖ < T * delta := by simpa [r] using hv
    calc
      T⁻¹ * ‖v‖ < T⁻¹ * (T * delta) :=
        mul_lt_mul_of_pos_left hvin (inv_pos.mpr hT)
      _ = delta := by field_simp [ne_of_gt hT]
  have huS : ‖u‖ < deltaS := hu.trans_le (min_le_left _ _)
  have huTquot : ‖u‖ < deltaT / (‖D‖ + 1) :=
    hu.trans_le (min_le_right _ _)
  have hDu_le : ‖d.alignment u‖ ≤ ‖D‖ * ‖u‖ := by
    simpa [D] using D.le_opNorm u
  have hLu : ‖d.alignment u‖ < deltaT := by
    by_cases hDzero : ‖D‖ = 0
    · have hzero : ‖d.alignment u‖ = 0 := by
        apply le_antisymm
        · simpa [hDzero] using hDu_le
        · exact norm_nonneg _
      linarith
    · have hDpos : 0 < ‖D‖ := lt_of_le_of_ne (norm_nonneg D) (Ne.symm hDzero)
      have hmul : ‖D‖ * ‖u‖ < ‖D‖ * (deltaT / (‖D‖ + 1)) :=
        mul_lt_mul_of_pos_left huTquot hDpos
      refine hDu_le.trans_lt (hmul.trans_le ?_)
      have hfrac : ‖D‖ / (‖D‖ + 1) ≤ 1 := by
        rw [div_le_one hdenD]
        linarith
      calc
        ‖D‖ * (deltaT / (‖D‖ + 1)) =
            deltaT * (‖D‖ / (‖D‖ + 1)) := by ring
        _ ≤ deltaT * 1 := mul_le_mul_of_nonneg_left hfrac hdeltaT.le
        _ = deltaT := mul_one _
  let gammaNew : ℝ → E × E := alphaS (zS, u)
  let gammaOld : ℝ → E × E :=
    GeodesicTransport.chartTransitionState x₁ s.anchor gammaNew
  let mu : ℝ → E × E :=
    FTransitionGeodesicMap.mappedState F gammaOld
  let deltaCurve : ℝ → E × E :=
    GeodesicTransport.chartTransitionState s.target (s.map x₁) mu
  let eta : ℝ → E × E := alphaT (zT, d.alignment u)
  rcases hAlphaS u huS with
    ⟨hgammaNew0, hgammaNewDerWithin, hgammaNewMem, hgammaNewTarget, _hhomS⟩
  rcases hAlphaT (d.alignment u) hLu with
    ⟨heta0raw, hetaDerWithin, hetaMem, hetaTarget, _hhomT⟩
  have hgammaNewAt : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt gammaNew
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₁) (gammaNew t)) t := by
    exact IsometryInstantiate.geodesicFlow_hasDerivAt_on_shrunk_Icc
      (g := g) (x₀ := x₁) (γ := gammaNew)
      (a := -epsS) (b := epsS) (c := 0) (d := T)
      (by linarith [hepsS]) hTepsS hgammaNewDerWithin
  have hetaAt : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt eta
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField
            roundSphereMetric3 (s.map x₁)) (eta t)) t := by
    exact IsometryInstantiate.geodesicFlow_hasDerivAt_on_shrunk_Icc
      (g := roundSphereMetric3) (x₀ := s.map x₁) (γ := eta)
      (a := -epsT) (b := epsT) (c := 0) (d := T)
      (by linarith [hepsT]) hTepsT hetaDerWithin
  have hgammaNewGood : ∀ t ∈ Icc (0 : ℝ) T, Good (gammaNew t).1 := by
    intro t ht
    have htBig : t ∈ Icc (-T) T :=
      ⟨(neg_nonpos.mpr hT.le).trans ht.1, ht.2⟩
    have hdist :=
      GeodesicTransport.plFlowPosition_dist_anchor_le_radius_mul_abs
        (g := g) (x₀ := x₁) (ε := epsS) (τ := T)
        (a := aS) (α := alphaS) (v₀ := u)
        hT.le hTepsS.le hgammaNew0 hgammaNewDerWithin hgammaNewMem htBig
    have habs : |t| = t := abs_of_nonneg ht.1
    have haSnonneg : 0 ≤ (aS : ℝ) := NNReal.coe_nonneg aS
    have hdistlt : dist (gammaNew t).1 zS < rGood := by
      have hmul : (aS : ℝ) * |t| ≤ (aS : ℝ) * T := by
        gcongr
        simpa [habs] using ht.2
      have hstrict : ((aS : ℝ) + 1) * T < rGood := by
        have hstrict' : T * ((aS : ℝ) + 1) < rGood :=
          (lt_div_iff₀ (by positivity : 0 < (aS : ℝ) + 1)).mp hTrGood
        simpa [mul_comm] using hstrict'
      exact hdist.trans_lt (hmul.trans_lt (by nlinarith))
    apply hrGoodSub
    exact mem_ball.mpr hdistlt
  have hdeltaAt : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt deltaCurve
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField
            roundSphereMetric3 (s.map x₁)) (deltaCurve t)) t := by
    intro t ht
    have hq := hgammaNewGood t ht
    change Good (gammaNew t).1 at hq
    rcases hq with
      ⟨hnewTarget, holdSource, hnewCut, holdCut, hOldTarget,
        hNorm, hNe, holdTarget, hnewSource, holdTargetCut, hnewTargetCut⟩
    have hgammaOldAt : HasDerivAt gammaOld
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g s.anchor) (gammaOld t)) t := by
      simpa [gammaOld] using
        GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
          g x₁ s.anchor (hgammaNewAt t ht)
            hnewTarget holdSource hnewCut holdCut
    let w : E := eM.symm (gammaOld t).1
    have hright : eM w = (gammaOld t).1 := by
      exact eM.right_inv (by simpa [gammaOld, inner] using hOldTarget)
    rcases htransition w (by simpa [w, gammaOld, inner] using hNorm)
        (by simpa [w, gammaOld, inner] using hNe) with
      ⟨_wsrc, _Lwsrc, hF2w, _hFstrictw, _hcutSw, _hcutTw, htransw⟩
    have hF2 : ContDiffAt ℝ 2 F (gammaOld t).1 := by
      simpa [F, eM, hright] using hF2w
    have hFtrans :
        GeodesicTransport.chartChristoffelField roundSphereMetric3 s.target
            (F (gammaOld t).1)
            ((fderiv ℝ F (gammaOld t).1) (gammaOld t).2)
            ((fderiv ℝ F (gammaOld t).1) (gammaOld t).2) =
          (fderiv ℝ F (gammaOld t).1)
              (GeodesicTransport.chartChristoffelField g s.anchor
                (gammaOld t).1 (gammaOld t).2 (gammaOld t).2) -
            ((fderiv ℝ (fun q : E => fderiv ℝ F q) (gammaOld t).1)
              (gammaOld t).2) (gammaOld t).2 := by
      simpa [F, eM, hright] using htransw (gammaOld t).2
    have hmuAt : HasDerivAt mu
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 s.target)
          (mu t)) t := by
      simpa [mu] using
        FTransitionGeodesicMap.mappedState_hasDerivAt_of_F_transition
          F
          (GeodesicTransport.chartChristoffelField g s.anchor)
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 s.target)
          hgammaOldAt hF2 hFtrans
    simpa [deltaCurve] using
      GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
        roundSphereMetric3 s.target (s.map x₁) hmuAt
          (by simpa [mu, gammaOld, inner] using holdTarget)
          (by simpa [mu, gammaOld, inner] using hnewSource)
          (by simpa [mu, gammaOld, inner] using holdTargetCut)
          (by simpa [mu, gammaOld, inner] using hnewTargetCut)
  have hinnerCanonical :
      HasFDerivAt inner (fderiv ℝ inner zS) zS := by
    exact (by simpa [inner] using hinnerDeriv.differentiableAt.hasFDerivAt)
  have hFCanonical0 :
      HasFDerivAt F (fderiv ℝ F (eM d.v)) (eM d.v) := by
    have hFcont : ContDiffAt ℝ 2 F (eM d.v) := by
      simpa [F, eM] using hF₂d
    exact (hFcont.differentiableAt (by norm_num)).hasFDerivAt
  have hFCanonical :
      HasFDerivAt F (fderiv ℝ F (inner zS)) (inner zS) := by
    rw [hinnerPoint]
    exact hFCanonical0
  have houterCanonical0 :
      HasFDerivAt outer (fderiv ℝ outer qT) qT := by
    exact (by simpa [outer] using houterDeriv.differentiableAt.hasFDerivAt)
  have hFinner : F (inner zS) = qT := by
    rw [hinnerPoint]
    exact hFpoint
  have houterCanonical :
      HasFDerivAt outer (fderiv ℝ outer (F (inner zS))) (F (inner zS)) := by
    rw [hFinner]
    exact houterCanonical0
  have hmiddleDeriv := hFCanonical.comp zS hinnerCanonical
  have htotalDeriv := houterCanonical.comp zS hmiddleDeriv
  change HasFDerivAt
    (DifferentialInducedSuccessor.reanchoredChartMap s x₁)
    ((fderiv ℝ outer (F (inner zS))).comp
      ((fderiv ℝ F (inner zS)).comp (fderiv ℝ inner zS))) zS at htotalDeriv
  have hDcomp :
      (fderiv ℝ outer (F (inner zS))).comp
          ((fderiv ℝ F (inner zS)).comp (fderiv ℝ inner zS)) =
        (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) :=
    htotalDeriv.fderiv.symm.trans (by
      simpa [zS] using d.hasFDerivAt_reanchoredChartMap.fderiv)
  have hdelta0fst : (deltaCurve 0).1 = zT := by
    change outer (F (inner (gammaNew 0).1)) = zT
    have hgammaNew0' : gammaNew 0 = (zS, u) := by
      simpa [gammaNew, zS] using hgammaNew0
    rw [hgammaNew0']
    exact (congrArg outer hFinner).trans houterPoint
  have hdelta0snd : (deltaCurve 0).2 = d.alignment u := by
    have hucomp := congrArg (fun L : E →L[ℝ] E => L u) hDcomp
    have hgammaNew0' : gammaNew 0 = (zS, u) := by
      simpa [gammaNew, zS] using hgammaNew0
    simpa [deltaCurve, mu, gammaOld, gammaNew, inner, outer,
      FTransitionGeodesicMap.mappedState,
      GeodesicTransport.chartTransitionState, hgammaNew0'] using hucomp
  have hdelta0 : deltaCurve 0 = (zT, d.alignment u) :=
    Prod.ext hdelta0fst hdelta0snd
  have heta0 : eta 0 = (zT, d.alignment u) := by
    simpa [eta] using heta0raw
  have hdeltaCont : ContinuousOn deltaCurve (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn hdeltaAt
  have hetaCont : ContinuousOn eta (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn hetaAt
  have hcompact : IsCompact
      (deltaCurve '' Icc (0 : ℝ) T ∪ eta '' Icc (0 : ℝ) T) :=
    (isCompact_Icc.image_of_continuousOn hdeltaCont).union
      (isCompact_Icc.image_of_continuousOn hetaCont)
  rcases hcompact.isBounded.subset_closedBall ((0 : E), (0 : E)) with
    ⟨R, hR⟩
  rcases
      GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        roundSphereMetric3 (s.map x₁) ((0 : E), (0 : E)) R with
    ⟨K, hLip⟩
  have hdeltaMem : ∀ t ∈ Ico (0 : ℝ) T,
      deltaCurve t ∈ closedBall ((0 : E), (0 : E)) R := by
    intro t ht
    exact hR (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  have hetaMem' : ∀ t ∈ Ico (0 : ℝ) T,
      eta t ∈ closedBall ((0 : E), (0 : E)) R := by
    intro t ht
    exact hR (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)
  have heq : EqOn deltaCurve eta (Icc (0 : ℝ) T) := by
    exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ => geodesicFlowField
        (GeodesicTransport.chartChristoffelField
          roundSphereMetric3 (s.map x₁)))
      (s := fun _ : ℝ => closedBall ((0 : E), (0 : E)) R)
      (K := K)
      (fun _ _ => hLip)
      hdeltaCont
      (fun t ht => (hdeltaAt t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      hdeltaMem
      hetaCont
      (fun t ht => (hetaAt t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      hetaMem' (hdelta0.trans heta0.symm)
  have hstateT : deltaCurve T = eta T := heq ⟨hT.le, le_rfl⟩
  have hsourceExp := hExpS u huS T ⟨hT.le, hTtauS.le⟩
  have htargetExp := hExpT (d.alignment u) hLu T ⟨hT.le, hTtauT.le⟩
  have hsourceChart :
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁ v =
        (gammaNew T).1 := by
    have htargetPos : (gammaNew T).1 ∈ (extChartAt I x₁).target :=
      hgammaNewTarget T ⟨(neg_nonpos.mpr hepsS.le).trans hT.le, hTepsS.le⟩
    change extChartAt I x₁ (GeodesicTransport.expAt g x₁ v) = (gammaNew T).1
    rw [← hTu, hsourceExp]
    exact (extChartAt I x₁).right_inv htargetPos
  have htargetChart :
      GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map x₁) (d.alignment v) =
        (eta T).1 := by
    have hLv : d.alignment v = T • d.alignment u := by
      rw [← hTu]
      exact map_smul d.alignment.toContinuousLinearEquiv T u
    have htargetPos : (eta T).1 ∈ (extChartAt I (s.map x₁)).target :=
      hetaTarget T ⟨(neg_nonpos.mpr hepsT.le).trans hT.le, hTepsT.le⟩
    change extChartAt I (s.map x₁)
      (GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (d.alignment v)) =
        (eta T).1
    rw [hLv, htargetExp]
    exact (extChartAt I (s.map x₁)).right_inv htargetPos
  have hfst := congrArg Prod.fst hstateT
  rw [hsourceChart, htargetChart]
  simpa [deltaCurve, mu, gammaOld, gammaNew,
    FTransitionGeodesicMap.mappedState,
    GeodesicTransport.chartTransitionState,
    DifferentialInducedSuccessor.reanchoredChartMap, inner, outer] using hfst

/--
On one uniform punctured predecessor normal ball, every differential-induced
successor has a genuine positive new-anchor normal ball on which the
predecessor's re-anchored chart map satisfies exponential naturality.
-/
theorem exists_reanchoredChartMap_expAtChart_naturality_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 →
          ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
            DifferentialInducedSuccessor.reanchoredChartMap s x₁
                (GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₁ v) =
              GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := roundSphereMetric3) (s.map x₁) (d.alignment v) := by
  rcases
      UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law
        (g := g) hcurv s.anchor s.target s.alignment with
    ⟨rho, hrho, _Afield, _Bfield, DF, _hDF, htransition⟩
  refine ⟨rho, hrho, ?_⟩
  exact reanchoredChartMap_expAtChart_naturality_ball_of_transition
    g s rho DF htransition

/--
For fixed predecessor anchors, one positive predecessor-normal radius supports
closed-interval exponential naturality for every tangent alignment.  The
resulting new-anchor normal-ball radius may depend on the alignment and
successor datum.
-/
theorem exists_uniform_reanchoredChartMap_expAtChart_naturality_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x0 p0,
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk x0 p0 L) x₁),
          ‖d.v‖ < rho → d.v ≠ 0 →
            ∃ r > (0 : ℝ), ∀ v : E, ‖v‖ < r →
              DifferentialInducedSuccessor.reanchoredChartMap
                  (CartanChain.ChainState.mk x0 p0 L) x₁
                  (GeodesicTransport.expAtChartOpenPartialHomeomorph
                    (g := g) x₁ v) =
                GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3)
                  ((CartanChain.ChainState.mk x0 p0 L).map x₁)
                  (d.alignment v) := by
  rcases
      UniformTangentAlignmentGeodesicTransition.exists_uniform_cartanChartMap_chartChristoffelField_self_F_transition_law
        (g := g) hcurv x0 p0 with
    ⟨rho, hrho, htransitionAll⟩
  refine ⟨rho, hrho, ?_⟩
  intro L
  rcases htransitionAll L with
    ⟨_Afield, _Bfield, DF, _hDF, htransition⟩
  exact reanchoredChartMap_expAtChart_naturality_ball_of_transition
    g (CartanChain.ChainState.mk x0 p0 L) rho DF htransition

/-- Curvature supplies the coordinate ball needed by the strict-common-source
consumer.  Thus the only premises left for a full rigid step are the two
literal global cover conditions: every common-source predecessor value stays
in the new target chart, and every common-source new normal coordinate stays
inside the ODE naturality ball. -/
theorem exists_rigidStepCompatibleWith_of_common_source_ball_cover
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 →
          ∃ r > (0 : ℝ),
            (∀ x ∈ s.germ.source ∩ d.successor.germ.source,
              s.map x ∈ (extChartAt I (s.map x₁)).source) →
            (∀ x ∈ s.germ.source ∩ d.successor.germ.source,
              ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₁).symm ((chartAt E x₁) x)‖ < r) →
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                s x₁ d.alignment := by
  rcases exists_reanchoredChartMap_expAtChart_naturality_ball g hcurv s with
    ⟨rho, hrho, hball⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd hdne
  rcases hball d hd hdne with ⟨r, hr, hballr⟩
  refine ⟨r, hr, ?_⟩
  intro hmapNew hnorm
  exact rigidStepCompatibleWith_of_expAtChart_ball_cover
    s d hballr hmapNew hnorm

/-- The same full-overlap cover interface for all small differential data.
When the stored vector is zero, the successor is already the predecessor and
the two cover hypotheses are unused. -/
theorem exists_rigidStepCompatibleWith_of_common_source_ball_cover_all
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho →
          ∃ r > (0 : ℝ),
            (∀ x ∈ s.germ.source ∩ d.successor.germ.source,
              s.map x ∈ (extChartAt I (s.map x₁)).source) →
            (∀ x ∈ s.germ.source ∩ d.successor.germ.source,
              ‖(GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := g) x₁).symm ((chartAt E x₁) x)‖ < r) →
              InducedAlignment.CompatibleStep.RigidStepCompatibleWith
                s x₁ d.alignment := by
  rcases exists_rigidStepCompatibleWith_of_common_source_ball_cover
      g hcurv s with ⟨rho, hrho, hcover⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd
  by_cases hdne : d.v ≠ 0
  · exact hcover d hd hdne
  · refine ⟨1, zero_lt_one, ?_⟩
    intro _hmapNew _hnorm
    exact DifferentialSuccessorZero.rigidStepCompatibleWith_of_vector_eq_zero
      d (not_ne_iff.mp hdne)

omit [T2Space M] in
/-- Convert one exponential-naturality ball into an open neighborhood on which
the predecessor and differential successor agree on their strict common
source. -/
private theorem exists_local_eqOn_differentialSuccessor_of_expAtChart_ball
    (g : ClosedSmoothRiemannianMetric 3 M)
    (s : CartanChain.ChainState g) {x₁ : M}
    (d : DifferentialInducedSuccessor.Data s x₁) {r : ℝ}
    (hr : 0 < r)
    (hballr : ∀ v : E, ‖v‖ < r →
      DifferentialInducedSuccessor.reanchoredChartMap s x₁
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₁ v) =
        GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map x₁) (d.alignment v)) :
    ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
      EqOn s.germ d.successor.germ
        (V ∩ (s.germ.source ∩ d.successor.germ.source)) := by
  have hxOld : x₁ ∈ s.germ.source := d.anchor_mem_predecessor_source
  have hsCont : ContinuousAt s.map x₁ := by
    change ContinuousAt s.germ x₁
    exact s.germ.continuousOn.continuousAt
      (s.germ.open_source.mem_nhds hxOld)
  have hmapNew : ∀ᶠ x in nhds x₁,
      s.map x ∈ (extChartAt I (s.map x₁)).source := by
    exact hsCont.preimage_mem_nhds
      ((isOpen_extChartAt_source (s.map x₁)).mem_nhds
        (mem_extChartAt_source (s.map x₁)))
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁
  have hzeroSource : (0 : E) ∈ eM.source :=
    GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
      (g := g) x₁
  have hzeroTarget : eM (0 : E) ∈ eM.target := eM.map_source hzeroSource
  have heMzero : eM (0 : E) = extChartAt I x₁ x₁ := by
    change GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x₁ (0 : E) = (chartAt E x₁) x₁
    exact CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor g x₁
  have hvCont : ContinuousAt
      (fun x : M => eM.symm (extChartAt I x₁ x)) x₁ := by
    have heCont : ContinuousAt eM.symm (extChartAt I x₁ x₁) := by
      rw [← heMzero]
      exact eM.continuousAt_symm hzeroTarget
    simpa [Function.comp_def] using
      heCont.comp (continuousAt_extChartAt x₁)
  have hanchorInv : eM.symm (extChartAt I x₁ x₁) = (0 : E) := by
    rw [← heMzero]
    exact eM.left_inv hzeroSource
  have hzeroBall : (0 : E) ∈ ball (0 : E) r := by
    simpa [mem_ball, dist_eq_norm] using hr
  have hnorm : ∀ᶠ x in nhds x₁,
      ‖eM.symm ((chartAt E x₁) x)‖ < r := by
    have hballN : ball (0 : E) r ∈
        nhds (eM.symm (extChartAt I x₁ x₁)) := by
      rw [hanchorInv]
      exact isOpen_ball.mem_nhds hzeroBall
    have hmem := hvCont.eventually hballN
    simpa only [extChartAt_coe, mem_ball, dist_eq_norm, sub_zero] using hmem
  have hgood :
      {x : M | s.map x ∈ (extChartAt I (s.map x₁)).source ∧
        ‖eM.symm ((chartAt E x₁) x)‖ < r} ∈ nhds x₁ :=
    hmapNew.and hnorm
  rcases mem_nhds_iff.mp hgood with ⟨V, hVsub, hVopen, hxV⟩
  refine ⟨V, hVopen, hxV, ?_⟩
  intro x hx
  have hconditions := hVsub hx.1
  exact predecessor_germ_eq_successor_germ_of_expAtChart_norm_lt
    s d hballr hx.2 hconditions.1 (by simpa [eM] using hconditions.2)

/-- The uniform coordinate-ball theorem yields a genuine open neighborhood of
the new anchor on which the predecessor and its differential-induced successor
agree on their strict common source.  This is the local rigidity seed needed
by adjacent-overlap continuation; no full-overlap ray-cover assumption is used.
-/
theorem exists_local_eqOn_differentialSuccessor
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 →
          ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
            EqOn s.germ d.successor.germ
              (V ∩ (s.germ.source ∩ d.successor.germ.source)) := by
  rcases exists_reanchoredChartMap_expAtChart_naturality_ball g hcurv s with
    ⟨rho, hrho, hball⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd hdne
  rcases hball d hd hdne with ⟨r, hr, hballr⟩
  exact exists_local_eqOn_differentialSuccessor_of_expAtChart_ball
    g s d hr hballr

/--
For fixed predecessor anchors, one positive predecessor-normal radius gives a
local differential-successor equality neighborhood for every tangent
alignment and every nonzero successor datum in that radius.
-/
theorem exists_uniform_local_eqOn_differentialSuccessor
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x0 p0,
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk x0 p0 L) x₁),
          ‖d.v‖ < rho → d.v ≠ 0 →
            ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
              EqOn (CartanChain.ChainState.mk x0 p0 L).germ
                d.successor.germ
                (V ∩
                  ((CartanChain.ChainState.mk x0 p0 L).germ.source ∩
                    d.successor.germ.source)) := by
  rcases exists_uniform_reanchoredChartMap_expAtChart_naturality_ball
      g hcurv x0 p0 with ⟨rho, hrho, hballAll⟩
  refine ⟨rho, hrho, ?_⟩
  intro L x₁ d hd hdne
  rcases hballAll L d hd hdne with ⟨r, hr, hballr⟩
  exact exists_local_eqOn_differentialSuccessor_of_expAtChart_ball
    g (CartanChain.ChainState.mk x0 p0 L) d hr hballr

/-- Zero-vector re-anchors are already globally identical to their
predecessors, so the local equality seed extends from the punctured ball to the
whole sufficiently small differential-data ball. -/
theorem exists_local_eqOn_differentialSuccessor_all
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho →
          ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
            EqOn s.germ d.successor.germ
              (V ∩ (s.germ.source ∩ d.successor.germ.source)) := by
  rcases exists_local_eqOn_differentialSuccessor g hcurv s with
    ⟨rho, hrho, hlocal⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd
  by_cases hdne : d.v ≠ 0
  · exact hlocal d hd hdne
  · have hd0 : d.v = 0 := not_ne_iff.mp hdne
    have hrigid :=
      DifferentialSuccessorZero.rigidStepCompatibleWith_of_vector_eq_zero d hd0
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ x₁, ?_⟩
    intro x hx
    exact hrigid (by
      simpa [DifferentialInducedSuccessor.Data.successor] using hx.2)

/--
The fixed-anchor local equality radius is uniform over all tangent alignments
and all successor data in the ball, including the zero-vector case.
-/
theorem exists_uniform_local_eqOn_differentialSuccessor_all
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x0 p0,
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk x0 p0 L) x₁),
          ‖d.v‖ < rho →
            ∃ V : Set M, IsOpen V ∧ x₁ ∈ V ∧
              EqOn (CartanChain.ChainState.mk x0 p0 L).germ
                d.successor.germ
                (V ∩
                  ((CartanChain.ChainState.mk x0 p0 L).germ.source ∩
                    d.successor.germ.source)) := by
  rcases exists_uniform_local_eqOn_differentialSuccessor
      g hcurv x0 p0 with ⟨rho, hrho, hlocalAll⟩
  refine ⟨rho, hrho, ?_⟩
  intro L x₁ d hd
  by_cases hdne : d.v ≠ 0
  · exact hlocalAll L d hd hdne
  · have hd0 : d.v = 0 := not_ne_iff.mp hdne
    have hrigid :=
      DifferentialSuccessorZero.rigidStepCompatibleWith_of_vector_eq_zero d hd0
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ x₁, ?_⟩
    intro x hx
    exact hrigid (by
      simpa [DifferentialInducedSuccessor.Data.successor] using hx.2)

end DifferentialSuccessorIntervalNaturality
end Poincare
