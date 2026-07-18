import Poincare.Global.ChartTransitionGeodesicMap
import Poincare.Global.DifferentialInducedSuccessor
import Poincare.Global.ExponentialRayLaw
import Poincare.Global.UniformAnchoredGeodesicTransition
import Poincare.Global.UniformTangentAlignmentGeodesicTransition

/-!
# Geodesic naturality of differential-induced successors

This module feeds the curvature-only Cartan F-transition into the successor
whose alignment is the predecessor's actual differential.  Source and target
geodesics are transported into the predecessor charts, ODE uniqueness is
applied there, and the result is transported back to the new target chart.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorNaturality

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

omit [T2Space M] in
private theorem geodesicGermChartSolution_eventually_solves
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (v : E) :
    ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt (GeodesicTransport.geodesicGermChartSolution g x v)
        (geodesicFlowField (GeodesicTransport.chartChristoffelField g x)
          (GeodesicTransport.geodesicGermChartSolution g x v t)) t := by
  have hε := GeodesicTransport.geodesicGermRadius_pos g x v
  have hI :
      Ioo (-(GeodesicTransport.geodesicGermRadius g x v))
          (GeodesicTransport.geodesicGermRadius g x v) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  exact Filter.eventually_of_mem hI
    (GeodesicTransport.geodesicGermChartSolution_spec g x v).2.1

omit [T2Space M] in
private theorem geodesicGermChartSolution_fst_tendsto
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (v : E) :
    Tendsto
      (fun t : ℝ =>
        (GeodesicTransport.geodesicGermChartSolution g x v t).1)
      (nhds 0) (nhds (extChartAt I x x)) := by
  have hsol := geodesicGermChartSolution_eventually_solves g x v
  have hcont := hsol.self_of_nhds.continuousAt.fst
  change Tendsto
    (fun t : ℝ =>
      (GeodesicTransport.geodesicGermChartSolution g x v t).1)
    (nhds 0)
    (nhds
      (GeodesicTransport.geodesicGermChartSolution g x v 0).1) at hcont
  rw [(GeodesicTransport.geodesicGermChartSolution_spec g x v).1] at hcont
  exact hcont

omit [T2Space M] in
/-- The re-anchored coordinate expression is definitionally the preferred
target-chart coordinate of the predecessor map along the source germ. -/
theorem reanchoredChartMap_geodesicGermChartSolution_eq_targetChart_map_geodesicGermAt
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (x₁ : M) (u : E) :
    (fun t : ℝ =>
      DifferentialInducedSuccessor.reanchoredChartMap s x₁
        (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =
      fun t : ℝ =>
        extChartAt I (s.map x₁)
          (s.map (GeodesicTransport.geodesicGermAt g x₁ u t)) := by
  rfl

omit [T2Space M] in
/-- The ODE-uniqueness argument underlying successor naturality, parameterized
only by the complete local geodesic-transition package it consumes. -/
private theorem reanchoredChartMap_geodesicGerm_naturality_of_transition
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
      ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
        (fun t : ℝ =>
          DifferentialInducedSuccessor.reanchoredChartMap s x₁
            (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ =>
          (GeodesicTransport.geodesicGermChartSolution
            roundSphereMetric3 (s.map x₁) (d.alignment u) t).1) := by
  intro x₁ d hd hdne u
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := g) s.anchor
  let eS := GeodesicTransport.expAtChartOpenPartialHomeomorph
    (g := roundSphereMetric3) s.target
  let F := CartanDifferential.cartanChartMap
    g s.anchor s.target s.alignment
  let γnew : ℝ → E × E :=
    GeodesicTransport.geodesicGermChartSolution g x₁ u
  let γold : ℝ → E × E :=
    GeodesicTransport.chartTransitionState x₁ s.anchor γnew
  let μ : ℝ → E × E :=
    FTransitionGeodesicMap.mappedState F γold
  let δ : ℝ → E × E :=
    GeodesicTransport.chartTransitionState s.target (s.map x₁) μ
  let η : ℝ → E × E :=
    GeodesicTransport.geodesicGermChartSolution
      roundSphereMetric3 (s.map x₁) (d.alignment u)
  rcases htransition d.v hd hdne with
    ⟨hdvsrc, hLdsrc, hF₂d, hFstrictd, hcutS, hcutT, htransd⟩
  let zS : E := extChartAt I x₁ x₁
  have hzS_target : zS ∈ (extChartAt I x₁).target := by
    change extChartAt I x₁ x₁ ∈ (extChartAt I x₁).target
    exact (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
  have hsymmS : (extChartAt I x₁).symm zS = x₁ := by
    change (extChartAt I x₁).symm (extChartAt I x₁ x₁) = x₁
    exact (extChartAt I x₁).left_inv (mem_extChartAt_source x₁)
  have hinnerPoint :
      GeodesicTransport.chartTransition x₁ s.anchor zS = eM d.v := by
    change extChartAt I s.anchor ((extChartAt I x₁).symm zS) = eM d.v
    rw [hsymmS]
    simpa [eM] using d.source_coordinate
  have hγnewSolves : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt γnew
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₁) (γnew t)) t := by
    simpa [γnew] using geodesicGermChartSolution_eventually_solves g x₁ u
  have hγnewPos :
      Tendsto (fun t : ℝ => (γnew t).1) (nhds 0) (nhds zS) := by
    simpa [γnew, zS] using geodesicGermChartSolution_fst_tendsto g x₁ u
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
  have hnewCutN :
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
        nhds (GeodesicTransport.chartTransition x₁ s.anchor zS) := by
    rw [hinnerPoint]
    exact hcutS
  have holdCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) s.anchor
        (GeodesicTransport.chartTransition x₁ s.anchor q) = 1} ∈
          nhds zS :=
    hinnerDeriv.continuousAt.preimage_mem_nhds holdCutAt
  have hγoldSolves : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt γold
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g s.anchor) (γold t)) t := by
    simpa [γold] using
      GeodesicTransport.chartTransitionState_eventually_solves_of_initial_nhds
        g x₁ s.anchor hγnewSolves hγnewPos hnewTargetN holdSourceN
          hnewCutN holdCutN
  have hγold0fst : (γold 0).1 = eM d.v := by
    change GeodesicTransport.chartTransition x₁ s.anchor (γnew 0).1 = eM d.v
    dsimp [γnew]
    rw [(GeodesicTransport.geodesicGermChartSolution_spec g x₁ u).1]
    exact hinnerPoint
  have hγoldPos :
      Tendsto (fun t : ℝ => (γold t).1) (nhds 0) (nhds (eM d.v)) := by
    have hcont := hγoldSolves.self_of_nhds.continuousAt.fst
    change Tendsto (fun t : ℝ => (γold t).1) (nhds 0)
      (nhds (γold 0).1) at hcont
    rwa [hγold0fst] at hcont
  have heMdvTarget : eM d.v ∈ eM.target := eM.map_source hdvsrc
  have hγoldTarget : ∀ᶠ t in nhds (0 : ℝ), (γold t).1 ∈ eM.target :=
    hγoldPos.eventually (eM.open_target.mem_nhds heMdvTarget)
  have hvTendsto :
      Tendsto (fun t : ℝ => eM.symm (γold t).1) (nhds 0) (nhds d.v) := by
    have hcomp := (eM.continuousAt_symm heMdvTarget).tendsto.comp hγoldPos
    change Tendsto (fun t : ℝ => eM.symm (γold t).1) (nhds 0)
      (nhds (eM.symm (eM d.v))) at hcomp
    rw [eM.left_inv hdvsrc] at hcomp
    exact hcomp
  have hdBall : d.v ∈ ball (0 : E) rho := by
    simpa [mem_ball, dist_eq_norm] using hd
  have hvNorm : ∀ᶠ t in nhds (0 : ℝ), ‖eM.symm (γold t).1‖ < rho := by
    have hmem := hvTendsto.eventually (isOpen_ball.mem_nhds hdBall)
    simpa [mem_ball, dist_eq_norm] using hmem
  have hdCompl : d.v ∈ ({0} : Set E)ᶜ := by
    simpa using hdne
  have hvNe : ∀ᶠ t in nhds (0 : ℝ), eM.symm (γold t).1 ≠ 0 := by
    have hmem := hvTendsto.eventually (isClosed_singleton.isOpen_compl.mem_nhds hdCompl)
    simpa using hmem
  have hF₂ : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 2 F (γold t).1 := by
    filter_upwards [hγoldTarget, hvNorm, hvNe] with t hqt hvnorm hvne
    let vt : E := eM.symm (γold t).1
    have hright : eM vt = (γold t).1 := eM.right_inv hqt
    rcases htransition vt (by simpa [vt] using hvnorm) (by simpa [vt] using hvne) with
      ⟨_vsrc, _Lvsrc, hF₂t, _hFstrict, _hcut0, _hcut1, _htrans⟩
    simpa [F, eM, hright] using hF₂t
  have hFtrans : ∀ᶠ t in nhds (0 : ℝ),
      GeodesicTransport.chartChristoffelField
          roundSphereMetric3 s.target (F (γold t).1)
          ((fderiv ℝ F (γold t).1) (γold t).2)
          ((fderiv ℝ F (γold t).1) (γold t).2) =
        (fderiv ℝ F (γold t).1)
            (GeodesicTransport.chartChristoffelField
              g s.anchor (γold t).1 (γold t).2 (γold t).2) -
          ((fderiv ℝ (fun q : E => fderiv ℝ F q) (γold t).1)
            (γold t).2) (γold t).2 := by
    filter_upwards [hγoldTarget, hvNorm, hvNe] with t hqt hvnorm hvne
    let vt : E := eM.symm (γold t).1
    have hright : eM vt = (γold t).1 := eM.right_inv hqt
    rcases htransition vt (by simpa [vt] using hvnorm) (by simpa [vt] using hvne) with
      ⟨_vsrc, _Lvsrc, _hF₂t, _hFstrict, _hcut0, _hcut1, htranst⟩
    simpa [F, eM, hright] using htranst (γold t).2
  have hμSolves : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt μ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField roundSphereMetric3 s.target)
          (μ t)) t := by
    simpa [μ] using
      FTransitionGeodesicMap.mappedState_eventually_solves_of_F_transition
        F
        (GeodesicTransport.chartChristoffelField g s.anchor)
        (GeodesicTransport.chartChristoffelField roundSphereMetric3 s.target)
        hγoldSolves hF₂ hFtrans
  let qT : E := extChartAt I s.target (s.map x₁)
  let zT : E := extChartAt I (s.map x₁) (s.map x₁)
  have hFendpoint : F (eM d.v) = eS (s.alignment d.v) := by
    change eS (s.alignment (eM.symm (eM d.v))) = eS (s.alignment d.v)
    rw [eM.left_inv hdvsrc]
  have hFpoint : F (eM d.v) = qT := by
    rw [hFendpoint]
    simpa [qT, eS] using d.target_coordinate.symm
  have hμ0fst : (μ 0).1 = qT := by
    change F (γold 0).1 = qT
    rw [hγold0fst]
    exact hFpoint
  have hμPos : Tendsto (fun t : ℝ => (μ t).1) (nhds 0) (nhds qT) := by
    have hcont := hμSolves.self_of_nhds.continuousAt.fst
    change Tendsto (fun t : ℝ => (μ t).1) (nhds 0) (nhds (μ 0).1) at hcont
    rwa [hμ0fst] at hcont
  have hqTtarget : qT ∈ (extChartAt I s.target).target := by
    simpa [qT] using
      (extChartAt I s.target).map_source d.target_mem_oldChart
  have hsymmT : (extChartAt I s.target).symm qT = s.map x₁ := by
    simpa [qT] using
      (extChartAt I s.target).left_inv d.target_mem_oldChart
  have houterPoint :
      GeodesicTransport.chartTransition s.target (s.map x₁) qT = zT := by
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
      {q : E | GeodesicTransport.cutoff (n := 3) s.target q = 1} ∈ nhds qT := by
    rw [← hFpoint]
    exact hcutT
  have houterDeriv :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      s.target (s.map x₁) hqTtarget (by
        rw [hsymmT]
        exact mem_extChartAt_source (s.map x₁))
  have hnewCutAt :
      {q : E | GeodesicTransport.cutoff (n := 3) (s.map x₁) q = 1} ∈
        nhds (GeodesicTransport.chartTransition s.target (s.map x₁) qT) := by
    rw [houterPoint]
    simpa [zT] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := 3) (s.map x₁))
  have hnewCutN :
      {q : E | GeodesicTransport.cutoff (n := 3) (s.map x₁)
        (GeodesicTransport.chartTransition s.target (s.map x₁) q) = 1} ∈
          nhds qT :=
    houterDeriv.continuousAt.preimage_mem_nhds hnewCutAt
  have hδSolves : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt δ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField
            roundSphereMetric3 (s.map x₁)) (δ t)) t := by
    simpa [δ] using
      GeodesicTransport.chartTransitionState_eventually_solves_of_initial_nhds
        roundSphereMetric3 s.target (s.map x₁) hμSolves hμPos
          holdTargetN hnewSourceN holdTargetCutN hnewCutN
  have hηSolves : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt η
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField
            roundSphereMetric3 (s.map x₁)) (η t)) t := by
    simpa [η] using
      geodesicGermChartSolution_eventually_solves
        (M := RoundSphere3) roundSphereMetric3 (s.map x₁) (d.alignment u)
  let inner : E → E := GeodesicTransport.chartTransition x₁ s.anchor
  let outer : E → E :=
    GeodesicTransport.chartTransition s.target (s.map x₁)
  have hinnerCanonical :
      HasFDerivAt inner (fderiv ℝ inner zS) zS := by
    exact (by simpa [inner] using hinnerDeriv.differentiableAt.hasFDerivAt)
  have hFCanonical0 :
      HasFDerivAt F (fderiv ℝ F (eM d.v)) (eM d.v) := by
    have hFcont : ContDiffAt ℝ 2 F (eM d.v) := by
      simpa [F, eM] using hF₂d
    have hdiff : DifferentiableAt ℝ F (eM d.v) :=
      hFcont.differentiableAt (by norm_num)
    exact hdiff.hasFDerivAt
  have hFCanonical :
      HasFDerivAt F (fderiv ℝ F (inner zS)) (inner zS) := by
    have hpoint : inner zS = eM d.v := by simpa [inner] using hinnerPoint
    rw [hpoint]
    exact hFCanonical0
  have houterCanonical0 :
      HasFDerivAt outer (fderiv ℝ outer qT) qT := by
    exact (by simpa [outer] using houterDeriv.differentiableAt.hasFDerivAt)
  have hFinner : F (inner zS) = qT := by
    rw [show inner zS = eM d.v by simpa [inner] using hinnerPoint]
    exact hFpoint
  have houterCanonical :
      HasFDerivAt outer (fderiv ℝ outer (F (inner zS)))
        (F (inner zS)) := by
    rw [hFinner]
    exact houterCanonical0
  have hmiddle := hFCanonical.comp zS hinnerCanonical
  have htotal := houterCanonical.comp zS hmiddle
  change HasFDerivAt
    (DifferentialInducedSuccessor.reanchoredChartMap s x₁)
    ((fderiv ℝ outer (F (inner zS))).comp
      ((fderiv ℝ F (inner zS)).comp (fderiv ℝ inner zS))) zS at htotal
  have hDcomp :
      (fderiv ℝ outer (F (inner zS))).comp
          ((fderiv ℝ F (inner zS)).comp (fderiv ℝ inner zS)) =
        (d.alignment.toContinuousLinearEquiv : E →L[ℝ] E) :=
    htotal.fderiv.symm.trans (by
      simpa [zS] using d.hasFDerivAt_reanchoredChartMap.fderiv)
  have hδ0fst : (δ 0).1 = zT := by
    change GeodesicTransport.chartTransition s.target (s.map x₁) (μ 0).1 = zT
    rw [hμ0fst]
    exact houterPoint
  have hδ0snd : (δ 0).2 = d.alignment u := by
    have hu := congrArg (fun D : E →L[ℝ] E => D u) hDcomp
    have hsymmS' : (chartAt E x₁).symm zS = x₁ := by
      simpa [extChartAt_coe] using hsymmS
    simpa [δ, μ, γold, γnew, inner, outer,
      FTransitionGeodesicMap.mappedState,
      GeodesicTransport.chartTransitionState,
      (GeodesicTransport.geodesicGermChartSolution_spec g x₁ u).1,
      hsymmS', zS] using hu
  have hδ0 : δ 0 = (zT, d.alignment u) := Prod.ext hδ0fst hδ0snd
  have hη0 : η 0 = (zT, d.alignment u) := by
    simpa [η, zT] using
      (GeodesicTransport.geodesicGermChartSolution_spec
        roundSphereMetric3 (s.map x₁) (d.alignment u)).1
  have hδη : δ =ᶠ[nhds (0 : ℝ)] η :=
    geodesicFlowField_eventuallyEq_of_contDiffAt
      (GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiffAt
        roundSphereMetric3 (s.map x₁) (d.alignment u))
      hδ0 hη0 hδSolves hηSolves
  filter_upwards [hδη] with t ht
  have hfst := congrArg Prod.fst ht
  simpa [δ, μ, γold, γnew, η,
    FTransitionGeodesicMap.mappedState,
    GeodesicTransport.chartTransitionState,
    DifferentialInducedSuccessor.reanchoredChartMap] using hfst

/--
On one uniform punctured predecessor normal ball, the predecessor Cartan chart
map carries every chosen geodesic germ through a differential-induced anchor
to the chosen round-sphere geodesic germ with the induced initial velocity.

The conclusion is stated in the new target chart.  Its left side is the old
Cartan chart map conjugated from the new source and target charts, while its
right side is the canonical target chart-geodesic position.
-/
theorem exists_reanchoredChartMap_geodesicGerm_naturality_radius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
          (fun t : ℝ =>
            DifferentialInducedSuccessor.reanchoredChartMap s x₁
              (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =ᶠ[nhds (0 : ℝ)]
          (fun t : ℝ =>
            (GeodesicTransport.geodesicGermChartSolution
              roundSphereMetric3 (s.map x₁) (d.alignment u) t).1) := by
  rcases
      UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law
        (g := g) hcurv s.anchor s.target s.alignment with
    ⟨rho, hrho, _Afield, _Bfield, DF, _hDF, htransition⟩
  refine ⟨rho, hrho, ?_⟩
  exact reanchoredChartMap_geodesicGerm_naturality_of_transition
    g s rho DF htransition

/--
For fixed source and target anchors, one positive predecessor-normal radius
supports differential-successor geodesic-germ naturality for every tangent
alignment chosen at those anchors.
-/
theorem exists_uniform_reanchoredChartMap_geodesicGerm_naturality_radius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x0 : M)
    (p0 : RoundSphere3) :
    ∃ rho > (0 : ℝ),
      ∀ L : CartanMap.TangentAlignment g x0 p0,
        ∀ {x₁ : M}
            (d : DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk x0 p0 L) x₁),
          ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
            (fun t : ℝ =>
              DifferentialInducedSuccessor.reanchoredChartMap
                (CartanChain.ChainState.mk x0 p0 L) x₁
                (GeodesicTransport.geodesicGermChartSolution g x₁ u t).1) =ᶠ[nhds (0 : ℝ)]
            (fun t : ℝ =>
              (GeodesicTransport.geodesicGermChartSolution
                roundSphereMetric3
                ((CartanChain.ChainState.mk x0 p0 L).map x₁)
                (d.alignment u) t).1) := by
  rcases
      UniformTangentAlignmentGeodesicTransition.exists_uniform_cartanChartMap_chartChristoffelField_self_F_transition_law
        (g := g) hcurv x0 p0 with
    ⟨rho, hrho, htransitionAll⟩
  refine ⟨rho, hrho, ?_⟩
  intro L
  rcases htransitionAll L with
    ⟨_Afield, _Bfield, DF, _hDF, htransition⟩
  exact reanchoredChartMap_geodesicGerm_naturality_of_transition
    g (CartanChain.ChainState.mk x0 p0 L) rho DF htransition

/--
Manifold-valued form of differential-induced geodesic-germ naturality.

The predecessor Cartan map itself, rather than merely its conjugated chart
expression, carries every source geodesic germ based at the new anchor to the
round-sphere germ with initial velocity given by the induced differential.
The same punctured predecessor-normal-ball radius works for every successor
datum and every new-chart velocity.
-/
theorem exists_map_geodesicGermAt_naturality_radius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 → ∀ u : E,
          (fun t : ℝ =>
            s.map (GeodesicTransport.geodesicGermAt g x₁ u t)) =ᶠ[nhds (0 : ℝ)]
          (fun t : ℝ =>
            GeodesicTransport.geodesicGermAt
              roundSphereMetric3 (s.map x₁) (d.alignment u) t) := by
  rcases exists_reanchoredChartMap_geodesicGerm_naturality_radius
      g hcurv s with ⟨rho, hrho, hcoord⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd hdne u
  let γs : ℝ → M :=
    GeodesicTransport.geodesicGermAt g x₁ u
  let γt : ℝ → RoundSphere3 :=
    GeodesicTransport.geodesicGermAt
      roundSphereMetric3 (s.map x₁) (d.alignment u)
  let η : ℝ → E × E :=
    GeodesicTransport.geodesicGermChartSolution
      roundSphereMetric3 (s.map x₁) (d.alignment u)
  have hsourceTendsto : Tendsto γs (nhds (0 : ℝ)) (nhds x₁) := by
    have hz : extChartAt I x₁ x₁ ∈ (extChartAt I x₁).target :=
      (extChartAt I x₁).map_source (mem_extChartAt_source x₁)
    have hpos := geodesicGermChartSolution_fst_tendsto g x₁ u
    have hsymm := continuousAt_extChartAt_symm'' hz
    have hsymmT : Tendsto (extChartAt I x₁).symm
        (nhds (extChartAt I x₁ x₁))
        (nhds ((extChartAt I x₁).symm (extChartAt I x₁ x₁))) := hsymm
    rw [(extChartAt I x₁).left_inv (mem_extChartAt_source x₁)] at hsymmT
    simpa [γs, GeodesicTransport.geodesicGermAt] using hsymmT.comp hpos
  have hsourceOld : ∀ᶠ t in nhds (0 : ℝ), γs t ∈ s.germ.source :=
    hsourceTendsto.eventually
      (s.germ.open_source.mem_nhds d.anchor_mem_predecessor_source)
  have hmapTendsto :
      Tendsto (fun t : ℝ => s.map (γs t)) (nhds 0) (nhds (s.map x₁)) := by
    have hscont := s.germ.continuousAt d.anchor_mem_predecessor_source
    have hsT : Tendsto s.germ (nhds x₁) (nhds (s.germ x₁)) := hscont
    have hcomp := hsT.comp hsourceTendsto
    simpa only [Function.comp_apply, CartanChain.ChainState.germ,
      CartanChain.ChainState.map] using hcomp
  have hmapNewChart : ∀ᶠ t in nhds (0 : ℝ),
      s.map (γs t) ∈ (extChartAt I (s.map x₁)).source :=
    hmapTendsto.eventually
      (extChartAt_source_mem_nhds (s.map x₁))
  have htargetNewChart : ∀ᶠ t in nhds (0 : ℝ),
      γt t ∈ (extChartAt I (s.map x₁)).source := by
    simpa [γt] using
      GeodesicTransport.geodesicGermAt_eventually_mem_source
        roundSphereMetric3 (s.map x₁) (d.alignment u)
  have htargetCoord :
      (fun t : ℝ => extChartAt I (s.map x₁) (γt t)) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ => (η t).1) := by
    have hmem :=
      (GeodesicTransport.geodesicGermChartSolution_spec
        roundSphereMetric3 (s.map x₁) (d.alignment u)).2.2.2
    filter_upwards [hmem] with t ht
    exact (extChartAt I (s.map x₁)).right_inv ht.1
  have hmapCoord :
      (fun t : ℝ => extChartAt I (s.map x₁) (s.map (γs t))) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ => (η t).1) := by
    simpa [γs, η] using hcoord d hd hdne u
  have hchartEq :
      (fun t : ℝ => extChartAt I (s.map x₁) (s.map (γs t))) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ => extChartAt I (s.map x₁) (γt t)) :=
    hmapCoord.trans htargetCoord.symm
  filter_upwards [hsourceOld, hmapNewChart, htargetNewChart, hchartEq] with
    t _htOld htMap htTarget htEq
  exact (extChartAt I (s.map x₁)).injOn htMap htTarget htEq

/--
Right-ray exponential naturality obtained from the manifold geodesic-germ
identity and the fixed-time exponential ray law.

For each differential-induced successor datum in the uniform punctured ball,
there is one positive velocity radius on which all source directions and their
aligned target directions satisfy exponential naturality as germs from the
nonnegative side.  This is the strongest conclusion exported by the current
`expAt` interface without a closed-interval PL-flow/germ identification.
-/
theorem exists_map_expAt_ray_naturality_radius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (s : CartanChain.ChainState g) :
    ∃ rho > (0 : ℝ),
      ∀ {x₁ : M} (d : DifferentialInducedSuccessor.Data s x₁),
        ‖d.v‖ < rho → d.v ≠ 0 →
          ∃ tau > (0 : ℝ), ∃ delta > (0 : ℝ), ∀ u : E, ‖u‖ < delta →
            (fun t : ℝ =>
              s.map (GeodesicTransport.expAt g x₁ (t • u))) =ᶠ[
                nhdsWithin (0 : ℝ) (Ici 0)]
            (fun t : ℝ =>
              GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
                (t • d.alignment u)) := by
  rcases exists_map_geodesicGermAt_naturality_radius g hcurv s with
    ⟨rho, hrho, hgerm⟩
  refine ⟨rho, hrho, ?_⟩
  intro x₁ d hd hdne
  rcases GeodesicTransport.expAt_eventually_eq_geodesicGermAt_nhdsGE
      g x₁ with ⟨taus, htaus, deltas, hdeltas, hsray⟩
  rcases GeodesicTransport.expAt_eventually_eq_geodesicGermAt_nhdsGE
      roundSphereMetric3 (s.map x₁) with
    ⟨taut, htaut, deltat, hdeltat, htray⟩
  let D : E →L[ℝ] E := d.alignment.toContinuousLinearEquiv
  let delta : ℝ := min deltas (deltat / (‖D‖ + 1))
  have hden : 0 < ‖D‖ + 1 := by positivity
  have hquot : 0 < deltat / (‖D‖ + 1) := div_pos hdeltat hden
  have hdelta : 0 < delta := by
    exact lt_min hdeltas hquot
  refine ⟨min taus taut, lt_min htaus htaut, delta, hdelta, ?_⟩
  intro u hu
  have hus : ‖u‖ < deltas := hu.trans_le (min_le_left _ _)
  have huquot : ‖u‖ < deltat / (‖D‖ + 1) :=
    hu.trans_le (min_le_right _ _)
  have hDu_le : ‖d.alignment u‖ ≤ ‖D‖ * ‖u‖ := by
    simpa [D] using D.le_opNorm u
  have hD_nonneg : 0 ≤ ‖D‖ := norm_nonneg D
  have hDu : ‖d.alignment u‖ < deltat := by
    have hmul : ‖D‖ * ‖u‖ < ‖D‖ * (deltat / (‖D‖ + 1)) ∨ ‖D‖ = 0 := by
      rcases hD_nonneg.eq_or_lt with hzero | hpos
      · exact Or.inr hzero.symm
      · exact Or.inl (mul_lt_mul_of_pos_left huquot hpos)
    rcases hmul with hmul | hzero
    · refine hDu_le.trans_lt (hmul.trans_le ?_)
      have hfrac_le_one : ‖D‖ / (‖D‖ + 1) ≤ 1 := by
        rw [div_le_one hden]
        linarith
      calc
        ‖D‖ * (deltat / (‖D‖ + 1)) =
            deltat * (‖D‖ / (‖D‖ + 1)) := by ring
        _ ≤ deltat * 1 := mul_le_mul_of_nonneg_left hfrac_le_one hdeltat.le
        _ = deltat := mul_one _
    · have hDuZero : ‖d.alignment u‖ = 0 := by
        apply le_antisymm
        · simpa [hzero] using hDu_le
        · exact norm_nonneg _
      linarith
  have hsmap :
      (fun t : ℝ => s.map (GeodesicTransport.expAt g x₁ (t • u))) =ᶠ[
          nhdsWithin (0 : ℝ) (Ici 0)]
        (fun t : ℝ =>
          s.map (GeodesicTransport.geodesicGermAt g x₁ u t)) := by
    filter_upwards [hsray u hus] with t ht
    rw [ht]
  have hgerm' := (hgerm d hd hdne u).filter_mono
    (show nhdsWithin (0 : ℝ) (Ici 0) ≤ nhds 0 from inf_le_left)
  exact hsmap.trans (hgerm'.trans (htray (d.alignment u) hDu).symm)

end DifferentialSuccessorNaturality
end Poincare
