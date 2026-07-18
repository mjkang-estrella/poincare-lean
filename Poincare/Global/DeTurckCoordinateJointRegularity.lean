import Poincare.Global.MetricFlowJointScalarTraceZoneBridge
import Poincare.Global.DeTurckLocalFrameRegularity

/-!
# Joint regularity of the coordinate DeTurck contraction

The coordinate DeTurck vector field is the inverse-metric trace of the
difference between the evolving and background Christoffel fields.  This file
first records that finite-dimensional contraction as an honest model-space
field and proves its joint regularity directly from the joint metric-entry
regularity already available for the two metrics.

The subsequent geometric identification with the intrinsic DeTurck field is
kept separate: the theorem here is the analytic contraction needed by that
bridge and contains no hidden choice of a pointwise tangent basis.
-/

noncomputable section

open Bundle FiberBundle Filter
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DeTurckCoordinateJointRegularity

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n
local notation "I" => closedSmoothModelWithCorners n
local notation "TM" => (TangentSpace I : M → Type _)

/-- The chart coordinate of one intrinsic connection-difference value is the
difference of the two chart Christoffel fields throughout the cutoff-one
zone.  The ordinary derivative of the transported section cancels between
the two connections. -/
theorem chartInverseTangentEquiv_deTurckConnectionDifferenceAt_zone
    (g bg : ClosedSmoothRiemannianMetric n M) (x : M) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1)
    (u w : E) :
    let y : M := (extChartAt I x).symm z
    let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
    e.symm (deTurckConnectionDifferenceAt g bg y (e u) (e w)) =
      GeodesicTransport.chartChristoffelField g x z w u -
        GeodesicTransport.chartChristoffelField bg x z w u := by
  dsimp only
  let y : M := (extChartAt I x).symm z
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let U : ∀ q : M, TM q := extend E (x := y) (e u)
  let S : ∀ q : M, TM q := extend E (x := y) (e w)
  let Vg : ∀ q : M, TM q := fun q ↦ g.leviCivita S q (U q)
  let Vb : ∀ q : M, TM q := fun q ↦ bg.leviCivita S q (U q)
  let V : ∀ q : M, TM q := fun q ↦ Vg q - Vb q
  let Sc : E → E :=
    CovariantDerivative.chartTransportedLeviCivitaSection x S
  let Uc : E → E :=
    CovariantDerivative.chartTransportedLeviCivitaSection x U
  have hy : y ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hzchart : extChartAt I x y = z := by
    simpa [y] using (extChartAt I x).right_inv hz
  have hzchart' : (chartAt E x) y = z := by
    simpa [extChartAt_coe] using hzchart
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z := by
    exact chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hroundtrip : ∀ A : ∀ q : M, TM q,
      e (CovariantDerivative.chartTransportedLeviCivitaSection x A z) =
        A y := by
    intro A
    have happly :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := A) (y := y) hy
    rw [hzchart] at happly
    rw [happly]
    have hround :=
      CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
        (x₀ := x) hy (A y)
    have hround' :
        ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z
            ((mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) y) (A y)) =
          A y := by
      rw [← hzchart']
      simpa [ChartCurvatureBridgeZone.chartInverseTangent, extChartAt_coe] using hround
    calc
      e ((mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) y) (A y)) =
          ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z
            ((mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) y) (A y)) := by
        exact congrArg
          (fun L : E →L[ℝ] E ↦
            L ((mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) y) (A y))) he
      _ = A y := hround'
  have hSy : S y = e w := by simp [S]
  have hUy : U y = e u := by simp [U]
  have hSc : Sc z = w := by
    apply e.injective
    rw [show e (Sc z) = S y by simpa [Sc] using hroundtrip S]
    rw [hSy]
  have hUc : Uc z = u := by
    apply e.injective
    rw [show e (Uc z) = U y by simpa [Uc] using hroundtrip U]
    rw [hUy]
  have hVy : V y = deTurckConnectionDifferenceAt g bg y (e u) (e w) := by
    simp [V, Vg, Vb, U, S, deTurckConnectionDifferenceAt]
  have htransportV :
      CovariantDerivative.chartTransportedLeviCivitaSection x V z =
        e.symm (deTurckConnectionDifferenceAt g bg y (e u) (e w)) := by
    apply e.injective
    rw [hroundtrip V, e.apply_symm_apply, hVy]
  have hsplit :
      CovariantDerivative.chartTransportedLeviCivitaSection x V z =
        CovariantDerivative.chartTransportedLeviCivitaSection x Vg z -
          CovariantDerivative.chartTransportedLeviCivitaSection x Vb z := by
    have hVapp :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := V) (y := y) hy
    have hgapp :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := Vg) (y := y) hy
    have hbapp :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := Vb) (y := y) hy
    rw [hzchart] at hVapp hgapp hbapp
    rw [hVapp, hgapp, hbapp]
    simp [V, map_sub]
  have hSdiff : MDiffAtTangentField S y := by
    simpa [S, MDiffAtTangentField] using
      (FiberBundle.mdifferentiableAt_extend
        (M := M) (V := TM) (x := y) I E (e w))
  have hχone' : ∀ᶠ z' in nhds (extChartAt I x y),
      GeodesicTransport.cutoff (n := n) x z' = 1 := by
    rw [hzchart]
    exact hχone
  have hgNat :=
    ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
      (g := g) (x₀ := x) (y := y) hy hχone' S U hSdiff
  have hbNat :=
    ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
      (g := bg) (x₀ := x) (y := y) hy hχone' S U hSdiff
  rw [hzchart] at hgNat hbNat
  rw [← htransportV, hsplit, hgNat, hbNat]
  change
    (fderiv ℝ Sc z (Uc z) +
        GeodesicTransport.chartChristoffelField g x z (Sc z) (Uc z)) -
      (fderiv ℝ Sc z (Uc z) +
        GeodesicTransport.chartChristoffelField bg x z (Sc z) (Uc z)) =
      GeodesicTransport.chartChristoffelField g x z w u -
        GeodesicTransport.chartChristoffelField bg x z w u
  rw [hSc, hUc]
  abel

/--
The inverse-metric contraction of the difference of the evolving and
background anchor-chart Christoffel fields.

The fixed model basis is used only to write the finite trace.  The evolving
inverse metric raises the first coordinate covector, while the two
Christoffel fields provide the connection difference.
-/
noncomputable def anchorChartDeTurckContractionFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) : E :=
  let b := Module.finBasis ℝ E
  ∑ i,
    let raised := (anchorBlendedMetricFlow gt x t z).inverse
      (LinearMap.toContinuousLinearMap (b.coord i))
    anchorChartChristoffelFieldFlow gt x t z raised (b i) -
      anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x t z raised (b i)

/-- Throughout the cutoff-one part of an honest anchor chart, the explicit
inverse-metric Christoffel contraction is the coordinate representative of
the intrinsic DeTurck vector field. -/
theorem anchorChartDeTurckContractionFlow_eq_chartCoordinateTangentField_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1) :
    anchorChartDeTurckContractionFlow gt bg x t z =
      chartCoordinateTangentField x (deTurckVectorField gt bg t) z := by
  classical
  let g := gt t
  let y : M := (extChartAt I x).symm z
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let B := chartTangentBasisAt (n := n) (M := M) x hz
  let G := anchorBlendedMetricFlow gt x t z
  let phi : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  let raised : Fin (Module.finrank ℝ E) → E := fun i ↦
    G.inverse (phi i)
  let W : ∀ q : M, TM q := deTurckVectorField gt bg t
  have hχ : GeodesicTransport.cutoff (n := n) x z = 1 :=
    hχone.self_of_nhds
  have hy : y ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hzchart : extChartAt I x y = z := by
    simpa [y] using (extChartAt I x).right_inv hz
  have he : (e : E →L[ℝ] E) =
      ChartCurvatureBridgeZone.chartInverseTangent (n := n) x z := by
    exact chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hBasis : ∀ i, B i = e (b i) := by
    intro i
    rw [show B = b.map e.toLinearEquiv by
      simpa [B, b, e] using
        chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv x hz]
    rfl
  have hRaised : ∀ i,
      e (raised i) = metricDualVectorAt g y (B.coord i) := by
    intro i
    simpa [raised, G, phi, g, y, e, B, b] using
      chartInverseTangentEquiv_anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt_zone
        gt x t hz hχ i
  have hCoordinate :
      e (chartCoordinateTangentField x W z) = W y := by
    have hcoordinate :=
      chartCoordinateTangentField_apply_chart_eq_transported x W hy
    have htransport :=
      CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
        («I» := I) (x₀ := x) (σ := W) (y := y) hy
    rw [hzchart] at hcoordinate htransport
    rw [hcoordinate, htransport]
    change (e : E →L[ℝ] E)
      ((mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I x) y) (W y)) = W y
    rw [he]
    have hround :=
      CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
        (x₀ := x) hy (W y)
    rw [hzchart] at hround
    simpa [ChartCurvatureBridgeZone.chartInverseTangent,
      extChartAt_coe] using hround
  have hsum :
      e (anchorChartDeTurckContractionFlow gt bg x t z) =
        deTurckVectorFieldAt g bg y := by
    unfold anchorChartDeTurckContractionFlow
    rw [map_sum]
    calc
      ∑ i, e
          (anchorChartChristoffelFieldFlow gt x t z (raised i) (b i) -
            anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x t z
              (raised i) (b i)) =
        ∑ i, deTurckConnectionDifferenceAt g bg y (B i)
          (metricDualVectorAt g y (B.coord i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hbridge :=
          chartInverseTangentEquiv_deTurckConnectionDifferenceAt_zone
            g bg x hz hχone (b i) (raised i)
        have hbridge' := congrArg e hbridge
        calc
          e
              (anchorChartChristoffelFieldFlow gt x t z (raised i) (b i) -
                anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x t z
                  (raised i) (b i)) =
              deTurckConnectionDifferenceAt g bg y (e (b i))
                (e (raised i)) := by
            simpa [anchorChartChristoffelFieldFlow, g, y, e] using hbridge'.symm
          _ = deTurckConnectionDifferenceAt g bg y (B i)
                (metricDualVectorAt g y (B.coord i)) := by
            rw [hBasis i, hRaised i]
      _ = deTurckVectorFieldAt g bg y := by
        symm
        exact deTurckVectorFieldAt_eq_trace_in_basis g bg y B
  apply e.injective
  exact hsum.trans (by
    change W y = e (chartCoordinateTangentField x W z)
    exact hCoordinate.symm)

/-- Joint `C³` metric entries for the evolving and static background metrics
make their coordinate DeTurck contraction jointly `C²` at the anchor. -/
theorem anchorChartDeTurckContractionFlow_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 2
      (Function.uncurry (anchorChartDeTurckContractionFlow gt bg x))
      (t₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have hbg : MetricEntriesJointContDiffAt (fun _ : ℝ ↦ bg) t₀ x 3 :=
    metricEntriesJointContDiffAt_const bg t₀ x
  have hGammaG : ContDiffAt ℝ 2
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries hgt
  have hGammaB : ContDiffAt ℝ 2
      (Function.uncurry
        (anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries hbg
  have hInv : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ (anchorBlendedMetricFlow gt x p.1 p.2).inverse)
      (t₀, q) := by
    simpa [q] using
      anchorBlendedMetricFlow_inverse_jointContDiffAt_two_of_metricEntries hgt
  unfold anchorChartDeTurckContractionFlow
  apply ContDiffAt.sum
  intro i _hi
  let coord : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (b.coord i)
  have hcoord : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ coord) (t₀, q) :=
    contDiffAt_const
  have hraised : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦
        (anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (t₀, q) :=
    hInv.clm_apply hcoord
  have hbi : ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ b i) (t₀, q) :=
    contDiffAt_const
  have hGammaGi : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦ anchorChartChristoffelFieldFlow gt x p.1 p.2
        ((anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (b i))
      (t₀, q) := by
    simpa [Function.uncurry] using
      (hGammaG.clm_apply hraised).clm_apply hbi
  have hGammaBi : ContDiffAt ℝ 2
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow (fun _ : ℝ ↦ bg) x p.1 p.2
          ((anchorBlendedMetricFlow gt x p.1 p.2).inverse coord) (b i))
      (t₀, q) := by
    simpa [Function.uncurry] using
      (hGammaB.clm_apply hraised).clm_apply hbi
  simpa [Function.uncurry, q, coord] using hGammaGi.sub hGammaBi

/-- Joint `C³` metric entries make the actual coordinate representative of
the intrinsic DeTurck vector field jointly `C²` at the preferred-chart
anchor.  The proof transfers regularity from the explicit finite contraction
through their cutoff-zone equality on a genuine product neighborhood. -/
theorem deTurckChartCoordinateField_jointContDiffAt_two_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {bg : ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hgt : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContDiffAt ℝ 2
      (Function.uncurry (fun t z ↦
        chartCoordinateTangentField x (deTurckVectorField gt bg t) z))
      (t₀, extChartAt I x x) := by
  let q : E := extChartAt I x x
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have htargetMem : (extChartAt I x).target ∈ nhds q := by
    exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have honeOpen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have honeMem : oneLocus ∈ nhds q := by
    apply honeOpen.mem_nhds
    simpa [oneLocus, q] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have htargetPair :
      ∀ᶠ p : ℝ × E in nhds (t₀, q), p.2 ∈ (extChartAt I x).target :=
    continuousAt_snd.eventually htargetMem
  have honePair :
      ∀ᶠ p : ℝ × E in nhds (t₀, q), p.2 ∈ oneLocus :=
    continuousAt_snd.eventually honeMem
  have heq :
      Function.uncurry (fun t z ↦
          chartCoordinateTangentField x (deTurckVectorField gt bg t) z)
        =ᶠ[nhds (t₀, q)]
      Function.uncurry (anchorChartDeTurckContractionFlow gt bg x) := by
    filter_upwards [htargetPair, honePair] with p hpTarget hpOne
    have hχone : ∀ᶠ z' in nhds p.2,
        GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    simpa only [Function.uncurry] using
      (anchorChartDeTurckContractionFlow_eq_chartCoordinateTangentField_zone
        gt bg x p.1 hpTarget hχone).symm
  have hcontraction :=
    anchorChartDeTurckContractionFlow_jointContDiffAt_two_of_metricEntries
      (bg := bg) hgt
  exact (by
    simpa [q] using hcontraction.congr_of_eventuallyEq heq)

/-- At the preferred-chart anchor, the coordinate contraction is exactly the
coordinate representative of the intrinsic DeTurck vector field. -/
theorem anchorChartDeTurckContractionFlow_apply_anchor
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M) (x : M) (t : ℝ) :
    anchorChartDeTurckContractionFlow gt bg x t (extChartAt I x x) =
      chartCoordinateTangentField x (deTurckVectorField gt bg t)
        (extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let W : ∀ y : M, TangentSpace I y := deTurckVectorField gt bg t
  have hcoordinate :=
    chartCoordinateTangentField_apply_chart_eq_transported
      x W (mem_extChartAt_source x)
  have htransport :=
    CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x) (σ := W) (y := x)
      (mem_extChartAt_source x)
  rw [mfderiv_extChartAt_self] at htransport
  have hcoordinateValue :
      chartCoordinateTangentField x W (extChartAt I x x) = W x := by
    rw [hcoordinate, htransport]
    rfl
  rw [show chartCoordinateTangentField x (deTurckVectorField gt bg t)
      (extChartAt I x x) = W x by exact hcoordinateValue]
  change anchorChartDeTurckContractionFlow gt bg x t (extChartAt I x x) =
    deTurckVectorFieldAt (gt t) bg x
  rw [deTurckVectorFieldAt_eq_trace_in_basis (gt t) bg x b]
  unfold anchorChartDeTurckContractionFlow
  apply Finset.sum_congr rfl
  intro i _hi
  rw [anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt]
  change
    anchorChartChristoffelFlow gt x t (extChartAt I x x) (b i)
          (metricDualVectorAt (gt t) x (b.coord i)) -
        anchorChartChristoffelFlow (fun _ : ℝ ↦ bg) x t
          (extChartAt I x x) (b i)
          (metricDualVectorAt (gt t) x (b.coord i)) =
      deTurckConnectionDifferenceAt (gt t) bg x (b i)
        (metricDualVectorAt (gt t) x (b.coord i))
  rw [← connectionValue_eq_anchorChartChristoffelFlow gt x t,
    ← connectionValue_eq_anchorChartChristoffelFlow
      (fun _ : ℝ ↦ bg) x t]
  rfl

end DeTurckCoordinateJointRegularity
end Poincare
