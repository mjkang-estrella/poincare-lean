import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.AnchoredExtendRegularity
import Poincare.Global.ChartCurvatureBridgeZoneClose

/-!
# Joint continuity of coordinate covariant Ricci entries

This module expands one coordinate component of the covariant derivative of
Ricci in a fixed anchor chart and identifies it with the intrinsic covariant
derivative on the cutoff-one chart zone.
-/

noncomputable section

open Bundle Filter Function FiberBundle
open scoped Manifold ContDiff Topology

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

/-- A fixed-coordinate component of the anchor-chart covariant derivative of
Ricci. The Christoffel field keeps its section-first argument order. -/
noncomputable def anchorChartCovRicciEntryFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z a i j : E) : ℝ :=
  let b := Module.finBasis ℝ E
  fderiv ℝ (fun z' : E ↦ anchorChartRicciEntryFlow gt x t z' i j) z a -
    (∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (anchorChartChristoffelFieldFlow gt x t z i a) *
      anchorChartRicciEntryFlow gt x t z (b r) j) -
    ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
        (anchorChartChristoffelFieldFlow gt x t z j a) *
      anchorChartRicciEntryFlow gt x t z i (b r)

set_option maxHeartbeats 5000000 in
/-- On the cutoff-one part of an anchor chart, the coordinate covariant-Ricci
entry is the corresponding intrinsic covariant derivative of Ricci. -/
theorem anchorChartCovRicciEntryFlow_eq_covTensor2DerivAt_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in 𝓝 z,
      GeodesicTransport.cutoff (n := n) x z' = 1)
    (a i j : E) :
    let y := (extChartAt I x).symm z
    let e := chartInverseTangentEquiv x z hz
    anchorChartCovRicciEntryFlow gt x t z a i j =
      covTensor2DerivAt (gt t) (ricciVariationField (gt t))
        y (e a) (e i) (e j) := by
  classical
  dsimp only
  let g : ClosedSmoothRiemannianMetric n M := gt t
  let y : M := (extChartAt I x).symm z
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let K : ∀ q : M, TM q := extend E (x := x) i
  let L : ∀ q : M, TM q := extend E (x := x) j
  let A : ∀ q : M, TM q := extend E (x := x) a
  let F : M → ℝ := fun q ↦ ricciVariationField g q (K q) (L q)
  have hy : y ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hz
  have hzy : extChartAt I x y = z :=
    (extChartAt I x).right_inv hz
  have he : (e : E →L[ℝ] E) =
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm)
        (Set.range I) z := by
    exact chartInverseTangentEquiv_toContinuousLinearMap x z hz
  have hinv_apply (v : TM y) :
      e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y v) = v := by
    have hcomp :=
      CovariantDerivative.chartTransportedLeviCivita_direction_roundtrip
        x hy v
    rw [hzy] at hcomp
    change (e : E →L[ℝ] E)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y v) = v
    rw [he]
    exact hcomp
  have hKcoord :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (K y) = i := by
    simpa [K] using
      (mfderiv_extChartAt_extend_apply (n := n) (M := M) (x := x) hy i)
  have hLcoord :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (L y) = j := by
    simpa [L] using
      (mfderiv_extChartAt_extend_apply (n := n) (M := M) (x := x) hy j)
  have hAcoord :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (A y) = a := by
    simpa [A] using
      (mfderiv_extChartAt_extend_apply (n := n) (M := M) (x := x) hy a)
  have hKy : K y = e i := by
    calc
      K y = e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (K y)) :=
        (hinv_apply (K y)).symm
      _ = e i := by rw [hKcoord]
  have hLy : L y = e j := by
    calc
      L y = e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (L y)) :=
        (hinv_apply (L y)).symm
      _ = e j := by rw [hLcoord]
  have hAy : A y = e a := by
    calc
      A y = e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (A y)) :=
        (hinv_apply (A y)).symm
      _ = e a := by rw [hAcoord]
  have hK : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% K) y := by
    simpa [K] using anchoredExtend_mdifferentiableAt_of_mem_source x i hy
  have hL : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% L) y := by
    simpa [L] using anchoredExtend_mdifferentiableAt_of_mem_source x j hy
  have hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, E)) (T% A) y := by
    simpa [A] using anchoredExtend_mdifferentiableAt_of_mem_source x a hy
  have hDiff : CovTensor2ExtDifferentiableAt (ricciVariationField g) y :=
    covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y
  have hAddL : Tensor2AddLeft (ricciVariationField g) :=
    tensor2AddLeft_ricciVariationField g
  have hSMulL : Tensor2SMulLeft (ricciVariationField g) :=
    tensor2SMulLeft_ricciVariationField g
  have hAddR : Tensor2AddRight (ricciVariationField g) :=
    tensor2AddRight_ricciVariationField g
  have hSMulR : Tensor2SMulRight (ricciVariationField g) :=
    tensor2SMulRight_ricciVariationField g
  have hRicAt : ∀ v w : E,
      anchorChartRicciEntryFlow gt x t z v w =
        ricciVariationField g y (e v) (e w) := by
    intro v w
    rw [anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
      gt x t hz hχone]
    unfold deTurckChartRicciBilin
    rw [CovariantDerivative.chartMetric_apply]
    rw [← he]
    rfl
  have hχnear : ∀ᶠ z' in 𝓝 z, ∀ᶠ w in 𝓝 z',
      GeodesicTransport.cutoff (n := n) x w = 1 :=
    eventually_eventually_nhds.2 hχone
  have hRicGerm :
      (fun z' : E ↦ anchorChartRicciEntryFlow gt x t z' i j) =ᶠ[𝓝 z]
        (fun z' : E ↦ F ((extChartAt I x).symm z')) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz, hχnear]
      with z' hz' hχ'
    let y' : M := (extChartAt I x).symm z'
    have hy' : y' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hzy' : extChartAt I x y' = z' :=
      (extChartAt I x).right_inv hz'
    have hKcoord' :
        mfderiv I 𝓘(ℝ, E) (extChartAt I x) y' (K y') = i := by
      simpa [K] using
        (mfderiv_extChartAt_extend_apply (n := n) (M := M) (x := x) hy' i)
    have hLcoord' :
        mfderiv I 𝓘(ℝ, E) (extChartAt I x) y' (L y') = j := by
      simpa [L] using
        (mfderiv_extChartAt_extend_apply (n := n) (M := M) (x := x) hy' j)
    have hchart := CovariantDerivative.chartMetric_apply_chart
      (fun q ↦ ricciContinuousBilinAt g q) x hy' (K y') (L y')
    rw [hKcoord', hLcoord', hzy'] at hchart
    rw [anchorChartRicciEntryFlow_eq_deTurckChartRicciBilin_zone
      gt x t hz' hχ']
    simpa [deTurckChartRicciBilin, F, ricciVariationField, g, y'] using hchart
  let hLfield : ∀ q : M, TM q → TM q → ℝ :=
    fun q p _ ↦ ricciVariationField g q p (L q)
  have hLfieldDiff : CovTensor2ExtDifferentiableAt hLfield y := by
    intro p q
    simpa [hLfield] using
      tensor2_moving_right_mdiffAt
        (g := g) (h := ricciVariationField g) (x := y) (K := L)
        hL hDiff hAddR hSMulR p
  have hLfieldAdd : Tensor2AddLeft hLfield := by
    intro q p₁ p₂ r
    simpa [hLfield] using hAddL q p₁ p₂ (L q)
  have hLfieldSMul : Tensor2SMulLeft hLfield := by
    intro q c p r
    simpa [hLfield] using hSMulL q c p (L q)
  have hFdiff : MDifferentiableAt I 𝓘(ℝ) F y := by
    simpa [F, hLfield, ricciVariationField, K, L] using
      tensor2_moving_left_mdiffAt
        (g := g) (h := hLfield) (x := y) (K := K)
        hK hLfieldDiff hLfieldAdd hLfieldSMul (0 : TM y)
  have hpushA :
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) y (e a) = a := by
    rw [← hAy]
    exact hAcoord
  let dF : TM y →L[ℝ] ℝ := extDerivFun F y
  have hD :
      fderiv ℝ (fun z' : E ↦ anchorChartRicciEntryFlow gt x t z' i j) z a =
        dF (e a) := by
    rw [hRicGerm.fderiv_eq]
    have hfixed :
        dF (e a) =
          fderiv ℝ (F ∘ (extChartAt I x).symm) z a := by
      simpa only [dF, hzy, hpushA] using
        (extDerivFun_apply_fixed_chart hy hFdiff (e a : TM y))
    exact hfixed.symm
  have hKconst :
      CovariantDerivative.chartTransportedLeviCivitaSection x K =ᶠ[𝓝 z]
        (fun _ : E ↦ i) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with z' hz'
    let y' : M := (extChartAt I x).symm z'
    have hy' : y' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hzy' : extChartAt I x y' = z' :=
      (extChartAt I x).right_inv hz'
    have h := chartTransportedLeviCivitaSection_extend_apply_chart
      (n := n) (M := M) (x := x) (y := y') hy' i
    rw [hzy'] at h
    simpa [K] using h
  have hLconst :
      CovariantDerivative.chartTransportedLeviCivitaSection x L =ᶠ[𝓝 z]
        (fun _ : E ↦ j) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with z' hz'
    let y' : M := (extChartAt I x).symm z'
    have hy' : y' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hzy' : extChartAt I x y' = z' :=
      (extChartAt I x).right_inv hz'
    have h := chartTransportedLeviCivitaSection_extend_apply_chart
      (n := n) (M := M) (x := x) (y := y') hy' j
    rw [hzy'] at h
    simpa [L] using h
  have hAconst :
      CovariantDerivative.chartTransportedLeviCivitaSection x A =ᶠ[𝓝 z]
        (fun _ : E ↦ a) := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with z' hz'
    let y' : M := (extChartAt I x).symm z'
    have hy' : y' ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hz'
    have hzy' : extChartAt I x y' = z' :=
      (extChartAt I x).right_inv hz'
    have h := chartTransportedLeviCivitaSection_extend_apply_chart
      (n := n) (M := M) (x := x) (y := y') hy' a
    rw [hzy'] at h
    simpa [A] using h
  have hχone' : ∀ᶠ z' in 𝓝 (extChartAt I x y),
      GeodesicTransport.cutoff (n := n) x z' = 1 := by
    rw [hzy]
    exact hχone
  have hConnK :
      g.leviCivita K y (e a) =
        e (anchorChartChristoffelFieldFlow gt x t z i a) := by
    have hnat :=
      ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
        (g := g) (x₀ := x) (y := y) hy hχone' K A hK
    rw [hzy] at hnat
    have hformula :
        (GeodesicTransport.chartLeviCivita g x)
            (CovariantDerivative.chartTransportedLeviCivitaSection x K) z
            (CovariantDerivative.chartTransportedLeviCivitaSection x A z) =
          fderiv ℝ
              (CovariantDerivative.chartTransportedLeviCivitaSection x K) z
              (CovariantDerivative.chartTransportedLeviCivitaSection x A z) +
            anchorChartChristoffelFieldFlow gt x t z
              (CovariantDerivative.chartTransportedLeviCivitaSection x K z)
              (CovariantDerivative.chartTransportedLeviCivitaSection x A z) := by
      rfl
    rw [hformula, hKconst.fderiv_eq, hKconst.self_of_nhds,
      hAconst.self_of_nhds] at hnat
    have hzero : fderiv ℝ (fun _ : E ↦ i) z a = 0 := by simp
    rw [hzero, zero_add] at hnat
    have happ := CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x)
      (σ := fun q : M ↦ g.leviCivita K q (A q)) (y := y) hy
    rw [hzy] at happ
    have hcoordConn :
        mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
            (g.leviCivita K y (A y)) =
          anchorChartChristoffelFieldFlow gt x t z i a := by
      exact happ.symm.trans hnat
    calc
      g.leviCivita K y (e a) = g.leviCivita K y (A y) := by rw [hAy]
      _ = e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
          (g.leviCivita K y (A y))) := (hinv_apply _).symm
      _ = e (anchorChartChristoffelFieldFlow gt x t z i a) := by
        rw [hcoordConn]
  have hConnL :
      g.leviCivita L y (e a) =
        e (anchorChartChristoffelFieldFlow gt x t z j a) := by
    have hnat :=
      ChartCurvatureBridgeZoneClose.chartTransportedLeviCivitaSection_closed_hom_apply_chart_at
        (g := g) (x₀ := x) (y := y) hy hχone' L A hL
    rw [hzy] at hnat
    have hformula :
        (GeodesicTransport.chartLeviCivita g x)
            (CovariantDerivative.chartTransportedLeviCivitaSection x L) z
            (CovariantDerivative.chartTransportedLeviCivitaSection x A z) =
          fderiv ℝ
              (CovariantDerivative.chartTransportedLeviCivitaSection x L) z
              (CovariantDerivative.chartTransportedLeviCivitaSection x A z) +
            anchorChartChristoffelFieldFlow gt x t z
              (CovariantDerivative.chartTransportedLeviCivitaSection x L z)
              (CovariantDerivative.chartTransportedLeviCivitaSection x A z) := by
      rfl
    rw [hformula, hLconst.fderiv_eq, hLconst.self_of_nhds,
      hAconst.self_of_nhds] at hnat
    have hzero : fderiv ℝ (fun _ : E ↦ j) z a = 0 := by simp
    rw [hzero, zero_add] at hnat
    have happ := CovariantDerivative.chartTransportedLeviCivitaSection_apply_chart
      («I» := I) (x₀ := x)
      (σ := fun q : M ↦ g.leviCivita L q (A q)) (y := y) hy
    rw [hzy] at happ
    have hcoordConn :
        mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
            (g.leviCivita L y (A y)) =
          anchorChartChristoffelFieldFlow gt x t z j a := by
      exact happ.symm.trans hnat
    calc
      g.leviCivita L y (e a) = g.leviCivita L y (A y) := by rw [hAy]
      _ = e (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y
          (g.leviCivita L y (A y))) := (hinv_apply _).symm
      _ = e (anchorChartChristoffelFieldFlow gt x t z j a) := by
        rw [hcoordConn]
  have hMapRepr : ∀ q : E,
      (∑ r, b.coord r q • e (b r)) = e q := by
    intro q
    have hrepr : (∑ r, b.coord r q • b r) = q := by
      change (∑ r, (b.repr q) r • b r) = q
      exact b.sum_repr q
    calc
      (∑ r, b.coord r q • e (b r)) =
          ∑ r, e (b.coord r q • b r) := by simp
      _ = e (∑ r, b.coord r q • b r) := by rw [map_sum]
      _ = e q := by rw [hrepr]
  have hRight : ∀ v q : E,
      (∑ r, b.coord r q * g.ricciAt y (e v) (e (b r))) =
        g.ricciAt y (e v) (e q) := by
    intro v q
    let R : E →L[ℝ] ℝ := ricciContinuousBilinAt g y (e v)
    calc
      (∑ r, b.coord r q * g.ricciAt y (e v) (e (b r))) =
          ∑ r, R (b.coord r q • e (b r)) := by
        apply Finset.sum_congr rfl
        intro r _
        calc
          b.coord r q * g.ricciAt y (e v) (e (b r)) =
              b.coord r q * R (e (b r)) := by
            rw [show R (e (b r)) = g.ricciAt y (e v) (e (b r)) by
              exact ricciContinuousBilinAt_apply g y (e v) (e (b r))]
          _ = b.coord r q • R (e (b r)) := rfl
          _ = R (b.coord r q • e (b r)) := by rw [map_smul]
      _ = R (∑ r, b.coord r q • e (b r)) := by rw [map_sum]
      _ = R (e q) := by rw [hMapRepr]
      _ = g.ricciAt y (e v) (e q) :=
        ricciContinuousBilinAt_apply g y (e v) (e q)
  have hFirstCorrection :
      (∑ r, LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x t z i a) *
        anchorChartRicciEntryFlow gt x t z (b r) j) =
        ricciVariationField g y (g.leviCivita K y (e a)) (e j) := by
    let Γ := anchorChartChristoffelFieldFlow gt x t z i a
    calc
      (∑ r, LinearMap.toContinuousLinearMap (b.coord r) Γ *
          anchorChartRicciEntryFlow gt x t z (b r) j) =
          ∑ r, b.coord r Γ * g.ricciAt y (e (b r)) (e j) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hRicAt]
        rfl
      _ = ∑ r, b.coord r Γ * g.ricciAt y (e j) (e (b r)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [g.ricciAt_symm]
      _ = g.ricciAt y (e j) (e Γ) := hRight j Γ
      _ = g.ricciAt y (e Γ) (e j) := g.ricciAt_symm y _ _
      _ = ricciVariationField g y (g.leviCivita K y (e a)) (e j) := by
        rw [hConnK]
        rfl
  have hSecondCorrection :
      (∑ r, LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x t z j a) *
        anchorChartRicciEntryFlow gt x t z i (b r)) =
        ricciVariationField g y (e i) (g.leviCivita L y (e a)) := by
    let Γ := anchorChartChristoffelFieldFlow gt x t z j a
    calc
      (∑ r, LinearMap.toContinuousLinearMap (b.coord r) Γ *
          anchorChartRicciEntryFlow gt x t z i (b r)) =
          ∑ r, b.coord r Γ * g.ricciAt y (e i) (e (b r)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hRicAt]
        rfl
      _ = g.ricciAt y (e i) (e Γ) := hRight i Γ
      _ = ricciVariationField g y (e i) (g.leviCivita L y (e a)) := by
        rw [hConnL]
        rfl
  have hbridge :=
    tensor2_moving_both_extDerivFun_eq_covTensor2DerivAt_add_corrections
      (g := g) (h := ricciVariationField g) (x := y)
      (K := K) (L := L) hK hL hDiff hAddL hSMulL hAddR hSMulR (e a)
  rw [hKy, hLy] at hbridge
  unfold anchorChartCovRicciEntryFlow
  dsimp only
  rw [hD, hFirstCorrection, hSecondCorrection, hbridge]
  dsimp [dF, F, g, y, e]
  ring

private theorem continuousAt_finset_sum_real
    {X ι : Type*} [TopologicalSpace X] {p : X}
    (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ r ∈ s, ContinuousAt (f r) p) :
    ContinuousAt (fun q ↦ ∑ r ∈ s, f r q) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) p)
  | @insert r s hr ih =>
      have hrCont : ContinuousAt (f r) p :=
        hf r (Finset.mem_insert_self r s)
      have hsCont : ContinuousAt (fun q ↦ ∑ k ∈ s, f k q) p :=
        ih (fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert hr] using hrCont.add hsCont

/-- Joint `C³` metric entries make each fixed-coordinate covariant Ricci
entry jointly continuous in time and anchor-chart position. -/
theorem anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3)
    (a i j : E) :
    ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z a i j))
      (t₀, extChartAt I x x) := by
  classical
  let b := Module.finBasis ℝ E
  let q : E := extChartAt I x x
  have hDMap : ContinuousAt
      (fun p : ℝ × E ↦
        fderiv ℝ
          (fun z : E ↦ anchorChartRicciEntryFlow gt x p.1 z i j) p.2)
      (t₀, q) := by
    simpa [q] using
      anchorChartRicciEntryFlow_spatialFDeriv_continuousAt_of_metricEntries
        hJoint i j
  have hD : ContinuousAt
      (fun p : ℝ × E ↦
        fderiv ℝ
          (fun z : E ↦ anchorChartRicciEntryFlow gt x p.1 z i j) p.2 a)
      (t₀, q) :=
    hDMap.clm_apply continuousAt_const
  have hGamma : ContDiffAt ℝ 2
      (Function.uncurry (anchorChartChristoffelFieldFlow gt x)) (t₀, q) := by
    simpa [q] using
      anchorChartChristoffelFieldFlow_jointContDiffAt_two_of_metricEntries
        hJoint
  have hGammaIA : ContinuousAt
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow gt x p.1 p.2 i a) (t₀, q) := by
    simpa [Function.uncurry] using
      ((hGamma.clm_apply (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ i) (t₀, q))).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ a) (t₀, q))).continuousAt
  have hGammaJA : ContinuousAt
      (fun p : ℝ × E ↦
        anchorChartChristoffelFieldFlow gt x p.1 p.2 j a) (t₀, q) := by
    simpa [Function.uncurry] using
      ((hGamma.clm_apply (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ j) (t₀, q))).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ 2 (fun _ : ℝ × E ↦ a) (t₀, q))).continuousAt
  have hFirstCorrection : ContinuousAt
      (fun p : ℝ × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFlow gt x p.1 p.2 i a) *
          anchorChartRicciEntryFlow gt x p.1 p.2 (b r) j)
      (t₀, q) := by
    apply continuousAt_finset_sum_real Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x p.1 p.2 i a)) (t₀, q) := by
      exact (continuousAt_const.clm_apply hGammaIA)
    have hRic : ContinuousAt
        (fun p : ℝ × E ↦
          anchorChartRicciEntryFlow gt x p.1 p.2 (b r) j) (t₀, q) := by
      simpa [Function.uncurry] using
        (anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
          hJoint (b r) j).continuousAt
    exact hcoord.mul hRic
  have hSecondCorrection : ContinuousAt
      (fun p : ℝ × E ↦
        ∑ r, LinearMap.toContinuousLinearMap (b.coord r)
            (anchorChartChristoffelFieldFlow gt x p.1 p.2 j a) *
          anchorChartRicciEntryFlow gt x p.1 p.2 i (b r))
      (t₀, q) := by
    apply continuousAt_finset_sum_real Finset.univ
    intro r _hr
    have hcoord : ContinuousAt
        (fun p : ℝ × E ↦ LinearMap.toContinuousLinearMap (b.coord r)
          (anchorChartChristoffelFieldFlow gt x p.1 p.2 j a)) (t₀, q) := by
      exact (continuousAt_const.clm_apply hGammaJA)
    have hRic : ContinuousAt
        (fun p : ℝ × E ↦
          anchorChartRicciEntryFlow gt x p.1 p.2 i (b r)) (t₀, q) := by
      simpa [Function.uncurry] using
        (anchorChartRicciEntryFlow_jointContDiffAt_one_of_metricEntries
          hJoint i (b r)).continuousAt
    exact hcoord.mul hRic
  unfold anchorChartCovRicciEntryFlow
  dsimp only
  simpa [Function.uncurry, q, b] using
    (hD.sub hFirstCorrection).sub hSecondCorrection

end Poincare
