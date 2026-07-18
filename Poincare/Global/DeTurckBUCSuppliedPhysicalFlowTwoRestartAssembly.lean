import Poincare.Global.DeTurckBUCSuppliedPhysicalFlowLocalInverseAssembly
import Mathlib.Analysis.ODE.Gronwall

/-!
# Two-restart ODE package for the supplied physical point flow

The existing symmetric DeTurck point-flow construction exports a family
started at one physical time.  Endpoint invertibility needs one additional,
standard piece of flow structure: the same ODE restarted at the endpoint,
with both families staying in one region on which the vector field is
Lipschitz.

This file isolates exactly that missing package.  Gronwall uniqueness proves
the forward/backward endpoint maps are inverse germs; no inverse law or
invertible differential is retained as a premise.  The forward ODE germ used
by the variational assembly is also extracted from the genuine trajectory
equation.
-/

noncomputable section

open Bundle FiberBundle Filter Function Set
open scoped Manifold ContDiff NNReal Topology

universe u

namespace Poincare

section EndpointUniqueness

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions in one Lipschitz-controlled region which agree at the left
endpoint agree on the whole closed interval. -/
theorem odeSolutions_eqOn_Icc_of_eq_at_leftEndpoint
    {V : ℝ → E → E} {S : Set E} {K : ℝ≥0}
    {a b : ℝ} {alpha beta : ℝ → E}
    (hLip : ∀ s ∈ Icc a b, LipschitzOnWith K (V s) S)
    (hAlpha : ∀ s ∈ Icc a b,
      HasDerivAt alpha (V s (alpha s)) s)
    (hAlphaMem : ∀ s ∈ Icc a b, alpha s ∈ S)
    (hBeta : ∀ s ∈ Icc a b,
      HasDerivAt beta (V s (beta s)) s)
    (hBetaMem : ∀ s ∈ Icc a b, beta s ∈ S)
    (hInitial : alpha a = beta a) :
    EqOn alpha beta (Icc a b) := by
  apply ODE_solution_unique_of_mem_Icc_right
    (v := V) (s := fun _ ↦ S) (K := K)
  · intro s hs
    exact hLip s ⟨hs.1, le_of_lt hs.2⟩
  · exact HasDerivAt.continuousOn hAlpha
  · intro s hs
    exact (hAlpha s ⟨hs.1, le_of_lt hs.2⟩).hasDerivWithinAt
  · intro s hs
    exact hAlphaMem s ⟨hs.1, le_of_lt hs.2⟩
  · exact HasDerivAt.continuousOn hBeta
  · intro s hs
    exact (hBeta s ⟨hs.1, le_of_lt hs.2⟩).hasDerivWithinAt
  · intro s hs
    exact hBetaMem s ⟨hs.1, le_of_lt hs.2⟩
  · exact hInitial

/-- Two solutions in one Lipschitz-controlled region which agree at the right
endpoint agree on the whole closed interval. -/
theorem odeSolutions_eqOn_Icc_of_eq_at_rightEndpoint
    {V : ℝ → E → E} {S : Set E} {K : ℝ≥0}
    {a b : ℝ} {alpha beta : ℝ → E}
    (hLip : ∀ s ∈ Icc a b, LipschitzOnWith K (V s) S)
    (hAlpha : ∀ s ∈ Icc a b,
      HasDerivAt alpha (V s (alpha s)) s)
    (hAlphaMem : ∀ s ∈ Icc a b, alpha s ∈ S)
    (hBeta : ∀ s ∈ Icc a b,
      HasDerivAt beta (V s (beta s)) s)
    (hBetaMem : ∀ s ∈ Icc a b, beta s ∈ S)
    (hFinal : alpha b = beta b) :
    EqOn alpha beta (Icc a b) := by
  apply ODE_solution_unique_of_mem_Icc_left
    (v := V) (s := fun _ ↦ S) (K := K)
  · intro s hs
    exact hLip s ⟨le_of_lt hs.1, hs.2⟩
  · exact HasDerivAt.continuousOn hAlpha
  · intro s hs
    exact (hAlpha s ⟨le_of_lt hs.1, hs.2⟩).hasDerivWithinAt
  · intro s hs
    exact hAlphaMem s ⟨le_of_lt hs.1, hs.2⟩
  · exact HasDerivAt.continuousOn hBeta
  · intro s hs
    exact (hBeta s ⟨le_of_lt hs.1, hs.2⟩).hasDerivWithinAt
  · intro s hs
    exact hBetaMem s ⟨le_of_lt hs.1, hs.2⟩
  · exact hFinal

end EndpointUniqueness

section TwoRestartPackage

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A forward point flow based at time `0` and a backward restart based at
time `t`, both solving the same ODE in one uniqueness region.

Only the endpoint regularity actually consumed downstream is included:
joint `C³` for the forward family at `(t,z₀)` and joint `C¹` for the
backward family at `(0,y₁)`.  The endpoint inverse laws are deliberately
absent: they are consequences of the two trajectory clauses. -/
structure TwoRestartPointFlowPackage
    (V : ℝ → E → E) (Phi Psi : ℝ → E → E)
    (t : ℝ) (z₀ y₁ : E) where
  K : ℝ≥0
  controlledSet : Set E
  endpoint_eq : Phi t z₀ = y₁
  forward_jointC3 :
    ContDiffAt ℝ 3 (Function.uncurry Phi) (t, z₀)
  backward_jointC1 :
    ContDiffAt ℝ 1 (Function.uncurry Psi) (0, y₁)
  lipschitzOn : ∀ s ∈ Icc (0 : ℝ) t,
    LipschitzOnWith K (V s) controlledSet
  forward_flow : ∀ᶠ q in nhds z₀,
    Phi 0 q = q ∧
      ∀ s ∈ Icc (0 : ℝ) t,
        HasDerivAt (fun tau ↦ Phi tau q) (V s (Phi s q)) s ∧
          Phi s q ∈ controlledSet
  backward_flow : ∀ᶠ q in nhds y₁,
    Psi t q = q ∧
      ∀ s ∈ Icc (0 : ℝ) t,
        HasDerivAt (fun tau ↦ Psi tau q) (V s (Psi s q)) s ∧
          Psi s q ∈ controlledSet

namespace TwoRestartPointFlowPackage

variable {V : ℝ → E → E} {Phi Psi : ℝ → E → E}
variable {t : ℝ} {z₀ y₁ : E}

/-- The fixed-time backward endpoint map is `C¹` at its base target. -/
theorem backward_zero_contDiffAt_one
    (H : TwoRestartPointFlowPackage V Phi Psi t z₀ y₁) :
    ContDiffAt ℝ 1 (Psi 0) y₁ := by
  have hpath : ContDiffAt ℝ 1 (fun q : E ↦ ((0 : ℝ), q)) y₁ :=
    contDiffAt_const.prodMk contDiffAt_id
  simpa only [Function.uncurry] using
    H.backward_jointC1.comp y₁ hpath

/-- A genuine point-flow trajectory equation supplies the ordinary time
derivative germ used by the mixed-variational theorem. -/
theorem forward_ODE_germ
    (H : TwoRestartPointFlowPackage V Phi Psi t z₀ y₁)
    (ht : 0 < t) :
    (fun q ↦ deriv (fun s ↦ Phi s q) t) =ᶠ[nhds z₀]
      (fun q ↦ V t (Phi t q)) := by
  filter_upwards [H.forward_flow] with q hq
  exact (hq.2 t ⟨ht.le, le_rfl⟩).1.deriv

/-- Interval ODE uniqueness turns the forward endpoint and the backward
restart endpoint into two-sided local inverse germs. -/
theorem endpoint_twoSidedInverseGerms
    (H : TwoRestartPointFlowPackage V Phi Psi t z₀ y₁)
    (ht : 0 < t) :
    (fun q ↦ Psi 0 (Phi t q)) =ᶠ[nhds z₀] (fun q ↦ q) ∧
      (fun q ↦ Phi t (Psi 0 q)) =ᶠ[nhds y₁] (fun q ↦ q) := by
  have hPhiC1 : ContDiffAt ℝ 1 (Phi t) z₀ := by
    have hpath : ContDiffAt ℝ 1 (fun q : E ↦ (t, q)) z₀ :=
      contDiffAt_const.prodMk contDiffAt_id
    simpa only [Function.uncurry] using
      (H.forward_jointC3.of_le (by norm_num)).comp z₀ hpath
  have hPhiToTarget : Tendsto (Phi t) (nhds z₀) (nhds y₁) := by
    rw [← H.endpoint_eq]
    exact hPhiC1.continuousAt
  have hbackwardAfterForward : ∀ᶠ q in nhds z₀,
      Psi t (Phi t q) = Phi t q ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Psi tau (Phi t q))
              (V s (Psi s (Phi t q))) s ∧
            Psi s (Phi t q) ∈ H.controlledSet :=
    hPhiToTarget H.backward_flow
  have hleft :
      (fun q ↦ Psi 0 (Phi t q)) =ᶠ[nhds z₀] (fun q ↦ q) := by
    filter_upwards [H.forward_flow, hbackwardAfterForward] with q hforward hbackward
    have heq := odeSolutions_eqOn_Icc_of_eq_at_rightEndpoint
      (V := V) (S := H.controlledSet) (K := H.K)
      (alpha := fun s ↦ Phi s q)
      (beta := fun s ↦ Psi s (Phi t q))
      H.lipschitzOn
      (fun s hs ↦ (hforward.2 s hs).1)
      (fun s hs ↦ (hforward.2 s hs).2)
      (fun s hs ↦ (hbackward.2 s hs).1)
      (fun s hs ↦ (hbackward.2 s hs).2)
      hbackward.1.symm
    calc
      Psi 0 (Phi t q) = Phi 0 q :=
        (heq ⟨le_rfl, ht.le⟩).symm
      _ = q := hforward.1
  have hPsiC1 : ContDiffAt ℝ 1 (Psi 0) y₁ :=
    H.backward_zero_contDiffAt_one
  have hPsiBase : Psi 0 y₁ = z₀ := by
    have h := hleft.self_of_nhds
    simpa only [H.endpoint_eq] using h
  have hPsiToSource : Tendsto (Psi 0) (nhds y₁) (nhds z₀) := by
    rw [← hPsiBase]
    exact hPsiC1.continuousAt
  have hforwardAfterBackward : ∀ᶠ q in nhds y₁,
      Phi 0 (Psi 0 q) = Psi 0 q ∧
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt (fun tau ↦ Phi tau (Psi 0 q))
              (V s (Phi s (Psi 0 q))) s ∧
            Phi s (Psi 0 q) ∈ H.controlledSet :=
    hPsiToSource H.forward_flow
  have hright :
      (fun q ↦ Phi t (Psi 0 q)) =ᶠ[nhds y₁] (fun q ↦ q) := by
    filter_upwards [H.backward_flow, hforwardAfterBackward] with q hbackward hforward
    have heq := odeSolutions_eqOn_Icc_of_eq_at_leftEndpoint
      (V := V) (S := H.controlledSet) (K := H.K)
      (alpha := fun s ↦ Phi s (Psi 0 q))
      (beta := fun s ↦ Psi s q)
      H.lipschitzOn
      (fun s hs ↦ (hforward.2 s hs).1)
      (fun s hs ↦ (hforward.2 s hs).2)
      (fun s hs ↦ (hbackward.2 s hs).1)
      (fun s hs ↦ (hbackward.2 s hs).2)
      hforward.1
    calc
      Phi t (Psi 0 q) = Psi t q := heq ⟨ht.le, le_rfl⟩
      _ = q := hbackward.1
  exact ⟨hleft, hright⟩

end TwoRestartPointFlowPackage

end TwoRestartPackage

section TwoRestartSuppliedFlowAssembly

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

variable {ι κ : Type*}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Supplied physical-flow assembly from a genuine two-restart ODE package.

The package, rather than separate derivative identities and inverse germs,
supplies joint endpoint regularity, the point-flow ODE, and a backward
restart.  ODE uniqueness and differentiation discharge every point-flow
premise of the local-inverse assembly. -/
theorem isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_twoRestartPackage
    (rt : ℝ → ClosedSmoothRiemannianMetric n M)
    (D : M → RecenteredDeTurckShapedBUCRemainderData
      («E» := E) (F := CoordinateTwoTensor E) ι κ)
    (K : ℝ≥0)
    (u₀ : M → SemilinearBUCBoundedData
      («E» := E) (F := CoordinateTwoTensor E) K)
    (Phi : M → ℝ → E → E)
    (Psi : ℝ → E → E)
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (bg : ClosedSmoothRiemannianMetric n M)
    (anchor : M) {y₀ y₁ : M} {t : ℝ}
    (ht₀ : 0 < t)
    (htT : t <
      ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
        (D anchor)).uniformLifespan K : ℝ))
    (hy₀ : y₀ ∈ (extChartAt I anchor).source)
    (hy₁ : y₁ ∈ (extChartAt I anchor).source)
    (hχ₀ : ∀ᶠ z' in nhds (extChartAt I anchor y₀),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hχ₁ : ∀ᶠ z' in nhds (extChartAt I anchor y₁),
      GeodesicTransport.cutoff (n := n) anchor z' = 1)
    (hfullGerm :
      (fun z' ↦ coordinateBilinearFormAt
          (reconstructedCoordinateMetricPath
            (D anchor) K (u₀ anchor) t) z') =ᶠ[
            nhds (Phi anchor t (extChartAt I anchor y₀))]
        CovariantDerivative.chartMetric (gt t).inner anchor)
    (hidentifyRHS :
      coordinateBilinearFormAt
          ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
              (D anchor)).uniformInteriorGeneratorValue K (u₀ anchor) t +
            (D anchor).base.nonlinearity
              ((AffineRecenteredDeTurckShapedBUCRemainderData.ofShiftedBackground
                  (D anchor)).uniformInteriorState K (u₀ anchor) t +
                (D anchor).background))
          (Phi anchor t (extChartAt I anchor y₀)) =
        deTurckChartMetricEvolutionBilin gt bg anchor t
          (Phi anchor t (extChartAt I anchor y₀)))
    (H : TwoRestartPointFlowPackage
      (fun s ↦ inverseDeTurckChartCoordinateField gt bg anchor s)
      (Phi anchor) Psi t
      (extChartAt I anchor y₀) (extChartAt I anchor y₁))
    (hrealize : ∀ s z,
      z ∈ (extChartAt I anchor).target →
      CovariantDerivative.chartMetric (rt s).inner anchor z =
        chartwiseReconstructedInverseGaugeMetricSpacetime
          D K u₀ Phi (suppliedPhysicalPointFlowSpatialDifferential Phi)
            s anchor z) :
    IsClosedRicciFlowSolutionAt rt t y₀ := by
  have hODE := H.forward_ODE_germ ht₀
  rcases H.endpoint_twoSidedInverseGerms ht₀ with ⟨hleft, hright⟩
  apply
    isClosedRicciFlowSolutionAt_of_suppliedPhysicalPointFlow_and_localInverseGerms
      (y₀ := y₀) (y₁ := y₁) (t := t)
      rt D K u₀ Phi gt bg anchor ht₀ htT hy₀ hy₁ hχ₀ hχ₁
        H.endpoint_eq hfullGerm hidentifyRHS H.forward_jointC3 hODE
        (Psi 0) H.backward_zero_contDiffAt_one hleft hright hrealize

end TwoRestartSuppliedFlowAssembly

end Poincare
