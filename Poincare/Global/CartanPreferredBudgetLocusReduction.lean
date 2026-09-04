import Poincare.Global.CartanFixedChartGenericInverseEndpointODETailOverlapReduction

/-!
# Preferred trajectory budgets on a restricted generic locus

This file restricts each preferred exponential source to the time-radius
budget of one actual PL trajectory package.  The restricted family has the
same normal and inverse-normal functions as the original generic family, and
its target locus lies inside the original target locus.

The budget is automatic on that restricted locus.  The fixed-chart ODE chain
therefore proves inverse-endpoint agreement there without a moving chart or
cutoff premise.  Recovering an ordinary uniform positive-radius contract still
requires the honest topological input that the restricted target locus is a
neighborhood of the centered parameter.
-/

noncomputable section

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

namespace GeodesicTransport

/-- A fixed preferred package used only to define its positive velocity budget. -/
noncomputable def budgetPreferredPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    PreferredChartExpAtTrajectoryPackage g x :=
  Classical.choice (exists_preferredChartExpAtTrajectoryPackage g x)

theorem budgetPreferredPackage_budget_pos
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    0 < (budgetPreferredPackage g x).time *
      (budgetPreferredPackage g x).velocityRadius :=
  mul_pos (budgetPreferredPackage g x).time_pos
    (budgetPreferredPackage g x).velocityRadius_pos

/-- The public exponential chart restricted to the chosen PL package's exact
time-radius product.  Its function and inverse function are unchanged. -/
noncomputable def budgetExpAtChartOpenPartialHomeomorph
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    OpenPartialHomeomorph E E :=
  let P := budgetPreferredPackage g x
  (expAtChartOpenPartialHomeomorph (g := g) x).restrOpen
    (Metric.ball (0 : E) (P.time * P.velocityRadius)) Metric.isOpen_ball

@[simp] theorem budgetExpAtChartOpenPartialHomeomorph_coe
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    (budgetExpAtChartOpenPartialHomeomorph g x : E → E) =
      expAtChartOpenPartialHomeomorph (g := g) x := rfl

@[simp] theorem budgetExpAtChartOpenPartialHomeomorph_symm_coe
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    ((budgetExpAtChartOpenPartialHomeomorph g x).symm : E → E) =
      (expAtChartOpenPartialHomeomorph (g := g) x).symm := rfl

theorem mem_budgetExpAtChart_source_iff
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (v : E) :
    v ∈ (budgetExpAtChartOpenPartialHomeomorph g x).source ↔
      v ∈ (expAtChartOpenPartialHomeomorph (g := g) x).source ∧
        ‖v‖ < (budgetPreferredPackage g x).time *
          (budgetPreferredPackage g x).velocityRadius := by
  change v ∈ (expAtChartOpenPartialHomeomorph (g := g) x).source ∩
      Metric.ball (0 : E)
        ((budgetPreferredPackage g x).time *
          (budgetPreferredPackage g x).velocityRadius) ↔ _
  simp [Metric.mem_ball, dist_eq_norm]

end GeodesicTransport

namespace CartanSourceExponential

/-- The generic normal family with each exponential source restricted to one
chosen preferred package's velocity budget. -/
noncomputable def budgetRestrictedGenericFamily
    (g : ClosedSmoothRiemannianMetric 3 M) : Family g where
  normal x :=
    (chartAt E x).trans
      (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).symm
  anchor_mem_source x := by
    let e := GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x
    let P := GeodesicTransport.budgetPreferredPackage g x
    have hzero : (0 : E) ∈ e.source := by
      rw [GeodesicTransport.mem_budgetExpAtChart_source_iff]
      exact ⟨GeodesicTransport.zero_mem_expAtChartOpenPartialHomeomorph_source
          (g := g) x,
        by simpa using GeodesicTransport.budgetPreferredPackage_budget_pos g x⟩
    change x ∈ (chartAt E x).source ∩ (chartAt E x) ⁻¹' e.target
    refine ⟨mem_chart_source E x, ?_⟩
    have himage := e.map_source hzero
    simpa [e, GeodesicTransport.expAt_zero, extChartAt_coe] using himage
  normal_anchor x := by
    simpa [GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph] using
        CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x

/-- Membership in the restricted family's joint target supplies exactly the
preferred velocity budget absent from the original IFT family. -/
theorem norm_lt_budgetPreferredPackage_of_mem_budgetRestrictedTargetLocus
    (g : ClosedSmoothRiemannianMetric 3 M) {x : M} {v : E}
    (hv : (x, v) ∈ (budgetRestrictedGenericFamily g).targetLocus) :
    ‖v‖ < (GeodesicTransport.budgetPreferredPackage g x).time *
      (GeodesicTransport.budgetPreferredPackage g x).velocityRadius := by
  change v ∈
    ((chartAt E x).trans
      (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).symm).target at hv
  rw [OpenPartialHomeomorph.trans_target] at hv
  have hvSource : v ∈
      (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).source := hv.1
  exact (GeodesicTransport.mem_budgetExpAtChart_source_iff g x v).1 hvSource |>.2

/-- The restricted target locus is contained in the original generic target
locus; both normal-coordinate functions are globally identical. -/
theorem budgetRestrictedTargetLocus_subset_genericTargetLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    (budgetRestrictedGenericFamily g).targetLocus ⊆
      (genericFamily g).targetLocus := by
  rintro ⟨x, v⟩ hv
  change v ∈
    ((chartAt E x).trans
      (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).symm).target at hv
  change v ∈
    ((chartAt E x).trans
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x).symm).target
  rw [OpenPartialHomeomorph.trans_target] at hv ⊢
  refine ⟨?_, ?_⟩
  · exact
      (GeodesicTransport.mem_budgetExpAtChart_source_iff g x v).1 hv.1 |>.1
  · simpa using hv.2

/-- Membership in the budget-restricted target is exactly ordinary generic
target membership together with the selected preferred-package budget. -/
theorem mem_budgetRestrictedTargetLocus_iff
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (v : E) :
    (x, v) ∈ (budgetRestrictedGenericFamily g).targetLocus ↔
      (x, v) ∈ (genericFamily g).targetLocus ∧
        ‖v‖ < (GeodesicTransport.budgetPreferredPackage g x).time *
          (GeodesicTransport.budgetPreferredPackage g x).velocityRadius := by
  constructor
  · intro hv
    exact ⟨budgetRestrictedTargetLocus_subset_genericTargetLocus g hv,
      norm_lt_budgetPreferredPackage_of_mem_budgetRestrictedTargetLocus g hv⟩
  · rintro ⟨hgeneric, hbudget⟩
    change v ∈
      ((chartAt E x).trans
        (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).symm).target
    change v ∈
      ((chartAt E x).trans
        (GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := g) x).symm).target at hgeneric
    rw [OpenPartialHomeomorph.trans_target] at hgeneric ⊢
    refine ⟨?_, ?_⟩
    · have hgenericSource : v ∈
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x).source := by
        simpa using hgeneric.1
      have hbudgetSource : v ∈
          (GeodesicTransport.budgetExpAtChartOpenPartialHomeomorph g x).source :=
        (GeodesicTransport.mem_budgetExpAtChart_source_iff g x v).2
          ⟨hgenericSource, hbudget⟩
      simpa using hbudgetSource
    · simpa using hgeneric.2

/-- Set-level form of the exact budget-restricted target description. -/
theorem budgetRestrictedTargetLocus_eq
    (g : ClosedSmoothRiemannianMetric 3 M) :
    (budgetRestrictedGenericFamily g).targetLocus =
      (genericFamily g).targetLocus ∩
        {q : M × E |
          ‖q.2‖ <
            (GeodesicTransport.budgetPreferredPackage g q.1).time *
              (GeodesicTransport.budgetPreferredPackage g q.1).velocityRadius} := by
  ext q
  exact mem_budgetRestrictedTargetLocus_iff g q.1 q.2

/-- A locally uniform positive lower bound for the selected package budgets
turns any centered generic-target neighborhood into a centered neighborhood
of the budget-restricted target. -/
theorem budgetRestrictedTargetLocus_mem_nhds_of_genericTargetLocus_mem_nhds_of_eventually_budget_lower
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (hgeneric : (genericFamily g).targetLocus ∈ nhds (x₀, (0 : E)))
    {r : ℝ} (hr : 0 < r)
    (hbudget : ∀ᶠ x in nhds x₀,
      r ≤ (GeodesicTransport.budgetPreferredPackage g x).time *
        (GeodesicTransport.budgetPreferredPackage g x).velocityRadius) :
    (budgetRestrictedGenericFamily g).targetLocus ∈
      nhds (x₀, (0 : E)) := by
  have hproduct :
      {x : M |
          r ≤ (GeodesicTransport.budgetPreferredPackage g x).time *
            (GeodesicTransport.budgetPreferredPackage g x).velocityRadius} ×ˢ
          Metric.ball (0 : E) r ∈ nhds (x₀, (0 : E)) :=
    prod_mem_nhds hbudget (Metric.ball_mem_nhds (0 : E) hr)
  have hbudgetLocus :
      {q : M × E |
        ‖q.2‖ <
          (GeodesicTransport.budgetPreferredPackage g q.1).time *
            (GeodesicTransport.budgetPreferredPackage g q.1).velocityRadius} ∈
        nhds (x₀, (0 : E)) := by
    refine Filter.mem_of_superset hproduct ?_
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hvNorm : ‖v‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    exact hvNorm.trans_le hx
  rw [budgetRestrictedTargetLocus_eq]
  exact inter_mem hgeneric hbudgetLocus

/-- Continuity at the anchor of the selected time-radius product supplies the
local lower bound required by the preceding neighborhood theorem. -/
theorem budgetRestrictedTargetLocus_mem_nhds_of_genericTargetLocus_mem_nhds_of_budget_continuousAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (hgeneric : (genericFamily g).targetLocus ∈ nhds (x₀, (0 : E)))
    (hbudgetContinuous : ContinuousAt
      (fun x : M =>
        (GeodesicTransport.budgetPreferredPackage g x).time *
          (GeodesicTransport.budgetPreferredPackage g x).velocityRadius) x₀) :
    (budgetRestrictedGenericFamily g).targetLocus ∈
      nhds (x₀, (0 : E)) := by
  let R : ℝ := (GeodesicTransport.budgetPreferredPackage g x₀).time *
    (GeodesicTransport.budgetPreferredPackage g x₀).velocityRadius
  let r : ℝ := R / 2
  have hR : 0 < R := by
    simpa [R] using
      GeodesicTransport.budgetPreferredPackage_budget_pos g x₀
  have hr : 0 < r := half_pos hR
  have hbudgetStrict : ∀ᶠ x in nhds x₀,
      r < (GeodesicTransport.budgetPreferredPackage g x).time *
        (GeodesicTransport.budgetPreferredPackage g x).velocityRadius := by
    apply hbudgetContinuous
    exact Ioi_mem_nhds (half_lt_self hR)
  exact
    budgetRestrictedTargetLocus_mem_nhds_of_genericTargetLocus_mem_nhds_of_eventually_budget_lower
      g x₀ hgeneric hr (hbudgetStrict.mono fun _ hx => hx.le)

/-- Joint regularity of the original generic family plus continuity of the
selected package budget at one anchor is sufficient for the exact remaining
budget-neighborhood obligation. -/
theorem budgetRestrictedTargetLocus_mem_nhds_of_genericJointRegularity_of_budget_continuousAt
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (hregular : GenericJointRegularity g)
    (hbudgetContinuous : ContinuousAt
      (fun x : M =>
        (GeodesicTransport.budgetPreferredPackage g x).time *
          (GeodesicTransport.budgetPreferredPackage g x).velocityRadius) x₀) :
    (budgetRestrictedGenericFamily g).targetLocus ∈
      nhds (x₀, (0 : E)) := by
  have hcenter : (x₀, (0 : E)) ∈ (genericFamily g).targetLocus := by
    change (0 : E) ∈ ((genericFamily g).normal x₀).target
    have hmap := (genericFamily g).normal x₀ |>.map_source
      ((genericFamily g).anchor_mem_source x₀)
    simpa [(genericFamily g).normal_anchor x₀] using hmap
  exact
    budgetRestrictedTargetLocus_mem_nhds_of_genericTargetLocus_mem_nhds_of_budget_continuousAt
      g x₀ (hregular.isOpen_targetLocus.mem_nhds hcenter) hbudgetContinuous

@[simp] theorem budgetRestrictedGenericFamily_normal_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x z : M) :
    (budgetRestrictedGenericFamily g).normal x z =
      (genericFamily g).normal x z := rfl

/-- The restricted and original normal evaluations are equal as global
two-variable functions, even though their partial-homeomorphism domains differ. -/
theorem budgetRestrictedGenericFamily_normal_function
    (g : ClosedSmoothRiemannianMetric 3 M) :
    (fun q : M × M => (budgetRestrictedGenericFamily g).normal q.1 q.2) =
      fun q : M × M => (genericFamily g).normal q.1 q.2 := by
  funext q
  exact budgetRestrictedGenericFamily_normal_apply g q.1 q.2

@[simp] theorem budgetRestrictedGenericFamily_symmEval
    (g : ClosedSmoothRiemannianMetric 3 M) (q : M × E) :
    (budgetRestrictedGenericFamily g).symmEval q =
      (genericFamily g).symmEval q := rfl

/-- The inverse normal evaluations are globally the same function. -/
theorem budgetRestrictedGenericFamily_symmEval_function
    (g : ClosedSmoothRiemannianMetric 3 M) :
    (budgetRestrictedGenericFamily g).symmEval =
      (genericFamily g).symmEval := by
  funext q
  exact budgetRestrictedGenericFamily_symmEval g q

end CartanSourceExponential

namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

open CartanSourceExponential

/-- Minimal locus-parameterized version of generic inverse agreement.  The
endpoint remains the original generic inverse; only the admissible locus is
shrunk. -/
def GenericInverseEndpointAgreementOn
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    (L : Set (M × E)) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈ L →
      C.fixedTimeEndpoint x w =
        (genericFamily g).symmEval
          (x, fixedToAnchorVelocity x₀ (x, w))

/-- The ODE comparison provider with only its eligibility locus generalized. -/
def GenericInverseEndpointODEComparisonProviderOn
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    (L : Set (M × E)) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈ L →
      Nonempty (C.GenericInverseEndpointODEComparison x w)

/-- A comparison on any sublocus of the original generic target proves the
corresponding locus-restricted inverse agreement. -/
theorem genericInverseEndpointAgreementOn_of_odeComparison
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)}
    (hL : L ⊆ (genericFamily g).targetLocus)
    (hcomparison : C.GenericInverseEndpointODEComparisonProviderOn L) :
    C.GenericInverseEndpointAgreementOn L := by
  intro x w hxAnchor hwSource htargetL
  have htarget : (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus := hL htargetL
  rcases hcomparison x w hxAnchor hwSource htargetL with ⟨data⟩
  let z : M := (genericFamily g).symmEval
    (x, fixedToAnchorVelocity x₀ (x, w))
  have hfixedSource :
      C.fixedTimeEndpoint x w ∈ (chartAt E x).source :=
    data.fixedEndpoint_mem_preferredChartSource
  have hgenericSource : z ∈ (chartAt E x).source :=
    genericSymmEval_mem_preferredChartSource htarget
  have hcoordinate :
      (chartAt E x) (C.fixedTimeEndpoint x w) = (chartAt E x) z := by
    calc
      (chartAt E x) (C.fixedTimeEndpoint x w) =
          GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
            (fixedToAnchorVelocity x₀ (x, w)) :=
        data.fixedEndpoint_preferredChart_eq_publicExp hxAnchor
      _ = (chartAt E x) z :=
        (preferredChart_genericSymmEval_eq_expAtChart htarget).symm
  calc
    C.fixedTimeEndpoint x w =
        (chartAt E x).symm ((chartAt E x) (C.fixedTimeEndpoint x w)) :=
      ((chartAt E x).left_inv hfixedSource).symm
    _ = (chartAt E x).symm ((chartAt E x) z) :=
      congrArg (chartAt E x).symm hcoordinate
    _ = z := (chartAt E x).left_inv hgenericSource

/-- The downstream fixed-time agreement needs only a small-velocity inclusion
into the supplied sublocus, not agreement on the whole generic target. -/
theorem fixedPositiveTimeEndpointAgreement_of_genericInverseEndpointAgreementOn
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)} {radius : ℝ}
    (hL : L ⊆ (genericFamily g).targetLocus)
    (hinverse : C.GenericInverseEndpointAgreementOn L)
    (htarget : ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
      (extChartAt I x₀ x, w) ∈ C.endpoint.source →
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
        (x, fixedToAnchorVelocity x₀ (x, w)) ∈ L) :
    C.FixedPositiveTimeEndpointAgreement radius := by
  refine {
    point_mem_anchorChart := ?_
    vector_mem_genericExpSource := ?_
    endpoint_coordinate := ?_ }
  · intro x w hxAnchor hwSource hnorm
    have hmemL := htarget x w hxAnchor hwSource hnorm
    have hmem := hL hmemL
    rw [hinverse x w hxAnchor hwSource hmemL]
    exact genericSymmEval_mem_preferredChartSource hmem
  · intro x w hxAnchor hwSource hnorm
    exact genericExpSource_of_mem_genericTargetLocus
      (hL (htarget x w hxAnchor hwSource hnorm))
  · intro x w hxAnchor hwSource hnorm
    have hmemL := htarget x w hxAnchor hwSource hnorm
    have hmem := hL hmemL
    rw [hinverse x w hxAnchor hwSource hmemL]
    exact preferredChart_genericSymmEval_eq_expAtChart hmem

/-- A neighborhood of the centered parameter in an arbitrary admissible locus
is the exact topological input needed to recover an anchor slice and a uniform
small-velocity radius. -/
theorem exists_openAnchorRestriction_targetRadius_of_locus_mem_nhds
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)} (hL : L ∈ 𝓝 (x₀, (0 : E))) :
    ∃ (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
        (radius : ℝ),
      0 < radius ∧
      ∀ (x : M) (w : E),
        x ∈ (C.restrictToOpenAnchorSet V hV hx₀V).rawLocalFamily.anchors →
        ‖fixedToAnchorVelocity x₀ (x, w)‖ < radius →
          (x, fixedToAnchorVelocity x₀ (x, w)) ∈ L := by
  rcases mem_nhds_prod_iff.mp hL with
    ⟨U, hU, W, hW, hproduct⟩
  rcases _root_.mem_nhds_iff.mp hU with
    ⟨V, hVU, hVopen, hx₀V⟩
  rcases Metric.mem_nhds_iff.mp hW with
    ⟨radius, hradius, hball⟩
  refine ⟨V, hVopen, hx₀V, radius, hradius, ?_⟩
  intro x w hxAnchor hnorm
  have hxV :=
    C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset
      V hVopen hx₀V hxAnchor
  have hvBall : fixedToAnchorVelocity x₀ (x, w) ∈
      Metric.ball (0 : E) radius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm
  exact hproduct ⟨hVU hxV, hball hvBall⟩

variable [T2Space M]

/-- The preferred-budget provider is automatic when its eligibility locus is
the budget-restricted generic target. -/
theorem exists_preferredPackage_budget_of_mem_budgetRestrictedTargetLocus
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E)
    (_hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (_hw : (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source)
    (htarget : (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (budgetRestrictedGenericFamily g).targetLocus) :
    ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
      ‖fixedToAnchorVelocity x₀ (x, w)‖ < P.time * P.velocityRadius := by
  exact ⟨GeodesicTransport.budgetPreferredPackage g x,
    norm_lt_budgetPreferredPackage_of_mem_budgetRestrictedTargetLocus
      g htarget⟩

/-! ## Locus-parametric automatic ODE continuation -/

/-- Preferred-package budget production with an arbitrary eligibility locus.
The selector domain is supplied separately by restricting the endpoint source. -/
def GenericInverseEndpointODEPreferredVelocityBudgetProviderOn
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    (L : Set (M × E)) : Prop :=
  ∀ (x : M) (w : E)
      (_hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors),
    (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈ L →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        ‖fixedToAnchorVelocity x₀ (x, w)‖ <
          P.time * P.velocityRadius

/-- The fixed endpoint-source restriction and the preferred budget on `L`
construct an ODE comparison on `L`.  No openness of `L` is used. -/
theorem restrictToSelectorInitialBall_genericInverseEndpointODEComparisonProviderOn_of_preferredVelocityBudget
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)}
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (hbudget :
      C.restrictToSelectorInitialBall.GenericInverseEndpointODEPreferredVelocityBudgetProviderOn
        L) :
    C.restrictToSelectorInitialBall.restrictToFixedAnchorCutoffOne.GenericInverseEndpointODEComparisonProviderOn
      L := by
  let D := C.restrictToSelectorInitialBall
  intro x w hx hw hL
  rcases hbudget x w hx hw hL with ⟨P, hvelocity⟩
  have hwD : (extChartAt I x₀ x, w) ∈ D.endpoint.source := by
    simpa only [restrictToFixedAnchorCutoffOne_endpoint] using hw
  have hselectorD :=
    C.restrictToSelectorInitialBall_endpoint_source_selectorInitial_mem hwD
  have hselector :
      (extChartAt I x₀ x,
          D.restrictToFixedAnchorCutoffOne.time⁻¹ • w) ∈
        closedBall (extChartAt I x₀ x₀, (0 : E))
          (D.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational.initialRadius : ℝ) := by
    simpa only [restrictToFixedAnchorCutoffOne_time,
      restrictToFixedAnchorCutoffOne_selector] using hselectorD
  rcases
      D.restrictToFixedAnchorCutoffOne.nonempty_reparameterized_admissibility_of_velocity_budget
        x w P hselector hvelocity with
    ⟨Q, _hQtime, ⟨admissible⟩⟩
  have hprotectedD :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          D.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀ := by
    simpa only [D, restrictToSelectorInitialBall,
      restrictEndpointSource_selector] using hprotectedFixed
  rcases
      D.nonempty_genericInverseEndpointODETailOverlapData_of_fixedSourceChartCutoff_protectedInnerBall_automatic
        hx admissible hprotectedD with
    ⟨tail⟩
  let positive := tail.toPositiveTimeOverlapData
  let pointwise := positive.toPointwiseOverlapData hx
  exact ⟨pointwise.toODEPrimitiveData.toODEComparison⟩

/-- On a sublocus of the original generic target, the preferred budget alone
proves generic inverse-endpoint agreement after the two fixed package
restrictions. -/
theorem restrictToSelectorInitialBall_genericInverseEndpointAgreementOn_of_preferredVelocityBudget
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)}
    (hL : L ⊆ (genericFamily g).targetLocus)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (hbudget :
      C.restrictToSelectorInitialBall.GenericInverseEndpointODEPreferredVelocityBudgetProviderOn
        L) :
    C.restrictToSelectorInitialBall.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreementOn
      L :=
  genericInverseEndpointAgreementOn_of_odeComparison
    C.restrictToSelectorInitialBall.restrictToFixedAnchorCutoffOne hL
    (C.restrictToSelectorInitialBall_genericInverseEndpointODEComparisonProviderOn_of_preferredVelocityBudget
      hprotectedFixed hbudget)

/-- The chosen budget package supplies the preferred-budget provider on the
budget-restricted generic target locus. -/
theorem genericInverseEndpointODEPreferredVelocityBudgetProviderOn_budgetRestrictedTargetLocus
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀) :
    C.GenericInverseEndpointODEPreferredVelocityBudgetProviderOn
      (budgetRestrictedGenericFamily g).targetLocus := by
  intro x w hx hw htarget
  exact C.exists_preferredPackage_budget_of_mem_budgetRestrictedTargetLocus
    x w hx hw htarget

/-- A protected fixed package can therefore be chosen with inverse-endpoint
agreement on the full budget-restricted generic target locus. -/
theorem exists_fixedChartAnchorEndpointPackage_with_genericInverseEndpointAgreementOn_budgetRestrictedTargetLocus
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      C.restrictToSelectorInitialBall.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreementOn
        (budgetRestrictedGenericFamily g).targetLocus := by
  rcases
      exists_fixedChartAnchorEndpointPackage_with_fixedSourceChartCutoff_protectedInnerBall
        g x₀ with
    ⟨C, hprotectedFixed⟩
  refine ⟨C, ?_⟩
  exact
    C.restrictToSelectorInitialBall_genericInverseEndpointAgreementOn_of_preferredVelocityBudget
      (budgetRestrictedTargetLocus_subset_genericTargetLocus g)
      hprotectedFixed
      (C.restrictToSelectorInitialBall.genericInverseEndpointODEPreferredVelocityBudgetProviderOn_budgetRestrictedTargetLocus)

/-! ## Recovering the ordinary positive-radius contract -/

/-- Locus-restricted inverse agreement survives an open restriction of the
anchor slice. -/
theorem genericInverseEndpointAgreementOn_restrictToOpenAnchorSet
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)}
    (hinverse : C.GenericInverseEndpointAgreementOn L)
    (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V) :
    (C.restrictToOpenAnchorSet V hV hx₀V).GenericInverseEndpointAgreementOn
      L := by
  intro x w hxAnchor hwSource htarget
  have hxOld :=
    C.restrictToOpenAnchorSet_rawLocalFamily_anchors_subset_original
      V hV hx₀V hxAnchor
  simpa only [restrictToOpenAnchorSet_endpoint,
    restrictToOpenAnchorSet_fixedTimeEndpoint] using
      hinverse x w hxOld
        (by simpa only [restrictToOpenAnchorSet_endpoint] using hwSource)
        htarget

/-- If the admissible locus is a neighborhood of the centered parameter, its
locus-restricted inverse agreement yields the usual open anchor restriction
and one positive-radius endpoint agreement. -/
theorem exists_openAnchorRestriction_fixedPositiveTimeEndpointAgreement_of_locus_mem_nhds
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}
    (C : FixedChartAnchorEndpointPackage g x₀)
    {L : Set (M × E)}
    (hL : L ⊆ (genericFamily g).targetLocus)
    (hinverse : C.GenericInverseEndpointAgreementOn L)
    (hLnhds : L ∈ nhds (x₀, (0 : E))) :
    ∃ (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
        (radius : ℝ),
      0 < radius ∧
        (C.restrictToOpenAnchorSet V hV hx₀V).FixedPositiveTimeEndpointAgreement
          radius := by
  rcases C.exists_openAnchorRestriction_targetRadius_of_locus_mem_nhds hLnhds with
    ⟨V, hV, hx₀V, radius, hradius, htarget⟩
  let C' := C.restrictToOpenAnchorSet V hV hx₀V
  have hinverse' : C'.GenericInverseEndpointAgreementOn L :=
    C.genericInverseEndpointAgreementOn_restrictToOpenAnchorSet
      hinverse V hV hx₀V
  have hendpoint : C'.FixedPositiveTimeEndpointAgreement radius :=
    C'.fixedPositiveTimeEndpointAgreement_of_genericInverseEndpointAgreementOn
      hL hinverse' (fun x w hx hw hnorm => htarget x w hx hnorm)
  exact ⟨V, hV, hx₀V, radius, hradius, hendpoint⟩

/-- The budget-restricted route reaches the ordinary positive-radius endpoint
contract precisely when its target locus is a neighborhood of `(x₀, 0)`.
This theorem does not assert that neighborhood condition. -/
theorem exists_budgetRestricted_openAnchorRestriction_fixedPositiveTimeEndpointAgreement
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    (hbudgetNhds :
      (budgetRestrictedGenericFamily g).targetLocus ∈
        nhds (x₀, (0 : E))) :
    ∃ (C : FixedChartAnchorEndpointPackage g x₀)
        (V : Set M) (hV : IsOpen V) (hx₀V : x₀ ∈ V)
        (radius : ℝ),
      0 < radius ∧
        (C.restrictToOpenAnchorSet V hV hx₀V).FixedPositiveTimeEndpointAgreement
          radius := by
  rcases
      exists_fixedChartAnchorEndpointPackage_with_genericInverseEndpointAgreementOn_budgetRestrictedTargetLocus
        g x₀ with
    ⟨C₀, hinverse⟩
  let C := C₀.restrictToSelectorInitialBall.restrictToFixedAnchorCutoffOne
  rcases
      C.exists_openAnchorRestriction_fixedPositiveTimeEndpointAgreement_of_locus_mem_nhds
        (budgetRestrictedTargetLocus_subset_genericTargetLocus g)
        hinverse hbudgetNhds with
    ⟨V, hV, hx₀V, radius, hradius, hendpoint⟩
  exact ⟨C, V, hV, hx₀V, radius, hradius, hendpoint⟩

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
