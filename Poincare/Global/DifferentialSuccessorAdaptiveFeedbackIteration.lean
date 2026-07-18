import Poincare.Global.DifferentialSuccessorStrictFactorCurvatureTransport

/-!
# The remaining adaptive-feedback iteration

Every realized strict-factor insertion schedule now has two finite positive
radius families.  This file first collapses each family to one scalar positive
minimum without changing the adaptive quantifier order.  It then formalizes
what repeated geometric refinement can and cannot prove.

At stage `n`, the first radius `epsilon n` is always available.  The second
radius is available only after the first insertion defect is below
`epsilon n`.  The active threshold is therefore `epsilon n` in the failing
first phase, and the minimum of the two radii once the first phase succeeds.
If a response stage makes both defects smaller than the preceding active
threshold, then either that response validates or its new active threshold is
strictly smaller.  Thus finite iteration gives validation or a finite strict
descent of positive minima; positivity alone does not rule out the latter.

An additional uniform positive lower bound on these active thresholds, plus
defects tending uniformly to zero, does close the feedback.  This isolates the
exact compactness/continuous-dependence statement still absent from the
current geometric development.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorAdaptiveFeedbackIteration

universe u

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorInsertionTransport
open DifferentialSuccessorStrictFactorCurvatureTransport
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveGridRefinement
open DifferentialSuccessorPostRealizationMeshCertificate

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The common-scalar version of the two-stage strict-factor certificate.
Both scalar radii control every insertion in every factor gap. -/
def StrictFactorCommonRadiusCertificate
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) (initial : CartanChain.ChainState g)
    (k : ℕ) (e : ℕ → ℕ)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∃ epsilon > (0 : ℝ),
    ((∀ n : Fin k,
      ∀ i : Fin (factorGapNodes refined e n).length,
        dist
            (insertNodeListSchedule
              (factorRefinementStage seed refined e n) (e n)
              (factorGapNodes refined e n) (i + 1) (e n + i + 1))
            ((chain n (i + 1)).state (e n + i)).anchor < epsilon) →
      ∃ radius > (0 : ℝ),
        ((∀ n : Fin k,
          ∀ i : Fin (factorGapNodes refined e n).length,
            dist
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) i (e n + i + 1))
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) (i + 1)
                    (e n + i + 1)) < radius) →
          coarseChain.state k = refinedChain.state (e k)))

/-- A finite dependent radius certificate admits common positive scalar
radii.  The empty-insertion case is handled directly from the vacuous
dependent certificate, so no artificial nonemptiness hypothesis is needed. -/
theorem StrictFactorRadiusCertificate.toCommon
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (hcert : StrictFactorRadiusCertificate seed refined initial k e
      coarseChain refinedChain chain) :
    StrictFactorCommonRadiusCertificate seed refined initial k e
      coarseChain refinedChain chain := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases hcert with ⟨epsilonAt, hepsilonAt, hafterFirst⟩
  let A := Σ n : Fin k, Fin (factorGapNodes refined e n).length
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      refine ⟨1, zero_lt_one, ?_⟩
      intro _hfirst
      have hfirstAt : ∀ n : Fin k,
          ∀ i : Fin (factorGapNodes refined e n).length,
            dist
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) (i + 1)
                    (e n + i + 1))
                ((chain n (i + 1)).state (e n + i)).anchor <
              epsilonAt n i := by
        intro n i
        exact isEmptyElim (α := A) (⟨n, i⟩ : A)
      rcases hafterFirst hfirstAt with
        ⟨_radiusAt, _hradiusAt, hafterSecond⟩
      refine ⟨1, zero_lt_one, ?_⟩
      intro _hsecond
      apply hafterSecond
      intro n i
      exact isEmptyElim (α := A) (⟨n, i⟩ : A)
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      let epsilon : ℝ :=
        Finset.univ.inf' Finset.univ_nonempty
          (fun a : A ↦ epsilonAt a.1 a.2)
      have hepsilon : 0 < epsilon := by
        dsimp [epsilon]
        apply (Finset.lt_inf'_iff _).2
        intro a _ha
        exact hepsilonAt a.1 a.2
      refine ⟨epsilon, hepsilon, ?_⟩
      intro hfirst
      have hfirstAt : ∀ n : Fin k,
          ∀ i : Fin (factorGapNodes refined e n).length,
            dist
                (insertNodeListSchedule
                  (factorRefinementStage seed refined e n) (e n)
                  (factorGapNodes refined e n) (i + 1)
                    (e n + i + 1))
                ((chain n (i + 1)).state (e n + i)).anchor <
              epsilonAt n i := by
        intro n i
        exact (hfirst n i).trans_le
          (Finset.inf'_le
            (fun a : A ↦ epsilonAt a.1 a.2)
            (Finset.mem_univ (⟨n, i⟩ : A)))
      rcases hafterFirst hfirstAt with
        ⟨radiusAt, hradiusAt, hafterSecond⟩
      let radius : ℝ :=
        Finset.univ.inf' Finset.univ_nonempty
          (fun a : A ↦ radiusAt a.1 a.2)
      have hradius : 0 < radius := by
        dsimp [radius]
        apply (Finset.lt_inf'_iff _).2
        intro a _ha
        exact hradiusAt a.1 a.2
      refine ⟨radius, hradius, ?_⟩
      intro hsecond
      apply hafterSecond
      intro n i
      exact (hsecond n i).trans_le
        (Finset.inf'_le
          (fun a : A ↦ radiusAt a.1 a.2)
          (Finset.mem_univ (⟨n, i⟩ : A)))

/-- Constant curvature therefore supplies common scalar radii for a strict
factor schedule, still with the first radius chosen before the second. -/
theorem ReachableChain.strictFactorCommonRadiusCertificate_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorCommonRadiusCertificate seed refined initial k e coarseChain
      refinedChain chain := by
  letI : MetricSpace M := g.toMetricSpace
  apply StrictFactorRadiusCertificate.toCommon
  exact ReachableChain.strictFactorRadiusCertificate_of_curvature
    hcurv seed refined k e heZero heStrict heValue coarseChain refinedChain
      chain

/-- The post-realization strict refining grid carries common scalar two-stage
radii on every realized row schedule.  This is the scalar-minimum form needed
by the feedback iteration below; its quantifier order is unchanged from the
dependent certificate. -/
theorem exists_postRealization_refining_grid_with_row_commonRadius_certificates_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0) (htmono : Monotone t)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (htstrict : ∀ n < k, t n < t (n + 1))
    (rowChain : ∀ m : Fin (k + 2),
      ReachableChain (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      Data (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (((∀ alternateRowChain : ∀ m : Fin (k + 2),
            ReachableChain (homotopyGridRow F t m) initial,
          (alternateRowChain 0).state (k + 1) =
            (alternateRowChain (Fin.last (k + 1))).state (k + 1)) ∨
        (∃ m : Fin (k + 2), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j)) ∨
        (∃ m : Fin (k + 1), ∃ j : Fin (k + 1),
          eta ≤ dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)))) ∧
      ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
        0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
          Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
          (∀ n, r (e n) = t n) ∧
          (∀ n < k, e n < e (n + 1)) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F r n (m + 1))
              (homotopyGridRow F r n m) < eta) ∧
          (∀ n m : ℕ,
            dist (homotopyGridRow F r (n + 1) (m + 1))
              (homotopyGridRow F r n (m + 1)) < eta) ∧
          ∀ (m : ℕ)
            (coarseRowChain : ReachableChain
              (homotopyGridRow F t m) initial)
            (refinedRowChain : ReachableChain
              (homotopyGridRow F r (e m)) initial)
            (insertionChain : ∀ n i : ℕ,
              ReachableChain
                (insertNodeListSchedule
                  (factorRefinementStage
                    (homotopyGridRow F t m)
                    (homotopyGridRow F r (e m)) e n)
                  (e n)
                  (factorGapNodes (homotopyGridRow F r (e m)) e n) i)
                initial),
            StrictFactorCommonRadiusCertificate
              (homotopyGridRow F t m) (homotopyGridRow F r (e m))
              initial k e coarseRowChain refinedRowChain insertionChain) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_postRealization_refining_grid_with_row_transport_certificates_of_curvature
        hcurv F initial hinitial t htzero htmono k htone htstrict rowChain
          rungData bottomAtUpper rungAtNext with
    ⟨eta, heta, hcertificate, r, K, e, hK, hrZero, hrMono, hrOne,
      heMono, heZero, heBound, heValue, heStrict, hhorizontal, hvertical,
      hrow⟩
  refine ⟨eta, heta, hcertificate, r, K, e, hK, hrZero, hrMono, hrOne,
    heMono, heZero, heBound, heValue, heStrict, hhorizontal, hvertical, ?_⟩
  intro m coarseRowChain refinedRowChain insertionChain
  exact StrictFactorRadiusCertificate.toCommon
    (homotopyGridRow F t m) (homotopyGridRow F r (e m)) k e
      coarseRowChain refinedRowChain insertionChain
      (hrow m coarseRowChain refinedRowChain insertionChain)

section FixedRealizedHistories

/-- The exact finite index type of insertion histories used by one fixed
strict-factor realization up to coarse column `k`. -/
def StrictFactorRealizedHistoryIndex
    (refined : ℕ → M) (k : ℕ) (e : ℕ → ℕ) :=
  Σ n : Fin k, Fin (factorGapNodes refined e n).length

instance strictFactorRealizedHistoryIndexFintype
    (refined : ℕ → M) (k : ℕ) (e : ℕ → ℕ) :
    Fintype (StrictFactorRealizedHistoryIndex refined k e) := by
  unfold StrictFactorRealizedHistoryIndex
  infer_instance

/-- The realized predecessor state attached to a fixed strict-factor
insertion-history index. -/
def strictFactorRealizedPredecessorState
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (a : StrictFactorRealizedHistoryIndex refined k e) :
    CartanChain.ChainState g :=
  (chain a.1 (a.2 + 1)).state (e a.1 + a.2)

omit [T2Space M] in
/-- The predecessor states occurring in one fixed strict-factor realization
form a finite set.  This is topology-free and records the strongest concrete
compactness fact available for the current `ChainState`, which has no topology
instance. -/
theorem strictFactorRealizedPredecessorState_range_finite
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) :
    Set.Finite
      (Set.range
        (strictFactorRealizedPredecessorState seed refined k e chain)) := by
  classical
  exact Set.finite_range _

end FixedRealizedHistories

section AbstractIteration

/-- The positive threshold currently available from a two-stage adaptive
certificate.  Before the first test passes it is `epsilon`; afterwards it is
the smaller of `epsilon` and the newly available second radius. -/
def twoStageActiveThreshold
    (epsilon firstDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ) (n : ℕ) : ℝ :=
  if h : firstDefect n < epsilon n then min (epsilon n) (radius n h)
  else epsilon n

/-- A stage validates precisely when its first test unlocks the second
radius and its second defect lies below that radius. -/
def TwoStageValidated
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ) (n : ℕ) : Prop :=
  ∃ h : firstDefect n < epsilon n, secondDefect n < radius n h

theorem twoStageActiveThreshold_pos
    (epsilon firstDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    (hepsilon : ∀ n, 0 < epsilon n)
    (hradius : ∀ n h, 0 < radius n h) (n : ℕ) :
    0 < twoStageActiveThreshold epsilon firstDefect radius n := by
  by_cases h : firstDefect n < epsilon n
  · simp [twoStageActiveThreshold, h, hepsilon n, hradius n h]
  · simp [twoStageActiveThreshold, h, hepsilon n]

/-- One failed response step strictly lowers the active positive threshold.

The response bounds refer only to the preceding threshold, so there is no
circular requirement involving the response stage's not-yet-chosen radius. -/
theorem twoStageActiveThreshold_strict_descent_of_not_validated
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    {n : ℕ}
    (hfirstResponse : firstDefect (n + 1) <
      twoStageActiveThreshold epsilon firstDefect radius n)
    (hsecondResponse : secondDefect (n + 1) <
      twoStageActiveThreshold epsilon firstDefect radius n)
    (hfail : ¬TwoStageValidated epsilon firstDefect secondDefect radius
      (n + 1)) :
    twoStageActiveThreshold epsilon firstDefect radius (n + 1) <
      twoStageActiveThreshold epsilon firstDefect radius n := by
  by_cases hfirst : firstDefect (n + 1) < epsilon (n + 1)
  · have hnotSecond : ¬secondDefect (n + 1) < radius (n + 1) hfirst := by
      intro hsecond
      exact hfail ⟨hfirst, hsecond⟩
    have hradius_le : radius (n + 1) hfirst ≤ secondDefect (n + 1) :=
      le_of_not_gt hnotSecond
    rw [twoStageActiveThreshold]
    simp only [dif_pos hfirst]
    exact (min_le_right _ _).trans_lt
      (hradius_le.trans_lt hsecondResponse)
  · have hepsilon_le : epsilon (n + 1) ≤ firstDefect (n + 1) :=
      le_of_not_gt hfirst
    rw [twoStageActiveThreshold]
    simp only [dif_neg hfirst]
    exact hepsilon_le.trans_lt hfirstResponse

/-- Finite adaptive iteration has an exact dichotomy: a response validates,
or all active positive minima encountered so far form a strict descent. -/
theorem exists_validated_or_activeThreshold_strict_descent
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    (hresponse : ∀ n,
      firstDefect (n + 1) <
          twoStageActiveThreshold epsilon firstDefect radius n ∧
        secondDefect (n + 1) <
          twoStageActiveThreshold epsilon firstDefect radius n)
    (N : ℕ) :
    (∃ n, 1 ≤ n ∧ n ≤ N ∧
      TwoStageValidated epsilon firstDefect secondDefect radius n) ∨
      ∀ n < N,
        twoStageActiveThreshold epsilon firstDefect radius (n + 1) <
          twoStageActiveThreshold epsilon firstDefect radius n := by
  by_cases hvalid : ∃ n, 1 ≤ n ∧ n ≤ N ∧
      TwoStageValidated epsilon firstDefect secondDefect radius n
  · exact Or.inl hvalid
  · right
    intro n hn
    apply twoStageActiveThreshold_strict_descent_of_not_validated
      epsilon firstDefect secondDefect radius (hresponse n).1 (hresponse n).2
    intro hstage
    exact hvalid ⟨n + 1, by omega, by omega, hstage⟩

/-- Positivity at every stage and arbitrarily many strict response steps do
not by themselves force validation: the available radii may converge to
zero.  This concrete counterexample shows why a compactness theorem uniform
over changing histories, or an equivalent lower-bound principle, is genuinely
new input rather than a consequence of finite minima. -/
theorem strict_responses_with_positive_radii_can_fail_forever :
    let epsilon : ℕ → ℝ := fun n ↦ (1 / 2 : ℝ) ^ n
    let firstDefect : ℕ → ℝ := epsilon
    let secondDefect : ℕ → ℝ := fun _ ↦ 0
    let radius : ∀ n, firstDefect n < epsilon n → ℝ :=
      fun n h ↦ False.elim ((lt_irrefl (epsilon n)) h)
    (∀ n, 0 < epsilon n) ∧
      (∀ n h, 0 < radius n h) ∧
      (∀ n,
        firstDefect (n + 1) <
            twoStageActiveThreshold epsilon firstDefect radius n ∧
          secondDefect (n + 1) <
            twoStageActiveThreshold epsilon firstDefect radius n) ∧
      ∀ n, ¬TwoStageValidated epsilon firstDefect secondDefect radius n := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    positivity
  · intro n h
    exact False.elim ((lt_irrefl ((1 / 2 : ℝ) ^ n)) h)
  · intro n
    have hpow : 0 < (1 / 2 : ℝ) ^ n := by positivity
    constructor
    · simp only [twoStageActiveThreshold, lt_self_iff_false, ↓reduceDIte,
        pow_succ]
      nlinarith
    · simp only [twoStageActiveThreshold, lt_self_iff_false, ↓reduceDIte]
      exact hpow
  · intro n
    simp [TwoStageValidated]

/-- A uniform positive lower bound on active thresholds, together with
uniformly vanishing two-stage defects, forces a validating stage.

This is the exact additional uniformity that compactness would have to supply
over all changing realized histories in order to close adaptive feedback. -/
theorem exists_twoStageValidated_of_uniform_lowerBound_of_vanishing_defects
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    {delta : ℝ}
    (hlower : ∀ n, delta ≤
      twoStageActiveThreshold epsilon firstDefect radius n)
    (hvanish : ∃ N, ∀ n ≥ N,
      firstDefect n < delta ∧ secondDefect n < delta) :
    ∃ n, TwoStageValidated epsilon firstDefect secondDefect radius n := by
  rcases hvanish with ⟨N, hN⟩
  have hfirstBelow := (hN N le_rfl).1
  have hsecondBelow := (hN N le_rfl).2
  have hfirst : firstDefect N < epsilon N := by
    by_contra hnot
    have hactive : twoStageActiveThreshold epsilon firstDefect radius N =
        epsilon N := by
      simp [twoStageActiveThreshold, hnot]
    have hepsilon_le : epsilon N ≤ firstDefect N := le_of_not_gt hnot
    have : delta ≤ firstDefect N := by
      calc
        delta ≤ twoStageActiveThreshold epsilon firstDefect radius N :=
          hlower N
        _ = epsilon N := hactive
        _ ≤ firstDefect N := hepsilon_le
    exact (not_lt_of_ge this) hfirstBelow
  refine ⟨N, hfirst, ?_⟩
  have hradiusLower : delta ≤ radius N hfirst := by
    have hactive := hlower N
    simp only [twoStageActiveThreshold, dif_pos hfirst] at hactive
    exact hactive.trans (min_le_right _ _)
  exact hsecondBelow.trans_le hradiusLower

section CompactHistoryUniformity

/-- A positive lower-semicontinuous radius selector on a nonempty compact
history set has one positive uniform lower bound.

Lower semicontinuity is the minimal one-sided regularity needed here:
continuity is unnecessary.  This packages the precise compactness step that a
geometric space of all reachable histories would need to discharge. -/
theorem exists_uniform_positive_lowerBound_on_compact_of_lowerSemicontinuous
    {A : Type*} [TopologicalSpace A] {K : Set A}
    (hKne : K.Nonempty) (hK : IsCompact K) (threshold : A → ℝ)
    (hthreshold : LowerSemicontinuousOn threshold K)
    (hpositive : ∀ a ∈ K, 0 < threshold a) :
    ∃ delta > (0 : ℝ), ∀ a ∈ K, delta ≤ threshold a := by
  rcases hthreshold.exists_isMinOn hKne hK with ⟨a, ha, hminimum⟩
  exact ⟨threshold a, hpositive a ha, fun b hb ↦ hminimum hb⟩

/-- Compact-history closure of the adaptive feedback loop.

The stage histories must lie in one fixed compact set, and their active
thresholds must be restrictions of one positive lower-semicontinuous selector
on that set.  Compactness then supplies the uniform lower bound required by
`exists_twoStageValidated_of_uniform_lowerBound_of_vanishing_defects`.

This theorem is directly composable with a future geometric parameterization
of reachable Cartan-chain histories.  The present repository has neither that
compact parameterization nor the lower-semicontinuity theorem for its adaptive
radius selector. -/
theorem exists_twoStageValidated_of_compact_history_lowerSemicontinuous_threshold
    {A : Type*} [TopologicalSpace A] {K : Set A}
    (hK : IsCompact K) (stage : ℕ → A) (hstage : ∀ n, stage n ∈ K)
    (threshold : A → ℝ)
    (hthreshold : LowerSemicontinuousOn threshold K)
    (hpositive : ∀ a ∈ K, 0 < threshold a)
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    (hparameterized : ∀ n,
      twoStageActiveThreshold epsilon firstDefect radius n =
        threshold (stage n))
    (hvanish : ∀ delta > (0 : ℝ), ∃ N, ∀ n ≥ N,
      firstDefect n < delta ∧ secondDefect n < delta) :
    ∃ n, TwoStageValidated epsilon firstDefect secondDefect radius n := by
  have hKne : K.Nonempty := ⟨stage 0, hstage 0⟩
  rcases
      exists_uniform_positive_lowerBound_on_compact_of_lowerSemicontinuous
        hKne hK threshold hthreshold hpositive with
    ⟨delta, hdelta, hlower⟩
  apply exists_twoStageValidated_of_uniform_lowerBound_of_vanishing_defects
    epsilon firstDefect secondDefect radius
  · intro n
    rw [hparameterized n]
    exact hlower (stage n) (hstage n)
  · exact hvanish delta hdelta

/-- Continuous positive threshold selectors are a convenient stronger input
to the compact-history closure theorem. -/
theorem exists_twoStageValidated_of_compact_history_continuous_threshold
    {A : Type*} [TopologicalSpace A] {K : Set A}
    (hK : IsCompact K) (stage : ℕ → A) (hstage : ∀ n, stage n ∈ K)
    (threshold : A → ℝ) (hthreshold : ContinuousOn threshold K)
    (hpositive : ∀ a ∈ K, 0 < threshold a)
    (epsilon firstDefect secondDefect : ℕ → ℝ)
    (radius : ∀ n, firstDefect n < epsilon n → ℝ)
    (hparameterized : ∀ n,
      twoStageActiveThreshold epsilon firstDefect radius n =
        threshold (stage n))
    (hvanish : ∀ delta > (0 : ℝ), ∃ N, ∀ n ≥ N,
      firstDefect n < delta ∧ secondDefect n < delta) :
    ∃ n, TwoStageValidated epsilon firstDefect secondDefect radius n := by
  apply exists_twoStageValidated_of_compact_history_lowerSemicontinuous_threshold
    hK stage hstage threshold hthreshold.lowerSemicontinuousOn hpositive
      epsilon firstDefect secondDefect radius hparameterized hvanish

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold I ∞ M] in
/-- Any positive threshold assignment on the exact histories of one fixed
strict-factor realization has a common positive lower bound.  The proof views
the finite history index as a discrete compact space and instantiates the
compact lower-semicontinuity theorem above. -/
theorem exists_common_positive_threshold_for_fixed_strictFactor_histories
    (refined : ℕ → M) (k : ℕ) (e : ℕ → ℕ)
    (threshold : StrictFactorRealizedHistoryIndex refined k e → ℝ)
    (hpositive : ∀ a, 0 < threshold a) :
    ∃ delta > (0 : ℝ), ∀ a, delta ≤ threshold a := by
  classical
  let A := StrictFactorRealizedHistoryIndex refined k e
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      refine ⟨1, zero_lt_one, ?_⟩
      intro a
      exact isEmptyElim a
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      have hbound :=
        exists_uniform_positive_lowerBound_on_compact_of_lowerSemicontinuous
          (K := Set.univ) Set.univ_nonempty isCompact_univ threshold
          continuous_of_discreteTopology.continuousOn.lowerSemicontinuousOn
          (fun a _ha ↦ hpositive a)
      simpa using hbound

/-- A countable succession of individually finite realized-history fibers is
not compact merely because every stage is finite.  In the discrete topology,
even the union with one history per stage is noncompact.

This is the precise failure of trying to apply the fixed-grid finite minimum
at every refinement stage: a compactness or accumulation theorem controlling
the union across stages is additional geometric content. -/
theorem countable_union_of_finite_history_fibers_not_compact_in_general :
    letI : TopologicalSpace (Σ _ : ℕ, Fin 1) := ⊥
    ¬IsCompact (Set.univ : Set (Σ _ : ℕ, Fin 1)) := by
  letI : TopologicalSpace (Σ _ : ℕ, Fin 1) := ⊥
  letI : DiscreteTopology (Σ _ : ℕ, Fin 1) := ⟨rfl⟩
  intro hcompact
  have hfiniteUniv : (Set.univ : Set (Σ _ : ℕ, Fin 1)).Finite :=
    hcompact.finite_of_discrete
  letI : Finite (Σ _ : ℕ, Fin 1) := Finite.of_finite_univ hfiniteUniv
  have hinjective : Function.Injective
      (fun n : ℕ ↦ (⟨n, 0⟩ : Σ _ : ℕ, Fin 1)) := by
    intro n m hnm
    exact congrArg Sigma.fst hnm
  letI : Finite ℕ := Finite.of_injective _ hinjective
  exact not_finite ℕ

end CompactHistoryUniformity

end AbstractIteration

end DifferentialSuccessorAdaptiveFeedbackIteration
end Poincare
