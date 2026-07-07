import Poincare.Global.BlockDiagonal
import Poincare.Global.ScalarPin
import Poincare.Global.UniformFlowExport

/-!
# Transverse block exports at the uniform-flow selector

This module packages the bounded transverse-transverse block identities at the
same source and target families exported by `UniformFlowExport`.  The initial
norm-state identities are discharged from the enriched base and linearized
packages; the remaining quantitative norm-system bounds are kept as explicit
non-vacuous hypotheses and are passed to the bounded `ScalarPin` adapters.
-/

noncomputable section

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

open Bundle Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace TransverseExport

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

omit [T2Space M] in
/-- The enriched selector starts every hosted linearized field at zero position. -/
theorem normA_initial_eq_zero_of_enriched_packages
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} {aPkg : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ) :
    ∀ w : E3,
      JacobiNormSystem.normA g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1) 0 = 0 := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hbase with ⟨hγ0, _hγder, _hγder0T, _hγAt, _hγmem, _hγtarget,
    _hγtarget0T, _hγcut, _hγχ0T, _hspeed, _hendpoint⟩
  rcases hlin with ⟨hΨ0, _hΨder, _hΨder0T, _hΨAt, _hflow, _hspeedConst⟩
  intro w
  have hγ0_fst := congrArg Prod.fst hγ0
  have hΨ0_fst := congrArg Prod.fst (hΨ0 w)
  simp [JacobiNormSystem.normA, hγ0_fst, hΨ0_fst]

omit [T2Space M] in
/-- The enriched selector starts the mixed norm at zero. -/
theorem normB_initial_eq_zero_of_enriched_packages
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} {aPkg : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ) :
    ∀ w : E3,
      JacobiNormSystem.normB g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ => (Ψ w τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 = 0 := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hbase with ⟨hγ0, _hγder, _hγder0T, _hγAt, _hγmem, _hγtarget,
    _hγtarget0T, _hγcut, _hγχ0T, _hspeed, _hendpoint⟩
  rcases hlin with ⟨hΨ0, _hΨder, _hΨder0T, _hΨAt, _hflow, _hspeedConst⟩
  intro w
  have hγ0_fst := congrArg Prod.fst hγ0
  have hΨ0_fst := congrArg Prod.fst (hΨ0 w)
  simp [JacobiNormSystem.normB, hγ0_fst, hΨ0_fst]

omit [T2Space M] in
/--
The enriched selector starts the derivative norm at the rescaled anchor metric
quadratic value.
-/
theorem normC_initial_eq_anchor_of_enriched_packages
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T ε : ℝ} {aPkg : ℝ≥0} {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3}
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ) :
    ∀ w : E3,
      JacobiNormSystem.normC g x₀
          (fun τ : ℝ => (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
          (fun τ : ℝ =>
            (Ψ w τ).2 +
              (chartChristoffelField g x₀
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).1)
                (α (extChartAt I3 x₀ x₀, T⁻¹ • v) τ).2 (Ψ w τ).1) 0 =
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w) := by
  dsimp [EnrichedCascade.BaseCurvePackage] at hbase
  dsimp [EnrichedCascade.LinearizedFamilyPackage] at hlin
  rcases hbase with ⟨hγ0, _hγder, _hγder0T, _hγAt, _hγmem, _hγtarget,
    _hγtarget0T, _hγcut, _hγχ0T, _hspeed, _hendpoint⟩
  rcases hlin with ⟨hΨ0, _hΨder, _hΨder0T, _hΨAt, _hflow, _hspeedConst⟩
  intro w
  have hγ0_fst := congrArg Prod.fst hγ0
  have hγ0_snd := congrArg Prod.snd hγ0
  have hΨ0_fst := congrArg Prod.fst (hΨ0 w)
  have hΨ0_snd := congrArg Prod.snd (hΨ0 w)
  simp [JacobiNormSystem.normC, hγ0_fst, hγ0_snd, hΨ0_fst, hΨ0_snd]

/--
Source transverse block at an enriched selector datum.  The bounded norm-system
side conditions are exactly the quantitative data consumed by `ScalarPin`;
the initial norm identities are supplied here from the enriched packages.
-/
theorem source_transverseTransverse_of_selector_bounded_data
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1) (x₀ : M)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage g x₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage g x₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.sourceAnchorChartMetric g x₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm B : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hAopNormPL : ‖Aop‖ ≤ (KNorm : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ))
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric g.inner x₀
          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.sourceAnchorChartMetric g x₀) v a') := by
  exact
    ScalarPin.source_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
      (g := g) hcurv (x₀ := x₀) (T := T) (ε := ε) (speed := speed)
      (C := C) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      hAopNormPL hcenter hbound hmulT hAop hC hAopNorm hqBound
      hgronwallRadius hpinnedRadius
      (normA_initial_eq_zero_of_enriched_packages
        (g := g) (x₀ := x₀) hbase hlin)
      (normB_initial_eq_zero_of_enriched_packages
        (g := g) (x₀ := x₀) hbase hlin)
      (normC_initial_eq_anchor_of_enriched_packages
        (g := g) (x₀ := x₀) hbase hlin)

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/-- Target transverse block at the enriched round-sphere selector datum. -/
theorem target_transverseTransverse_of_selector_bounded_data
    (p₀ : RoundSphere3)
    {T ε speed C qmax : ℝ} {aPkg : ℝ≥0}
    {α : E3 × E3 → ℝ → E3 × E3}
    {Ψ : E3 → ℝ → E3 × E3} {v : E3} (hT : 0 < T)
    (hbase : EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀ T ε aPkg α v)
    (hlin : EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀ T ε α v Ψ)
    (hΨadd : ∀ w w' : E3,
      (Ψ (w + w') T).1 = (Ψ w T).1 + (Ψ w' T).1)
    (hΨsmul : ∀ (c : ℝ) (w : E3),
      (Ψ (c • w) T).1 = c • (Ψ w T).1)
    (hspeed_ne : speed ≠ 0)
    (hanchorSpeed :
      CartanMap.targetAnchorChartMetric p₀ (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm KNorm B : ℝ≥0} (hRpos : 0 < (R : ℝ))
    (hAopNormPL : ‖Aop‖ ≤ (KNorm : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ))
    (hAop : ∀ x : Triple,
      Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1))
    (hC : 0 ≤ C) (hAopNorm : ‖Aop‖ ≤ C)
    (hqBound : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        |chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax)
    (hgronwallRadius :
      qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ))
    (hpinnedRadius : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      CartanMap.targetAnchorChartMetric p₀ v w = 0 →
        (MembershipBound.speedPinnedMembershipRadius speed
          (chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) :
    ∀ a a' : E3,
      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
          ((expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀) v)
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a) T).1
          (Ψ (CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p₀) v a') T).1 =
        JacobiNormSystem.speedPinnedScale speed T *
          CartanMap.targetAnchorChartMetric p₀
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a)
            (T⁻¹ • CartanPullback.transversePart
              (CartanMap.targetAnchorChartMetric p₀) v a') := by
  exact
    ScalarPin.target_transverseTransverse_of_enriched_gronwall_feed_of_center_norm_bound
      (p₀ := p₀) (T := T) (ε := ε) (speed := speed)
      (C := C) (qmax := qmax) (aPkg := aPkg) (α := α) (Ψ := Ψ) (v := v)
      hT hbase hlin hΨadd hΨsmul hspeed_ne hanchorSpeed Aop hRpos
      hAopNormPL hcenter hbound hmulT hAop hC hAopNorm hqBound
      hgronwallRadius hpinnedRadius
      (normA_initial_eq_zero_of_enriched_packages
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) hbase hlin)
      (normB_initial_eq_zero_of_enriched_packages
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) hbase hlin)
      (normC_initial_eq_anchor_of_enriched_packages
        (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀) hbase hlin)

/--
Common source/target selector export.  For every vector in the selected ball,
the theorem returns the same `Ψs` and `Ψt` families produced by
`UniformFlowExport`, together with continuations that turn bounded norm-system
data into the source and target transverse block identities consumed by
`BlockDiagonal`.
-/
theorem exists_common_time_with_selector_transverse_block_exports
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) (p₀ : RoundSphere3)
    (align : CartanMap.TangentAlignment g x₀ p₀) :
    ∃ ρ > (0 : ℝ), ∃ T > (0 : ℝ),
      ∀ v : E3, ‖v‖ < ρ →
        ∃ εs : ℝ, ∃ as : ℝ≥0, ∃ αs : E3 × E3 → ℝ → E3 × E3,
          ∃ εt : ℝ, ∃ aTgt : ℝ≥0, ∃ αt : E3 × E3 → ℝ → E3 × E3,
            ∃ Ψs : E3 → ℝ → E3 × E3,
              ∃ hadds : ∀ w w' : E3,
                (Ψs (w + w') T).1 = (Ψs w T).1 + (Ψs w' T).1,
              ∃ hsmuls : ∀ (c : ℝ) (w : E3),
                (Ψs (c • w) T).1 = c • (Ψs w T).1,
              ∃ Ψt : E3 → ℝ → E3 × E3,
                ∃ haddt : ∀ w w' : E3,
                  (Ψt (w + w') T).1 = (Ψt w T).1 + (Ψt w' T).1,
                ∃ hsmult : ∀ (c : ℝ) (w : E3),
                  (Ψt (c • w) T).1 = c • (Ψt w T).1,
                  v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source ∧
                  align v ∈
                    (expAtChartOpenPartialHomeomorph
                      (g := roundSphereMetric3) p₀).source ∧
                  EnrichedCascade.BaseCurvePackage g x₀ T εs as αs v ∧
                  EnrichedCascade.LinearizedFamilyPackage g x₀ T εs αs v Ψs ∧
                  HasStrictFDerivAt
                    (expAtChartOpenPartialHomeomorph (g := g) x₀)
                    (linearizedEndpointCLM (Ψ := Ψs) T hadds hsmuls) v ∧
                  (Ψs v T).1 =
                    T • (αs (extChartAt I3 x₀ x₀, T⁻¹ • v) T).2 ∧
                  EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀
                    T εt aTgt αt (align v) ∧
                  EnrichedCascade.LinearizedFamilyPackage roundSphereMetric3 p₀
                    T εt αt (align v) Ψt ∧
                  HasStrictFDerivAt
                    (expAtChartOpenPartialHomeomorph (g := roundSphereMetric3) p₀)
                    (linearizedEndpointCLM (Ψ := Ψt) T haddt hsmult) (align v) ∧
                  (Ψt (align v) T).1 =
                    T • (αt (extChartAt I3 p₀ p₀, T⁻¹ • align v) T).2 ∧
                  (∀ {speed C qmax : ℝ} {Aop : Triple →L[ℝ] Triple}
                      {R radius rNorm LNorm KNorm B : ℝ≥0},
                    speed ≠ 0 →
                    CartanMap.sourceAnchorChartMetric g x₀
                        (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2 →
                    0 < (R : ℝ) →
                    ‖Aop‖ ≤ (KNorm : ℝ) →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      ‖(((0 : ℝ), (0 : ℝ),
                        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ +
                          (radius : ℝ) ≤ (B : ℝ)) →
                    ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ) →
                    (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ) →
                    (∀ x : Triple,
                      Aop x =
                        (2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
                          -2 * speed ^ 2 * x.2.1)) →
                    0 ≤ C → ‖Aop‖ ≤ C →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
                        |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) →
                    qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ) →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
                        (MembershipBound.speedPinnedMembershipRadius speed
                          (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
                            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) →
                    ∀ a a' : E3,
                      CovariantDerivative.chartMetric g.inner x₀
                          ((expAtChartOpenPartialHomeomorph (g := g) x₀) v)
                          (Ψs (CartanPullback.transversePart
                            (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1
                          (Ψs (CartanPullback.transversePart
                            (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1 =
                        JacobiNormSystem.speedPinnedScale speed T *
                          CartanMap.sourceAnchorChartMetric g x₀
                            (T⁻¹ • CartanPullback.transversePart
                              (CartanMap.sourceAnchorChartMetric g x₀) v a)
                            (T⁻¹ • CartanPullback.transversePart
                              (CartanMap.sourceAnchorChartMetric g x₀) v a')) ∧
                  (∀ {speed C qmax : ℝ} {Aop : Triple →L[ℝ] Triple}
                      {R radius rNorm LNorm KNorm B : ℝ≥0},
                    speed ≠ 0 →
                    CartanMap.targetAnchorChartMetric p₀
                        (T⁻¹ • align v) (T⁻¹ • align v) = speed ^ 2 →
                    0 < (R : ℝ) →
                    ‖Aop‖ ≤ (KNorm : ℝ) →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      ‖(((0 : ℝ), (0 : ℝ),
                        chartGeodesicMetric roundSphereMetric3 p₀
                          (extChartAt I3 p₀ p₀)
                          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ +
                          (radius : ℝ) ≤ (B : ℝ)) →
                    ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ) →
                    (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ) →
                    (∀ x : Triple,
                      Aop x =
                        (2 * x.2.1, x.2.2 - speed ^ 2 * x.1,
                          -2 * speed ^ 2 * x.2.1)) →
                    0 ≤ C → ‖Aop‖ ≤ C →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      CartanMap.targetAnchorChartMetric p₀ (align v) w = 0 →
                        |chartGeodesicMetric roundSphereMetric3 p₀
                          (extChartAt I3 p₀ p₀)
                          (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) →
                    qmax * Real.exp (C * T) + qmax ≤ (radius : ℝ) →
                    (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
                      CartanMap.targetAnchorChartMetric p₀ (align v) w = 0 →
                        (MembershipBound.speedPinnedMembershipRadius speed
                          (chartGeodesicMetric roundSphereMetric3 p₀
                            (extChartAt I3 p₀ p₀)
                            (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)) →
                    ∀ a a' : E3,
                      CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
                          ((expAtChartOpenPartialHomeomorph
                            (g := roundSphereMetric3) p₀) (align v))
                          (Ψt (CartanPullback.transversePart
                            (CartanMap.targetAnchorChartMetric p₀) (align v) a) T).1
                          (Ψt (CartanPullback.transversePart
                            (CartanMap.targetAnchorChartMetric p₀) (align v) a') T).1 =
                        JacobiNormSystem.speedPinnedScale speed T *
                          CartanMap.targetAnchorChartMetric p₀
                            (T⁻¹ • CartanPullback.transversePart
                              (CartanMap.targetAnchorChartMetric p₀) (align v) a)
                            (T⁻¹ • CartanPullback.transversePart
                              (CartanMap.targetAnchorChartMetric p₀) (align v) a')) := by
  rcases
      UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors
        (g := g) (x₀ := x₀) (p₀ := p₀) align with
    ⟨ρ, hρ_pos, T, hT_pos, εs, _hεs_pos, as, αs, εlinS, _hεlinS_pos,
      hεlinS_le, _hT_lt_εlinS, _δs, _hδs_pos, _hα0S, _hαderS,
      _hαmemS, _hαtargetS, _hexpS, _aPLS, _rS, _LipS, _KS, _hrS,
      εt, _hεt_pos, aTgt, αt, εlinT, _hεlinT_pos, hεlinT_le,
      _hT_lt_εlinT, _δt, _hδt_pos, _hα0T, _hαderT, _hαmemT,
      _hαtargetT, _hexpT, _aPLT, _rT, _LipT, _KT, _hrT, hsel⟩
  refine ⟨ρ, hρ_pos, T, hT_pos, ?_⟩
  intro v hv
  rcases hsel v hv with
    ⟨hvsrc, hvtgt, _hvscaledS, _hvscaledT, hbaseS, hbaseT, _hplS,
      hΨsPack, _hplT, Ψt, haddt, hsmult, hlinT, hstrictT, hRayT⟩
  rcases hΨsPack with ⟨Ψs, hadds, hsmuls, hlinS, hstrictS, hRayS⟩
  have hbaseSlin :
      EnrichedCascade.BaseCurvePackage g x₀ T εlinS as αs v :=
    IntervalAlign.baseCurvePackage_restrict_interval
      (g := g) (x₀ := x₀) (ε' := εlinS) hεlinS_le hbaseS
  have hbaseTlin :
      EnrichedCascade.BaseCurvePackage roundSphereMetric3 p₀
        T εlinT aTgt αt (align v) :=
    IntervalAlign.baseCurvePackage_restrict_interval
      (M := RoundSphere3) (g := roundSphereMetric3) (x₀ := p₀)
      (ε' := εlinT) hεlinT_le hbaseT
  refine
    ⟨εlinS, as, αs, εlinT, aTgt, αt, Ψs, hadds, hsmuls, Ψt, haddt, hsmult,
      hvsrc, hvtgt, hbaseSlin, hlinS, hstrictS, hRayS, hbaseTlin, hlinT,
      hstrictT, hRayT, ?_, ?_⟩
  · intro speed C qmax Aop R radius rNorm LNorm KNorm B hspeed_ne
      hanchorSpeed hRpos hAopNormPL hcenter hbound hmulT hAop hC
      hAopNorm hqBound hgronwallRadius hpinnedRadius
    exact
      source_transverseTransverse_of_selector_bounded_data
        (g := g) hcurv (x₀ := x₀) (T := T) (ε := εlinS)
        (speed := speed) (C := C) (qmax := qmax) (aPkg := as)
        (α := αs) (Ψ := Ψs) (v := v) hT_pos hbaseSlin hlinS hadds hsmuls
        hspeed_ne hanchorSpeed Aop hRpos hAopNormPL hcenter hbound hmulT
        hAop hC hAopNorm hqBound hgronwallRadius hpinnedRadius
  · intro speed C qmax Aop R radius rNorm LNorm KNorm B hspeed_ne
      hanchorSpeed hRpos hAopNormPL hcenter hbound hmulT hAop hC
      hAopNorm hqBound hgronwallRadius hpinnedRadius
    exact
      target_transverseTransverse_of_selector_bounded_data
        (p₀ := p₀) (T := T) (ε := εlinT) (speed := speed) (C := C)
        (qmax := qmax) (aPkg := aTgt) (α := αt) (Ψ := Ψt)
        (v := align v) hT_pos hbaseTlin hlinT haddt hsmult hspeed_ne
        hanchorSpeed Aop hRpos hAopNormPL hcenter hbound hmulT hAop hC
        hAopNorm hqBound hgronwallRadius hpinnedRadius

end TransverseExport
end Poincare
