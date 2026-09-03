import Poincare.Global.CovRicciNormBasis
import Poincare.Global.MetricFlowJointCovRicciEntryRegularity

/-!
# Joint continuity of the coordinate covariant Ricci norm

This module forms the full fixed-basis contraction of the coordinate
covariant Ricci entries, identifies it with the intrinsic squared norm in the
cutoff-one chart zone, and transfers coordinate continuity back to the
space-time manifold.
-/

noncomputable section

open Bundle Filter Function
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

/-- The full fixed-basis contraction of two coordinate covariant Ricci
entries against three inverse-metric coefficient fields. -/
noncomputable def anchorChartCovRicciNormSqFlow
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (x : M)
    (t : ℝ) (z : E) : ℝ :=
  let e := Module.finBasis ℝ E
  ∑ a, ∑ i, ∑ j, ∑ b, ∑ k, ∑ l,
    anchorChartInverseMetricCoeffFlow gt x t z a b *
      anchorChartInverseMetricCoeffFlow gt x t z i k *
      anchorChartInverseMetricCoeffFlow gt x t z j l *
      anchorChartCovRicciEntryFlow gt x t z (e b) (e k) (e l) *
      anchorChartCovRicciEntryFlow gt x t z (e a) (e i) (e j)

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

/-- Joint `C³` metric entries make the full coordinate covariant Ricci norm
contraction jointly continuous at the time-space anchor. -/
theorem anchorChartCovRicciNormSqFlow_continuousAt_of_metricEntries
    {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt
      (Function.uncurry (anchorChartCovRicciNormSqFlow gt x))
      (t₀, extChartAt I x x) := by
  classical
  let e := Module.finBasis ℝ E
  unfold anchorChartCovRicciNormSqFlow
  dsimp only
  apply continuousAt_finset_sum_real Finset.univ
  intro a _ha
  apply continuousAt_finset_sum_real Finset.univ
  intro i _hi
  apply continuousAt_finset_sum_real Finset.univ
  intro j _hj
  apply continuousAt_finset_sum_real Finset.univ
  intro b _hb
  apply continuousAt_finset_sum_real Finset.univ
  intro k _hk
  apply continuousAt_finset_sum_real Finset.univ
  intro l _hl
  have hab : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z a b))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint a b).continuousAt
  have hik : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z i k))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint i k).continuousAt
  have hjl : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartInverseMetricCoeffFlow gt x t z j l))
      (t₀, extChartAt I x x) :=
    (anchorChartInverseMetricCoeffFlow_jointContDiffAt_two_of_metricEntries
      hJoint j l).continuousAt
  have hbkl : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z
          (e b) (e k) (e l)))
      (t₀, extChartAt I x x) :=
    anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
      hJoint (e b) (e k) (e l)
  have haij : ContinuousAt
      (Function.uncurry
        (fun t z ↦ anchorChartCovRicciEntryFlow gt x t z
          (e a) (e i) (e j)))
      (t₀, extChartAt I x x) :=
    anchorChartCovRicciEntryFlow_continuousAt_of_metricEntries
      hJoint (e a) (e i) (e j)
  exact ((((hab.mul hik).mul hjl).mul hbkl).mul haij)

set_option maxHeartbeats 5000000 in
/-- On the cutoff-one part of the preferred chart, the full coordinate
contraction is the intrinsic squared norm of the covariant Ricci derivative. -/
theorem anchorChartCovRicciNormSqFlow_eq_covRicciNormSqAt_zone
    (gt : ℝ → ClosedSmoothRiemannianMetric n M)
    (x : M) (t : ℝ) {z : E}
    (hz : z ∈ (extChartAt I x).target)
    (hχone : ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1) :
    anchorChartCovRicciNormSqFlow gt x t z =
      covRicciNormSqAt (gt t) ((extChartAt I x).symm z) := by
  classical
  let g : ClosedSmoothRiemannianMetric n M := gt t
  let y : M := (extChartAt I x).symm z
  letI : FiniteDimensional ℝ (TM y) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let e : E ≃L[ℝ] E := chartInverseTangentEquiv x z hz
  let b := Module.finBasis ℝ E
  let B := chartTangentBasisAt (n := n) (M := M) x hz
  let G := anchorBlendedMetricFlow gt x t z
  let raised : Fin (Module.finrank ℝ E) → E := fun i ↦
    G.inverse (LinearMap.toContinuousLinearMap (b.coord i))
  let T : TM y →ₗ[ℝ] TM y →ₗ[ℝ] TM y →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦
        { toFun := fun p ↦
            { toFun := fun q ↦
                covTensor2DerivAt g (ricciVariationField g) y v p q
              map_add' := fun q q' ↦
                covTensor2DerivAt_add_right
                  (g := g) (h := ricciVariationField g) (x := y)
                  (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y)
                  (tensor2AddRight_ricciVariationField g) v p q q'
              map_smul' := fun c q ↦
                covTensor2DerivAt_smul_right
                  (g := g) (h := ricciVariationField g) (x := y)
                  (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y)
                  (tensor2SMulRight_ricciVariationField g) c v p q }
          map_add' := by
            intro p p'
            apply LinearMap.ext
            intro q
            exact covTensor2DerivAt_add_left
              (g := g) (h := ricciVariationField g) (x := y)
              (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y)
              (tensor2AddLeft_ricciVariationField g) v p p' q
          map_smul' := by
            intro c p
            apply LinearMap.ext
            intro q
            exact covTensor2DerivAt_smul_left
              (g := g) (h := ricciVariationField g) (x := y)
              (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g y)
              (tensor2SMulLeft_ricciVariationField g) c v p q }
      map_add' := by
        intro v v'
        apply LinearMap.ext
        intro p
        apply LinearMap.ext
        intro q
        exact covTensor2DerivAt_add_deriv
          (g := g) (h := ricciVariationField g) (x := y)
          (tensor2AddLeft_ricciVariationField g)
          (tensor2AddRight_ricciVariationField g) v v' p q
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro p
        apply LinearMap.ext
        intro q
        exact covTensor2DerivAt_smul_deriv
          (g := g) (h := ricciVariationField g) (x := y)
          (tensor2SMulLeft_ricciVariationField g)
          (tensor2SMulRight_ricciVariationField g) c v p q }
  have hχ : GeodesicTransport.cutoff (n := n) x z = 1 :=
    hχone.self_of_nhds
  have hBasis : ∀ i, B i = e (b i) := by
    intro i
    rw [show B = b.map e.toLinearEquiv by
      simpa [B, b, e] using
        chartTangentBasisAt_eq_finBasis_map_chartInverseTangentEquiv x hz]
    rfl
  have hRaised : ∀ i,
      e (raised i) = metricDualVectorAt g y (B.coord i) := by
    intro i
    simpa [raised, G, g, y, e, B, b] using
      chartInverseTangentEquiv_anchorBlendedMetricFlow_inverse_coord_eq_metricDualVectorAt_zone
        gt x t hz hχ i
  have hInv : ∀ i k,
      anchorChartInverseMetricCoeffFlow gt x t z i k =
        b.coord k (raised i) := by
    intro i k
    rfl
  have hEntry : ∀ a i j,
      anchorChartCovRicciEntryFlow gt x t z a i j =
        T (e a) (e i) (e j) := by
    intro a i j
    simpa [T, g, y, e] using
      anchorChartCovRicciEntryFlow_eq_covTensor2DerivAt_zone
        gt x t hz hχone a i j
  have hLinearSum (R : E →ₗ[ℝ] ℝ) (q : E) :
      (∑ r, b.coord r q * R (b r)) = R q := by
    calc
      (∑ r, b.coord r q * R (b r)) =
          ∑ r, R (b.coord r q • b r) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [map_smul]
            rfl
      _ = R (∑ r, b.coord r q • b r) := by rw [map_sum]
      _ = R q := by
        change R (∑ r, (b.repr q) r • b r) = R q
        rw [b.sum_repr]
  have hThird : ∀ v w q : E,
      (∑ l, b.coord l q * T (e v) (e w) (e (b l))) =
        T (e v) (e w) (e q) := by
    intro v w q
    simpa using
      hLinearSum (((T (e v)) (e w)).comp e.toLinearEquiv.toLinearMap) q
  have hMiddle : ∀ v q w : E,
      (∑ k, b.coord k q * T (e v) (e (b k)) (e w)) =
        T (e v) (e q) (e w) := by
    intro v q w
    simpa using
      hLinearSum (((T (e v)).flip (e w)).comp e.toLinearEquiv.toLinearMap) q
  have hFirst : ∀ q v w : E,
      (∑ a, b.coord a q * T (e (b a)) (e v) (e w)) =
        T (e q) (e v) (e w) := by
    intro q v w
    simpa using
      hLinearSum
        (((T.flip (e v)).flip (e w)).comp e.toLinearEquiv.toLinearMap) q
  have hTriple : ∀ a i j,
      (∑ b', ∑ k, ∑ l,
        b.coord b' (raised a) * b.coord k (raised i) *
          b.coord l (raised j) * T (e (b b')) (e (b k)) (e (b l))) =
        T (e (raised a)) (e (raised i)) (e (raised j)) := by
    intro a i j
    calc
      (∑ b', ∑ k, ∑ l,
          b.coord b' (raised a) * b.coord k (raised i) *
            b.coord l (raised j) * T (e (b b')) (e (b k)) (e (b l))) =
          ∑ b', b.coord b' (raised a) *
            (∑ k, b.coord k (raised i) *
              (∑ l, b.coord l (raised j) *
                T (e (b b')) (e (b k)) (e (b l)))) := by
            simp [Finset.mul_sum, mul_assoc]
      _ = ∑ b', b.coord b' (raised a) *
            (∑ k, b.coord k (raised i) *
              T (e (b b')) (e (b k)) (e (raised j))) := by
            apply Finset.sum_congr rfl
            intro b' _
            apply congrArg
            apply Finset.sum_congr rfl
            intro k _
            rw [hThird (b b') (b k) (raised j)]
      _ = ∑ b', b.coord b' (raised a) *
            T (e (b b')) (e (raised i)) (e (raised j)) := by
            apply Finset.sum_congr rfl
            intro b' _
            rw [hMiddle (b b') (raised i) (raised j)]
      _ = T (e (raised a)) (e (raised i)) (e (raised j)) :=
        hFirst (raised a) (raised i) (raised j)
  calc
    anchorChartCovRicciNormSqFlow gt x t z =
        ∑ a, ∑ i, ∑ j,
          (∑ b', ∑ k, ∑ l,
            b.coord b' (raised a) * b.coord k (raised i) *
              b.coord l (raised j) *
                T (e (b b')) (e (b k)) (e (b l))) *
            T (e (b a)) (e (b i)) (e (b j)) := by
      unfold anchorChartCovRicciNormSqFlow
      dsimp only
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b' _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      rw [hInv a b', hInv i k, hInv j l,
        hEntry (b b') (b k) (b l), hEntry (b a) (b i) (b j)]
    _ = ∑ a, ∑ i, ∑ j,
        T (e (raised a)) (e (raised i)) (e (raised j)) *
          T (e (b a)) (e (b i)) (e (b j)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hTriple a i j]
    _ = ∑ a, ∑ i, ∑ j,
        covTensor2DerivAt g (ricciVariationField g) y
            (metricDualVectorAt g y (B.coord a))
            (metricDualVectorAt g y (B.coord i))
            (metricDualVectorAt g y (B.coord j)) *
          covTensor2DerivAt g (ricciVariationField g) y
            (B a) (B i) (B j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← hRaised a, ← hRaised i, ← hRaised j,
        hBasis a, hBasis i, hBasis j]
      rfl
    _ = covRicciNormSqAt g y :=
      (ClosedSmoothRiemannianMetric.covRicciNormSqAt_eq_basis_sum
        (g := g) (x := y) B).symm
    _ = covRicciNormSqAt (gt t) ((extChartAt I x).symm z) := rfl

/-- Joint `C³` metric entries give genuine joint space-time continuity of
the intrinsic squared covariant Ricci norm. -/
theorem continuousAt_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    {t₀ : ℝ} {x : M}
    (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
    ContinuousAt
      (fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2) (t₀, x) := by
  let oneLocus : Set E :=
    {z | ∀ᶠ z' in nhds z,
      GeodesicTransport.cutoff (n := n) x z' = 1}
  have hopen : IsOpen oneLocus := isOpen_setOf_eventually_nhds
  have hone_mem : oneLocus ∈ nhds (extChartAt I x x) := by
    apply hopen.mem_nhds
    simpa [oneLocus] using
      (GeodesicTransport.cutoff_eventuallyEq_one (n := n) x)
  have hchart :
      ContinuousAt (fun p : ℝ × M ↦ extChartAt I x p.2) (t₀, x) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ p.2)
      (g := fun y : M ↦ extChartAt I x y)
      (x := (t₀, x)) (continuousAt_extChartAt x) continuousAt_snd
  have hchartPair :
      ContinuousAt
        (fun p : ℝ × M ↦ (p.1, extChartAt I x p.2)) (t₀, x) :=
    continuousAt_fst.prodMk hchart
  have hcoord :
      ContinuousAt
        (Function.uncurry (anchorChartCovRicciNormSqFlow gt x))
        (t₀, extChartAt I x x) :=
    anchorChartCovRicciNormSqFlow_continuousAt_of_metricEntries hJoint
  have hchartNorm :
      ContinuousAt
        (fun p : ℝ × M ↦
          anchorChartCovRicciNormSqFlow gt x p.1 (extChartAt I x p.2))
        (t₀, x) :=
    ContinuousAt.comp'
      (f := fun p : ℝ × M ↦ (p.1, extChartAt I x p.2))
      (g := Function.uncurry (anchorChartCovRicciNormSqFlow gt x))
      (x := (t₀, x)) hcoord hchartPair
  have hsource :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        p.2 ∈ (extChartAt I x).source :=
    continuousAt_snd.eventually (extChartAt_source_mem_nhds x)
  have hone :
      ∀ᶠ p : ℝ × M in nhds (t₀, x),
        extChartAt I x p.2 ∈ oneLocus :=
    hchart.eventually hone_mem
  have hEq :
      (fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2)
        =ᶠ[nhds (t₀, x)]
      (fun p : ℝ × M ↦
        anchorChartCovRicciNormSqFlow gt x p.1 (extChartAt I x p.2)) := by
    filter_upwards [hsource, hone] with p hpSource hpOne
    have hz : extChartAt I x p.2 ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source hpSource
    have hχone :
        ∀ᶠ z' in nhds (extChartAt I x p.2),
          GeodesicTransport.cutoff (n := n) x z' = 1 := by
      simpa only [oneLocus] using hpOne
    symm
    calc
      anchorChartCovRicciNormSqFlow gt x p.1 (extChartAt I x p.2) =
          covRicciNormSqAt (gt p.1)
            ((extChartAt I x).symm (extChartAt I x p.2)) :=
        anchorChartCovRicciNormSqFlow_eq_covRicciNormSqAt_zone
          gt x p.1 hz hχone
      _ = covRicciNormSqAt (gt p.1) p.2 := by
        rw [(extChartAt I x).left_inv hpSource]
  exact hchartNorm.congr_of_eventuallyEq hEq

/-- Global joint `C³` metric-entry regularity makes the intrinsic squared
covariant Ricci norm jointly continuous in real time and space. -/
theorem continuous_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
    {gt : ℝ → ClosedSmoothRiemannianMetric n M}
    (hJoint : ∀ t : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3) :
    Continuous (fun p : ℝ × M ↦ covRicciNormSqAt (gt p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  exact
    continuousAt_covRicciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
      (hJoint t x)

end Poincare
