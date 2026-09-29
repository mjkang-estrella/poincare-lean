# Core objective and proof consumers

Central objective: `Poincare.UniversalHamiltonConvergenceStatement`, equivalently universal positive-Einstein existence on the exact closed simply-connected smooth3 context. It remains unproved. The other universal assumption, `Poincare.ExistsSmoothabilitySmoothManifoldStatement`, also remains unproved.

Selected first input construction: `Nonempty (ClosedSmoothRiemannianMetric 3 M)` for every compact Hausdorff smooth3M. This supplies an actual initial metric without any curvature or recognition assumption. The next construction to use it is generic `ClosedRicciFlowNormalization.regularRicciFlowGoal g0` / `RicciDeTurckShortTimeExistence3 M`. Local existence alone does not imply global smooth normalized convergence for arbitrary g0: singularities, surgery/topology reconstruction and favorable-metric production remain substantive steps. A round-metric pullback cannot be used until a suitable smooth sphere identification is independently proved.

The non-circular construction route starts from charts and a positive symmetric fiber cone, constructs a smooth section by the existing partition-of-unity gluing theorem, proves its unit balls bounded in finite-dimensional fibers, and fills all five fields of the actual smooth metric. The global witness must be produced from the stated topological/smooth hypotheses alone; supplied metrics, sphere recognition, positive Ricci or compact smooth-limit realization may not be used.

Two independent helper tasks feed the concrete `SmoothInitialMetricExistence.exists_initial_metric` proof. Local pullback supplies actual symmetric positive smooth local sections. Positive-cone supplies convexity and bounded unit balls. The root existence proof must invoke these verified helpers in Mathlib's constructive smooth-section gluing theorem, not assume a global section.


## Exact source excerpt Poincare/Global/RiemannianContext.lean:26-46

```lean
universe u
namespace Poincare

/-- The model vector space for a boundaryless smooth `n`-manifold. -/
abbrev ClosedSmoothModel (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n)

/-- The model-with-corners used for boundaryless smooth `n`-manifolds. -/
abbrev closedSmoothModelWithCorners (n : ℕ) :
    ModelWithCorners ℝ (ClosedSmoothModel n) (ClosedSmoothModel n) :=
  𝓡 n

/--
A smooth Riemannian metric on the tangent bundle of a smooth `n`-manifold.

This is the single non-typeclass metric variable used by the project context.
All Mathlib bundle and distance typeclasses below are derived from this data.
-/
abbrev ClosedSmoothRiemannianMetric (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M] :=
```

## Exact source excerpt .lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean:227-254

```lean
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n n' : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

variable (IB n F E) in
/-- A family of inner product space structures on the fibers of a fiber bundle, defining the same
topology as the already existing one, and varying continuously with the base point. See also
`ContinuousRiemannianMetric` for a continuous version.

This structure is used through `RiemannianBundle` for typeclass inference, to register the inner
product space structure on the fibers without creating diamonds. -/
structure ContMDiffRiemannianMetric where
  /-- The scalar product along the fibers of the bundle. -/
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

/-- A smooth Riemannian metric defines in particular a continuous Riemannian metric. -/
def ContMDiffRiemannianMetric.toContinuousRiemannianMetric
```

## Exact source excerpt .lake/packages/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean:587-643

```lean

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : ℕ∞}

/-- Let `V` be a vector bundle over a σ-compact Hausdorff finite-dimensional topological manifold
`M`. Let `t : M → Set (V x)` be a family of convex sets in the fibers of `V`.
Suppose that for each point `x₀ : M` there exists a neighborhood `U_x₀` of `x₀` and a local
section `s_loc : M → V x` such that `s_loc` is $C^n$ smooth on `U_x₀` (when viewed as a map to
the total space of the bundle) and `s_loc y ∈ t y` for all `y ∈ U_x₀`.
Then there exists a global $C^n$ smooth section `s : Cₛ^n⟮I_M; F_fiber, V⟯` such that
`s x ∈ t x` for all `x : M`.
-/
theorem exists_contMDiffSection_forall_mem_convex_of_local
    {F_fiber : Type*} [NormedAddCommGroup F_fiber] [NormedSpace ℝ F_fiber]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F_fiber V)] [FiberBundle F_fiber V] [VectorBundle ℝ F_fiber V]
    (t : ∀ x, Set (V x)) (ht_conv : ∀ x, Convex ℝ (t x))
    (Hloc :
      ∀ x₀ : M, ∃ U_x₀ ∈ 𝓝 x₀, ∃ (s_loc : (x : M) → V x),
        (CMDiff[U_x₀] n (T% s_loc)) ∧ (∀ y ∈ U_x₀, s_loc y ∈ t y)) :
    ∃ s : Cₛ^n⟮I; F_fiber, V⟯, ∀ x : M, s x ∈ t x := by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ ⊆ ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_iff_mem_nhds.mpr (h_nhds x_pt)⟩
  -- Obtain a smooth partition of unity subordinate to this open cover.
  obtain ⟨ρ, hρU⟩ : ∃ ρ : SmoothPartitionOfUnity M I M univ, ρ.IsSubordinate U :=
    SmoothPartitionOfUnity.exists_isSubordinate
      I isClosed_univ U (fun x ↦ isOpen_interior) hU_covers_univ
  -- Define the global section `s` by taking a weighted sum of the local sections.
  let s x : V x := ∑ᶠ j, (ρ j x) • s_loc j x
  -- Prove that `s`, when viewed as a map to the total space, is smooth.
  have (j : M) : CMDiff n (T% (fun x ↦ (ρ j x) • (s_loc j x))) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_ isOpen_interior (hρU j)
      ((s_smooth j).mono interior_subset)
    exact ((ρ j).contMDiff).of_le (sup_eq_left.mp rfl) |>.contMDiffOn
  have hs : CMDiff n (T% s) := by
    apply ContMDiff.finsum_section_of_locallyFinite ?_ this
    -- Future: can grind do this?
    apply ρ.locallyFinite.subset fun i x hx ↦ ?_
    rw [support]
    rw [mem_setOf_eq] at hx ⊢
    exact left_ne_zero_of_smul hx
  -- Construct the smooth section and prove it lies in the convex sets `t x`.
  refine ⟨⟨s, hs⟩, fun x ↦ ?_⟩
  apply (ht_conv x).finsum_mem (ρ.nonneg · x) (ρ.sum_eq_one (mem_univ x))
  intro j h_ρjx_ne_zero
  have h_x_in_tsupport_ρj : x ∈ tsupport (ρ j) := subset_closure (mem_support.mpr h_ρjx_ne_zero)
  have h_x_in_Umap_j : x ∈ W j := interior_subset (hρU j h_x_in_tsupport_ρj)
  exact h_mem_t j x h_x_in_Umap_j

@[deprecated (since := "2025-12-17")]
alias exists_contMDiffOn_section_forall_mem_convex_of_local :=
```

## Exact source excerpt .lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Basic.lean:513-550

```lean
  rw [e.contMDiffWithinAt_iff]
  · change ContMDiffWithinAt IB IB n id a x₀ ∧ _ ↔ _
    simp [contMDiffWithinAt_id]
  · rwa [mem_source]

/-- Smoothness of a `C^n` section at `x₀` can be determined
using any trivialisation whose `baseSet` contains `x₀`. -/
theorem contMDiffAt_section_iff {s : ∀ x, E x} {x₀ : B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (hx₀ : x₀ ∈ e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact e.contMDiffWithinAt_section univ hx₀

/-- Smoothness of a `C^n` section on `s` can be determined
using any trivialisation whose `baseSet` contains `s`. -/
theorem contMDiffOn_section_iff {s : ∀ x, E x} {a : Set B}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] (ha : IsOpen a) (ha' : a ⊆ e.baseSet) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) a ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) a := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩ <;>
  have := (h x hx).contMDiffAt <| ha.mem_nhds hx
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mp this).contMDiffWithinAt
  · exact ((e.contMDiffAt_section_iff (ha' hx)).mpr this).contMDiffWithinAt

/-- For any trivialization `e`, the smoothness of a `C^n` section on `e.baseSet`
can be determined using `e`. -/
theorem contMDiffOn_section_baseSet_iff {s : ∀ x, E x}
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B))
    [MemTrivializationAtlas e] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, s x⟩).2) e.baseSet :=
  e.contMDiffOn_section_iff e.open_baseSet subset_rfl

end Bundle.Trivialization

```

## Exact source excerpt .lake/packages/mathlib/Mathlib/Topology/VectorBundle/Basic.lean:393-431

```lean
    [Trivialization.IsLinear R e] {b : B} (hb : b ∈ e.baseSet) (y : E b) :
    (continuousLinearMapAt R e b) y = (e ⟨b, y⟩).2 := by
  simp [coe_linearMapAt_of_mem e hb]

/-- Backwards map of `Bundle.Trivialization.continuousLinearEquivAt`, defined everywhere. -/
@[simps -fullyApplied apply]
def symmL (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : F →L[R] E b :=
  { e.symmₗ R b with
    toFun := e.symm b -- given explicitly to help `simps`
    cont := by
      by_cases hb : b ∈ e.baseSet
      · rw [(FiberBundle.totalSpaceMk_isInducing F E b).continuous_iff]
        exact e.continuousOn_symm.comp_continuous (.prodMk_right _) fun x ↦
          mk_mem_prod hb (mem_univ x)
      · refine continuous_zero.congr fun x => (e.symm_apply_of_notMem hb x).symm }

variable {R}

theorem symmL_continuousLinearMapAt (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : E b) : e.symmL R b (e.continuousLinearMapAt R b y) = y :=
  e.symmₗ_linearMapAt hb y

theorem continuousLinearMapAt_symmL (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∈ e.baseSet) (y : F) : e.continuousLinearMapAt R b (e.symmL R b y) = y :=
  e.linearMapAt_symmₗ hb y

variable (R) in
/-- In a vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
@[simps -fullyApplied apply symm_apply]
def continuousLinearEquivAt (e : Trivialization F (π F E)) [e.IsLinear R] (b : B)
    (hb : b ∈ e.baseSet) : E b ≃L[R] F :=
  { e.toPretrivialization.linearEquivAt R b hb with
    toFun := fun y => (e ⟨b, y⟩).2 -- given explicitly to help `simps`
    invFun := e.symm b -- given explicitly to help `simps`
    continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd
    continuous_invFun := (e.symmL R b).continuous }

```

## Exact source excerpt .lake/packages/mathlib/Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean:199-232

```lean

theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H p.1) ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl

```

## Exact source excerpt Poincare/Global/RoundSphereMetric.lean:44-58

```lean
    ((↑) : RoundSphere3 → RoundSphereAmbient4) x

/-- Pointwise pullback of the ambient inner product along the inclusion derivative. -/
noncomputable def roundSphereMetric3_inner (x : RoundSphere3) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ :=
  let A : TangentSpace (𝓡 3) x →L[ℝ] RoundSphereAmbient4 :=
    roundSphereMetric3_inclusionDeriv x
  ((ContinuousLinearMap.precomp (𝕜₁ := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (G := ℝ) A).comp (innerSL ℝ (E := RoundSphereAmbient4))).comp A

theorem roundSphereMetric3_inner_apply (x : RoundSphere3)
    (v w : TangentSpace (𝓡 3) x) :
    roundSphereMetric3_inner x v w =
      inner ℝ (roundSphereMetric3_inclusionDeriv x v)
        (roundSphereMetric3_inclusionDeriv x w) := by
```

## Exact source excerpt Poincare/Global/RoundSphereMetric.lean:90-117

```lean
  exact hv ((mfderiv_coe_sphere_injective (n := 3) (E := RoundSphereAmbient4) x) hA0)

theorem roundSphereMetric3_inner_isVonNBounded (x : RoundSphere3) :
    IsVonNBounded ℝ
      {v : TangentSpace (𝓡 3) x | roundSphereMetric3_inner x v v < 1} := by
  letI : NormedAddCommGroup (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 3)))
  letI : NormedSpace ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 3)))
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
  let A : TangentSpace (𝓡 3) x →L[ℝ] RoundSphereAmbient4 :=
    roundSphereMetric3_inclusionDeriv x
  have hAinj : Function.Injective A :=
    mfderiv_coe_sphere_injective (n := 3) (E := RoundSphereAmbient4) x
  obtain ⟨K, _hKpos, hK⟩ :=
    (A : TangentSpace (𝓡 3) x →ₗ[ℝ] RoundSphereAmbient4).injective_iff_antilipschitz.mp hAinj
  have hbounded_preimage : Bornology.IsBounded (A ⁻¹' Metric.ball (0 : RoundSphereAmbient4) 1) :=
    hK.isBounded_preimage Metric.isBounded_ball
  refine NormedSpace.isVonNBounded_of_isBounded ℝ
    (hbounded_preimage.subset ?_)
  intro v hv
  rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
  have hv' : inner ℝ (A v) (A v) < 1 := by
    simpa [A, roundSphereMetric3_inner_apply] using hv
  rw [← sq_lt_one_iff₀ (norm_nonneg _)]
  simpa [real_inner_self_eq_norm_sq] using hv'

```

## Exact source excerpt Poincare/Global/ClosedRicciFlowNormalization.lean:24-44

```lean
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [SecondCountableTopology M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

def normalizedFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧ ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x

def regularRicciFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
    gt 0 = g₀ ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, IsClosedRicciFlowSolutionAt gt t x) ∧
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M, MetricEntriesJointContDiffAt gt t x 3

def normalizationGoal : Prop :=
  (∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) →
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀

end Manifold
```

## Exact source excerpt Poincare/Global/DeTurck.lean:145-182

```lean
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

local notation "I3" => closedSmoothModelWithCorners 3
local notation "TM3" => (TangentSpace I3 : M → Type _)

/--
Hamilton-DeTurck short-time existence for the closed three-dimensional global
vocabulary: every initial metric admits a positive-time Ricci-DeTurck metric
family and DeTurck vector-field family.
-/
def RicciDeTurckShortTimeExistence3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ g₀ : ClosedSmoothRiemannianMetric 3 M,
    ∃ T : ℝ, 0 < T ∧
      ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
        ∃ Wt : ℝ → ∀ y : M,
          TangentSpace (closedSmoothModelWithCorners 3) y,
          gt 0 = g₀ ∧
            ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
              IsClosedRicciDeTurckSolutionAt gt Wt t x

/--
The gauge-pullback wall: a short-time Ricci-DeTurck family produces a
short-time Ricci-flow family with the same initial metric and interval.
-/
def DeTurckPullbackToRicciFlow3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ (g₀ : ClosedSmoothRiemannianMetric 3 M) {T : ℝ}
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    {Wt : ℝ → ∀ y : M,
      TangentSpace (closedSmoothModelWithCorners 3) y},
```
